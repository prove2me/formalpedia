-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4462
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:41:43.206166+00:00
-- url     : https://prove2.me/submissions/c5cf9b8d-4b3a-4616-9ed5-dc5bc1818f0d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 802338129 ≤ n < 802517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 802339379 1250 802338129 802338149
    0x612091516050c071d06090714042303070303020f0c0a0b030718030b0f0609012106050619080a03030e0d1b08070204140f1815070e1c03021501 63
    0x2600520781c802d9015000601054080d940c40710398501d6401c400c000d45098603058000e00741c04008407450700c0c030f4480398800360600300314811000c00b0503c40001d21460080c0780400104a00d01301c2407081c0d191084103014409070448000c02c0c0c590602030b6881150030701c00300580c8600344004c202030400380b0890080307030f0303103c0d000c03c1c01c41d00d88203c2902c4451000b01440b48036400381100201191041c80000d00940d0300100da4503c6090050034090108016004020303551000840d80c1d840c44602031021784190b400040000f4240c5540d400141d8041150a880d84980c51079080450f210710045107910300c451190300d080003076400340b035085515500c0c6482c0450200c0d80e64514106015000000503401034450402d140ca00b1886038005400c0ba00100111410750008608010944000480c0140c200c41d4020a43c2a20b041c41a02c080ea586216825000500400e001050001d400707a0b1401d00342010040c44101c408010041e0494500c48030346042d80184900c4004c8480c410f04448658107271811006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 802340629 1250 802339379 802339411
    0x10510090323030f040906051c0605101502010204090506042007050709110a020d230c030c060f0415060608070f0e130f05061c1e0206120915 62
    0x100c07640d00801d150b014038086500040e1a01954800340300400911021150580e250381c141000f210849156070030081c05100e2820017541e41d00443c000c03130646154000030114095544015001e001c030980c4c0d21500c4c194607a44a080c5000d03406401900664038043ca04114940d1000c00308410740d28615242d060f102508606900350b144003800524915010700d00300d9008960f14070607801106d0010140d09400301c0d002c90144065030341440381583d488001d2800e6a901c034003450000c0c2e0b0881000203104055180003854851881040c42607440c02058101901c2c131500d898500d40840200c200c0d003c4401800c52483c036400d00c0b180b0b1041e030050b28043c0c0c0c1c1d0350103103640b043c2d0191000807103140035009121040980b8800d9544140bc611800009035101003000401d603031004c010f4030b6018025600c0307014011040c007040096000301d844031603080450803891911115800703841140f000d0707001c0d4101c1ca0001c0c0fa078403501c0d101e1401750f000381e4491044940340012203101c85404c81094030030003120001d80e4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 802341879 1250 802340629 802340633
    0x111303150b09040b330f04090b0105060d1503230303091005090102090a0602071a0c280507060816050a0c0201050a0e031c0215090c010c0f060905060406050105100903 73
    0x154842d5101c00307651503101744426001c1c414100c400109180310310030803c005292009003000d00a02c02043c40c195000e01c020810360369100304401c014094076004a1020407510400940c81d0000d0740134850106038440c0446d107a061a008000d903200700d01c0c3d404c0019191491303c6a2000003228030800481c409866411105d003c0140071748809042c6020541d000e00191004d6075590701c140008002c1d0b50000d05116141284280385218141c009100200d402c0c044018502404900c0c1900000070300081d1380c3c1810a003028061343e4404010180183c420700c1008160690000d440314091016130306003820341c0700401000c903018450741c92070800107070704410a00015401080038081e598100d0402004500d20440460300e0452001d03034842c00072440310b10a98109030184180c0408140710381c840c1c8854906000d0141d542c03611a2805410071800003200c0703091140320740b049418140d02039424030504055040035070740d42100b0785007502c02c540342000015071407410020101074a0415120301039220300e19 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 802343129 1250 802341879 802341893
    0x4151112090d051014160e1c0503030f060f060304030c061d0d031d1507110c0904030e1009060c15060e0f0106081027111303150b0904 59
    0x241156074024840c000350900045041c052816440b40300540012803c0300385e83c1c003180f0440041c045001103456016258252940400010030107607003910401c207921844200d241981007221000f800c0d44c040070081c003000f80354066441d80904000c0301d404c0240300300101000001d101c2510002c01180c001a1108001602c5070860340c018003208000d1101011040301c145e00f0808030b0000580060354944428200001160046103c1e151020060881c04c0300c00103050007207c0c01602c00d0040c08101e01062000e03031010800458000f40241252003a03003007030326010b45540785015185100c0d00b4581e929400e038a01c00c0002004a5040d076543d908080043d0301ca299080210195122100e41c4514020402803240c0009500482c050480380c0542c2d0f00d0705030002d1800c503024158000d580103880c81003000c0c0710240722103082c00c41890011040c03c0c2e034007507038080100554200d8903803c180120740c804040c20220860070480b0700035080078084801c80c0c148101200e400b403c20035800f80f0400046000b2a8031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 802344379 1250 802343129 802343137
    0x140102160e0702160b040612060609120f0f030c1412180f0d030c0218040209191b18080a0f03031e0614011d010903060b010c080304050304151112 64
    0x6401500c48010700200354080b41e001355080707a480c0c031a0000301084006d5011841082000e5880710800c042d40c1404002010404248900340c90a0003c4500c0c40510070f81684071144075600040c4041c2004c0b244c035028049601c9036805840180588440b05d107084000304a00c02540f001d90313440c030f191100c0305c5004507003568072a151a404c20060200100c050b280c914044584a000381c03140c0b03490703495900c1000b0820108032a04590b16207103206110050721000c0b80b441e000105c0b40c80c006201c2e00c141031500b009006a007119852100d035940e21914894100c0c4005549255036682c69408684516100e40d461104500080415000001c45000310744280d20200103256069498604041c982d00c4a409403510790704281030620071810010b58035070304828051880c1e82805041c10b07407035140c0c00001e000f2051600c8007800301525499400411707803041c2c101c00042d9611100098890409007809540d0350010701640c50a0f6411034003a0300b080c2c1c001c90442900c602103800810404420f81000342203900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 802345629 1250 802344379 802344391
    0x10f1106010b2b0f150b070303110c030307030b042007060207080415030e0d2f07080d080405010c080c03010b0901090b0a0507021014040b0306060c03030709140102160e 74
    0xe0f101c001c0d00044102d421200c0452032001c0010401d0201c000201e4102d40c00c08010112150160000700401c030151030940f0141501410009070f05120a074500405105641002c0c1c0b807400000200310041c0d4155004c401803400a0f0ba017000a00d640c2a60a040c071801001d019504240c1442800e0000318503800401c202c6114441300303810a942e41070f45100b84485e920000c000310b5251041c2c0c0c1140380c42041842001c1407149031200280b5995401c540d82c8052502040b00812400007220314440400c003c400c00038295082128030007000001f00604800d4117541c01c5a0f01c3d4204210700b02e03410b1041815a0080d540b041c0e0f064071b141d20380320002c0082d034031111100b4103201202400180034010040034154001c090b450b050382d01d100c1e500c10007489080403040c420601a862814006405e240c209a405171000160140d50301e440b40d5000615a02460b884114030b40320000c00c0111842c1d02072203090031510792808804000f1a500016a2509010b410540c1c03035030303010507040000040c2c0c18030103030300b00c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 802346879 1250 802345629 802345657
    0xd050402040e160e0a0b011d0d0c0605040815010e160309020d08031909031218080705071a0f090103110c0105070f1b050d05130b0408010b010f1106010b 67
    0x92507182000741041400350b4100040c80c81100304004500b03108903629400122460208542020140040c048d4080080f820441c2c0f8001c1c01c190509450315081080740a0304085c101c0c0c1019994440244982d0160089101c0d9004144800c150b40b4502d2040a041e200800c2900d04156241040907e41040c01722044082545a80315400581c485a5440460b180600e200d180c3d41c2c0f9018801c5407907044180d00da2007103d4501440d041c00301c0e6222080d8500e0ba4081d403008909000703000480004102d0209010f8a001c0c0001240d504001c40014100102d450004140101c03220004442010b4041c00286101c000304c00c000d404107561203984010010b082240705d06e410104112007407070031a01c04440b004003064002441e09034103034108448483c0800007140c1c580b41c0703c800b0713581c19031100c071044194410700102082c818054510b401d080b801400c480c6038500e844543d0355241601034020700364164080345044011446c19449800ca100901c030a84008288030f0b440c103102c00d4682d9204021080030b032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 802348129 1250 802346879 802346891
    0x60f021c0e130501060e310c141b01060509010b0f28031508030a0512070923091b031311040e0a0209100e01181b03021209120d05040204 60
    0x4042c4038499207002c0e280750381e50502844039960900ca16a001014911046941f1000c1006480350200220000d011f0004000c0f0301c00800b54000c4d5400c01540714021084440440c00b10000e01101c4110f98030082100000c0c001c188ea20320a21141000a0141040f444010441c3e81c1c00e079840440100410040c1d80004481e2280d881d001580c800300048400001030344682009424110218244000d00400d01c040d524107815480050024800c448403a822074100100084101e4010070040c1c0c011f10750020701c0610314072076141c07440da488000308000c0e01c1248400003141d00c0303c000c10403004503519803070542d038a543c54101c21010315064410017207030050010100141c054130365006171104c452008004088a8020f0300c104401c039400101001d2f401038810500704141900150800e044642490240440140618600d0050200102d01c1c14900c2e00c86002c120190740c1c0340d401441c6981c0c000000150079141c00a9040c2c403035034049061219100c003400359200b000391640c40103030070620007071000400c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 802349379 1250 802348129 802348159
    0x80a03030b010e0d0f11040605130b0a030804060203040305010c0503010f0905062e1409061b07030b04080405310b010c0b0103140f1603080702030f0115060f021c0e 72
    0x10925131001c0c2180c0d03140031522044100102c461244101c1e1034111824403925003020081410421040b1941e038a45403581d82c1da000c01d44407014a10040c40d04481181e03601d94441c500a507582e8011310040343c0e29072030310403603030641c0c3e03ca0400d6905903000c000c42e000031103262485000181c14080c003c03070390050306941c200c0074201101c00d070305403107003490704400300341c403007615000b42c508280c8130b6211170380a0080052240c595101e6003110700d92012440c60480d810710201c059450021a0303000180060080700c20703c41409150406002160422103440305840400822f1203000303c0070350a20800c44c007154640503405402c035009002d16503c103252400010302c20f034a81000b912400e900565105560348068400e1040501c051280140058000c0940c400d00503800800300b06284805000104c1c081410000c55070300b8000c1c0d0300140d1494009000d0840701e400d0142032012140700b03040119a8084240705102e001107071030325131807014900c00401c10a09000a40792004460010303507009042c940c1e1415 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 802350629 1250 802349379 802349389
    0x605030c0c1006050f03010624140304110418021f0201021e030f100807030b060d0605090d08060d05100c0516030c0611030906131401090305070c0906080a03030b010e 73
    0x160b00051035000f180f4545418240320800003c6010540241d05066040c003100c0c108803c648103941c10302e0b42c4100d4441c003610085610008451a40b5642e800000034002804135800e00200101000c84d01000361506500d18a100300450f940029004812420148280c4510407000c0400b0809400090b240840e0782155a840000031200a104540084203000980b4040b101d001c1d84a00d2200e4007255482c10f042c811075503030915200c024802414031000506503210510320041e034075405401444942000008113440d80c40002c01440061403240014441d0b15014040718071a58210015195041d00041900050036000c06c040741400310030003090542014200030345114501235960508140c0c802d14107141514030141060080d141d003803040c00000940800c0c0944c0007504007244038111103644c6004660301c6140015402194070744420f807400c0c1030300708005044042c4592407911301552282c43d0002180c0c0c02d4010304005901899034000068085c2d4041e030706803030301410040ba01e1078440c40020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 802351879 1250 802350629 802350643
    0x30f020c060703090801050c03040f080c07181d24150604080f120406080f04060f0e0a020306090d0917072102010e01020604151e0203010b0901110708070605030c0c 72
    0x90000301c4450b81040640020b1094941080200c08102c0c89e5052544038201c006d10381c410003501d81c4000142d01c440c0300c00204400c030000c1c1000c18000c13184100120f00c400c0103108001c4028400803000480c211074801c0440c1081c0001c40b61842d118200540e4591030328003c3c0001c007010120070b1291a40e82503a03481300b000d8401820003a009129619001c3c0c6201e0400f404c600c3c6a4822000501050200d1908541c215510610f001d99604044d0740700e0500c18068208180314515192a05050140000300030071490003450007076089600684615140300c2c0c1c0d441c0c460444000084a100048c0f00000d54540c0d00d1003200e46445c1107844541d107035600107a400c0d850074903544100c0207540a05086580141640182d044240082c0c0050325054503590f00d0118411440707888150380740c560003030b14002c0c0c0b1700d40007600c24450421074032503071104008010f03580b14407000c80c0410780007682805010400115030b02610f03004006882010700e07101003038456400140c100c80c80742405208240104000f00012 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 802353129 1250 802351879 802351883
    0xc0307050703120e030a0311010b1305060406050603090a02040209011e0f141c150b07050607030e060405030405060f1b0d1d01091401020708070905090706050304030c030f020c0607 79
    0x1820803249186042d202c61003000701d44109001c0c030703613004540c0385e41d000c00d00c50388150b00b5050403070448505001c0766005148501c1c0740b80d0b0140805032618864407480c2e028038450b0809a400308091611340d8204000303800101c1d002001548620300c0074005080c81c2c2c001e00324101c41814034000301c1c00052012000c3c015400d050100143c0b00840d01e0034855440320f0503114201000c00301a250040b4035000300c4081c20700d100782412943e20b4101181c082100d160b1408001d103c20400e80d03803a01003c2c070705203417290029201d0f540000c1c18124010000c2c0004a41c982c05503074031000031442d0510f080300380005034000e40c5415036500f906000401961400c0119490f4058100020708400301e81d0200181c00c0f00e00d10050341178200018001c01402d41d0300030005000795200c40303001c100b2100c00400101c4c5032080517005803d040c010100001210401500118001d91564064509036a00c6010440e9240003c0701c000c0d0000700d441c100c03400845c1c0514804115211544141c9030f00304002c201060312a4060101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 802354379 1250 802353129 802353133
    0x40902032b092106110f04090e0c18220c12020306180a020909071a13060810050616020406080f06010503120f03072a12090315020a050c030705 63
    0x9070300007181d1200c000009005500307515046451864003024006000305002070900e59513180c49115009040d00f601c1c0071100d42c0660664071034807100e04102811041c041c1000754072440300712582c2450040800d0300c603841c0c1f10348462515070b54448040c081c14450071049030040010007660001c1091602d40001410640b00b081513901250701c18949403940c000c00c0a00c0119807010100d02d000d6001c00d00c0346c803254044030034048984554856904011960780072b03c0000e04025601c03000d110f40c1c80c0c05001d480e61040b031040d042560321541990361803800c07140150202c2c1020030078000f40ca052009081d141c00036800042a666a607800b003401ca0f00980c100321519445102d034542d501d00100201030142c4025009890011000405801e1600440640d0b440e8690040002608140b0503101200904515401041c44c40e44041c0b4215074408003107003e640d13440b4800901000140a00781c5c00c02203d910907000c403603010100549500039088281040c1c1040020485c1c011410810000f400301c66004d200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 802355629 1250 802354379 802354453
    0xe0a090501080c010815040f020c03070c05190b0a030e0f1f0b0315060f06070507030b06130506090402150f04030615120503030a15240806061804090203 67
    0x101c0929009460b9480c50400040304104410510031b070980710705900056030f0102d1a04904c11400b00079004800c140341032403102080d050188054084e1110817a441514650721400d032110f00d0716911501342c00303075a4441c9010044055140d1080d4083d480c24150344064071101e03401b10300d6160914842661082d150303640451005800e0001c0d100c1e94400100c1280108034004d6682e22030200340310001e00032445a1103002004902c0d1701d80c00c0440e1607940e4010701351006145c403450700101e00441502c84500400c149007600d9500382552044ca4001d50009045120b15500d039802c00c294407041c4142200916014002c003108048030303402400103148a502c0106030301e0303501c408102c0000140da00008404041b2070b0f010001c540f0204c101d9410142c520804106c804d021080f501814007075070300c80d02114000d041010783c01d0340102c0310b9820420307a031b07940e0b440d19480b00d00400c03225000f5044506100304c3d00c0c8806104520303003a0b0144400c60307c043c0a0300c9944032590058049100e480028481c5000411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 802356879 1250 802355629 802355639
    0x705030f0606070b1609082e06150c0501050a0614280b0d0b010c080f0d0603170a27050d1a0403090e0901050c030a1805060907030209010b0a08070f0e0a090501 70
    0x880c0305c4001d40b16420003232103940c00d40c40310745010580310030f00301c1640c058140d50006551030380d07000304e4003030310588002c5260417159030030080440d010740c181603a00d5483c18020034030311451802128129003440401c0300041c0c5480c3c04002036004001c11008007201c1d506071914080d075000007200c0041100e0000103403100068035000044c0d458180001d0f0400114004c034100003011001507484440c4046001c50310341c528504010000d180350740015101c280c021075000080d454640081080020a40c1d07044102264903090040031200e013011071056051030351701448103082241d03150050900400f0440a00341c8000000320400c03a003030741d00f0750004000b4075041c0010884941095080760141e80200b0003868040c89000160001402c5c441547d9120000181c042510241d0f407008a6000f806076480e509111507142d9540c00d003803004078000c0c0240c10001503084110400d5400b40d030100c0c3c9030743c240d40d0391720281201c546240383c1e40340c402e0050f101c40c6c11080ea152046400081d05e240000001c441d4101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 802358129 1250 802356879 802356887
    0x250c03020606330904050a0f0b0f090610020715020c0a080607020307080a021c03150504090206090405060109030503040f06110609070308030717040605100e0705030f0606070b16 78
    0x10091030043c801c110032025800c100c407902941c0340007100500c2d00001c10050046080344a40d4010541c01410507040c051a08441d5100d02403001100c2020002d0301c28038028000100000c02c01c2c190b00c4401c001c0003428900704030300114075941107441610400358a410107440c1108a0503c0800182d0105500341c109041c17a03000e18019149041c002c04540c82d004e80000d64a1082c100001e0038104003280d00c8011030300810400541c105410226200c802c40e0000c005c00402440b1200c01050004107400209800c2c1031154045480e0094030b26490300032100c0c14000035040185c030755070401c6158980040429000d102a00203850b07020103c6162510b007040c02070842d0340700b422000e0107801000c14002540d2001801c81e04480d402070541c1c0d1213548400081d01d1301e400d00301e21210801c20715400c0008001c02c40d8041d92003002d500b40352025541d00d030048080d00e400120f415001043d804c202040300d540311408a181c0c030030740007005246080069951400025000e0340c00c0950f410881104072282d2b500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 802359379 1250 802358129 802358131
    0x501080c1504080a080702040e03030901150603020906090f19090209041b0c170d1503021203090a0e1306020a0e0306090c010525020d031e0504030f0308250c030206 72
    0x90441d542490f0902140035198503820320004c1c0408400a0001c00b152a1a08840310b10446242030340e80302d00d00043c0041c0039094a034401d0000c20202c40d4045911030292003902d8000300c1c0680040d0800d12003d06100004c0c143ea40603039403240d255a21042e07940c0c50140f40e900540b800c40800342e100c00071302050209880307035286001a00b00ca6810050a940e0380b0485a07500c5170f403c100d98444400648080b41502e216104c040c0704200e0810000135910070107822074400322031096414000040100200036240d000e8403035220760104000310200b00c42d9111030002e0340c10049040d028940c031251035940c07000300c1c0c0c0100f00da08082401d42000d03101a16003030041345c0d8003c1c0c00030302030030410201e580000c05030b200c0e4a9007240c2c10003203011604c104004104d2403030301c913a6010f080c41d11000010306000d4903c0407443d000001b50010680c24088940c0300c0c00986040360b9000350099080b849541c1c042d5124900103240655441c5011101c9283c0c00f04105210b841c3c6e0705076203951441001c00e040083c20120 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 802360629 1250 802359379 802359409
    0x110a021f0914090a05040204240f0f080705060703110706120c0201061a0c07050a0e010312030b0109030f050a0605012615040f033c020a05070302040507030f0501080c 73
    0x102e0081c4010b0391550300b101a8000520072001445da0340e1840014028448884000900c501401c42034116450802c0c000060700c4500440041082e0740344200c540c1203400d03000703145040c3c0119000f0443c0d810034001414001c1d20904052051060502d1840e26210b81e551101001039044000e1a2440d04030303114050415640348024050305007005240da4048804c9060309410620006c1c0811180a050060f040078040050108128a0390398240b10000b4100380800c7c2c5030510b000c5000c00400e400f03403048928090f0103848440d41e951a507201c0d88511182003000340c3d02401035122010001c0c1c210710a46020380800c03160b200501c1036840403034180304815019510070f548000031a949901c04d484c603540d4855484081e41c00c111030340307181c112140b5000724518241e40344040800c2014180302582180390101b03c54800300740400c80c4004994a161240024001d50802e2a003800035041c19000641d120115040101d14403030746140340c504a4600b6407103040c4e5904034448a8800d17240084c507a02400f2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 802361879 1250 802360629 802360649
    0x3030105010e0904030c0201110c1c1a01320907090801150f0306020c03040e040303050106020625030b040204051c06050c1e09040f020d051e0c0a110a021f09 69
    0x32600343d030054000040c00781c010b4148007080041003271071081080070b4600c030400038106034040c40e01c0319040b2000007990041141c0341c081068101c48054040e0f4a89812900300301d0002c01c1394402c0d0070003499100b200180510561403120f18441403601c031400e07402c0c003689140d5a08005285840c18090031284004003039a080440600304101c0c002901c0200c40c140c90f001240107968900301c0300842e01e140700f6907018110f60b07500d080406c824103406902c840e04844c815001c1d240141e84805280c500c18025281d20211404844420100d0074800c1d8004900c280001c3d200510705526034002039201c0124015030b05840c0040c0d6180010802c20f401002e0b005110b201c6c3c2c681c1400342d184160104024107030203012601402042e40c10855443c0d400540b034030040c45200710740c0c51426500b00c4018060480740d55400d001c800c561004202a6032058074492141189904d0509200e480c1c110b030342401c8100e80148511503000381002503a96007600f203203419006a10112081060791000e8440d0109a0000c1d80f10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 802363129 1250 802361879 802361881
    0x40210090b040918050613060b090f0a0b0a031506080f0133050607061b0c050c040b031212010e07020d0905010c060213030605070215040c06110a1403030105010e09 72
    0x58403007000303031026200e11000204a1044158140d00703602a00c080142c440e10030300c0700b80300303d1015104450704010701412080c0030b00c00490041c4000202c0c02c4d141d0030380e0500c609000404145141e80b288070350302802007048103400c0c0d0321b0b11850f07107814030354030f44020240e9600400c0102490820480220b8401b04000340203882c1c00034101032000c00842035518501500342c07641c00d0300103000d4114138040c0c08010444c075169400d90030241c009041d5a1143d030a0703008410f01e101c0005008988855100c0d9001c0d008102c5140c200342400090b0194015480d00b51003600413400e034512021015001c51500e03e00003401c0c641c9044d90b482116040a03004000790b400180140c1c55040c3d125031403101341c610a00704105405c490b441d00c10005e00ca120788407194100901c4010081019903004079019018903801c44030000031010107100040d0094400502c140c403091001c000c241c1c0a68219144079041c682078414100030313520742814200840003002c0d03041e0000001070005681040c0d0f60704c0707104070580304003040b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 802364379 1250 802363129 802363139
    0x307020d09120f031202040810050601051612210f0605120d1b0f03080702062211181e0c0a230c160e160903030c0c12080304021009 58
    0x39001d5008001c3d018a40d038003298070900d0300402030112a104000411561aa5100d024035110b0510b0042040312031701b4140812442d600c00c0003602c0714181c00c560a484008841d59a6040024942c004203051008690744100d18031480e40f0412685000d11402040e801480e40b040d0b411107030960819441101400c0001d00c403041c0010308441208040e05109500e010003040740c00101c086041c00910201400b0400010154032586550107090340b5000c0303402c99103400b01050020041014010702c0f00510070148030210f0000117603850a988083e0201d069200201503032a1141030844083c00e1000203c903840660071508101194800d0340c1402050400005c200010007000c3d4038a1020742c07407696542d40d80d030728404135812030301880c01303490441e0810b281c4507440c41880742440c899400001600000a4842d40d184085032307a100b1f030baa5440c4100b69085940598804055040039244c041c0201408189007200901044002d8050103840fa100e00c2c0907c100101031a10003600703420081140f030304007c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 802365629 1250 802364379 802364399
    0x40614040e060f13020409020a09090605010b03151c2f0f0901050906030c1207291c0212070801031b06091205011b35010909060f050405030307020d09 66
    0x500051030504100203e2245e00018000c2c1151601c0a90b00c40311150001448040b87d502003082940708510a010a0fa600c280111070f0340012146440c02c00c0341c0100c101254605802416070380c04d591a550f01c40a051619401c10f00d101e15048d60700001001040001c7c41850b45054040a000c200d842e45080142d5201050321100c041c46494000d0740c0078400b14010350307014032103050b0800c0098800410072205c074001650b940d000344a11004408444410003001c416003404402ca480f16000312450410800d4107114450021082c0e0f900c0554217009131030742c9451400d4680e02a10700c6a5502c6000e50550400118081070140442d0021003001d03005c004003500801e40404a502e1040d24020020460405034090a00d0201d1100c0c1512200c04a4001a410a0b8200456150700c04050341160403c0148050703103520602c41070030302a0710030040000c841c0540081d11254401c04011605141405c0c145042c0c5105481c00c540030340000c810454200c2d070401522030300f1602d80c500954104c0c68121121 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 802366879 1250 802365629 802365631
    0x703090e060a14010e090a050612070e0f1329070302031603050a0b0603011e15140a05041509051c020f0607051e060a060e070f030b0f040614040e060f 66
    0x1c29451105040d00da0043c0c4400c070382c17060041d00c00300e080e00d44110300d00000c0c0002c640c0144107840c6c0e400c1004ca0301a0000c0c91100340c90408200c101f003030300c6005010424180040070b8030706061454810000047d80c600c2d203608040601000140500c1480032000e40c1e418000b40444201841401004599451094102d441e0074890900003610380340d401414001c1c210340350031a0f80000300000001480e54545812007001c0000b00900e0701126240d1440c040a000604400320000f8400300c0d140c15020300000c001e00c00100141001480c1a0366168030201b601ca1098400000c98081e402c1040a424030000031541800e0440100c1500083ca50008030380a8100d84240e01803003020600a080107010000c0320075800b80b540891003400309801c00c03182d6a1908541c81020769003010b100040c5942051001801003040361504010450244402c40c000c01944520a03409003855190b184541c803a03210b528003400310318040c010704001c010b05100c01c1d120456204541940a50100102e2810072140c032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 802368129 1250 802366879 802366889
    0x140a05041511160b100602010b100f0e0409050f060a06080709021b01020705030d0c030b0a050d0611030118060f030f0201080a0f0f0203150d0b1306020c010f020703090e060a 76
    0x4454102d0b00300819180a45800500030401c82d0f40c0c00c6042c003a41202140c03080031040380c51000d0303e03100d08049007030f0348001003ca60410340000c1c1c603182c400d01445800c181f100d06072401c02400003da0300020140c404441041c0e0f8550440003541107807007000d11940740e00c4a000302041c448149000441c0e51355052520841c1001a408202255000d41030104014140c032200c00a54441c0d12600f080e6449a101c480581c11030341ca08161441154080e0040b0440c202c1e000f08210500c0e454101400fa4015070300c03204440360f0b81c0d2400805075080d81c001c0954068142090341c10f10410114032074804980e540d40200190b070307401000400000382ea03001115441603080c0b03000341031912080202000781590300f80381c1c6291800d241c2d604420b03012a074003441c440c441400d01280c031880c00400340071940d11041006001c0c65a408005014482c0c40c6202003040d5124020041c681419071070510f00b110940000e2403030b241d03000039030300f02416800f00c08240500b58079202c501840c240000010340c0c0301101c0c071503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 802369379 1250 802368129 802368131
    0x703020102101a0301060603053108030c19081005010215070c050a060606020105151c0602180d082206020c040f02070b07181415250501140a050415 65
    0x54030751020000f8201d6120100c02a0003030091507142c80d4040c028080480780a000e840403030308100c1d1070007000c10a003420040d01010840280c00c15469000095100900440307101e4810811029407007801a1500d180358866540d400c55401d001c00150340824441e07104c64110f5208525508118a118000a4015142c1c2c00c0403141d0100c1c80c42d00c00d050010a503005010b0501d401c100058030358041d0031941c4507486801010390058210030410a1580c0c142c41d142d00c0044503d8803a80c0024416070082c000fa05140721031581d07840c422400203000b505c0020f011a4085000301d1500040b40304940c020f0b2801400006034100c050820000135070f102d600c0890b2030312444d122071100000c55001e40c11541030a4102c100f48a1524081c07201402e451465408076108080f0f0801c006008400124001c1e0810b000a0081d810200c54441400258118986644503400c245a412440d44503122010100b030344100004035000c0c000b01000c07003612070000e14000d402d80c00e140400002990b64044003651000d40c41d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 802370629 1250 802369379 802369391
    0xa06050a080a0e07030203120a09090c050a080c090d03020c040c030902030d05030a090b090f0c091e040602360f01050307080714040605090f0a1d0910020d050f09070302010210 77
    0x1250b50726001541c1c1c001b1b501800761020740124030810500400c3c0b0020303a501c0c1d40d20256501d039814000c40d100c0c2c51802d00018020700c442d0030200e01c5104800c0d004451962490b061206040016030030f0000a5030443c0960f1201400c034200381407500500c840c3c14054101004a05010380101c0c0d1034400e03174402da0b41005000800940e00070b0180d8001048103800266440242c81e082000d41c0c2d8400300d031a90840700340f040b1520003c8900d02040d03200d02c02d604240c080e080c20002d0320044008440c0c0603204944442d020302c695164141041c85047c4600c1c8000381100070000480d0304284100328860709580105014440c060859030010704617a000851861300b15213983d1a00d80031100007003110080321000d0300000c2c001946030f901802070714540302c048640d40c204c05071001c10410500482e01c21046182d422480a81001406420031796001403501d00799003010401001043c00c0b64000600d40b20180e40d90404e00c07034410303c4000e401e0b5000c0071500051204500f90340010750345074000300312182940d403113103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 802371879 1250 802370629 802370651
    0x5070b0117120a1205010e091006031e050f01110a0813030914041404110109080102030108100c17040606090b1806060313021804031403130f0305040e090c0a06050a080a 74
    0xd041d90784d0b15030008000300a1035854041b041c800100648020705a4800c5144034a64100d4908c030f04002c0341c0d8172895500010782ca010f81c10f908280d00010a44460003000c90b018a00721081c029402c1640040780f100350754001915020f04a0703070340a4190740e000a202284400043e0300500c0704d0b41580c00d1140c14101c003030500b4001174094001e001c1c0010000030380304180401c1184111030804683c2098858182983d120340c07026080f03000911a4800c10f0b8803c080c4c1210419803a070102c0042c2c401843c01700014601c0d000020380d400403c0e80c0884d8401d0340e8000400403020944110100e420049407001404003c00844000a840c0a4403080c456040000071490382030710030025a10b69039020b0074110400d06200030185036030740112400d42c01700301403000c0084112880320403684900b040910b14012007025072207444800070800001c4003402410480480c0c4100f010721001c1c0700d1008070004110300c0203140140242d4400641c406401c0c404107116444409800c071014a6000c0100040003c0d070903004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 802373129 1250 802371879 802371887
    0x1202030406020405030d0305010303021c0c0f05030c060108030c1612020f2101140106081009050702072616060e09040f020409050601080706090f0b091f05070b0117120a 74
    0x50780616170600c22007051000c82509900054101c0b4000e40941da4040003207001951080a00300d0fa00d400201d82d4003c0b600010429000120740d00e004404036800c2049035242c90707182100a0304604031542c03002c01c80240004e030030080440204101100442c8903460546510060f14a9540007489442c652084a115884050203a91a01c0c03254444c420b280e0b01c0700340703182d008006040c0c40114240e080c500201d0103031302450703807107000340445150f902150b031400078500010300002e0145421030051483c0014042c05503075905400b1a0801d41c512654103524a82d03e02e8540c0c0340c2c1e1840180000307030000b00292a0440c810100000040d40c189050b9680e928020402000c0d060f8000d41c0546440103d00078824002003540c141c031010411688031544400c01074496800b60b205960601040030820301c02500024040c210f442409004032803141d8034403a030b0028040d4645003501c00200049800d0052095110705207004002c039000020f60380c03d2603a003098135000e420b0a00e05400d2000216810030601c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 802374379 1250 802373129 802373137
    0x3091401061404050105030f03041a0c07150f1103041203090b030c070b070e031207020d121d090903040317041205010501030b0708071709030403050a0b0702011506120203040602 78
    0xa04002080342903203814950386030112120b102c0e4020342c13901d0000310782c508001450f030464142c40b00046003040d2402c0010041e5034420003000c00c80000034000862817440400c044809081c1d9a80303240d80340c20960300c00501c802142456181007050b0040c90000e44580481140c060b0381403481045030040050405603400c41b51540b111010701c10000c1000008100706025041c00381c420310704a55a40c0b10100c080b6001c4501e2502ea69054002110350341d000f00e00d00c130082c61080e00c0a001d05500940545505a00724035050381000426401c034400c620510818403108000c0c0d10848180d1346905014890303507683d001d5804028407280010b01b00c10207821214082c2c0c2c004003d103c6450390300d5885c901d8030b240a4403080c0320490300c0704129404980c40c1405480064420b0009603190030700034084140f4000440320103040030f4514001008040081402482800307a8580100450461030416410007401c403201c01c5404800404000418818194804a00000d0550602c1c0c00f6031661500e04201c002841 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 802375629 1250 802374379 802374413
    0x71d21120c01061508040507050603040f06180605100e040b070201020c070b0c0d031a0f2202091924030b0a0e04030e0103050603030d0518072403021206010309 70
    0x2004151000c2203407054114000f501c000b655000c803011500c11058626500a903001445c9402208082c0818103041000c0d5920500910282d21945215240e800803030350782039088141141400f408600388240750144c190010104010305803d5440d00d00c21f0260040090300080964003010003240300c03580701b5015a18010b581d101a81c403400c0d80c407803032489280d02c0f014681d912806408a405a418000d11820182654545500d82195a00401c1003400d922020486034080d011010785c0e050403812924092808c0408400166107001c0a020460a480c00308020b0004c0850514103010700d80d41d41d13004100c00074000344410150041c5100079000351454040c11a003040302d15200140184e0241c44040c062800b944a00385185042e01c01103042e50011a00160940d1080000481e000700951100343d1000340100c01c2d07001002502c01c031600341401c07544072629810f100307010007001d40e5221038110101c5400e800d0441c0381c100d0300f0300c0d0b0204001006111905150755581c0d60000c0c4416802c007019101 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 802376879 1250 802375629 802375663
    0x2a0607140106151107060509061b010f050a021e03061c1a070c031803030e0f0f0d050c0315040f020904050f07180f090818060d0507030203071d21 64
    0x60701c451002413080800ba69a4042407084001c0044c105000b541142d00c0342038041d1016140a94101c0d1401c1000c04079205041d0329035a500743c2c138011040502c03509010b0843c4160141e0344140030300350500d01198400750040e0010b41002888481d80d0b07088401601041d101c01c1c070411020070350818007070f410102c00d1400e820b21583c0e410014941d40c405100340c42035110381c94403071000550540d825805021800000c01240381c1294111061500e80000b0300d50f003000601c4c11103217000280120b46444004d030800c0b1800e0740541c481c18000e1030b081c82440c04d20105010344442601d003945030902c000c41c18050190040c0c95070008281407003003d11100307540203e60790455030700940e01d0910900010b00a410751501c0e620304050007110701d04034094034048076000810349082100e0540070704000b0207103c00303a03a4800300412618000c00014000c42b880b800003a200181c40c0d240c0f800000d410b140401307141c200e400d1801c4030a40b07510303a520001500844075046141c800d000300786800900e042c0b09024090106 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 802378129 1250 802376879 802376909
    0x111c14270303040809090906061315081621030816030b06130609060504060503010e090109120203041e05310e0106030213021c02030403030b0a06022a0607140106 71
    0x4450340000411701400d050b1200c0b0099501ca80e01c0c81e80382d000c1075030006ea000440b06410424400550800c0c1d00792141c060f0f041c8641f0342d4506030705150501038205040408081501044411145148500c0d8030b0f000d0395054a000c2030a543c01020010024541880d210000c44d448c101d4500c82d0703114594010015214640d20865a04c01d4288140288108000100300842c00f165541c8500180c0f421581262961415642421f4500e0103204004104081a42d42c0c1c000c110046560391001c100c00c0c046075000345070b699051072000e43c8100c1011003d46c003500c07a054000c10254540b586100340204868096000c41e15040d11100c0b0303040312980c1c005100c182007070290340940c0c4041d804041100d1007119208003180001c0102426800b03010100c4160004142d15a030107044543c0040d43d005219241c00100c00c00302c1e00c00203c910700c480d08131200680c8544c007180e0f0b413074910800d90414112418400340b548244400090441d12810400030500408c10f001441042d03000d4210704050081c01140100c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 802379379 1250 802378129 802378133
    0x406020c010c05040b07030302031f120309060903110d03030b09090c13050f0403080408070b041109090f030412020f030604050109020118141c06111c1427030304 71
    0x2a41245006106a519010841d1100c0b402001100e00b102e444021a500b0310080d524140c0c000d4000030107034503045c0d0050051100c40e6100461150262520711000c4090036a86d0034010f10103881d0b03401c038400384803054000748046151380d0404d810301070b0304803490076802143d03150443c040d161005c41140c20182c0303001400358890000caa00c00d5052070644500951000015428050302d0040e140701c0b491021841c045000b081c031071134000381d1203401102060b00c0c042c256558121041e004640a4568040c2e1140000140c58030040441d04412000003c00c0c42c200240d01603526442244114802c41c00e9111800c2d00b1034480e8100811117000003402c8d10040d00e09810032502805981074103d00080804046082000142d08020182c44005408a542f003030454203001104010300c440760100c0901142003000101c950207401c103100ca05900f06900d524182142180400c2d810a282e0703012070070610342c0686c032017a42d82c190781d10203208903c64440b070604447c0110061800009200603000002c10401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 802380629 1250 802379379 802379381
    0x2c04030f1205150d020339190b1c02120a1d070603020a2a02010912033e0606090606040e0a11040807060206091c02060106050f0702090406 61
    0x3000155510303800800711400009004441e000c49030b55240e40d011028a0140e030901e850001a4144040c045804c0751000b500c0180c820702140c2c8990415510329480306681d03044100d600c828099065031514007054031100e18050001072800303448041c500104403c1c0e861001c032070440752400c65000c0c04541e1405116801c580b40a421552180b10360b003003034517520380182941c040300c01251204025280140c01c20504070040c2d8020f50b101c80801c282c2400c0808494991800900c499880207041c1316941c1491002503c0d990a0ba803100c2e8515801003a21070200307401c440d40050035800a588241c40c0c600c031000c0072025180074006400b4104085c4008102100b002545d28081e01e402c44804010365150000c1001d580f059019141c000c12480000c660060a2900241000302001d040c050a2603164510103140541903030042006a00aa0a10860341418480d004030000c030407041510020440c500a03503598010301c10f410801000042c0030311011100b000390394085a00903c004618141810000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 802381879 1250 802380629 802380647
    0xb0403260a0606090302060d0507020307020a14030d0305070c031404081f050c090105220e2404050f0f100e0c0301091a031b03010603020d1b1401092c0403 68
    0x200c1d298900100820454000c0c9094800c5a5004040a15250120740c140010344406044541584004d102400060355a6480f503c05000300408516070080b0600405181288903210f4600789880d12003070000c0e02e540044028840d54040c10070f6251440801c40d030101c13521070350303000d03800e6030040380c28070a0070406840c030104403418031070000e201503100c6030000907951280780f41e1540802d4003000310301c0710170416000122400194601c0150002c1d07960003840c110728412546c1c2e8082c283e07840c0038258502d1103105259000344040d00c0412061078041d9200242e440c000d40289c0324a044940054040c1408d807404102500d074110700c907501350404111002d419002030041e29565800c2025400082d02c0d203120074002200000e000700300c07645100c48030fa44d021525031450764055403039840110150301c807400790002c5c0d5813103500c80c0301c0e20041c01c41d81c0345c901030140d400001004408002003c00390307a01000403410385030303182c2100d00c40d80803100650642c0d11440e81c4840540c0c00b400100030600d60400024 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 802383129 1250 802381879 802381891
    0x1090b0405060c19080c13060807020d09050a140d06090f021809121b190c0e0403020d0e0120070608090f06040813081504021504120b040326 62
    0xb914030303407203401d54002d0341d015400741c10b01281e440d1210740d00c42c035102d02d450981181041c1c442c0c43c070303281c032101c1c080c050071110341c001401103602202401555903040119004c0d261103480d0540c1418203086c0001d44540c11442035a1045501141c4c9500f16a5082040101554040c80410100b0010302d00224548042c4100780c0c412140313241e00050380000c44d8485072007074070000094040418400e1407813072103400000d40e044440540e074800800c40101000100d20950b1095881842502c2c42d1410802e541c415420210002c0096410300c40041d0300054202d98001580c00e01c03010345218000101e50310000a031000020076441200c45c900040081542016209159100c1c1e0b07242e9100b035200c1c1c0e9101da0103440ca4055600070303800140880c08200240044041c44076040381035590301c1d03882ca03143c01482d48000b41e4901e00d980c11703c030452510480e8030940b07400d48919181441e04d841840c42e400d0084200180010303100c14000350402d84076504261419808400300d1484d000055008005176204440c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 802384379 1250 802383129 802383133
    0xa1811190206060609010c0f050c0607200d03140d150603091101081e04080c06010b0406091e0b0d0e0303090a020f040b0f19050d06090501051b0904090206040801090b0405 75
    0xf084041c140310084a00e91070060715810100c200650340c400601d64540c1c0b05680c1c600901c0e032048034580e00d100042c5030584c0200148011290711001901100404408541c461307482d40e00b0100c00070f07802c24501c01c0003d00c00c0710215102d50344101d0b4080505100701d40030014240e00d40000c14a03a40507804100c515004442c14540d02c0c00c1d03c0c0064504140940311202c404d00100b803007440c0c9a00c01260f03d6401441005e09508280d00e004505240150a030090740551030b0104050281581c070808503401031086c0080c2e800c3c04000199004032103000f0340692850b8105c0003030308608400c02ea40004084614010440ba52454084030701a25840b4840040b4403901107044852824501406854201b0034010801030500c10140104410318a0300754100d001d1400303d00380000c1a0703595401440200c0c0c0941404240210145455401c544008081c1114540c030f00da024581c11340102c0588803070700c02c266000518174015000241c401e0145071b01c03400541d0700700207a100c10060107000f07141c01a442501 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 802385629 1250 802384379 802384381
    0x3030c0e01171605120403030603210509011202070f050705150c0c0d02030f0f060106090e0f0106030e0304260f030307080703200310031502090a1811190206 69
    0x4607810038507010b40100d0092000c02040150002400c4201c0049160503c5841c0048101c0494080c0d20308803030650100e590344500300300f40212401414550080c07051016650aa20340700036205010b140c000e2410454081e030030800c41d8840e0703411500d03210b402108003044c1821520b000c0366580c240380038550041030b58241d544c03119402d0100f83c030705041204020b0129241d080c0d003480304442d001a001d9a2610502c010305030000c0c018821a2041003030940a0b040340d40c10101d01808494032a8442c01400d15a00700b0082030130003140e0071a05540183c44c001c9440e000d98030800b031450040750421055240c500345003503c2e00241000c582c1420f840242030b16107000f10f2502c0c0c541c5a010865041d0040f50000700010344a43c4030340c0c04000b004121544900100044041d40c3c0820b0b00102c4041c103400120040500502070b8003030421000c8e0580041c198600f00307403400454801401e510400148010b4881c1081a0380545d802c1514400300035010140c80700086000c20f211180841982e01c05402010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 802386879 1250 802385629 802385657
    0x9050c07050a0b0a0f150b130f3203150408040f0b130501020102040b040e0613090f03120b030a0818190306060501030b1807020a021012180201080718030f03030c 71
    0x1000c2e51425446e018501c803142c52178060a50030a5207c1d80822082490401c404100c20b15400403400103440191004880c0c2e02c0c45032080b030414200031240c00380d020816070442d8030340d950000c7c8117071030103803141c440d812551900d10f07281c5940d0255070003004a4815604000c101040008058000d40c0004040e41040c15506e10069080344144d0080c13101520003000144442200c2c0045503400038000340003000704007551020700088440a00c000c0740c2d00c403411401001499800300c5101030f25604070000b00042540f0100082d6100028140106419000716011910f65402c4c80d81e040c034220042d048500403c005201c12594030791901046030100c3c0383c0500442e840d4030074850001c4401029100300703440541c0c1d03081c0f50301e0700c400142508114440e8260b1200141c49200c401c000c18a4030362980b410051258050700b09a0358209068503044241c5a5a10003503a4400038154100440d814051101d100e03412a061013150a60000341680c4c5041030306604150f03040c3c0c80302c1a44480e079030701d90080740000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 802388129 1250 802386879 802386881
    0x31e0f08060a15050304050c06030103030f0e152a070311090a050c1b0c0d0606090c0c1505100807030302160605180f0402130914160909050c07050a0b0a0f 68
    0x43d01461a10540c09601803190074003450041da0420b0280c0100c40102e00d91030000b0f007030380d8001d0300704a0001e48224a48800300e80c1027800081c6c030304011a0107036080c807692089540d2034001c00f0f4900c40142481385224101074000c59102001480402c2610f48146d100d0921035400302d800c0840d1030007100c0c0e1f40001503a20742c191045c1340c020070030005a140ba00c0d40c0b1665441d0320010001c50400a40039841ba040310700c0c0d885040682c0d240d0722608001c103542d072401107203e0484e50300c030f041039082c058400c02c05030009011b0428003c2c5c40c030343c1d90300c00a040e490740420802041d030340360090707100c41c4507546011080c560002810360003107690010050700142c13601070485250103014078600e048040d02c0c9403d0719518003001c101e45505806480107007005482844251034504a0340640360b001d039503540700040045034441c010360100301c000c9506003500301004010300c042101d120340f003981944e4030003107050721036420700711555580c000c412650045414108040d40740c0c01030300d1015400b4504410170814aa032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 802389379 1250 802388129 802388149
    0x62b0515070810031b0e1303020c0301020a090317190206090715020606010f0e030a030c02030f06240409080d050609011428150f020114060a12031e0f0806 68
    0x20b00700c4183c14140396680708028915400f03407014110300080300100d04001d0510441b0310401c1c075009166140c9102c1d0401078104040864094001e0740100241c040241d0080594012640d210003004441c00844500c0011381c0188003d2506111041c010911010ba000495500034111881078030340c00e030741d01c5801c01d184105400590b0096000040051201e40c0903403608040c52800b81030a40b01174101c44002420b1008006044000c42c01d8107880b4800c1d42801c004103084100d42a0050a01303041158801030714608094241c2110000654449041d40344d94212200c01644040c03d41d459211100000014280c1155118040c158403400003d14902d0308d101e015a0450142c00600d82405090301d00e00754030110402418004904400000e09180341640711611840c01d81d91040440b0002c08001d09440b0460201e82c1800311000070f019003641e4100c002e1003200c01c4903103200440c4280b45020740b80c1d10319492456458003c04500b0008075600300c00c00c0e21680301c981e90b0720303405940c46034108225102 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 802390629 1250 802389379 802389391
    0x1107030f0f0203070302030d050706060905090a120c050a0606091b0503070c0c050616120201020c07090c02150c0417060c0702090c1e180612062b05150708 68
    0xc040d0006404100721000160980e80050240c501c400d85030740110740f40180107014403001904c000740c41c0d03003886400d104103009841c2412080c0502d0400001250340d51000c01405442c01c0c04003c0240200e038052200e03603403510b5101050313603810303013450500304028a0b5501c25811801d0800d070b9295041c2a8101822402d4025510b4243c03e5482c4c04100b10b512154011080341c21681c10800071a250351210042d200c07a13a4040c007208002c6006d4509207107a1002c0000d11802d6a0060001220700d40d0003041030400d44403480c1c1c000920400e10308080345812205074420b001001c450341484010110703100100309a4945070110308020f4040c2d549565540d0342102d2140090405210304001071a00300c480607044101401c010342400b090300e094008294034000e9902e100000000c00b00081c2d20700500303038040004100c0d841d40c100501041d40c103114520090032140720b84504102500c840700c00e6814082a08000e034540c060441c10342c641150351300782961414807940101030019603414031030001a032040b4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 802391879 1250 802390629 802390643
    0x10e070e040e0a1115031906051509220f0608062208030618091516080403030e2a09010b04031502090102030912010c080705180609180f0106110703 65
    0x1070316448401880c1400701321681d0042d12454106200400c480245004000088581c4640010513011808440044d8059805600002c1940701d50826200c19070300042c1080d981e031301021404041500b00040d004010342816454440759400302e84c00c07070b03000d034050341c0b2080c00703e490580b2200260300d80e11a0710b15071700342c00c01c00b002c99480001d0042c40c00303160082c0c00900508260583c0c40550441130a0803680700e000b56021440600d0b1315140e8900300c1e50007040c400d00b10f0a442c030a5000c024150003009101500385520b9200d440c100d0101003065140300030030340d600032240c003590040c0354003c40c81c0100c40074802c0088600129490310742e48103c0d000c0300c0e132000070740e075045c01d0100c0d9040c082d4000309042410341c04244481c46003501d0729142000b0002c662000024140c00c180d1001e041c3c40c0d4080d105000308132007805610f2200d40c11090040d10040c08403461034903818034000103111984947d00e0405170712032410901144803540c0c480941680c0090319001820741c003162401e5503401ca1448050580 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 802393129 1250 802391879 802391893
    0x1b060a0c0c0510171518062101090c05060f1606090602030c0702130b1011070332123103050337180806010e070e040e 52
    0x166028188400d40144100185802169180009455401903580840205903031050700c0c1d910401000c001548225100c12408046409601160300c140840e207080f0b4841194001155076030352200125510351911514524034103168010303250190091000844a04040101c08202c03403600300184c4066128260001b0700300500c541020001c04100f20095450070307600d48001c80860103c2c00103501c2400110310040c3c3c2c1e6621481441410124910841c8030b02d450b19511a490703070341b2038907104008015840c0050064600b01c02c510b040c92000c0d40b000385490003440034a44510342a42000040103083c2c9040d8106058000103da164000d00b18070306401d0904004070080309803070140b10261042090680c245045100d11100c0c0a07407010307041900c1a9001003440c940c40464001c81e2150403c4c588165049144031814030000c1102c130981c500c082c041e14800d28020b82d032403500707058002e14005044400d0b5503920031075507041c01c00559145000903050340c080c0c500c40c01c1074064900c0042c6404010801c3e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 802394379 1250 802393129 802393147
    0xf010c080415050c0c0604060c080105090f0f09120714161206021305180103060f0b030312130209070c0203060a020f1b0709060609230a030305090301060905181b06 72
    0x520004101380300d545410310018010000810045104510901c00003070340b5040d24a010b4030203401644014400c4000a0400032070854410050303400200040415080342ca0b0500d01c075050452500d03020040c1d02c4003081caa824401d48400398041201d00c1019600118041e4080d0703084044617020b0500062014074090340008e01c03650090503c0001446828030311a25600015007010860f00386105440c140340040c400d1000c9031082d101450052a0100098002e410201b5128020444040d50242078440098180e030003440d00405150b900402d43d002a14004601a0080030b181c2402da0192040600103046034a0510803200d100001e44002810989201603201c004040070080c0c0c911401030a200144010403401004090603e17521142c0100742041d400d039009640c3c8900c000c000c0d5100082200d0ba039210640100c054a41600d0080d5a40c0482c4010a01400b2103910036a400b91812080002c001c21540e4100d92440400f001d95414030002c0000e05000e00d01110400d5103d0740800c41038503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 802395629 1250 802394379 802394381
    0x4050c0702011e020c100203070606060806240403060203090706020105310f17090405060402041d040f051b040b0907081602010f020406080106021204080c121e0f010c080415 76
    0x442c10f4450710448080840302804a0100102003021801503800071032414208100340c0500400750480d807030505628600600000c01a500000d00303803400d40d41e0504859402000e9a080302c001d160050303c20741d074900303241ca0015912202da1241800552070b240c045a00e61078501c084c0c00300c000815150045d050100c40182c55040610785003111514100c0004900003005010421004161400102c2e2241c0ca442c040c0000e81c1d000614a40c4a00c0c030400060100442c1555607070128030303d481c008100ca69951502c040310300701c0c0000242c403034810310003074098011061200b800c808078255424031500130040144030502c4800d41e030010100d2840c5002079054001501c42d081c60041c50b2001080740c059075144081241e011b0b4000d000000c451034018429039404100031505482c9140c0c040c0e00e054980021140c864480c552114440e2000f441e00d00103910007000020941c0689050b0342104551420b1441c3d9104011400342c8059400c0c0508910090300031441c2c03d22503504007e50308000141584620 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 802396879 1250 802395629 802395677
    0x60c08090f0f03250b0301051005091c120306122004090605160e01050a0e0405060a08250503010e0c0402033417010602100c02030c0a0c0504050c070201 67
    0x10b8125180006403030090341d040200c0b81004070303190151070381c0e002800690004540070b81c11407801141d08000401580c0c0b1840c88a90b030303140d004c0c0b0349181c680408400164011008019104031405c8002000c2d00f400002505001d404070b1a413010014955181210380994140304409070803950000300b44407242c603c010034110710b018024000188025903a55a9084410607203860911b00c0e52611200e00e003c2d00050f40480725042400d02e0703428610039080013407a403111400007501a42e100c0010412580714800248050103802007500c80e284d9112000b040c1001c0d09060b1103070a9800c00100060904040c85020200160200508a655002c0040c800a5130019207450410004811030030040c481500c0907102d1160a90624004542000c01c001c0500c0740781100c000200300c5000042008680000310000c070f0a4045802140c08a0400016825400340641700070560107485078a60400112960f07a5003652000c03102044540c03180b16a001d46801030f54402801b0413500c2003110f08a01d22a5941 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 802398129 1250 802396879 802396909
    0x903020316050708012a030c050d02040602060f060a050f0108061f0203070501151202010c021206090f010e010c02070e150406060c05061b0301062f0313060c0809 71
    0x480c5001c40d141d49035206444200310030782c1c4030341100200b4419038400f07001d00000c8a11400640b070100300100b43c808200c0484c4032034001815070300e0840510050080d415a00d006c48074072005c540311943c55401039180e181c1203881042d5860038900040c160325041120f4821350380050980700c848042000151400300e005401d01c1d510040e07a03e103400e6400d000c0ca040700514000c0380d020f1525440f2901d001c41c01d41382012905100c448020805000200a0845622103c2d40910700104250850300200f00c03083e8100107100c0007405001c082140000c030010f4001903940c0c04400170070400202400950888156010140058000e290100550414030b900140c01080600c1d1401001c10800002800c980003540401d02080b090900b1505010b414080136604c10100c24410f5075a170414510070025200c14020071040c810b03600038510304900250b0f100003800078400440e840140e035045080356240c204000003916070079440000300702684142c1d103604040740d0208401d81402191410080704031001155 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 802399379 1250 802398129 802398133
    0x80a0b06040801020c011e050417090f0a080609070611030307030c1b050d080112020904020105161b0329070e0609090a06080d030b031903170420041e090302 69
    0x7001c21445070a1004180300268800001544c03808007003000060304142e0201c0d4030309032510042101180d11010040f2141c810400002d543c6c1c190000042e80c0442c102d16201d8022200000c0449d15040001d0054010358040c400c450700c0b6075403810101d4030000c00c0e140140713045e0824404614928040d40011000c00150b042a40b90001034007402c0036085520799065443d1751000d10828001038000c0081400341075828a817401207945038011a04400b4017500081c100100016500020422080c0601d00603501a0182c06040c2510248201079940c81c0800d9410804d510000b0f6071003070042c503c040c800040718501154607a1007a509940425540b44040d80101c420004184c437555a003003140d1081214800005011f41402c4010345000b000860100a0514101a8000c10303a0005000c1ca8890122404a24401e180c0d180440701002c1034602101d2071121041400100102c15200410784221005c155503130740056010401601c07102034000700300007080c0b00d5400101d170480d00408000350080c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 802400629 1250 802399379 802399387
    0x90a0512190c0618150804060f0216050d030c0c0b060307090608010c0f03060501090b1b03030118050a05040b0a2301060309030e03030301060509061b120901110d080a0b06 75
    0x16149050400381c0400c84030901040300c00e0107550b8110312a856495a001d44a08201d4240b040712410110b014200d1020b000c070040c005400c001c0c05405c15405c129803901c040d5290110810b00107480401200b088405010341860414814070030300c2284840e00c0d09980d402013214072038407007250380c10004e043e95800d40104040032414003543e000e19001051501c000246548076481c1c010301011401140200709414900c08000503030b88903040d80c05803074440e49071940e03410140818400c03003000c0070f020003d28040400002500d440450414402c00102c9a0a0102d65243c00704042111000c66008001d102540c001c40c000050b00e92081c0d030385108240d030701c1d0070103203a080003984441000d83c4050006511030900c0020035500a6840100260940045056505084020b81315000c0e1790450f9004010108540702ea0704c0399101c2101881031a10300381d6801c00e10070080d030106035204912050215041e00f000c0c00314104c000503601d4815801d641c40382d0183d100e0300321410141c98103080300d5030f002034148 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 802401879 1250 802400629 802400653
    0x302090711190b07020109051011090a090213080303040b010b031e01030c080f070b0403110112022a0303041101050307020717030301081c17130b1317090a0512 70
    0x80603034101d0000500602c84152070b4a8184000f100c001d20000c11641418490400a5000202c455210916210220b00f94901e80e510303107000d00408114a41c0408940c00000b0031100d1940180b03106004c60035000c0308581c03500c04441d030f04d10042c2c070010001c0490000400805802e00c029507045603a80050480c0154403090b81d030882c0c8400c0e00b0940b001c804500040205020400c103030310580a440300609012450b00c00741085502461002400200641d21205d00e21381c40b0780207100110368900411900c91000d1008580c0300441400d60680300f84c0301c2181d10540c810004141d1b88200da000ea0254803803043e1b00011a0b071604090404415442001800b00c3c0c002c1c0074100c00c04c0070181c0c4800075078882d89800c40c1640350641030380c96026810f29040205225580c480c0041602d0a5400031a40da10b4807201c4a005541204420240003544214207120f2050500490003000a02501030741038442207416245145106a0f140300340e00c814400401c02840c1059846405440300200039100150707024 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 802403129 1250 802401879 802401883
    0xd060b091015030e0606090402030304240e0f060702040f06171f050106050a032007050a06060e220218092103070507140c060d06030c1409010302090711 67
    0x540d520303101101030380d5041c8150b0124400500c00c4142900e400d000b00c140000b00592510700140c4100d00032102e14000a040d5101081180c0082003400d030000c0b100c1c0f4480300c1c14806c1d5080301003210001510325030000c07501d182054000c107800030000c01701c41c0351501c0740c0c0c2084010003000144030381c01621420001900100248181e91401c0088080e1040076030840180c00d10000402003254400d16001c010320850b80e1000c00c1c1c400c0a6242d007000204016082d00f0916170001403d035500c80c0c4540040c3c0300c0d040050200c0e50300040d0b40324603030a01c10f55444104c1d00d102c098045940e80240c081c5e50b1f2050321046040b0040c40802800500801d41c181e42107100351303c5c4030700201c60b2206681e2148540e40c100c102012900c0400580113440075080d81050400205244228a4043c0c2240c900d4001200c3c2c0e06402c0c41644803210004107016641d8245005980141072340e480309541d109a039800014070714800000c0c00c8a4168000c2c251030840e1b086500300008840302520a404025500300305020384402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 802404379 1250 802403129 802403131
    0xe120703140705010915020601180f1a01081e0a0c03020d0203040f0c0906352d03041203230c150a0212010e06010509090a05012c060d060b09 62
    0x120750050074605040c007001412508240d4000544050013a4411a10590101e100e5041d2180c1110340420040030f90001e4002c6c165080c0c2d00c2080c1d6182112040c010321102d1312107000c3d25401c1c2c03109105035591a0464444a080320642181ca2403044006503101c1900c0c1d000d4800b15899050040c1881100c801c014100e0300129400c803588031160105c44140001c0907001c0000704107000d01408030700d0615994111000c00d10b0181c0c0441310303412280e8202062000c0304182c08900c0c141c11078094483c01c500a402000920112220a40880040303140500300402143c041d192000310349103a1501076542100e20795499001e5004104c183c4c40c0200f40c1d50f403e0001403000c03400460003000d803489041411800030001070042c8145610420402000440c202c82c41811551280c03020a16660b414006880910078800c00d1035000142c0001c2000850040d440b1074140c1d8040321030341080c9030b0344010b010794103290700100d001031400039000150203141456605020300e2040c0741c0415403a980c1000f2426600d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 802405629 1250 802404379 802404413
    0x31d1f061d01050f12031804060302060a1709010b0f100504120f03030b010e010806151905030a0b0a0e0a15180203070e150a03021b2e020304030e120703 67
    0x41c0c500300400040c504201901810242254104c4440c82d0700348005542e03119103440410007404880f001206542c1b6640010015030300074042c9965a642079100074400b04d8402c8410321010702120110307040d82014461a181c882018001440c280c18071001c101030800141804010043c04100c0030074105143c06e500300c0314070b00c03510745e500d80001780c2e190240c140c40300c002d420b41c100f041e4111103003003581c0d0015000740c004c9000d94904c0079a5140c0418074015204003014080d4582401989401c80b1b9031150040d4840d5121020800401031000d080000c0c000c0c0354403031f041c241d904c0d030b4000c5144002c480d8030400c20643c854110a58081c2d483c101d400050104082c034a4510360b0200401c81e14075007000c034035440440d0403224003442c40d58003441c889441c000d040c00c8101300359000c142d480c030f015500b10100035183c807000101c900b65008006681d032558681d00c603a5030742c08980342c0380d000c07102001d0091728056030303042d1561054034565a0030b00800d0700d14121410303847d05c02c8034000804100f00f01d81c0d60603142 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 802406879 1250 802405629 802405679
    0xc0702040c0c05012f0d0b0402040b040e01050d0203060c0c16121b030818010201091a07090b130501030c0c0f0b0a0e0c1302030601090308040b0703031d1f06 69
    0x1e5043c420b0071280b01000e900012584211001561443d40d091040d884400c46503080d141c0003820250310040800a25464000384002008512203c5202c0074004640844520207056a221020b1280d80802280e0003505a0320000c042099581840007405500f0140e008a401c401d102c0304102d901043c4623403005071601080d2108009000380d880c200e0740320144580a90740020328507900e060461250000d0015114883d0507010b00581c401e40111034501e80040244580300040340440406540559018010030900e10000640d14200010344039100c0d24611800e4a0914080c01500a04031382d042010800c0b400030f02e000005405c504280d0b51280c003440f01b034011860400d00840071559410298509035004062001c1c0540d81c01040c04409031081201686030303100c2d480143c41901079138200819a101c041001700e0200740c400040d10443d8001c3d0b40a0184030808071801c8042d01c114031607110144c01006203c4045101c48400e010105440840010701c650388003d444512401c840301d0079485 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 802408129 1250 802406879 802406897
    0xe07031502370e011d011211070c050102250e1314070e1308030103080d0209030708010506040f1b031a0604030c0513020c060f1003081c1a030709050c0702040c 70
    0xb181e030000800800714400c2c280210390030311000820103c030b959070b1031803030401c00c0016185540082c04d42024001c80026641561500081d182c01401b56405020302030040c032591114040ba1301c0ea8900700350001248204140c1902d08202c007440410400409001d11014003a402e4400030344814914802501a0310107444a00e08100f0881c505c4c540141045546010710303c1d40102080601c012241100e0348503075400c1d544d001d1b000000010f4050310440d030794075001c1c01c10000f44d00c0c032040d004248038084c101d8003003103000c0c03059440308115042c1c3e0f6800b403111000c51510006c0c8901991116554821306443c1100d4124000000380c041e6004e90401ca60810703c011081109043c0307100003100c9401e0340901175007090075a0011580d2403600504810303607083d411002c0748040d4900017400010352b801000241e0342b13910500b0204420080c0510602e80c0601e0201d00038005a048000100c9218009020b059882d10b0315171702034041d040c042d00103401d40300c0070012000180e403203100d0581202840d44411000e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 802409379 1250 802408129 802408237
    0x1101090b040b1c051b030a06080604050a05060906130308040c0e010f09060b07050c0118080106060e010f0207060e040b0112050901050403260402090a200306040e07031502 75
    0x3c0a450ba82c54081c014240414000b0350f0703041e50070101d5240205c41d001d030384035035503200e020000d02916072180d603290003404203001c1404004103001070400d01803003c0302c02a03143c04041603034911088641a0101034070707240380b0000900c03031011b698109001c0c02032601a141c490100394a003400030790001d00440c000e000700304000d070f1060041100411040350502e041c1107003525000d0321112400103071810402d00034142091200c40014140140c016500204501500e03080e02034810000c5010407800305030701082c0300105600c00180042500c1680d80e41c5e0044520b001d042c0809019444000307414000800c410041503e250b2091610822290700041100d08140c240078102d00306c2151041d4202c20402040b103102c1d004000420b41040d41a20541155514014440024100380246000072141182803c0080f200040070354010481110100702103a0384c0c01215560320681d04c0010060043c4c0043c150b43d0a482ea4013401c50f12035002c0307044140d000c41c2c1702d44400200c59010f4504a4140302c81c4c0c03140e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 802410629 1250 802409379 802409407
    0x30f0c050a09080c0603040f1401090c061403190c02031b15010b03040b191410062c061308060f1005090103030806122d1015031101090b040b 62
    0xb000b002100c015004411200c40850018840108040c0142d2150002d08003001850340d0715103501a4410000c003c032075140d02c0c001e4001d481601c07a0800060890040700c202c20342c0181141e028110309040e0314200d6a01500701d20103040c002080740d00b540018480320940030308082003402c414841501414544414440340e07050a0413307048406010000c0c410040065103c89401d9041640007280364039680740041c2800c00341885900d040c80d03161070745082c402d1000380300c03013900300707695441d1604481607420043c02c4255441d0070180001c1214054211102414101d00900780020410302480c40b10761910012450b02e907099800c4c18100e04080100400450300314038143c043d08040710b1030100e070b500d151002044d1403409030019200700c0503075684490403842041841303d01c2d903a0003002110307100b5140541c81d50707840b407a80000d0340d0700541c0150700005459208401d03c071b5040303090309107005017103807103020300303040002d0401d41800350140c0c0c0803540f0900c0102500081000801d420390352071048080302 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 802411879 1250 802410629 802410647
    0x3030a0320160b04020d17120f090307030309020a0b12010603110f07061d06010f03021201151e03080d0504020f18010605090409060501030303050601170606040501050307030f0c050a 80
    0x10401c0310140090458500c00c0032800000d290401060038031501c0768000181c0f2040c01c481c0040c0754201e0070010045860200c00a03200c0d41007503403140d021035544c41c4034040b404001220308000c00d4000300310140020340203030f1042021074009000340f640d907600d0781124011544600001102641c0450040084640c18015105d101c514000454103060540c484014180108840108440d07144c03021111118402400c1280c402c0d441c13022a40d081d65510104e0301c082c3c007240000da01511030700000c0020000140140c541400b0010440000c00313140900501040e09403031020340d0502d004500000104102d100500640c802891700014141414410019106480183c460203885503841d40741ca0001441d9405046941c6130400d941d680c05150001002040d02240c0181101d1501001005040e40b59010710310902d82033b01c0c0c030ba000c0e411a03c1e06d01d40119085401681c030440401083c491948964003a5030000e200d400c2c0401d84503c50080041030310150105980001c0012440b14044c0d90300003015 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 802413129 1250 802411879 802411931
    0x203151e060a03050c0d2f0313031115070305100e0f06060a0306090f0606170112060f0f05041a0705040501020709180c090b0306010b12180c03030a03 66
    0x58400d00d080c0403070078501440d1002d005141c1e41303e001400340f841c008120b48080d40c070031a0804c032035400c0041c0341e407841400d02c0d10328600054408401c140002420100c03401a00c401020a500d02110790301210122403100d142280340c007842e14814120005600040d00852443d1000314482ca00080c00e00c840700c600341e010b1001005580d05004410740e010b24041e42101d0705841e00303580c80c00d20841c20b8018028942c441d022003840d003c0c07141107440c1b05500c507400b5912170356620400200c202c0000303e5420800c1c00b8101d10b803c8c0c040250400078010b9408210071000301c2d080031500c0044600d410b4101d80702141d0555500c1000501401c25800c03001c81542e2007895424028245401c0000003541d58442d0b0040f840195645c11003090381c80e21042450040c11f621041445040351108a94805070000714083da000740700e070b28008035590401d1420348011640e08885500d0503610f1091b80800004500c40c00c6805000700e1003450415181840200410441903c0110702c0140c61410005450209804 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 802414379 1250 802413129 802413169
    0xb03060a090b180f030d140a0b061606200a0e0103050115181a0c0d0201090b0705070f0b090307140d021c0212030a0f05090705210c04020315 62
    0x24030006080d015115403c01c10700f1407002d92201c200c00180c1d1425000b03e0510081d031101080510b101d864507080746280d82c550034500c03141a02d441507407006490f0344200456003d0401e10901070b13034460003040d40100324094800414500c079a210308080e007240b00017140f509588002010343c500c07500007040e10030410080c0380400581d1716000c036418205800101820420082c0007061860442000060300175081d419480c00c8603803250b80016007990310200d0108003d0140c3c0b030304a02460700600c204d103203040e002507540203650740d100d408640ba540403000440c0c420400d51480008a0620031025114260f480019540e4900d6400d10407801c180d883c0140340d03140d0182c40c02d506030680c007081e035064a4034a5214090f51890704d950983c1850036160301102141c030088108604203685422580d103400c144107040001c2d854201909849610900840f908112a060a042d002c41d2172132918001c01c0305502030315003129241380018140d902c10345140c070801100803440800d03440c0c8401a60507101e001c41d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 802415629 1250 802414379 802414391
    0x50603061b03070e0619020a050709050f0f13051c1205011404092604150f0914011b0f05062a070c03020d030216050a0f03020906041404060b03060a 65
    0x62000d0403480001c0a2030f04000d012100d0103929150b10381580c1004480d413886c40b0b01c11082e02c02c02951607200f011305071134912404200160002552040074024000000c03480400c0c0c0d200000c0080c2c5400141900311410700d4006c00300c0c0419024002c1c440404d15000c141043c140e0321041c02840100c0c228602a046454207004000070581904000e80c0d024042d40c0102d4450100e0a0440128040c0d9107000307410110761a103001454000d00c004d20a0700d0740322900704001486040d003241e04014242c00e12001c80c0d15000188907249001d04a103400e204149401c0c0b40f60840320f02c1c05402451042011a19540a00340c0b20301081b009100061f442004440c41d4407826100704c0c04103002c244080c050703034101d01c000940902440740400740b40c1d015540240000c540d03503110f403600941c0c4400c8102c08443e42c8407041e4012407180750032002c40003101c08121035100e085044d9002c002280b400900350f20340c081d6503140b1400e4a03640490340188118042d1034000f40d024884d0041c0760410310001c1c0600701e2189001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 802416879 1250 802415629 802415671
    0xd390602070b121b070501020415031a130615020a050d0302250219060e0427150605100908060a05190e01060e2d06370905060306 57
    0x100594480e2543c040c07460700703a619101600d5008110581080849140c001140028844150018021681c0640c0d65005082160fa0100d013120204107814000b02c0a05c1070140c103618002c0360880801c0105440045c0b101d80da5158a51010101a00000541c00c001c0300d4209010341441244051074103400c01b90718040c84084407819480742c9444c880761184d00c2454402c10742d00e8400405101b14408081c1c2d845003903d40b01d01620440c181b1440360b20640c14100240240c41b485042e1408840c801d010302d4040342d819945000d01200e482c1580c2c0040c40c1c0d0b84000046503a1440e030150180d030301584412001600f46a04141021001018207204034205028003030098205400f107510410940400200c4286841500c7d01412060f8032030110903611409100d001012400c1c14008010202c0040800304c2807440c010080c00d4040f50680c3d44190321000301780c43d040c85481c1a0019000008405420000b401a042c0e2403c40c00d810031121140e60b0000c001241c01e08002154001140c03206400b5090440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 802418129 1250 802416879 802416899
    0x90a0903020c060a110607090512010b09060609040e120c06070306061209020f0a0f0503011d030a05070f0b0708040c050405090c1c080705210c030304020d39060207 72
    0x2071161940030f8500002c080da02e0300d00c1002c003041c40c410075506031021400c03c2140144541000e000d8a8401e03000480760f030303881120500c1780500742b450207401c490542d6543c0b4108040d580108030025003180d111306614591003010310a900902040701d4009449000802d15140f0b4080024600c005042c40c05606000070b0360041c05900707052420311404145000144040385c0c020748498411900a42e0003070700854543c0341c1608000940304103030001c108980c1d0609290001511540d889045508104281c8134120300c01c50003014228080c0084012081c0e9540e2001107652040b0f844c040015140d0080c0000c118407541804003c0100311814002030602555a41c2c03641c201c440351600ca034006182d900d540d050b400081080031034204039510b4031800b45060803a1607000005e0311011841221841070030800e0404d0a4408542030716008500303580d1180d09000311401507001c140c504074904242c1e40b0003242001400502908641c9408510036078140e0038699800c290340104042d90030400080c0042160 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 802419379 1250 802418129 802418143
    0x40c0302061b1e010e030f030a020309030c0703050a03030510060e0108040c1a0c12031e0a0207080f07120504060512180f0f0606010c111e0a06090302090a090302 71
    0x11190507a031040111141c40e112445030907440e00780d0082c810450f02c1001000b0258910340301c00d400a100358100c02454a850344101401400240014004290100581c3e8051540404010226484e201aa1113050315022807030b40200c40f60f900c248403c204050341401141d8000c1101e90302a07902da403c0c0b84c0d020700107965402400e41005035020000c1c0c01c2c45114101a03005148600e40442c1d030341b00640066486901c921032140f40c2c0e10803c2400e260741300380304046034400d502003580c0b40c1c020340b5a0040e4111810014014070340c00c5409020000100c0c2c0c50000074845006c251032010358680b1140f401c2e80c1d010101441400500005000400ca510f400c10104c40c095000885406035641d14640800c030b210460069800280c030440c1c0e003035002c1d1300340041c078000000400e008944082c0d40c3c640046944800320000141252078600e105549818400066141034001c0c074051b2000c0c3c80f040c800701340d000145511141c00264140e50400075814450891070300b0001490003032000810549003c0e585d440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 802420629 1250 802419379 802419383
    0x309010e01030c0e212a0111030403081308100509100902120f0304170303061c03170a0606350c070602030109020a08280c0912060c08060306040c03 65
    0xd00e40c070300480c0c600c4c840d4040352003095008051301083c9269102c074a0b003008084880c456103114640c60500c0d943c000c3c4154500ca0011905042c0040002500450340c007030fa40314120300d95220038000030000500e94809401003420301c002c9054614038025800d45001900804844114a01410b00c18180d401040d091008000a100451040018404203060700a2402c5c1c00c2082e020b030006c513915800000c4000d01c11148407c2d0914000c1c100009400d440c0d1105a0340c4a03032120b1681c3c0341e40c0104101c0c0c54000d2031540203003800c00d010191581c242280b4003003106c0000c2e01907a200e83c1806555000128900001c8601c11104174407520000d441d9500c030b12183d00d0060603009540020086d0322103408a4040307035070000c0c0964403941e440150740d020f50418800034020078200000a40d90102c0e03180711310711010880031100030310705010038043e00030301182081004115400c040842e0035540070828840c03851049600007030001d4000c00007008040042d1480c1e12a80041090201107001244c0c0e007002d9903 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 802421879 1250 802420629 802420631
    0x10909090b040204231e0f071b11060c070608090304030b011e030f2d0510050a0f062c1009020a261506040b0f07020409050304080d0e030309010e0103 66
    0x2500d9411010384000e40d1944403251981403008200112041c203120fa07030182c0700c528510346d0300d484694007600d880700d0454005000601d03c1420b2480c0c6264881c01d60903450040c01003104000c80c0101182465008030300494070f65101c3d0360b0401100340d1000743c082d070001115014504050031591040c2841c0810f03c1403450782002c4000c25607001001d26500c8004541c030040600080607545001d403a4000540c055010001042d0301c00070210424070707003032041c095004005d041030f260152440303001400c000e1701c061000d5640d001020b88074680d031f11501d009440382c00b50300321030404030000c000c004a189a01a010360446882400240070b8280303d064141c0302c400b01c000d41c4904000d8800c96030401d87d080b42032000b11550641490300c56000c1089805042540c60358520021002e003845042e2040384142d4089803410016001629050006022294402400403c5440031502c4081c5160010341040005401004003000c0380c3d50011f40800311950150051030520318800006490078003404a840c0c181 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 802423129 1250 802421879 802421891
    0x7062a11031801140c0304030c0f0b0403030f110a0213020c1009021c0303021e070b091501050f0d0b070906021009020102060109050a09060903091401020703110120030c0c010909090b040204 83
    0x3013900b9056840c03402513107007140d8450f43d5a04190701540003d108503e1110881710000c00c0e81d2212034125411750b86c1541310030389841404101166050720084400c02e95029079031801006941c0d08200c48140007c0040168885501d1401c59080030031040c00c140314240392448210040e25034001e800000080703000400340d110b0141c10f090340a071040201d520413510309441c0010b110a20000500300d0300b8090010040e5981d2a00820350303807075261b150845844101301004101515010b100b0490502c030150030406601025910884204070994901012910f111000d02140360304111400719495040005d02c1620030680000c0c1d2144c8060140191860721007001a00040d45034000184180e481841007003903650f181401421000b00c2d010b50300d01444086010b0401d98400102c00040d0f98101151021021411005480858042100808406601107c21031b90141400078148169555002d44405205034000514008860300240007083c941031284002c0369000c0b141d542c5c85a4191000558 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 802424379 1250 802423129 802423157
    0x10c03060e0406110c0303090a14010b0d02060c0309040f020a08060a06080103060b1c060b03100e0615010e0928020a02031605070b0c0115090e0607030207062a11031801 74
    0x9135200714008100548400000c0c0301035000c00240d01c0f10002d000700c1d40c07619004000301d0900c3c00d881d00455415400161162807001528204c0300811290782c000003261f260440400106050fa414a51440d144650105155a8164000c50031591088003110400f000038188400074090103c1804007500d250b03501d80c01910b0984600047c4061f00700104044040d2080c2450402d006d80b100d80d1005000e0b0254206203001d0404078080c040c1c0681c00c01001d0a145d64588149803202c00100d4600c1d1b0402c84000039258040d101d0a0503d07005410502501070102c12840808001c40b62280e2001c2e5118410440800202c0c0c1c04020780c0c4803185e8a0300a5044001d5600300301d850700c0c07550341080d10b036202d0000315824200415804212200480035075115025600c05050301155480c0b800019280c1080340010032451295000340300c890310aa00c002414010b920f442124510044220394501f10440450f01c81183c0180e0f10054420005005500c1c203c124462041e040e5180410a41445028200a05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 802425629 1250 802424379 802424411
    0xd030c03260406150501110309010c230f1203060105090f0307031b05091812130b07060914072d0e0a06030218011a160203060c090102010c03060e0406 66
    0x80c04140141041c41c01d418542400001040c0300420428041d44443d4000341d01e5024503082c81c02c1c00020000707141007809240040d00c141600303860850b044e40c0001c02c98070004980c40340054412604400419039214103002d150318003c0341803076a0905038401e00400c03715a901208030340c11010300360b800380c0e51165160046841d1a07002d4000400d0820500f40303900c1c0030b08804a090f001c56004848030041900e0344607500c50030300c03d03000b0300c1c1d03106402034005400348024800042041402909094200030303a200e510000c00c4e00100300c21654039403280e00c0e54051240407410110901d00450281101d1846c104980609040c03402081c40c0c01900803d8503503801700030b07040c00001004011054899031821a195070018006400124821001941d407451740c60000390300075041c1c8074540385c403508481a9150301001c5404c048203030804a108000c070302005881c02e00006000d040c6170002c058886000c880003a0941340800103c00030940741503406c1010784103035030703070190403640010000a003501c0840b2881 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 802426879 1250 802425629 802425677
    0x614030c0c0a0f06050a15230102120a0201141e0411281a0a050d050a0b040e0d030516050d18020d03050703020d0503150f0a0906060903060b0d030c03 66
    0x340030521843c00e0642845480d800071352150020110401640700d0079403507081101040d0250801c1013020040000c485450781d603000b030b0036120500483d00b102008140072040f40d4809128900141d4650741c0201481c480c03070384070070303004042c0030b11400b000134110f01c1c0c0d03c5200340700820151541a0007800d10070300303444e95080381e10308166201110712161140d16100c140810203100e200410900850344a20b842194020f0f61503051a0381d03126441c09510800602c0a407802400990200f0b954501d4141c4d581e4131403080c140d0381040603001c1c00495001c40d0f809801c403040284000c000c60040c590b20b542d03aa034060202c44118520200004a200317840740300a1100030113000081d00700c0403401501c420706404c01e02418003280319508894500a085804680600082d00d140310031803020320440c3c58030318010917550501103020b050b0060f1190780c1c1c1401010f843e004d41c09000400c03c0304009009020190198003050041600c240141801c2da541c02031000102d15000740c10000c41078a415a4017400703108034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 802428129 1250 802426879 802426883
    0x2502060910031d150a09030c17090d06050604060603111e070203070803040e06060405010f0c03020f03031006110c06070b190606120f05010b04090c14130f0614030c0c0a 74
    0x1030402d0718521402c0c90340d100000401c001351400180d001655840d01c0d40107010445500d541c54010b024038030350341e0b001580000b0b440444c140320140441e1f407a81d110305040c2000c3c14020030700490982010000c4c08100c5410303401c014109401c100d48290804502d008403903080340880392400e0000710b1190081d803d8000c04400075854060050b00140d8004004094015110070104c524115150402004090310492080c0c030b0200e0601689103825500a49003810f210b0301030700689843d400d04512050859004030f80b02c604a0703d4204041c05040e6000c07907031501020000f4000c162080803003000401c28080c10740020114141d00707001601505404030081000044031005004294603000c0281c00c003800910920090781c64000042400d54407801490304a0388120004c1e880c02d810820311002401803000220b061103c00c2510b0800310442c280140104042802c1880503241082d084040c1002d00c1e611903801c0000c50f01c20213502c0006181101e8000300001a069520803868584904003a170361280 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 802429379 1250 802428129 802428161
    0x8120c030f12061507020d03120207060c020d020c1504050d0c03050102160b1609150c0c030b100807080d210c0c020411070308060d26250206091003 65
    0x500388600080c0b203412402044100c41c030820300000a240142c2902804030302070340c403108000c8014003107030042c0b00011340d40404000161614100d61110419030b05420440300042c0d220520a40520b90b060181170341c1d07100100c80d80d1241303450804602c42503014500400b840380143c41e040400300101420300c000117640c058020b545464004030701c0700342c0f105560700a071503550705c10300082d43e1900405403119510005480f00540300d42441d01000c507400340d8403010300600054500307071004038a2108405004520450703568125240101075036265007000d40c4a2212036000010500c401c6001052040d1091103510307120b1105480c0741e440c0091780845803070514030f151404001f050310903803080c0c4555009000381e0301409500003042220045214422000d000a80800f01090301c40c41c109200c5020307203000340608261820310080d203102d10f240c0a400310900c2c0800181c3c0150713440c00304403442c0c1b440c180c4e11072042c894212500400c00500c1110009481040b283c0c0403131004600a031300c0318201d642c80c1c0c20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 802430629 1250 802429379 802429387
    0x10c0b0c0712020f0717060411150f0c0d0c0c030b0915070806010314131719022a0603070c0c080d020c010810030314180d030e04051008120c030f 64
    0x5000f079141d108640807075009018242c800b1543c40303482501600d8004159005056660744c5459401ca980d54819805612414075a140c1c0e01da0401390340607001c2ea0005404580d40c40d01c0c400403161914180e40c0200090040110000b8085903203020004100ca8001e00c54010b141d42e030307921190500030300c1c10016030f0196800c41804000ba030b01c19520b600c90070081c0c80420141c8000e030490755101d0012070300070529501841c0b8001c00141c16414210b40310003e28a0039052110841051598452035100200144d00c04400600c4002c02009464000c0c841d40c0034450b580300704600850801e2000030254000c0c41211b0120400b00300103800c4c020000e02c1c00100b6200c112070040c00003074980902105107070001715030001141001c151240c08000302c1b507040d00e400746141c2560404604541002419103a07141e00b45403008440d0b02d0301180284502d11998451100d0640d0340300308011180c0c060003021f166044030009024100c000102c0c26a03260511035619114030903018070b130340785106120340031a5002c130210b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 802431879 1250 802430629 802430663
    0x2090403030f06060c020f030601080d0f0509041a190812072901062a061e0609051e07170603250602010c020a110d0c091802040506010e010c0b0c07 65
    0x85200c1301c00302d20840c7c4c00180444003008150341d0f0342080c0100715079500301e2401d620f4600e000300c2c58030101c00e400d410054140105100001c0c11070315024032400103c02ca03101007100b40d00e0007251f98011003c02d0038007030440d40d0030550b400e1765400305280c085a56040000d420b00c28006c641c1114040e041102803c90f03180c07030901c62848006c210a02c246804035660700290808030b08044500c14171842c20282000117206103845050141040d00704112030600001440c1d0f0f18a4800c1c080c2d2800782c041500b010450b0300300a04c5007e03000d404410703980c58991044061048050b801600308840300304242512034951600e600190500034120781f20101c11541c10721041c0c98290100c1240111185c54008211540030550181c4c4c4903040394000a0890652605030445c0703143c02064801c2d06800f880340050070545900080c002c890710025445e0846585512500071440e041c010300703a11a50030700c0c01002e20303803483c0006401458413440080c4a602081c0c00600811606801d4880d0943c101020f03a0140c400c030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 802433129 1250 802431879 802431887
    0x22050106150203040e060d06090b0f101a030712060801020d2a0836010f060f050a051c29100e040803072001020c0601050a030f02090403030f0606 64
    0x748110748404104506155060340080305450403650742c08a1702d0126581d132403c003c6c05051002040360b0960390303601c680c008621b07551b596903c19440031078220080c0c00c000c0c03264100c000310303a80408048000c9421445070075001900b941d0b00300f41113081c15044a2207140380c05016103441d17080300189602c04101c86a42480e6a0001e40449007601c2c131148040d040d00001c2c1204c400b0000c403501c003090840000c520109a018001508602d409015640c00050100090340e005644100182e19039107030b030340c8401114441d00c155001030401d01c40142031180340c00d0101b82020404d20506c1e110700840310002c80716081800d140b00085910503261107074503040c6204407083c5c60681c05100d0158842d0000103c018603641c9040e025180702d0300055520365034540d502c082a0f44010211401c00040411030030f000c0700045101010014075100151312002c929034450710302141644660f129107401daa007000850b506404e008011501903510313031001d40e2142003c1e030181101c69121111649454400114203500c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 802434379 1250 802433129 802433141
    0x304240b0303030a14150a032a12200102120d02040b2a0a02030a0605062206060e011b0204020c1e0705040609090317100807081005070504150305220501 67
    0x71012a501c50706e1700c0c912102d502c100301c00d03850340001a814042c801b00e4000129201c0d1001451400310003a0180032441e441d914465019440b980b6a000070441082510444110403a020041c5005031903903200001356921003075800c4500c44140041c0e41642042180c04480c060404c80f50251f03038615070030170303075042406029202244501603080f1005041b0400b1521501d5690010000e00f18440c040d25001c0c01400c0182801d5400414500c0c5d40701a55202c00b05180c030040d4440700042d00c4c62800c5006041c84002030202030403c2415410085491b442801007035240750151001a00e44400c00c20b09450b14120711100c984204204401c079102010026241c000d0781c1c42510b060100507034501d80c000c2070310310b130200040c04515181c50860b031011b400320702c0d075604c2040d107040c130b400e00c3d42c0d40d90041e420a01e45402c40d417038941211a01c1c0d80070607064003941d43c00c03030300d9890301a00e01850b0169038601e0301d03002980d640800d078641d00480c810007003141309007260030382c0018249451000d9242c035a000f004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 802435629 1250 802434379 802434401
    0xe0d061802030f0a0f02060d060512100b03210d1104170d0e01080f04021302070503090f01050c1b01120606020604030207060513050120030307080415020304240b0303030a 75
    0x210f0140441c408000114500d0420b69100c1407400501d4001d84c00c0007956000f02100452031540e500d80081d01355107440b035110f12403105001900340412108078082c15541d413048514001d6101ca50b1072820050080005031356005101005d94131801e0140ca50300207800307024031218803480045008503451420030020000010b02070100c4000d001d603814182c0d414500e207504180410303403803c00944419540303240654031a02c0200000814921000760318100c1c1c000502c1a40c4903400815a01c50600b02a01a17504090003401c10a040c00d55104c0d015a036a0356a9050344200c3e03450500250003640101c0d4480c8048401000134060316031030341c2009560304011201a80180b1030310381c0c00140c4500804c201e60b5504001002c4064203401c1500548051403102042414005001040c41142d0300c140050341c000e01040c0d507040300758181805d0400840d100c0c80459101a40b04005100010714204503a221070074a24000d5078842c4c032800e40450085c103540f44d0040c0c040c04000100402d0010551200e9a022 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 802436879 1250 802435629 802435633
    0x1d030301060f092103090e0112061a0306040212010b221d1b06042310110a02040e030c0703260909010b03130606030602031905040f030e0d06180203 65
    0x2600550858400b801c602c2000c01398006100078040c0e41d0030320301c0b00a041501a040820b201680d07002d29100c814802da01c041d4000765100300d541d0402280740540c0003082202c050003200d001e24480040e071210400380000380300781c80200c01644031040a41204440e810f00038440305041c058120780000f01c21030195507040740c610b080105034840300c0001003880110403240c01005103003400b82e100100020300414541e4000c505010001c0d0041542e078082e102410300c511102041030101080c0300410103c1c0c1e0400d4144070612811002910700050a00d98164044070042125048400300d01e0940c401c4010414a5001c0c822022081c010141511159461403080303069440384904498440c501903034050740d5018800c4001002002191409181c000c240030103020500b12060743c03403800b1100c031f607441110b03020780100800c280c0310f140c1ca40182c01500541e00070700483c034003070742c0e900200c0d0703000307003004090051a540021031525030400f80d00303c546d0f000004208030f045000c2c01001003d039a2604038402c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 802438129 1250 802436879 802436897
    0x170702060f0c0307210c090f0e0a050c040312020606030715080f090309130506241207030209030f07030b01050a061e0203090d0b0402010e0301150605030a1d03030106 73
    0x464400140c0e24451140707102440e8442c1c0340c40c42c64021607403010b0714031010043e000100ba50103005442d0750055aa40da40d0001503100d41681c00a08000e0075540612969103410700d041112540341400c1540c00003d0f110002025940d0b1500a1658001d81e0400781c018921b10840c161043d8000600c540904011400c0351199507036480340c043c10108010749440045d00e0840441c09007000918140e4104100c18180d0b420548480089069500d003036500e0b85c04943ca070014009541403c0c002d00c902640303d0000c00c8904140e000c01003005104d01c0c43c0030b01d0710121220004083d0303486a03040d00c2d800c800040031382d03000e180c0d402e40c0c095480d042d5000a685151034207000007001d18000042e001103898a4403500d8406108038600c0c0040b4882c0c601050039800f0070440e0101e244d84001624501520802c4254100d00300350000422080e420720442d03000b03038035007040c0d0301510b0b40c030180900c103c40041c40c101d0b6a81d5502c0899201400d41e80d40380803134441c40d01000c3d0b400d803040400610306a400c980d64030019 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 802439379 1250 802438129 802438141
    0xb07061506121b050a050304060e0d05120901050106140d060b0c010e1b030705120a05060f090c0a1a090109030506010906030311031905070203031b030c010608010b310c17 75
    0x414180404043c010420820040c400180504040c1d680140503c2c000221451240801c1d0300f88105004280700003503000940c1c000c1984110491500704607100c000708002e46c1804800740041080450882c80c2c80300c042101d0328802025005200034104100503c1d840c0c0e2891503405010f00400541040c050040d103070400071130072850603032000e80b80d4001c00501c0c00c689880c00384a00300c54090420b14040c01440c43d180003244081000a01940100d50200c03d645032488103513042845402210b0b100c1d2410120030017a0300100740b035030407c160842c04041d6070b505071040142d40001443e88010028010500001584422940802d003224000c0c4c8942c03450320b5180c00ba89171a0320940e413410585460410580701c4452050b009030102c1c134406022645010100e14026071034903c015000e09580e40001000d0075401420300408c401004144000d114650010000400156003402000903401482c0500c0304848900c041055491107944001c0003108050000100b00060707600d05107000c118404040b0742 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 802440629 1250 802439379 802439411
    0x1090309090f15030f0212010e1006060f09170a06090b04030f080420151305010e030703150e16090507170403081305071e08100b0a0b0706150612 64
    0x1510342d686a01c28a55134156a15040030056540060b038000515000050000809200310840d020343c0c0c500800300185c46a0100342511010f8200b1800c01c48031200c00e015007504a01d04e07009480019001b00002c05010884601d00520010081d107504d04090440c0140848010030a000340c0c0259601c40c8407141064041d508075000f51070045c420020044d0f9451090040800c1c032221400041101d11002069803079008140c02814214540c1e441c075100c10490b942e0085e0f02d5803003041040c0e010300409440c40e01e4212070244203c5003482e6094407210001c42c0b0b13090134000d018036a6203901d0710450007906c401c1110001d2008840d42004a40b0362146509018000b101462081d581030752455959500c9000340107000102c1c000840309032050b110041500d600c2e51441c044110040c81103c410340b071074a400030f0300d8040044d13803440001c1c1c40c059010b01103490303500281e403d460103030001940d686420b240c80802845083d001052411000801107050b66108045003105d001c0b58005004540025041c0e134 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 802441879 1250 802440629 802440641
    0x5010c0810030609030302070b0c030a0b03011112040215040609090e2a1f020a0b062e02250503010c020610091505060c0609070609030b060405150301090309090f 71
    0x41e54160041c0000c100042c042d402c440303c128403901c0d000d801c1800c295104140c0f80307400e41e030042c04035102008010b002c5103a84650045014110024851981c00c0c83d101c480600c580351081400d03000e580700080554031101d000b15903500034094916134550703035904020216543c1e401401909814001d00c0130300b00c2390004132000b0803220854600c0300b203070042180c01030545044512a4102205400c002c980b2404003824800c0748030f030b54024004900080c0751031544410020061482a0040e100006618081049807480c4080955640040c1c019400080c1c9c5403180c01d06035203070003801d00c07032031107104880300781e20034048500c150300a004580618006988a81c01110840441039501d0000c0081001c5604201c802c03c031001e07200c00075691110003148031644120802e1015500440a1014141e010417000c80140013070b1522086413402d50707030f0704400600054581c070300c02c940322400301e510700040340086900300390000c0080080c11301c1d038030780904003e80c64031a82c07201518000c00556180c13940e004035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 802443129 1250 802441879 802441891
    0x702222003160549140f04051603050a0c080a0b1506070f060222031a04081909050406090605030303060d1a010f03061b0e1002010b030d0c05010c08 65
    0x10340c07040c2d2a0300c001151150031190714a1040b040700004a039441e40e45100403841489000300c0c4050000c603450058110b49416408811550b181140d010000842e504459030800d4440501150030703100d50a00d03e02d0302c4030105880e04080d104110010410030000f41c0c0313140e140d21407104950312558030b07110b294480e2907840d0090a0200e0210004400ea81803c0003400c1c001d034000d0200341410901c0d2100302582206020032500d2981c0062813400000264040c1800551441d48004159003103076125038514801100e02e03201040c3c0e0b5408a400c20072800240d070107802009480c403001d00c3d00b254009051071580c2c806e1500540c13400b003002c26101291f000d460141c0390041c00461541e03d4241c02c1c4100c903241d4400a45030f0307130f207401c1e55404001a032103d000c1c001c060050009280c1402c5041c400c003210484213211140c1c050070f08a084800c0d802100c4980041d000300d44160700340b800d402c0e069015000010900d5454021600d1405c40c0301d0f00107402035039283c0500000c026200c0100000d07200d070f5200b6030304 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 802444379 1250 802443129 802443151
    0x15030a0213120f0201032a05030108010506030d0507060510170105180607140c07080d09081606090902070507090c03020a1206030203030702101b0f121805060702222003 74
    0x3c04003d94081e8000c001004c404184401c6c42d543c242e080d4140140b81d0740075010004000100400c40c0d40030901600d90000c90031800741440d03002c03044001c0d000e84560400180b01a494500184400110020640c010880f46241c800c1400a0b40d80781402068111a000b01c5040043d80149c030748140003d04511603030054840a07020000b00048450640204516418070311580c413010403907240502c20402c1d051080d4840342002070403d131005040040c0e140d0b01c00b000226110040040941c403d0280040720480e56005075503200600b0000d00704245134204051090411104440305035050340140b0a103c0d043e0707203210b2500b1001e150a019621b00f41f202070b6041d2b0091202d01c002d031030151a8400c4010b8682460b41502140c0c400903403005050500c03d03030b0a014001c101d141406819410138824080300d290451801e0701640000c03015011900403a400703a640865002c08648501d83da40800b841803021604000e154240000003800d8840c0340c03c0f1107210b130100b00024450542054a00032169a41 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 802445629 1250 802444379 802444403
    0x9030206030613021309091202030705030a0e06090d150b1c14100905241308090402130e04050706020303071b020a03080310140f03030409090215030a021312 69
    0x411100030803142042005581c00c11102d201c0703034030300f80b00b0200504106002081f071705c5490900080d00450081c580096400411001d40090b5001c0100c40300d480c424100114071500d00d1000c0f4038036011300b0424079042140301e54010240098150401c065801940e8140302c18240001808010583e40d100c030030580302103540c660005088110351500490844e8116880900000f0b00203040d00d207851000c2c6c3e625000307817810514000400300c4841d02503000790304444507414251201400c454418401600384007011a8030192651150110f48c010518242d146403ca6151071040f21510002d40702201e6500c00e803c00056040e001000781c03031044d0269180c6100c06003a05418090005996804aa12161003d4084005540c000103140155040d1780380c01081410404118200f11640440e14416040314003100c4442d0303000803c480590750f231803d022402c8046413004c2940d41040e0f101c5206244400f01c01c0001620140e4003a0500e13020728204524070580d00e05c480c8011881042c0041c2400304204 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 802446879 1250 802445629 802445641
    0x60908060c0906090d0b06030d050301050108040b0415060e01150e0108011806030c230a05030c04270f060c030204030c05040515060c03040302030f0312160e04060f150903020603 78
    0x18015142c6030102602080c606104200010440040200200d5860400c0070a200441c2800c0210045011090078094a103504200001c0c0025600400040060311040c0029080003aa400445442c818001c003c1c0b102d951a900610743c0c410703003400b640d406082032007072400c0f0040c8198803100c01700038181c545101fa40d08187c0180440d03c4034034040b50315540c40703680000c009001c3d06801001004c5000c0300c1c03254080c3d480e003100b0a54601c400098401c41400740240322607980840d11040c80d103000c40e40001c0740e6803a07054460060031424680302d902040c00c00035005100030200c86900192103020204640007100106074100d010324000902203040311701e0f081c4102d042a0f4405a003258910f10075035030310f09003c00015003c1d48404d08068003508049020411814100004100c00304650b02460620315020400c4c0e80c2090010944118400c2440c45070310240c3c090145031050302401360041c0304e0380e5155002c60010b60031511480440c3d280705441030705003920441c07406060380d900401c00c900d0f5032104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 802448129 1250 802446879 802446901
    0x90a05010f0b07060b061908060f0a060c030e150a0210060f0b0702060c070303030218153001091d0102030415020d0f14070912030903060c0908011d0706090806 70
    0x1c90f0b4211109580c07200c3c0020340d80d032508094030f200403010300025454919014000e15911015040030300581c007800240210380e441140da20180c1e0028a0014440007140c01c0454001301c840204a40002c2d071401440c81241c0da503001020782004036021141110890309102040703c00c1403052580030701258806100980d105401080c000d400140541e09188650081a0401210743d000700c002c40d0f40010050104407800321000c1d284d41085840400c64402e44c19400300030708c140509404034507141c4200909a0103649200c030340808940030f1b040459070310391113484000d005105d44250030ba0809c2c1e0039070716402014000c0300d10072944840c41e82d5602c60b29041c00300194100300ca0003803a468a500c1c2134401c2803110b104130409040d000c8213040640c00d0403840500309800541050b0b02a501403058030b00444e0b00a52084112a40023400244200b4542c4045031070b0380f82600061855400c0400c00100503907104445940980c2100c03e030b42028ac0d0340c41055034141d40703d1040f01529084403002840c00100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 802449379 1250 802448129 802448137
    0x3030712120f02120103020a0609080309190b03090609010b041a150d020d150b0405150c0715020307020a0501020c30030714010506060702371202090a05010f0b 70
    0x24180c1c0030540844421110007660005400c0413028208800100251300d00049400010522402d04496080c10701504507102e2254000c5140a2035240a4000d030588014030003000804140e2202ca4581c00c0c403640494a0f5101569000e1040d0300b40100e0040034a01841840c0c949a0b0070039003001c106d04942c0c14401d2074098482100600c54050152001e0180c0382d000404408882d01e60015100b01140c0d0080b403000482d0700501d044480c184030a000e544c85440700c218100d84100720750354039809960b0031103241080507089610100c0d000000194402d0300007002d408603620849032030503055111401286d94549004049038080402119408201016040c1010003141841501d0800780c0804841785140d05c65101103071b00ca03086035007040c0419404c0c400c290704800212034252a2503c9500000c0c1407d205041403040c4861803010008811306000c80d1a004039400108a00910303510110703080442c880c0c100c00d82c0541c02c0c550000e1600c092501c03c1c107050302c1c2611041c41d20b260070007190769002d402c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 802450629 1250 802449379 802449407
    0x1f0603050a1506020c18010e07110c0a0906140405060609100314010f060914010f050307030b0d12140c15131b060f030b031c091d01030302010b03030712 67
    0xe50b80015002500034024681c02610030783e0014a9240c051405018812100441d01d840c005409001440400400c25810341c0019003440c002c1006c0d82d1400c0000e041460180e28950711100505000500b0070140e00000e00b00c2e1180988000c0c4810440b05201c00d0301d104a0f8072039401442000039074010f00c1c0002840c2c1c542440c91038001528460014200c032070190a070009083c1c02e00e2420304200701d0386e102c40300302e01503c0c40100110200a407000042c105180d0001320070b05001000c00040c2d9158400d500240c5030030b6000b8900401803089050a089442d4030480d6540001c03010608020125200c0d01102c103c40c0c800c400034118181007010300d104410000e01082070280e5a5103100000c030f10300c3d0100c0b5098200303500c254800d8510f0681e000d08a0b2070107010340000d15041400811a075034010074a1a04650582480c00000c00301000480d080031264001d040c45001c080ea10302c040200141e01d50b4140c84c441d17002080000440410159603004507800101000c80c0b8180d4020740901c20186641445c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 802451879 1250 802450629 802450631
    0x13060f060317070605010618060c03110d0c0501061508040f03031b02010e070515120a0e010c0203030103021507120c0516090b030d050418051005150d051f0603050a 72
    0x949950b40c101c0c1d04000e0492072440c0400c003240b00814401584100c1c2c0c01050710342007801020070104000c040d05142c1c0d20480f0b040c0100407a035001858024002030705044040415034407908400100501250751104003035945600e0104041040d10718550010300989181d111000e0540d241e0780c55a40c1c1c070707405410440c105602d5011a200c18190b4400500340307500d05400105842e508017401d140b80c5030071644020720a40c0300404c840d4815440749c0c1261100d41c66051940d030140d6501c00384001074001500d40300702c20b610b082440030b2555808800303503043c0d9100b200d0b07540f080c4484010070700f9a40910000501050006000c91049600a1070a200c00714400e42c150f40092101c0c5501e07482e900e00c1a4881d100f0a500c907000383c055803a0074040c0702c0c0f0754949400e0440c00d0a09200203024064204030030b80072402e0769480841c05410300a51510b00800e401090304681c4c24600c070034100b082c2c0020121000341410000450074130041580410030324008120329000440c40e0060842c050080584075580d85 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 802453129 1250 802451879 802451891
    0xf030a0917070305060f0f0a091a0411091905100602030a0f0201150909050f01050708070e0a150509031002120f070c14030a110c0a120201270f06050313060f 69
    0x44c070900005101e02c3d003070b0014405601d4000b407204204c660042c81454640d1a05016000003105542e4079405c55484540041c03869480d45040b200c0c50031000801d41d4098085410404001f0001c10007038a10049003005015545404d0384144505865008840158005002c146401c1707205640308030302d2852900c00424207403814501071912880f2070300031240d0551281008020f000e020050420a5005e04c0001c100910303007510300404050380548050200500340240c0240d5071b440480590191010181085200c0c0c2020b902510170751040d010903020703000f5111410206036141c42900c0350582c0c1a0082c149554411020305030400005288009000d80f1034416400309029652140513240310000440c0c1da031044860140c900c5034034a8080326283d014640f07505454840403104c80c121204215103c2066009100580c1c0078100c14a204d888100e41c120103c11459446c440c50003112070700c19020480c9500e034542210580310440f0180d00c0d0707540900c003210028059900100000c03407850303400216 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 802454379 1250 802453129 802453133
    0x1080303060d05070e01030516050618131d0705092a2505060103020301240e06040b120c0a09091a04020a0f03062705070b03130c06110f030a09170703 66
    0xd00e02e00387c200341c41c154441c103119088282101d9001e8060101290128141003804c1c501c2900740c0010360582d0f0107080c915890703000403001604030000d60050141030750303c124501d10901d07588112502c6a544030b08000d001207044401c2c400c03481c180c0e1862041145514580310b448c3e4008960140049580000b86041404286040c210030503035603034441c401504055255004150960307a01c21003407140b0352416080446000c5440c040d0200711503038103081440c103684401c0020700070641e0030041500400307000085183d40801180011402c201103030141122511352074480210f441e00c00c0001e14801c84402c81301e84480b04400907951051000341004604c41e00d03490725905000c0107034030071901c0c141ca5038503000b00d07400d0aa0b088986805070303407074030701241c00641c8501d030b569035443c03103480d101003400008a03040300030619161113400e4100307000c82011071342c4660080c561510b44008070340901562710001c129220120481d1304c0800307580d840e109650306100942e58204204050f07450944200100040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 802455629 1250 802454379 802454399
    0x9030a0f05010c09150207030f1104090b10090902131a0a08070905090d0804020607080c03120f1f0b0a020703060e030903070603060b032d0f07021501080303060d0507 73
    0x48450701c280c0000c2440300c1c070204060040011604980f601e0300844013034510320303540012140100c0b504000590802c020600344500d00e95003d14a80b600582082c081e1418000100412405801c1202c405060f80d40d4403041107088880360341d002940002020911158600700340c02c0b02000050381180300f0070503241e400c0060034800b00380e8440c0d1030355000584200030f8484a44601e5a2022044001c0c0000d002c00d0340009060342030003000240b043d1408500c4009002400c41507034256000c1e102142c1d13494482d0341c448018290221f8500a081404000003a6840c581981880324030380c104480079051420102203a02e5500700d01d0124045120348440000480c0c180d0040d0a409074020000e155695485010b0500b4409030350000030500d41445020070440404000300d030740c41483c440100008640c142c800c4140500420004aa050820703c1806a0450030000b000d0103120203408451081200ea80000400f810074820040d1981051000500600f040e0b8241e1110600ca141910b21454540102c25 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 802456879 1250 802455629 802455653
    0x1141e12062706070807110706052a06070503060f091003020f010804050c04020d09050f07060e0a030c03060b01050903250b09100f0e03031c0f0c0f030209030a 70
    0x8420358400d030180700449111414a04410006900c040807410110000c43d40d41c420141c01307801001542d8000507541c900c81c041d5081ea01e4050342c1900c081c5a5140701c000d0107608184246810082e66450183c4250401c0c44103040039007075000030740800d0340d80c108259800c0d000140760f280c010707034a003007030380b031030340d41d0b124099100c2c2540900300b0070818154010b0108070404d4100341414421aa0203220200304002070702040b194080764090b940310384101721400600b040180080c40e40c456060b010076a01c001056a505903020755a50600500f9907404000c1800780a101c00740440703415100510101e00290015440e411060520a20b001c40c44c00c0030a2606400c1c81040d400c0511241030091540e035105902c40c020240c203140f0301d04020b4281c002034481040f00101500380200c000c950480b0303600964055010900040a603500c4824244100342c40405201c11040c810341340c4480000c1403160303442120041105941c0e01c2d6040c402d0954250002e40c0004800d603810310425840c100018101a002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 802458129 1250 802456879 802456909
    0x14011d0406080a0b060102030702010503130f081902060c19030f060f06020a0b070329030109060c11100c08240402030103030e040518120d0609052701020301141e 71
    0xc0101c122182800c134101440030300010b0464008001c04000350b82c0c4203080c2c0740c01c41c0075424085041e12851500c00003a500c5220b00811845010920801d40c0c031409400c4500c2007525001c0d40c0c203d503618036a100140c8104d5a03454024500c140c05440000d100f81e000d003003200c141500c0000c03815150840c48245808a41c01240183e008188000c02c00c01c8c4890743c140c0017401400c003171241e0007241640404842d0486d81d00e82404c80c18480c40c0400d40e03402d401000c0c00035001f075000c0040103280304008040510803280c0c00703c1c921807881c05121010031031040f015030328280c4d130311810181c5920058500307410100c0070400860000c00080001552144002c500075842901c40322801802e038820b200a48000400300c0f4809000d11501d100000d1000c1401c0036141c9085c0800796450114218100c01080c4035045810703001e2400d02000301040100b00d8103440103030b99186e00f81340141282c0f002c40c02d0340300c24003850804600c4100d4072046400d100008901510110910103059001080880d07026140c440758 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 802459379 1250 802458129 802458133
    0x28021b070306091a090a082505010b010f020307110d080c120307080a0c0207180228090b0a09052403040b040b0109021e0c19060c0305070914011d040608 67
    0x10740820044e40124580b2050f6105074030090301d03d0426402600c518005074050925200000c2e01d0000021740340c0c03401b0303850407102502039030f0669604055008080c40c0011501223050704e00c1400c511400001a15007065000080d0195030345100103000e03110701000801c40740da02c010701050030380b110309010300180c222030b031140a9242e20f42a11300030401c40d40980b00102091500c10949107860303010a1480559440544a041d241e9801300501c00a128805481c080700c03640304030325812403e40000340c80c1545460b41d2010080e40e11540d181d21688a14040c0708080790312408100028240040c01d0050181c103440c1080c41510450404a810760007100d04880b050b08000c20003041006008481b805001e07210011400d201007013528141c0c10303044802142c0f0300e40740400c1c5014024010001020002c0500120034032900b01460002c010340300341d201300c2004c28107240005110b00e22402643d42102c520780904001c801c100f07030055800036101800e155441800170401c980a841e02e002d013100034052400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 802460629 1250 802459379 802459391
    0x1406180f0a141f1718010c210b031c030204090204081c0201020c0a14010b0402040e150409021003021e0406050d0f02070c030b15040f0209040528021b070306 69
    0xc1001e007645100705403070001003c00340001d03040d500440d092040b081300705070500d0b107440740c0c110504040d004840500b2290b0800c5520618a40d00981140da241d04071009000040251300290003516220304003180c040c1c0c4240300004d4440b100e501510185180303820300514041d02e0b07981c4070f420390b8019007205440390b0101d00a900b03105061400c88404100e01d200841c10410f41502403510394034806000b409265440c02e40f60000070b4298048032000e840200f0441d40c40c1c1e80c4150000446070b048808810641c03261035115190704260080f00b8003030b139008241c0d0081460b405410340007508541106201d600c5030040419694002c07030002e00207040c1540f01e00341c5600300ca4132800d0a0385d841500d1181c030580103100010000342140041412707254040303069491951086544241c0310500f070b40b02640700d07041c138548012000da0360b4010039201c0010f03101400b8694860300040c2200c01803081003400c03050079401c100080b101e564050b00390b044824038800354901004c0e090601d0705545800a03548580d0301c1c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 802461879 1250 802460629 802460669
    0x5030d0615030e10111207091d07050304081602601303082502030a03050315030a05151305031206130f050708011406180f0a 55
    0x342014075503400782d2a0902014000c400015101c148800181a8140c1c552035045035005005017640e0910005048214842c03808003001031241116105d80343c0c0710000c14402d00320340100047c4c1c40c0e200780c0840c1c40d95440d40e1555540d260160784802440c40fa40144214031600507981c03a0302601d0703400b0003070b170360a28a001d100c110b0741c101032a0f02e052000322002a903c41c507046407120250704000c112020141019515111040800d440b070040c00d529000118000801041250000382c000c0080045410611810b02c0203100301c0c05080202c0a503260740084850000284944025540604d41051032a0000511030100b46410700b00582122990465a04107046076840c0d014507522145003c1c4110344640a80c803000e490344600079851495005010002d039071a10781d0908100400712110040154010031010070740140b0080d1189000112000000103100b81e420340d1000d10102c008001515203804925018403e88240c44c4141e00500c0001480100703170388000d10600107110200058100300888 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 802463129 1250 802461879 802461899
    0x10240507020f010909360c03170f0313030e060c0316061805100e162c040f050f030f040e060a0e13032a031b0203030c160e0c030f07030905030d06 64
    0xc01c1074080086c1550b110802055400541c58201ea0b040a4125101e0f103030358a0040b0300e0310a5000c1440d4051001060210000320796100d00b00981c02a03a629002503a2241004043c0c841c2c12101c0b0544c0c2e009010305100c51520081c80d0b0080c52040390000350300702c01410140c4980100700e4040d00c0d9034002004243c2c4901e45400f0707801c0ca51400401409003440d1282e25030198030b025000702c88201c030591890403142c1c56592146244141d0201c100f00351840c01d45800c240110310440212068016007004000a06001040d42d0b44c101100c003803176040c5403c0042c8100010b400504543d03004402d00400140d100d01c0c69805c500608581c1c0240d80841410304028100e280c0807035200040c40602e628140d40500c2c07400e10340f802270740e0600e0110b545100d0a5a000d01500c007a140c085e41c90b000002d444400c03d1000202c6080022600c951814003950382d040303a030080c9900301c82d807242c866010800138a04810052080394840e0705801c000900303404c0742c6c44803403031a00b00c02c8002c19815520401030041e0280 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 802464379 1250 802463129 802463201
    0xb01030e371a0709030b13020102100c0801090c03090206072f09060d03020c300105091c1404090c030b041e0b01120510240507020f010909 61
    0x1019800061041aa101c10070034005918031201c691904003c030b07002c2840740016500a41d046184009903081240d109208658803030000c0b03015219080302c43c0c42c0c2003c0c40c05840e6510344207450b288401c3c0e01e03011103000034120600105040699070380507c401a50b40b0300c0500202801001107103100311040801500041304524a1b007050310748002d52003180da5400a502354001c2003038070034005486407850241d10b8514801c41c0c480c0e010b0075540071034001050704428012440c00d010400400d40c640d04088900304d030b20a03290320003150020701c0011500c00e140070202508e01128584140300d05500320f206071682e017045e003103440d0360307502ca45d610060305516004818509008032410000b07070700303800d00d2004880012020f4480710f9131a1140407900d03a019000444402003126018007403440d1813065601400c05501465024590130300741000b102e000100292407c0ea0591102c42c40c040749034003044100c458500013a810000c0359140401e411200d80544400d05100a0540d1103400706a140d1340b411140b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 802465629 1250 802464379 802464463
    0xb091813020a0e0127020f12060f1005042c010801020d0b0405012d15020a060507110d03021309020415020c15071104230103110a14040b01030e 63
    0x204050041c000340700314800c0b1113814805802c0d172611031704c010140e8001074001c1d102280b98504003c070300310210141607803003c0c2c45034a08503006010041c00e01c0c100441071369000816000070f041030205214005840d40e501900c20145102d002883c01d2405031000190003d0f00b1405983e50041200d040201e121701074500c5086007114140515030400c2d040c0d01c01a01d841c0342162807103407141080c104001200c1001d40207000d04041e4108407000703c80c2d02958440019204840c0070f0707d404005030080d0701c1504140442071a010103010081c00c2100c040700a5000044108441e0b050b1a100180c0c080c0c0354030007000184100c0034a10125030480c100a41030000122456005070000120041d0030150201114030780d650000549102c10a010041001400500394140c0c100050611081102c4599400390b81200c3c8a0b00ca45440c00c0442400d004040da254401c40c100d50503d00c8810005241a0f04505112401854005a9031490b41c1900e0700d0440c040040308000c035844008501c0c410b40c07083c039824290b5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 802466879 1250 802465629 802465649
    0x909020405060313030c0611120901050408093114160f030f0204050d111f0906030902030f060720010603050307060c0908120301060e03060609010b091813020a 70
    0x20745000041041c611008203545944240005400d00f014000e0b00395800858004004102008c48040c078150b5941c44244400303080c0405c08006802100d05015061085a0210b80345007004142d805000003105941762404100400b14400c55003a0640040300075803249481001c07c881c80da05119031001038001d4080302e41e06001180304440f83c0d410261100c02450589000202e204185520400a004a8219960110300b00f0004402d0010311213000d054044212681c628400d45501c0e4034100c4601580000302051501d4400c1000340d010340e2040c6001030000d0300f500c0b545a00800114286401160040041481103032234007249103074600104451074a040c000c000b1981903442e10b5a50380290fa1005003619243e00d20040024812450f000007020740fa412501040a5452100020b800900618001031051100e040241c0f50000d40c0d0350182c0070260141c0402e03400c0c0a0a1003c42c3d02030044d907074118481c0650301c081411400c03200d80c4103614404160210f12a1071042024800c02da5014100341c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 802468129 1250 802466879 802466887
    0x60509030904050a09050a08030a0b150d1401060c0f0c08030a1e0e060f0f07140304031a04121d030708061603020a050d0f1103011d0c0a0c06021c06080d090902 70
    0x20b000000d90307d890903080b80c04c0d5500c3c0c0e40c2d5025503201a104c40454980c0200412198a080c896844041c02c500c10110700248628115404070410181c400d00c1100700241408100c1c1011074020340151514074001c010400c2d0300c5407144e212030310b10751014005074002541c0751744202d070101021480c06516000c61800f42c20ba840f60300005400307405503104500510700700058210a6114910403030346900e61040f03584012406081550351640c01a02c01030321710101d1004104c03241020080500d1180da4002c0a8010700100500d0403070341940c2d4140c6044420220804100c8507960400018000740f107004024040345c40c06104604c5802918049642070500511640c08215044400d440c218078000c5000611000400c02000142c4810707a80442d66000010011030861a09800041c0d1410340c2010814592103c80c0c04c801c0900c41c1003070706c1c4000340721601d03400e0000300f444d001011b240b2480005416003284d0f41030000225400e0707500c40364140c1e000c0049000d9150b042102c4d20020000c0384400c5080c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 802469379 1250 802468129 802468133
    0x3110f181228020d0f06110703050403030302131e0306140c0306090712290d03020c04090c1a22050a0b1b0d0315051f030e0a060509030904050a09 64
    0x941e1a44641e05510b00c40500750141072040e00d025030044454000703000451242d01c50904502c075401541060b1246401c1004005c4042800300c2241c16182c0e140e640e252506103540c40441c000d4000f01e500c1c0c1100351100d100008d285a103060000c8500d64850f0802d01041d06c4e5241150440e0b001918803906210701608000d10a1143c4040da030b0b0210381035a190010340d60303540040310099400d85421613110b280c032192a640320f001110b1180154034024480713030721030a0541000180d600b0780c080100180e00c115041d122904107500030f0000c040c400c84100030342c240c0f50305000c405040000c1204000707107004110a1803101c0305548141641540f0645444c10f42c6c00d03c000702c0c800124a0050b611444400140b604958a941c008244102d251200f030f41ca0600303a0f2040200909000c401816a00404d100040780501e0301e40941c0c0c030000c454250020044112010540203800c001c0c2d070f00c00150140410110100d800c5015140c400c05000014582c0e46144408000c2124006094008401d00e00707003950300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 802470629 1250 802469379 802469383
    0xc1808100f0522020a03060e0a0309050d0c03110a05060f090906190e04080702030a0501090201120c1e09050909012306030a020f3601090b030a08090103110f1812 71
    0xc80310400381641d0311075083e0303030011400001242c1c0c0000c3c051840c000c01c1010b4281c1c045455620548240d95069100341c0e12030400c11440f0800e8005448280d8180f81040003405181e0608490744000d8480d41000d6510710008046400404038072105000005071400c1e585060406c00354407000c2220301010225418030f00c101011041d019807400c00b000c000c00304050048000a40340041d81c02411544501518a4030078064441c41d60200d01007808030300b0056a8007164024403c0841c01d0703a0300d4480e500812491118114814810300051124103800407906807900018a8814004000040341a00c0012070310446050a0f81815840700203d00034400e80d903401145807409181c040b10712205541c00c4400113112040b82040c54008841a80104105030b110f9a407121102004201210840c1c0c2e40c0303d0141c0296012400708561581010109900082a400281136100410303d0005a81e0001d0000036860340c2c45481e09940314070000c2510004544804003841000c0025070b80101ca07109001030301a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 802471879 1250 802470629 802470661
    0x606040c180308031512150a0b091302030c01050307020d180b041712090a06210216170c0a0f0c03052b090503120d0e070308030702100606020c040c1808100f05 70
    0x11031418007c1010421110058000007028000145900082e0405802c40c0040d1507854504a019009080b0781005540c0201c0590b80300300340c1b41d0060411080d500400b1540303d43c41c40d0311028005200807021440030102c2015002601e10000038518590fa0718039541e15000342c2440004070408201309030503141c0c540743d847c80304031040c0d403c001480e2220b44910a00741e003500107803150814400701d05600010384062041c1411401488840c0c85142405000e6000d4440d400d0070b0019507004100d40d4001030b10900381c5650f40c3c0c4c001c0410200b050340700c0d80c85d00c0c2002c40080c0d486c1e16074000c542015904002c0003128140a6500d4180f8588181c0ba282c0070a8175020680d002c0e600b40c50b0049140704101e19282c0050100201500954002c15241d25003c3c4540e0000c0c0c404100501c40e0f0380442030f0703c1180d48500c41c19650140c009091403a00b002c1048054a668801c1c01d0801c0301306204c1e40700322010030103204003400c0c0305406042c01e54500d00d5403504485c00c0c52022800d5a0600047c01000f414104e151 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 802473129 1250 802471879 802471903
    0x20a051b0307051b010509180718050907050306030f07090504031103071515030501020708041e0803121302030a0c05031b1c060204150512070c03020606040c180308031512 75
    0x20b10541c66138540140d9080c0944030b182d0303400c940340c540601244245480094401d400c0c5481e0000c00c940080c8104c022090180505d5802c00e03075483c0400c180a020710080d6074441401422140300200010a1b10700b40081070780000d103016200d0041c0403c16802514080c849560795002b1820106a5207c071042910748484d88815140e48035011030350328080000700006903070003400943d5280e5070762a14001d00d600038800c1d401c14140701c59601c1c0e54014003104040071612004015401d00140f0400d142410340c001e00740d800140022016500161803d0000610640c05148000001407500042c5414901c80103c807074400e0030400686a0166903e0114440681c28a400e20002003184c1c541000203226030380180c60445402c2804803030780d070b5000d0028030b2a003903802080641622400000c2d91260306c0000b008025821200021341e0034101540003040520302c0c3d107800641c0b400d00d110341103844140e94005840e420000400c0001c002200f11210480d20700603030303105210300d228810260b2900e1a07c100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 802474379 1250 802473129 802473163
    0x5030304030c08130305030409060803040b0a0f031b050304060b01050c0a030818250e1501210f0f1401121502190f02010e0a0c2601020a051b030705 65
    0x1601400f62030b03015942d0200319446143d2810341c4909006590ba0041c0c4508040341d424118003241d80b041c048241c3d0115451004081e0901607a000305035004050858403000700355a4184c242400100c99911172198035450701c0781d075500e040c01c0c1030410a0318842082c43d41400001c00441850300700000d090851907815107016000361b11800c010f007043c0c00b0400c88000b542e116080d2003002000070742c5620b25031046444107007401d1030b9899000c90b14021080341c40040d032844180560099501072032038812200340101c4641030102c2d5202c03540048800b4a80c10320192995860341030401e40c503501c07403e40302c00c03280c1c0c2083c0c480d0340c03502600c1d540b1a030700960010064100c09880b105c22946a0b01a036222442c0303d0070105144410b07000090031400c5a918800c015801d104004900e000089000203420390004450a401c070b0a202c0f601c0c140022804403040c1000c21aa180d210180d17081c80504280130607039a0f404d5840021400c40313424800380000c58002600200b00e00b200040000030320020201803882 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 802475629 1250 802474379 802474397
    0x70c080301270e0d09120804060c111018120c050f06120f070906030506090c0c0a0507034d010c0f12020d0f0e06180a0f1805040503030403 61
    0x100360b003202076000d02c1c2110307010700784801c90078404800703d07055254061541c0c0da03030f00300ba90716050491205020030000d4800c8400700000e110032442007032010000c6011302c2e031081c0303600c4070f65000c600b103254046002000500b001c2c001409040e1002c110708014405200480c2000505440da03c11503202442454402d5070310204c1e081454a41500741c6080404840c0b01c0d05040c034200100c0c203e041d84c201d60005c0041c40c0410003003401406441450b0040ca0302a08082895813628041a0240c3c007400d408009403046202ca030002950401c284d1000d107100e800844a504061440002e521101070440c08101c8038101a021035038190000351a82c140c5032603900300c1141c0034040165288105c0260140030705610002035000e2044240c4c1880e2742c403507164203e42c8032454442c0304452020298504e040020b0008180645a2900c0d0002d00f000300001c03d4846881603101c1d0000d540c5c50b00c0daa000c440c0d10f0381c00c2c10b02004071001500b110b000072441c8103000d006e07510f0070707580c0c3c3c0da01ca02c4010802018489040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 802476879 1250 802475629 802475669
    0x1809080d2004031203150303021b03031c1b0905010c0308060d02041a0a050f0a090e010e1618060b0403060c120e0f0c0a0503060103260711030105070c080301 69
    0x507815400460201c80a41e0700ea483c0d08001c20043c0a0350352010100c0d007032941c10000783c0780440344c0c4d030116509640a40525031000300542d407041801603c84d030b4144001d11200c02e21140c545001c2c40710700429100040e00354034407801d807500c42d001051118240303c00d0001c10070013079030403c0740301004680c1403510200942c1c0e80c4000489603070300b8090203900705142001880181c1c03071050001c20321900403644866010395031410080d02060700428a074210841c1c1c403041141d080b071030300040308003030b003810000c10b80c11030007805903150400002080c0d0800365030100c00c000342022080707402c070555400070083c80b01e1810311442110600c81c902c4004d0a441c0ea510415160612500f0107056844403150280002c0c03100c080e040d43e03a512a46401c9403640511421017001c0d19000c2c009000b2508040e002c1d0089030320390b455012406407400511001c0b10410080c1c403030307800202c0c0014440d551080390030001100b1010306040c00c590009003020148540c55603400c010411032816281181d90400d00100d84c002c0c08 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 802478129 1250 802476879 802476911
    0x80f061602030f07030804060b0a050f01050c01020c060f04120513060c241d1506040b01090b0304030302130e042a0506030108030c0c060f1e07020d0c1809080d 70
    0x8075050a20f40b010210b070002c2010303440352500b4002d81c056a014840038903002e08001072480148229a44040301200003201d55000340060b1203882d69060006080488492a0030709046c802c584a0590401076000c00080240c00008401401d030589800c81c2060544105071003280000c2c0103690511503010b55035810494005503c42003d082c00201120082e54442504098034003070b211110a544408480744110100058080484203101a101d140380c48403418030000b40380010300c1504102d42c21602165103880c1c00e00039806284696170050b03890400000c10907440140360007e22500c03229038140004203002e4101c20020385480540c05118405110307035107038542c0300c0d6401036402c69804070000400d403c011020b0091140807038140d0300d03501c80c142c0401006205440072000040c000b800305200c1401c1010482e803244040070421807501005030006881220012002c84040a0640e030500003196001c00c0300c0d00c00d05c0c81030000d200f13004c803554a50080e801f40b02c0740b8a0307003284d540940805075030781 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 802479379 1250 802478129 802478137
    0x809060d020c0a020f0d02030a1506080d05130f0e041b05040623040b06030a1112040b250f081005040c110c0f15031b0409090309080f06160203 63
    0x100801190b0314000c1c880c031952941c180001c282e10441e0503c80c2c0392078504041400f2080340da4001e000d07000c000000d0740c0b0020584100c225000c6d00540c0ca03074020030715900800041e8150f00b0a505c9803525042816000301c441c3c007a5400542c007000ca10402001003461115007603070804d5002e000005210405c6072094010701ca00e40c0400d85c0241021000100294058005015001140c5542c00e01c44020f60522041d02e69880c0300c47c1c0c002c0d00400015401c82c081e40c0c4007182120000821502d00b0607607040300000400150b8055540e00003140074061940c4481c6010555410b014504141e28100408040c101d01450100340b818000079000050381c0c00841c0b100c0c180505002002040f16403000c01c4010b003210200e000c1500140305509040b60185400c2003c00d11804c0000c069001c0108007841e4503029030005482c00408200d5103849019034407641d030242010313101c03044000400004ca800c0081c4040c06551000c001303074120240d1b146110303901013445e641c851044107aa01982059690481c03844c0b00b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 802480629 1250 802479379 802479397
    0x100c0218010f0314010c020d180503010f020306030624130e1606020f0304051e04020d0603050d27031b0b0a1821060c17090c011808060103080906 64
    0x1403180c00105248800207001000d0780d0003444400c482207100c80d116400c8a07601c1c24014050381c400185181400d11070321000300c070034000714070300084c0a40c0c0340003007420b442007035141d94801c035004000c229450030b081151035400403440d00f03411b56944006852407060300e41c0d2250b080c0141c9aa01140c45108440d03085644115019011074030b1511034600201102d08071030040c0f000502410303101d40240c01000003902c0030f4070b00003055804400a1240d64800f0440904101a0416024000400480620301c5103000460180b03020303002c4541103c3c001802012041f0b4030315080030b00d6203d88500e80201074038150a5075030003101d080703424400c6920481c5000003170340007600e840e1000541c0c103c01e5500a00300c2c02201100032074202a075403109900100c00304410440800c000c55440ca11012502540001c45030302001e081908420b0705040050904078012035078810264000d0181c1d02ea02e5034400b0303545400d555001e078026255410315103100d8445070184400313008400c1c0840d0308019642c0e95000c541c1540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 802481879 1250 802480629 802480669
    0x13050613081209010e0d110910080105182404020603040201031107050a1a04030206070e0609040204060c170304051b030c040507030c020d09260a06050112110a05100c02 74
    0x1445402c50020342d43c809000e00c0e00007058030704000c055003041d800c032405041c1d018010315184c0c000c12090111100c1300608802e02004010000540100300313219150148404812075021080150009490498070319001c07200c10ba92202005001014000000d4002e03904645c81903807501d0700c2c001200604401c9012903003085000842c40d04002c8001511004144070f04600000564110301074070ba81c4a0858020b0050f0300131400051078035105030008003c40c04000c000509002007440860226009a004500840c4024481400740070180c40c110b85100c00f800c1405142d8a0036540d81a00d40c400410324161f05188189500d0302607a080c4081c4608103400b4000b0080c500d403250004001d000c031542c00784054010181c0058100e482601c008003658a9003291146070044914005114640251202c2107809030000540002d446409401d008002d0302d00b4400c2d07182050b01703141c400c4800041240d40710741841d81d0200081c0d2601d0000301c0320030020b410304010070383c494004a02e01d40f24582d0900f0240b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 802483129 1250 802481879 802481893
    0x2060d05011217030411060d090b0c0a11030a41031e0f1b071505190204051008190509100e0708070312021507020d141305061308 57
    0xd441c2220a542e207503030140b5821203003480b110f907401d50b10b031000b9a400382c02d0710322981d80c28207141040c0c001400d20314090000006e800d07101781c0f40d03407280b89003c0e00c10591209000a0b1040855400300d4100054002040078514050a0480242450300104900c4898140300d01c3d04030b03580c80c0b03201d0014440b01e44006070160004001001c3c4402540121803280100c40800f217188500c00412241510400418032a440b0a03100d0194035940c49209100c89100d08404011a8000a2010707040d98036100411602083c0b0341041c543e48000c402e010440c03080154410312040006640300d2018810300ba50704d0801514039100e441a00c0500c00307480368a540040d0519007030051540c00003400300000450040708200a1903079144150312240c01c0d01c00c8403010f074048a02840030039450000c05947c180b00d0700480340054040259070229920464060000d03800c01d000c0940c1c210f03000303002410b84001c40c0305c40300e00d04108898a8500c58113140a00d038007600340071900340d080900080d0b800c000303405180211100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 802484379 1250 802483129 802483139
    0x5130b091018020109270b2701050108130b010e15030a030f09061d090a151d01062a030e06070b0402040b0603010524130b12010608070c080702060d0501 67
    0x8031140c902c500f203000a901c040006450f00e40051451071820440315501c9083e02d02d061500082d121440f580c40d4480c0910007102100218100e180c0c0c0e0304000e00c5003110641d8502000540f030201e005110494400008030303540c001482401d5002c7c103540c0e031100541e00719103a28140c00460343c0d042100c10342502c56007000c0e8007413580203d0140c2d9511120350320180101d0715035404540606a40590300c0313a548282c844c0000d076207410210107500c00303248200004c0e42c420940c2c1d451200803140c1c1c000307440000c42441450301c5d2500c80803501d02400312810b04c040c1030100c0c3d6400c409901c400640c4045040c071000194020503128440d0003050302002000b0640301d11650510b44e02910301520228861464145100440d00309102540e049400040c440707050011050810300b00c2c5007200c100210309000400810441110700c1c800c00d80542440000c5607104d0503403c1c01c000c0503e4041e009101806603000800511039400001995031560004050f901d8500704d01c04180c00c1d004078103030b00201034205000414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 802485629 1250 802484379 802484411
    0x60b2215021b040c020c0402031b0301030803100605071e050703020909070e0a0614010f09030602040e040212151501090801050a0e0d170601030b030c0301050703051905130b0910 78
    0x128010485002050b00c5a144100412a0312142a030005600f20342c82107155880c082d806103503c01079000900040e8840c02006070381c142c0c000d0f00101c0c0d003850044148180ea040c03016445018202e541069881d0800d030781c6a4460211021400300040881d1071941401c200b41440084021a8080c00c100c3d0541000c03005241c44200c0340c09201200140803001a480b5a003d0242c01c003116490300c00580c0600148004403100c0d036a243d941c3c0305000c04224000002074041c802400242211840c0c0103260030b052041200e0b040512902e07451982c48602580d03580d4060039032450704441d414845203a95240c500050b9481d51090b03204011551908042082801ca640c1000f040c110f140070940b42820b64203d01515035144050404505c2c0b407000300020351a5000b58040300b03056200500301c541e00c01400b0f00081c2590401c840460001e42c488090244c002803105034640c0c886180b00e400d00992070401640d11342c0c1400e52901420f1101c1c2c10011a1036010144200c00c202e042c40c036814410042d250656903 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 802486879 1250 802485629 802485643
    0x330f0c02010e07030c0605091906051206220513020909060f011a0d050a090b0a3602040b04091e17030c1603020c0604141003060b221502 60
    0x25500706202c0c611006404200101a65800703500d000c00d003800d04d00700b2201038208403e00303030300481d2840c45540c4641d00800608001d0a0700c0d9141559014080f0000c04241c1e000381503580106040c0d00f6640d140e160070b003a486151601c480c00022544d4400785003043e80c022100019410100800c00e100e54980f004c030380c080c850120104030401507642c810341000480340300b81c48420070100a0100e07090100d90340d00030700d8125202000101d941d02c0144c96203a400541901d61100c00da0307444280e12510000c0c04003400440f20861038401150307021805e0408031414608000f48626070b2810104907681d62544080031b07590700701c40308a2001e00800115210f00620201c15280c00d94006800541c041c60141204d10407a010b0400c00d09041401c5401c800302210400d00718298014069401400e8680c00f01070801400d1301654950048490414051b85807a00c85141082505241040c821142060101c1c2d07110803e25a000f01424142500031030000320f29008566a20001140184983d07400200700f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 802488129 1250 802486879 802486901
    0x120f02040b060f390312180703060510080d1106090c010c0803070212030a060f2103050f0d020a080609180c1e0a030c030c0909330f 58
    0xc02144a200d07003000982d014054070f21040190400164a45000640140180d25032482c0e41040c0305440c03220f5402012a2422980302c4c41e030000c6409078034540e07200000c6402000b150f00d66440c00b1210101e00303445664074000901b03500e44034404207618021120004004082410941d0102142c00c4001070040542c0340b492401c43c400c3c140425100600480c40300c0d48103105844108548440d40c1c2d5031401604014040000c0d0700400a1518402d440140298820310a80c0000903105d81400f401d1402d80720b060f002040310a044001142c20a10403901c0144100c0d010b0401d540c84d02d001e030400d03480900c64070910201c1ca80c0007142c06e1807815040309807140501400c81e03c01030f80e17554120b210b10703410704202c0c042d00041d03000301140d00240c10100f0080c0c864840c5102c0e40c4d00418400c0d404078018446a51044074280103082c0c0420510030562010340c00381c00200828002c0610715200c0348420300c000036001044408181c4400e0380400c00c40060359600c901c550051100204102a03080149000c401d5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 802489379 1250 802488129 802488131
    0x40c021c1701060818010905060910051e13080c06011a070b06122104030308010b0a0503190207022e0f050706020a03061d2a07020d0804120f0204 64
    0x3008203460284498a407070881d8090541c400c0d80c42c0c400e08aa01c00c8016107030011140703411100703803101c035828015090221b0094000b411982014500320345008180c000d0340c01100d1818060107200040c1aa8103015141c500c481c02e80e664840c02c130711800d03144040b00d004041c00400600c0c00810407020611a04035003210107524410007044043c40e4080c459650001e140c60020000a02d151400300001c82040680600301c0e00314081101d005102030443d0080c1250603000807800b041010750200100340074003555052a41450308840c401342031400b010341110303a0543c0b0b1014804200089a064650040d00106101005108805208614140609510f0902034445082010140105c1ca0490051055078510b49456042c1c1c84140007074000f00103550402d07441d04800242c1e507010001403103030000740d00b011243c90304049000319071400a02210a402c461180d41c82c00030710f8081d90568001a405680b8035262000340e140c664028032a0350042c81010000e0b225000a00104d614181c1000740700340c034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 802490629 1250 802489379 802489423
    0x6040b0910110a12060801020d0506030c12122101090207120912060f0f0903020313080c150c0f0d0903022706100509100c060b01110d0e010c02040c02 66
    0x400e1000d8484410315007441440401503030f50040e00c1112014030aa082990014615803505251400d90b401104402e294540716414440b151a0520884025038002c503140b15210403580040c680f174504002a0b100440c0000c00c0c10520000c5a01e059280c820300464000c0c210f41e15400d84c1e000a4010301d906440c2100c11244965425000d01031103003e407107400e05109110f240594640c805449542ca29408454070707002c1c0d800001020b8041d07410311038401d8005d503440d2084205650150100b61b44083c1a0780e0009004070b03002c1e21504c02141e2840058501643d81d140901401842c04821f1a9040358903c200b0440503442c80d402210303074050f244216404803413500390350050203521104a9030444001c0c010000b03d9402e150165085902003164141242403040000000d0804140c00b00c0b00004900c11020410801006214003a80354600b4204070a04542441c105643c409030f58840c1c8007030110404645181d60300480006100c107a00400600200d4081140291940f5501c9100c0700c10034000c0c2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 802491879 1250 802490629 802490653
    0x3123c081909030203070210090303080903041a030c31091401060507140610030209060402070b15010c05100204060f110a08070611130302030601080f060604051806040b09 75
    0x21048601a000c40112606500c421110441c010304949400b00c040d0320007000300c400180c880d142011042515a02d94100080c51814050b100071001420841c040d08104002d10000c40e0000001081c0301441106d66200c1c1c0c1c480d1202c500610403219145200080c012000d40300841082d2800396142101d40c810310f2180e901c510340c4040d02c41d020101108240410011b001c083d10a0f800f5144090146902d56103a03800141c209007010801c1d141c01d17124840c0510103000b03506201ea81950032040544085282c03140b19220101484805880300513001038403440c40c08240e11550700b503031445d07410100780d47c1840300103500c2c10001d6000d0311032400820203800a0703200160240740803526201004000c0c09403107055a83c1c0521541c0401c004803805665050392011401080c000703005034103404c811320303c44241540101450b00c2c405070700200041e840203101da01f100b60041891608858261804101501d0303030b400c456418040820030030198070030b400401040c044040b0320300e80140c04c2801502d422182c55 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 802493129 1250 802491879 802491887
    0x20c0a11010e0f060a03060e070f1701031e060b03070b07061b08010b210103120314010501200717030a0f0906050a0503060d05010614040f02031003123c 67
    0x486032207a2014108143c4282130504500414800e0810301d0009105929040304480c072140c00d41d001400150030703444001c001c6400692160788a074200c195501039600d181e0343e6085500e000c51610300c0c4580b040c0c01c04010011560041201c0342c0c0b0040a58045580301c04c801101c54210090941e43c0c103007813044403150f2a840030002c4051148594800426a08218880d4050761100c2c40801016100c0700d00319590b05070545040780a144103d00808004907031200c0101079400304100310510030340d2100100460703070308141d400f1030b5004c54044011002d80e181101c03508082090340452049000c807107407520260004001800b1000c81500d9551b0b410039400e40417200500c507401810045041040703a0068039018a01640e4880c00080015004000c0d60303503030b80d00703441880e44031030080c0743c10581644040c0707880d01079043d140441d40411411881c3c40f202902c0111400c1c40b0152010146040c2c040340a41b191844c241c1300741e08580c14030240c0441d440280c000b00d034105142000380040c14281207826101d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 802494379 1250 802493129 802493147
    0x30601020613050f0d0c0b160e120a060c08010e09030301030302030d02160507090204230303040e0c0f0c1f0c23120f0106020c010906020a0f08070204020c0a1101 71
    0x40e40100116652880600926146114107a4a622131001c2c10b28031098100081c00a201c3c6a685048540b50b582c80c0c40d40a095020301b000b00c000016503801082194000d100b4138503100c00b1a098989a4000072038641003141c0b541003e810142000151617005800820343d5040719807000b00c112040c1c0d5160065074581c0820b000003001a001003051610108054014000428a4080002c01c04640c0e40d505c0c1c0c600701860717000708442e0ba00400c003042040c5050380c1404058a401d04040d41590b02100002d4584c4224081d4008d06802c00d000f00755009001e400340c46072915a0002c80d0740c0d401403e0071070b6a4452064400f440d144140e01d5003541d6803401c0d0301503283d1a030b8181c0c40d00000c000b84803144031703040008030b072401c2c2c240032091104582175541c0ca040c16024005812040c2019410468004d0a0a400b810500d05101c0002420043c45038006014034a16070404d140000083c0c01d031070103a0b090321540300040c2d801400400d490800d00004110a45010301c42c084868401c02908015105000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 802495629 1250 802494379 802494391
    0x4030905101409061b0a0b010f030203031603021c02030d050a090b06040c050c0a03090515040602061501050405060c010b010f141e0c011404120503040c17010e01020408010c090b03 79
    0x20194010b50440122030003601d2100f1009200500b0100c0059107040307813481c140c0d8280450341c0060b11020178040b0009180340036004a03822142d10303e0841d000f290f43c910622481180280c4d20320701210a0500c01d1124000c004260004055500c40303119009583750400840f10502a1508010525a20701881402e281e154040320303130700203940c843c0100001802444004003d04c54100809030032460144008580c3e5482a16006031060606d0180440c030aa212840c0d00741150412041c850b85070002142c50340030031000c0036414030740d0082c00103c996000765804181c014401013000b0689907010740148121440070781e00d200100310621300880f82c4082190304045101003c00400202c101c403202c001c242548840c0c1c0691821500c0074142e400c560900c5520001007808505010070041485044d9407407406c4d40c079006040d8142a2038001100840784100100c00c0e40182c945285d1007000e4104110749071901d00210344807513485060380d0281c130505030306000041801e680807440c003d030300d41503d0140c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 802496879 1250 802495629 802495637
    0x605040b16080f06060c0f0607030e0c0f150a03090c0f06170c04150207031a060a120b130f0c030309050109060c150513050a030e0906030d0806060f0d11030403090510 73
    0x51584000d11101d640311442070056801f800a480d195407070100310303590046480d1ba4000548040c04040c1a04200e0000c204274841c495540c29000b843d9200000707101402c44c940d1103035903240200501a001000d0b481001004041004400103410320b584a10070220740054940c8462041808003006a801e021a000c0d100304005100c00d00043c40107503405100350703131140102e4102c00d44a844203d112003940645900031442d110400c0748604003030504a00501180c60704121046455441d004130300300051130383c0401c0c42c00e050040d0500008420f00341269411441040741207441e810010280106402603501240c0d01110018040340708243d05d081d0240c1014414200c00003581003100640009402408060315007041c4501250b01403001510441c0707e40c80303501c07050035100d003407004a070001001786100ba001201e200880c15000102640c0c015402c0302e1095440c8418801140c09000f210081500c152914a2108413060000300a5019a002c1e840b491406a41c41c010007401c0c20f030702c00c4100001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 802498129 1250 802496879 802496881
    0x9090c010903120203131530091109070804020a290a0c050f01020c0106050d0506070305091f09140a0503040b07020a03122712080c01090605040b16080f 67
    0x450200c11007540f01244510540c0d1600d000801802103000b21750b004003c040b0054280514002c0d0080c00c9800d0b09000400407440c1a03d580207800d00316041c484a120032151124082c40400c0f220781828111914020030124803420001d000820350700045408030301032024180042046d81c2642e0490f00148009203172400d030f0314030580216000d5000a00f21005100582013844001601800803c008484140006842e0a107185005082da0f0041e405140a009442034060104402080f46644094582001b05154403181d040c1850076034010312000032003c0d51a182c0109000c203822041c2c202d4001d00340042d003958180c4c20036481d2086141c000305a580100020006211648003070800030b40000d2407016129625118001110402e05100001840c0000052003007001038a00ea9030508204c1070800d0303054140040041440c222600240c101203001c20100c2c80308809420442225500403c18000c80c1424501290000000e47c1e400306203c01000e10389410034030400c905842401c10310158051 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 802499379 1250 802498129 802498133
    0x4050f06091b040b030a240506010c0303021614010f110307090302010f0509150309010e0f06071209050a03200127080c1c0e01020c0d02040b1207090b09090c010903 72
    0x2c1e00c5800e050441e0099100c03403001c006903400f403100d41c920354001c121003402080300b0803511010b074944e405400410b0b8a00803c3c0045a640a0040d0b44100e50605005070364100300c02082003030500505004010144d4481c50501e05003064000c0303402e07128031000030301c001c5481e01c800045501044a0b050000b80000d803081015601c03900984001135107a00b00b5514007000100442d200d1503507049087c0c8950230020905c14500000d12130841e580c003003c2c000c0c1004100070081c203a00c80c03501070b241c041041803502209120b4041039025201c120361000803141155210b28000d0100c3e24510310041c16000c07848140540c1c084107000d4140e11040c0c21400004900203030382c2d00304c2c0d1001c5a403419648448240100313031556108110113850013424202003e400c007603c440c01003111001c2107603a411504070030b00500041d10b03400445ca0150b41d044501140000e80c6402242d507070042004419514404c0d01340004070856154481c07484040700341c800c511075a40c3c1c180b5596480b00b101c0415800a2900002040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 802500629 1250 802499379 802499413
    0x31d03150a020a11010f02030403110c1e0307080a0b0109060605041d07110f0729040e06040e07090f06050907020a0210050c012a170c0a0c060c0804050f0609 69
    0x2416080c18803022110420017800c4490400c0c0c0390b1a442c0c1c0c00020310050542002a400b00d03180107000800b8121410340c0402d111007a90381424082e0548206c5004082d541800050301402021048a2981c00c1c1400c200024100170321498160529008020400c0c51050044609585040c590350304052021542000a500010f000400704400c65010000b01c1e84180100c2c0c0c500002000204000f9061032081c0c0402d40307001c903003190010304071800058000c07070b0342041d80c048441041c1c000d00f480d50b806d00441c0151480300d240c5007150060b05004119860f0760392151200d200800d4041085603111400c0c0716442c0030980350400035a01a44a04005103030595110544103034500d001c034107010303000344040e081d00c1e4110031245900680810349404520740c000080c519441500d0510644000070301d4034403125070301506002041c50002803d003a242d00414030490a03c0d40500108286048080c004000b40000d0301c0444090040e605900b00070040040d0a07030280d00410050b00781d051007120185 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 802501879 1250 802500629 802500637
    0xc0d0f03140a0b03060c182e02060709051c0b2a040806060301090b010b0c0a1b090b0a081213080d03090515040803040b040501140103031d03150a02 65
    0x504054840314250003081d010340345180034420400c00414102180c00415081420003480c031317101404180880400d40c0300460042c0d4030b200e420340325803648015100d66405440082074607000720007800607001c4040d40e40010280e10a045940e20145140c3d150b000f08a8440c44d480d00004051240701c2c0b0120200300350b80411a00155815155800d202d24045940d41c44541c07a140e00e01802c00105041100e07000600c07080e948403100710001c1040500d66525450440f806010f003000303020b001b0410942c102d0080110081c0c03260003144110142d0220f01d0f0780f8110051901414440a050403240191401c1ca80606400d0722001c0c0c007c3c2402c2d04406503980001c5d04101c4000c03101c0c411044000840450a021850040040e42d802080700902818003500c0c280300012a9180c0e1392711102003001089a100c10740340c00592110241d013a030f844905241d07014211000c44401074a03c00030000040580000c400d0b402403c2c2ca0541c40e100000301000c240d01c8488101d004021740901500103080042c0c154024 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 802503129 1250 802501879 802501907
    0x2031510050715050723091311030a02030601020f1006262109121b0d080307030f0b030d0215010b040e0105060c0111130e0a020301061704170d0603170c0d 68
    0x100500c092030b48102c070091b085120252000319000403103954a050005003510b1400c03841c842482a0901c0324000d4a00e444010141d2008170781c00b02c0401d0042e8408c4c071103c90324076200380403101718164408094004200502c1141141e0001000460140300c00c1c0d04010031025600000e081d210510030185401002008060703c2d03c12000c0154141d65a41c82d404c6019507008580104200a412034100c0403000c201d420543c0705255004005e800203901404499001d845441e000c224070014a40c644040c185c140901e56142c041c40e24809503040c2d0004810201840d182407002842c0d80e943e11100c40c0d44501c1c050011a0030340070b4014005410075a00500c19845042c000081070846540320008540241403600c0444001305420001d074606611702c3c6820003a055030442c0345500d061030160110a4003080726440d600d600001a0500148a01e0001d00c44807a103105540d0701441913169004211501088811580000312440050710034025500c9118004000b0658504114416244442c8c29015 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 802504379 1250 802503129 802503137
    0x2100e070510020705130605150a0302040909030c030e01031503080f0f040e1605040e01051c0b1f080f0a030804110a09090203010f090b13020f0301020315100507150507 74
    0x1c0d4030b80754031485103407420a50303000e008040d042504016001d016140c00018481c1410300030b00c0151745069103840070f42c804901081e84c03541005410340284c010340d030022901614040b424018107410420380c01c4282d219039140d60b220044400190704986416021600710341d071030b810600000300b081004042240310800207906010b150340020001341e220b0b8000321440c01d0160180112005121419540048242070140c00c1c94101101a082e1080500c585442050318040d43c0241c401c2c082d600a4080d0f400c0300d0b802400f0702d802003245d00900000500c52607850401b0328001032015000c240d0061084c0c004014102c0e03404140c6040314982005442034a05104642400d00b07641c0d10303051050000c00a002022880c41e005004041c03c440e60a1201894181006494400190303000e4200390701902207501c284804070103001081c03c4c2c2222084468140d03100005000f14031601080354284e946084070000c500020b14101141c07a800340307403401451900c20610085421b466600001c0d400b03102450 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 802505629 1250 802504379 802504393
    0x1003081c0c03060b2a0d0906020d0c0b07050304021c110f030f1c02030409060f090e0303060a030303110c190516030803070c030e030d09090b0a06021015050d06020307031a0102100e 79
    0x2081c0b86c01e00c004c40c007540022401d01030b003c0000c69010b0014041301ca040e401e1119511a06498482d00311000401d08800c0100c0000014115039070a807852200c0c00c10350003400803c101034500b40f01c07c1007070a4541c9101d0300750005854223614000440509461001018001d142c141e0414128141400c520220a50009102c04503200386c10303225140c014030742602c4801c1c07003c2ca061a004c0481e07021051480964008104114003a100c40800c0003c8035890b05e000200c00107441101003560184102482032401001344d080c1c03045c0542a034110ba1103003d1416203020070503900a02c07440840520000f001554280001071403540581703000c00c2414003a0900d04001c0c40140002820030780000e55000c0803a048010a01c421110791290401c0c504003030318001c0b686403e008000c0e5175200f9542103280b140351a00006070543c000100760900601c00039000e01040740552038074030082c0d0011108840000c0c645205040d2030360400500712589a010b030060624680400758040c098800360001c42920300c1000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 802506879 1250 802505629 802505707
    0x70b10120c030f17070501020301031e0b070c08040f24030c2001060506120f010503010c09030609060f06061106060a06080610020c0303030c0d0e070b03010e1003081c0c03060b 77
    0x1c0000c142046c400c8000607669810b40c034100035908805034507d011f409110051000007945001e030075400201074203044100c2580c916042d8800d100d6500141078540402000094201440813150801590340300401e0301c600425104600b2101d00ca01d0700800a0030211001e00002890400e0700d019103983d01c000300d0103035180e0001c207841c2d0340b0040d00e50a04c1103d072000c1161400d880c4012501404c001c40081c0030076800094000e01c0b59004d400044c0c6000d0341d5100c03180c10001c032030344500304d46410100144851655a10040c10030031160740010f42d9030141030005941c61400b02d800400362406921000709a40f00e160a0003060a9180503000543c4600d6907113005503074041020b58420281c0c6400b45035119401d504a20a40348a001504400c1e40701600c240407450009040e0303810f440d4042c0c80bc02080c1d403507a000828801c030f135600140c00500d0001d261028044084082d0340e03d440604014002d8070545c1c982101282c80e1783c0724141001c4802d000042808841c0c111031085070380039250440d0310086403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 802508129 1250 802506879 802506923
    0x909051b1b1f050f0c091203040f03051501060315061b05150603100e0604080717030c030a14101401030f06170d0203190f09030602070b10120c030f 65
    0x10100041e40d00780c1802600030304801401095800139000c0c640d500e050800c07180c0440310f4018118a40d128160110440c07045003800c100366002846540d140750012a9039041050326078031400039a450646c1240000704075a40030303015500e01c01d80700206800031a072030141c0884200c1000c940d4000021101d030001c101140c000c1003160005a01143c031030009041c0b03074080524000c601d02d4001c41c0c1505205141c1d070b8502c00405c0d1198455000002203a5510403803038403003844207441d2070003092080e0200900140916020255210b0204070004000b6404440c0c510b103c43c490460360100b1851540e0030070f0000350603610300307544104418100400e20340c000c6641d880941d09a50031543d0703004142c40035800490003c012103980f8600e24000b40d03241c250351507880080e00108001c07403414800b103003540707440c3d1501c42c0120000450700078070215283c100c64038100d164800c060300c0c0c000b1401c2d01400c2c00320700c0d0200300014001040d80300c00c424030110b1650703940700b1078500081c4054402600b42100c1150b2100c0b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 802509379 1250 802508129 802508143
    0x101a09060f0a030f0f0c0207031412041202040b0f0d060c050408030403061a011404090903090e04030c030206090f0a15020f0c061911030402010c11060c0d0909051b1b 73
    0x1140c0f00411800c1c4825010804c41d540900c20b88195401e00c002405900c1c0c01254500960b40c2004100c900c4801ca1050340d440e1040c010300042e11264002000588203400710541d801192003160140b01e0910600100b003505c4140104003580807541c81154000640c0c541c1c044506103190381401420240d840081134159002580107903a001d4444110540000300c51702038040b01102420461011081c02035201e4150203140120f00310941e0f110600c10906009005210040001d6503072048ca910349860000c062201c00320013280503200c0c003c04180c040703d0100c0d100120501c0da000034052850b554442003d480481030000245035402c120700c0d03031404039010041100a0f5007200900150030160440030700084520450806149004c0250780c0d42d01d110801c40f0341068092801215141284c24191804113207400c400d540000c00003144103420401081c10f0001100d80c0d111020b480f66241c8030502940c20841d00115600c003000045920744000901500c040c41c031540410328114455002a45050340c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 802510629 1250 802509379 802509397
    0x305010c020307030320041806030b0103061a0a150507110a030c030c0611031204110405040b0a06050904020d020409030c0b0703021201080309030a1712100806101a09060f 75
    0x100084900900d40c140c0640c121041c50070a1030111482007400300b01b002e00641c081d0b28040e01d01c3c04501e4451500c42c0d00004061500150f005540356928030b041402480300d03003040418040601410440c5140c514488000c481c0f00c0041003c8101c11a4402c031205d90140c1000c03030300452079860f41d000c6500c654913910f02440c41081c2e00340c0400c0c118108414403d55644c01001001080001f16544c004003005588a030020840c96643c030351103601e48400164005000755030854900010041400540080701d80109150a800c229103503c0d002403001c182400c6034040d4028006100c80f01c01414a81e002030b10b068000d01d450800200c1c03d86e200986550251803003800250003007208800d130048665428018214940114900190300001c80d480e806440c1001d0468120b075000b00e060400c922040b83c200d0b42042820f0741c6145400017030320102c001349000b400704900c500c00003d03503000c480c01c09a40c10341e44403090041c0030b03041481000f95503030703c103061058011900b0312020320700b60310342d2000c2d181b102 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 802511879 1250 802510629 802510633
    0x30301140a0e0618280b09060907120c0e030105160806010302040b030f220c1e03030210110c0d08010807060c05120d11030103050a05120f120603070305030f1b12040e0403090305010c02 81
    0x6071904c020043e40c0807020308090b101327554036010300841a420a6410340c1d8080d0900010a500c16060420380ba040c1651800c1034055080004001002c0180800c01c003840d031464461038010b484181c0118100e00850040080490040012481171004c40703a0360355001c08004d0a0701c80340d01207441c00740b001c003141c808221900c2c1444181446403004243c5001d40c8561008124603501e0310750340f8004c1d540d0107100810110706036034640340001d11804504827000c09400034101c4980e000c4caa080202480000d1203070010394003540c40d000c902144100368940c0c4c02a0403a000b080700e02842081401a5401922402045540d44d84c0c00485400c0401c007540c001c40c042c0f0041c0c042c04256003806400c0003062010b03041400c10400904c0e0b00044041c00b55043c544203024403e416540b18000300b450302180390000b800903c00450b4003030b2104456001440300408007118045110300f01d401c4140c3c0c030610103c0107034041009001c14801150002c8107668494000d143ca000c03190b560ba103d0b28210740320941050016 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 802513129 1250 802511879 802511891
    0x12021306090c1d030303160e040b0916080c0f072913030201180210030e0c1906020f010c0516060b04090302250332030301140a0e061828 60
    0x1103440d070491190100550103546540b901035038070b02010340f147c1181406c2c06110b0b00c0504180e101c0c2c0c2e20080e480c0e02c02901140e103605000c0c95a481c800034100c40140019203203070028182c2c0c2045003d40d0030f00b40c0400303441400c00001c1e55804d02a140e020726080c0007204040c40e1a004001c28868a80c0100c0719000e80202032540e904009007510300207c00d0b0402115503151250058035070042c09401c0381140e02d000144e040345208036a09002c0c4030f643c45075214100d80e02050803070044400440c00c490b201e0f02102d14039101000e8413820f0319113054102c2c010403030920501c0c3e500b095080c0c001c10094410788000991140e008005402c07640d140500303600681c03143d00c1a840103003003480f18110500c1031714611001d0500e15694490803510b4400da100c1540190f2112070b24048210110502070194072080e00d807130f0360710703512511043d18058500307911402e2001d00c001000b11000c02d080d4010704028100102064507980500340f0514041c04001e00880d500030040800103070f003c036019009024003404070300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 802514379 1250 802513129 802513157
    0x6040c0905130e1005071e030c0918090203030316020d0c0c1401031b0f0906030204260a0804030f050d03091e08041706010f05030d120c030204030c0612050106080112021306090c 78
    0x550406222181f040c141742c00145050706410140b84400c5410312803c49600c3d001c0f49403450050400c54400039014070001c0240f00c0b12504034101070500358119800c45038074154403801246c00c0da08602d40a03042d910444018464a0007136103180000b240181004a42c420a4003903456000e054000000005415843c1d00d9002c1903020340800020800c0307103400c2d401c15042600e0129581cbd801071850013180051749018200700170038807510118541010b0b0150300c0725680e00380b440500d41c40c80d1303040302c00340120000d52049600070321410011503041200d40901442c1440b50084100a030b0b6402d488200f014400001c0c3c03600d238101e403000c0d00020b080140c030b06940f40c0384056031001c42c0c072b402c180d00c80c0e0045406c44217690303400300e000402010101c40104400c080d04c401500244501d4101411403032000c070700400c0682d001700d020048440e80c1c4004100903070342c4540407104103600380901c40050920b440c06101601c2c2540d80c210540c00c00d0040001e10710398510810b81124105e040007808214040360034a9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 802515629 1250 802514379 802514417
    0x1b080706090c170c040b01140306190b0a3903021f1e1407140f0706050f1008071403070b12060319052d120306040c0905130e100507 58
    0x300b40015101400142100c6d0000307054a002005071080c0110b0200021348190341c1d0030001c5a503d001d0203190040207498144181c01a0300071101c910104d212034076010010502010300f048448070200c82181400c4035005e19110340152400c05404620404142041c2c05000301c4903003130000c03c40da50005040c07094a00c00e64001c405145000381c91860030248045808082146d660320140c9841c00301140c00d00d18103091035a02039240d2400d64504082002130400c141c0341c0c40207005007582841e07603c0c1907071540c103011942141d078061030015401106007048400b0500020310b44489009054400d41600e400301c00081d608011000034140e12001c0501900d4107040c01544000001300c801486401820b0712080e07900c240307d0700810020007200c5190001d031585c101203505040090402d4a00c2c4c01c01c0e0100840320fa40080c1c03089842140703400785141c0007a0103005070404403203020344507402940b220381c02e1000810000101c643c0d24092400e031010003000621030346201d2104e0f500d5070544a829580621 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 802516879 1250 802515629 802515643
    0xb0a1b050304020607030806120f01050406060e090a080c0f03181005130b03040f12080708010b09030a080c0a0b0f0912180d1b060e040c1b080706090c17 67
    0x109201003001444091303140c101c01c0300c0c40725805003007651081d2920030103d031120060305030781c00c03050141c80f40d01c004c1490306401440c010b038001c01d010b00c101a11600004001002503996560b2759101e003e4440000d60f02c03001800b0b0042e840d04c141c1e0b951828802040e41964010000400203000e20b440d180b0030317842d001c1204408028240b40050500d078204030409151265030184a001041c0400042c4c10080d01a400b84c6015901501d5141200300c8803201401801081d60701e4400b040d420800490001c0c0325005a45540384000c3c01022040a40d4031886559800110850f03040c1c028031056402150f12098190b000f400e40c55aa20480c0c50030850481c203290400031171005450080080e00c10407030b602c41c410040c541c0c085882142e541c4032490b040200d050940c2d001199107a1003e40028442c1d0018908451040300342d4041c00015a4554100d88046210754a6640160940c81e41f0012640941c082c00702140b255000141031034150300d90940161071607104020076607880402c0b590154040c0010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 802517985 1106 802516879 802516931
    0x30e0c0d0b0a0c0f1b0f081207120203040b16110115060e04060e1b0409091101030e012a050d0f270f060b0d0b0a 50
    0x1101440c6045840c0c03039610707241c03220602406018401c2c1c040b02600380d544101150740480904034100c40c001c481954800b0300e0030904c00009442e00000c020703001240008d04001d10705510001d001040d030f400102d0800e4010b1050200003008090405e82190b0b50f052a9021030100400407a11a400150b84203400d608210540c034242c0d295454400a1340d203039580d6040c00d491407100b80400e40d9050300c00c3c1e030b00703103080400055602d10510301040861060442c12500d01565200c8100c20381ea1a8503081c0d4401e80c0e00c0d080070030250b0b094030901c200c01540038002e1040c0b102103241d00813001d45018050369445026500c101c060383c894030031554007000c201c400b00840c00d4601c8424008140300e46034035006040706001d0980c41900c0303052a0310910f500c20030155017140b042d03880401410310300181940154072490345100091070343d070700300740310300b8503028001030142d46900351030324044c251004 = true := by decide +kernel

theorem cover : BRFrame.Cov 802338129 802517985 := by
  have h0 := BRFrame.cov_init 802338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 802338129 ≤ n) (h2 : n < 802517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
