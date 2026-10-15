-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4809
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:48:08.055148+00:00
-- url     : https://prove2.me/submissions/b1af84c3-c36c-43de-a8b5-33487bd1071c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 864748201 ≤ n < 864928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 864749451 1250 864748201 864748219
    0x2150109091a04030e06190e100912080c15010e0115120e0a060f0b03060f0f13060608120a1710120203010b0d0c050307080c0f120a050d050d06050a0b0405 68
    0x1c05005020903c50310002070001500c4040212441c21450540c0c5071100100f201c0ba030714038a232030900b0042d51404010b65103408034010314140710b800c4220b901d01800d46000384248003072904050305000d81340940b0f16204481800c4d5050143c101c0c041d5a0613804034070703107030384040000c1a600e402071050441d0400701400000c254003944885400c02024110041070300f80b4104400c56060003540c004d00200f20160708482c00742ea2001400c030f6424034103450030480c0600e940d00040480b501102003c921500c610344c041080303a0703110310561500030384d9540c40307502c568003149040e00c0c00c0d03006001040380382d03031303a00c41c0042424250400c07603440c2d44a00070000881600740080056440941051000006c041e094101c900500c3c100981c2556103809124404d01416000064040000606d80d0740340700000e103048c0010314000c00b0041c5040c88500c0543c0d207030003411901008070710184039140540d411034448aa8440c02d5580400c100ca21903081603100e64200001405003914a9043e502074074401c0d244088 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 864750701 1250 864749451 864749453
    0xd0603082a062d0a0e0708010504020f0d020a03050105040f121d012a061d0a0b190f05161404030b1f1503092303030708071e02150109091a04 62
    0x400c620303003560f000f210003410350b09111304040c180e0300a0307002c0034405098612240d10792107072609036982610081d5001c03204505800c07261420900304110700b07100a114014056994ed9840d0a4600494041e80d0f002d600110030402c0c8445006008115407143c541100050303c0c00c220b803100250000901c0e410001300c0f0280c8c20400741c480b2600d205402c0c80c0350501164041c240380030406030030301d84550442d40c4c868041d0a21111000107403206401d501030403410b81542c4a1086008240700b0028003518151905814044180c0d540704e140d0046e4411140030040401502003d400c0d10b031051030113074207503004000820104540072080c9c2c1d00038800e41180c035804c002100303400c1c0040d4070036044a44028180015424100d03019407050b07011900c213500008070700c082c1c400c01060100c1d0100c803400494008100080c2914812940b045e4402c005003000800c03a90300485020a54511b6a03d80d805a400030600c0700b0184c1200c0b00c43c1c0e00414400c5020712000c1c60342d994503108003400c5510b9000c801a240c0100d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 864751951 1250 864750701 864750751
    0xc0901021f0b0414010f0b03061e0f040606030e0622030804021504060801090501050418020d05120c010e0c060c030a21140a2901050f0d0603082a06 65
    0x82c0851800420600406a56421031000c04e0020310038141400740070303480007800f0301041e402d6a1080c0001000c40c200b200c1d840340284006c4407054445a0700c102c0f16001504d460703690b8030400000d440d543d60001000700580003442c0c90028068554401c40f40c01600f400091800708a00f80a10b60b490301c7c2074645601c0c0da102195902c5900d03511021401d20106000c07682035484201c0354120ba081d060140f020b079a940061000721402100d00e403d0510400e50001c015061818284007010711501c00c4400f800340c80e1200c02c00c590005208086181d44460b02c030240140104911001c0300d00c2140c88500d4aa00d035652169244940d110300130030b02c2140a40d981c0340390b00c0f190b402c60451211784d405008444500304a19801c1d00b04035041e89034180340000400b4540c8191502062100f00500700c4141c2d85104001981d45401000d817144518204100800410a00c0c0c058980150321846145460f020b00103090300c00034603860f500700a4030882c00d0031019905000640c0ca40c0041d020b41003104081002034410b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 864753201 1250 864751951 864751961
    0x80601061803140604051b01120518071518050901050d05120c01061703130303030e03070501090f0201020d2a1109091c03020f18040204080d170c0901021f 68
    0x141140c0100c1c40c0f21000e00d040401c096114511500c1a07403541d0032401060551240344441d02800203a07048000740301c1500a5010700d400070115905903030384d81c0040843c00e00c4c00c81c40d80c01508404042e19411000070342c000040d40f2584100d0260009030a040001140061005200d203501c00d0242c5aa100c050000c107008003d00010189505691910164002c60180050303104141500c070320040d07082611207000c01900c80d03043c03042d0481001685180c4044000d024000382c00350b540d0104000300710001710309100741030b002441040100c1d0100000d000180c01e04901c02204410b0119030f98640f030b2425111a00000b10300c0d003258540c0c4100d903183c24400c041045a00106030040300200910007c0200010f030401204c5140c50035000e180070201d0300700c2c02e9000d10040090145400e010740c03889480c000318000a0064003600c0103003080c0e6102d03140d515004980c3c1c00c2a02041d00a946040400f01e684c519551040c180040ca501e0f1502c1070000075038a087e0089841c01c0541c1d8846201e411072825004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 864754451 1250 864753201 864753203
    0x1e070206040906150e030a11041b02010e070501020703020a060c060207020d0f440c0303040b092a060a0c0b01143303041703101e080601061803 63
    0x31894445898100c41002088039000c1c1d1060380c04801440c2c00718034031880a00c034031400e016002e00f01c0500e42c1d0f035032a101c4541c86400745500680714a0300e0100c40b04001e1000304000059070021420702803152110f4100142c0360032a83c1150080403043c80542c403140c4204040f6501450301c0c400c01103140c01d012000b4055800e000307520420400113901400850b0b00d400344040c1c021484030200312211840d0012040350340030300107060803040c00c5610543d204449580804141080b0941c079010300c502c042410b544c02200d04503007910050080c000c00e6001040b50302d40448510140c40800c1d010703200e56030081c44507103000c540f080d238001942c28180782c480c0100c00049944840404c60302c1d40c5903400c1210702007140b00424000e0200c0c5401c9000b480902d1062028025174038600c21014110109403985a0700040c01521544943d03c154a503009554000303520030016180089402410524000079010400c40704200010030034001348003030100410118110b540d1420654403602d1503190f1901444407030340c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 864755701 1250 864754451 864754459
    0x5030601060c03030b01210902011b08120112080d1116030f0f0507150902011e0801031a150919020c011410030302120a0504050306070c0308100b1e0702 67
    0x200000d10070360856800039600d07100c1d0f102446107507081c070011601040c40c0c503000360425540f181c4d0380303216445a522400005006140484055041540110241030403031421a12000c0000d1400e42a00c0100f0b0000d004d0320322502c82101c04580c07a12074201c1c90040101c00d034001592a100344515001c108202d900070702d61400003030742040c01410040c00c042c1000d41010007142c003004d181c00d02180f08204032290741e54481d910b05044102d84080710018842c50303030120306000c40400d0212200840303d070740442e25101541c42c16890b6045240000002d55122940c08000d4854030a00c050642007801006d1075000540740c034074040c9e48410448810310b0203c20b2111a55200142d10700aa40d810340240d100b03c0020440403c441d1219003074090580300d2480041d0050b0071a4048521a6010100034401d1022910f000c2d0f04094480c80007038105103040d928036002c0b644d84105042003680001c0c0d440d6102c0310800890801c0703480c01c0d0510f5041d05c24070140540b181400c0a410700064010b00603552241d401070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 864756951 1250 864755701 864755713
    0x2040b040b120709110c0712050c090405210309060f071422080d09030303090f1505160305060a06110111030910061202060919030501240806090a030c06060503 70
    0x9030583e00c4400c540110040c15040a103010600e82008080703a04110b801e1008146262924070b0020004c1c070103410448040c06144100030280c0e80e0386145038042d500520142840d85050100a201c0055403452803020300d00500801003401c802140e1107030702101000101643e42d4070000d044400080800030081d211201140382e122000059030303400504007060308003500098403200305a0785c1e0300d111403621001900c0d5000500000b4403a4101c020b002e0f00c2119140888840b0f40c0c0c4240d4050f20070409854002d50b04d0003008620b040c528070045000009040410250070f1520115800c0c0140340074040901003460340c0186070110035480741c07404943c1502c0250301c0e403e000701010307111f0203031a11036031000382011004180003250b201132400c030603030040580b403412448009104290706410b0b450884030b400c81c400000070906c03e019298003143e44c825150f42401c200d0070000001b424641180110742d21410400641010005040400c1c41c1c2500f426880c084081c0b41ca031015100942105805015a0f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 864758201 1250 864756951 864756979
    0x8060f0415021624050c03060d2a030b07081305300309070305070e010e070c03020a0506010602011509140601080c070c060f090e091e2a0307080703080702040b040b 72
    0x8901c18060040126200b80071740d4964996860b1140000e48420740c0c401302404610300012110903a038108105000303031680510b00c1c1c0c030742e0038030703030450598000d5a900b4192000c121800f039102078110b91000821801c54450b20480c1ca655075110000440c140b450300c1f8034600c6520503408204140708031000740e0003242c2c1d24a0801031450300c918080c07104032014813550002103200b00010349068181c8100414034002c59403444012608610250020781c2980155800d00f004030740c09020311030103001c0300e4001081e07018800f0114041e581c8140e21400c281d0385403615001200c501c40c3c0000742c1152003480c0040c540d031070340f1130034200f24490b581b001010305100d040002185600f00210500701101a16680380301035a4004a0880703000c1107503080100d0300600a401c25001e80001060449942c540441c1c16402141c072812200e0700e0701004410f4050703500308044100e1301c0c0821902000d00b2420005e44281850b566881801c4d01800038000d00c101e8968440203080d03240c3d5401700c1c1c000100209803030500050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 864759451 1250 864758201 864758243
    0xd0f03050a0c1401090311030307050a0f0915110601080c0d0f030908060a0b100c021f050d0e0304050a080d0f08060303070c031a150120010605150408060f04150216 72
    0x45c00d0012408200c0e0041507881200c1c011041e01d1040300f1503190146050000e40c0100d510501c04010310090000d2444003041c4090f481c5040c0c4108410313615480319007218146da03107140400c1603222043d16400550020515250300b0360358404d07142c0c072020003020211689819204503181e03401078500d0303108034000c012500d035450300000314103e4141d621511200e8034213012165060681070194008180c0b48501e11134442e107141d042c400102e6843c3c441d00f815070a49040c016680e203404200d4040c2d001090a004038079080007044001c159007030040090310030345540030f440203c1e80110700080c40030500024065072014022241520b0740b000d2a500c0da59102e140c00c80814007888841040944801c0c000ba0800c0310b07901c41002c04c03030710584440c0b00050307504481d14402c4001c0e1054031034a540301c42000030180c840d54401d0220111010005840f40d040408040c54060028000350500d0f001400340b001041010042c0c0501c904505400750382c0c0d03000381d840d0348000c1c0d61102009000203080704640c080c0000d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 864760701 1250 864759451 864759461
    0x30f01020a0f090e0f040b0a3c0c140d180b19050c030a09050304080f0a120822140d081005181501090b120a05060d0f03050a0c1401 58
    0x846403a0000070541310208591244000c80d030300c8064030b54120118000c903482c0b0f100141c1c0314480c41d401081c8090444903130704c0780d007002c1b0a883c1001400364110020000e074518a03d10f040e01105020080c08865883c000e02a00906c06441906076000610f000c8100310341c0c10030101011440810550442140b60421008004983e0010703925800b05121203410800d00a49001d50403c82180342142c440e50030550003030801c2c80d0101e4952104000000307411006000e5100d04619410240c1009a030605269012205d540c0360001080801010800202c001413401703101d00b080d90450022464503880c2004c40100084c00350043c51245c26205c03112194001c452910844851503648011a035450504ca40110291012440d5a080c00d0001e440f040e13080b1440c140706441454400295940c80b5034107645640a000d56001c2e00700c58804020914a0901600b6082581a6400c0c0509441610348040d005039056000f810800002a00c01d0128892654455500e4010700c04820056108a409000346 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 864761951 1250 864760701 864760727
    0x302010809100e0c2110112808180d0c0c1d090c03010e10200304031e08010308070210020708030c01090c33050d020d1d12070b06030f01020a 62
    0x1c0c1405071005c902c1213483c0d640100c441141d4020418043e2503241c107405065015031643c5c0c1c0903018000c1c85240540880d0318104920000c0c07414104056401000b4011600140700c840e113103000c000b454624607000201c441a5410624040001d0400b03031070b00929130a030b15448540013400d1301042070510b6510800960140c0d5458080341e00d036004c018107050903202850030341c0ca00707500f1000140d100541a908600030340490707003020300c0d85100a41c00c10402ea4005175003c2e4009814034160754610000821900d8061695062144056145980300001c0384a52400240101070482c1038130366007070003081800060013030541a0f0792910a5900414001d00410704180c03105240c001f030001d842c00320301000b0400201121080c8550300e032428101d050b14000310034000b00304a41040301d4000322400744050035810300400004a9810b4480d5190426100b481100e039649800501c030780c2c4032690301c503003c0700d403429402844203005541703140000f4144107031050b0b000c64650000904e0b0b0304982d44001e4518282c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 864763201 1250 864761951 864761959
    0x2805180d03110a12020915070c0e010b0301170109020a1502100b010806060f0c0d0c0203010e0d0f1d090106090305150403020d0804240c020f15010302010809100e0c 72
    0x35103010000c50a945030240514001c081c01c104110800380700d11000d84121100c0d0030003610f440c0c01100824440c000c01d8040790b10741c01c00400c24000f045841004c06000300103024001e1850b5060100300c5006100c10b116400224449a41c00c0c0142c08080d0000326020340c00400740f41081e0340e54030600340484020a401d02c014020032101d001c542c800361150011802042c1d4495002d0780e110300c1842030b07540c00001010341d607180a0282d40322800003005066007203002035580e8201d410840c4141820b40355405000400b44c0c02c00d640600089a0180d0224028495864404148200c4c090081e61005440ea061038000c03442c40008541c0d117420000b080c00b02ca102d10b00b1115003110b860360049540000341c0340100160040341031211040c0c030400e105500140680d0186403101d0441c500f002d180807012250102140c0c403525001c074010b405101504404050f03001510000c14680c10091861005000007130600c000ca0010501103401008210806103600404120090503840e85c3e07030741c801075400745070b210b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 864764451 1250 864763201 864763213
    0x305070e0d05011b03052202031c0c060c111005060a030503070b090c1002030f1b0f0c0901050a030b1f03080f07020f0609131a03101a0d0b280518 64
    0x8281e20901c06d03035119104c001c0c01412205c840b00103020001ca01217100380d0340b5100f000c0c50b40036030601c000c03582940500c2c19110103803006074510f07100003950110010f045c00d0000852030210000004203014032528011500094540e0301c020001e080018290400381192202240c40030800001320043c074010800c8404071644821218100507552003280c00d0140107130406d0203244500c000000190040d4000401616419440711035030602e0103c03421840c83c0c50b907200c4000e41d40d4905000c01c049015201c160342c62003040d411600d82c104801005042a84d180300c100d4003803210340107031016601c050f40c4c1c01602299901c903601050001a04950030981c815200d09410321010b140c80320444000304005800b820705200b824500344000c20f40104881080311105403011001d035001e11460001c5d020310b40d00021480700d02e03001d2030780010031003044a000720b10340c01c043c0c2c0118680c121004d5004098008410030300d900240a00807070300711300c40009065401c04080c400200321130700321224440240400c1b240 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 864765701 1250 864764451 864764501
    0x120c0302030f130f120c030602070201021c0c0b09120f1c0c0c05010f1a090402030c090702030c0105010b04030206070b090102040f12140d0504060c05070b04030503041a0a0f0305070e0d0501 83
    0xc4c2c0c841c40c0300002c004020100c002c07c000b03089500078016190050058544090720051040b460300f9800c82c6070400a008030701800100100380d03441301e4000c2c411000620703000303942102c825844e00c6200305440309404007242542c04402803820000347c41c06241c8051048686084002e4000051200c0443d803550911501c0001e80a89208514412003003211b2680f5002c01d11082c0504641c0290059825004100b2031a07c15100c02041070b00803103040d030080d41d0350b0f100744145500715403040e00b1003010904204820005682c50405407010140c01081c4541c403074031403d410f1802880b81e41d0040c9405041440001070003108845101d0f8071900941e080e0a04038061042640c65800f0301c2d40f0000415014001441094480c8a4011841c1d2041e42110071f065210f898051550b0801c1d40120b469078000102402125126910b203000c2d411020710003410b041ca004030140074028410300d694101a5203900203400300e40301e903102c80104c280240c00450038100506006000c0c2000480c544068030200041071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 864766951 1250 864765701 864765719
    0x6020d0509151303110a050109120f032a051e090a050613031709090f18030a2a060f06062705310605150403120c0302030f130f 56
    0x10b442884040f414101e0589540d4080e00e00501200c8162807502c549440302c00060720901c20b65010741e0045000b003120300701c1000300800e041c440e94081c408160900e14400500085000d0203152154800d42a045004100f070048506000304030341c030700c10011103422001c844401c0324000e00f0360f0141a07a143c0b41d05c80e260400d201c254814021800f203064075520041000c1404140c0c107040341e11090152614001017070340025102c0609130795400d050346051090000701d0003500100980d4038a1940a1030500450902c00b80c201125151aa002119841114000e25420001e5144d100d58040f40400100c0f070b44000c01001841c443c0220004100304a409004038042e803c0c01d003000c952000c00e000b150500300702c00c1c82415040700780c9124110713103117941051664a00110006901c035203a4000120546406e0410030903880b11982007903001e50030042403010402c00c0054078014155420158010380c51484c00320728500c41c803c125051400041180d054081100780c1c00411070724200c1156a400d51501002c0f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 864768201 1250 864766951 864766993
    0xd0b1806130216150e16080d0905010507110103150605120106110a110d02090c03040309060806011e0c061a0a080102040b071b0801050a0b1011070b090d06020d0509 72
    0x40030341c007240c03010030f50000301108803a01085240d002c001c902c41440d032500d0703032900401c0a90f12201c002c1a00090122100810402e00103284c2482e1011101d0300d0503001900030b2041d2100030303006000c00c01c613045059000e03030450302160f05060f00101c042d42d0b5824004161390000c0428514038001c0c40000500c0c240300340004105d50ba000c40250050401030303070740d124402d4459422590000c00311039414000d030b5180c4258921600b000e2212507901e161500d0300600c0305100383c0052080c058600248506664004515007441e4401900700c840864251000e9450500b04200100640d0074400c185081e04a2424904290314081d0b40d01c40010791901c40700d07401d03409103019811a42c4414450340b00030818050703a4184584464118040a5440c3c04c2c03442c2c00d450303049801217449600e0703046d0b1002a09200340c42c0c2d25034006a1901d80c810603d03455071552a001140f25085841d6400314181285995803040204859800001156251030312442100609001c44810245020381002c41403000c4c811624 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 864769451 1250 864768201 864768217
    0x90c12070c0b240406080f10050c03040206070303020c0a11040e030c0a1218030303060513090b013506010807060203120109021c02070f20010c080d0b18061302 70
    0x1544015655615409480d281c0c002012900710200c0c4000c10300c3da4a892180e0170141c9605c070013615002c2a0070038001d107404510484801c1c260301d0710040080d841070b03000983e50003030f0b811a601551340c829820304601900600c48091134600030300f508081003022803002400e2044040d42d06101c034501102140c0c0c9c503402403180148013900a400580c00040b840d1662031912096824040182c00414052040d4241c541e002100401c2d504c000a0005140541c03451000a02030b21080c80105059030303c14090020611800340c0c000c1035101e040701c1c010900c0c5064265604005101150140c141d20050f0344d9950070b20a81995000e4040c003c2021403021040300e203c02461450010181d103048920802036114482c805050780300329802c40b0075043e540c0004c3c0069806030420b1b5001e1216070601200c0c0c403020600400c0c0c00c960141d05e49115982120138a61201d41110800341c66001264000001d0442c6135122a07000102c10781d9105282030060a280c040c1d0410358840d04c105803040ca1400c100d120700d00c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 864770701 1250 864769451 864769463
    0x6080a02090a08031201032619031e1a06091008040201260402090108010b1804020310020406020f0d02030a090311120609071a03071e0201061503021c060f1a09090c12070c 75
    0x940c02241a204c82046041101481c0c0040d00340340d010bd101d1904444801200b40194443c0c03c0c59039088403441440c80c0c886001c64402d440c28007001d00091420b00011842c506114405c0000380642e8020104540c03840c0813008100c100500392035140300a484100c40c1248034082d00c60002c20702c80d00c14031a05500351405403d02c01d0745501c60051041c1403100400403a40b611450001c5039009813580042c100800407038004000d00c400524241d81840cbc0c0702c2002c141103520900030444461b510403260812a17400c10a4100022086804284944410804000240f09a10a1060384480050104101c0b5402c0c91030310070000101c400540d05200c19542080081d0507904000c3c0d24005036008844460514000041d0441d03a503920038904000300d090503800709a021820300705000100c140e4000c0198812004c018090400c200403110540e2801a08070095445955103500681001220703012080142501e036a0300d00b6004007280340d40900884091041c4450102d81c50a000300800084543d10032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 864771951 1250 864770701 864770707
    0x9050102190f0b0901060521010b0f0a090e07050d03050a1409030d0509010210050a150909150c090905090a111009050405100f0b130f06080a02090a080312010326 71
    0xb8842d40000d04000d01340c0e0480355604d000000340d0303542c0d403844600c484c0400c1d4454401220010740403400c58120328110348c003901242d190000650340b44826081a03e86070310002964968032142c091404c03540d42c1110350050300c2d2040c8001410b400c403020303115140450b50b6003050403400c0e0101c8141e80c00344680c2c69405503c000304000c444e81c041c00181c1581c030380c10b10440d01002c519146483c16208151aa4448295218041e41240700c0050102e0080d05081c030040c00302c00392980c0e450310404c080c007500d034401c25035650f500070080d441025002c0040c800c40e1414041810402d81742c50320341c0c0c0410022150700c90510518245428500c1e80c4820a228507140c0c40c42c2c0c00c0c6403a0500028107801050303003520f541c1140740421710360b52940074031307000e880c84200d5507032224001d8011f800300055a070020803a03403008860030000c9a038407120140d4401c12503140940c96078440000326048405582150300c0900021400780010050141070700d0499001d0018603801081e02a5181a10341c9440b4000c18584020 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 864773201 1250 864771951 864771953
    0x25090c11190303020d02070b0a0b01020a02030c09060f09040b01060e1017040305090d06050f0709080712050703060507030903020c010915050702030a080c033a0f14010609050102190f 80
    0x4001c2504660700070700b000741c6000080c0201c0c1c0126444190203c0d5050702d60710078000360030194441c171040c51001b03000070500e05079180c002035907611180690500c18941d540c00511191101314030035204a0300900405485c1c105850510240c4a00740940000a82d2100e00400d0601e098030034400006051380b02c88250300c1440080d00700901c002042070707040c00300400440c0210740303401c0540c4c90040d001e1000051a0305005001c0c20945c0f502804040070084030314000d100c001004110b0301c0880d070f09410480010085d43c07418909190041d44043c00c0300340340404025411350590000e2410034030030380c252000c410703907140150b03543c6015024260042c0b40801d030f903c14650241e0f00414525000408841d01c854050740c23503160b00e0340840410541034001150202802c204a5008401282010f0701d10740d45a0301d0180c01002a80483e04014096407242000341c003076a45075028680c02c0b4000e40c1109417540e1107800103014201c040c4180e41c018412100d41000354680180c2183d03521390f00a080780200007003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 864774451 1250 864773201 864773233
    0x3010b0708160c0902071106092115070c0b1609091d0111070b1b090d060e0d0f090b04050603010b07051c0815040b0114030925090c11 59
    0x2800b8000502e000401203007000c200603488600080c0602e20016a40303568500d800c0700400038000145005941c2440108410ba0b584069172040003866020f6030002d50426030320600d001f10400541e10007141500501c01c00c03661084035410386034003514401e2901c2d01c9040c41006e1092821079101c00040e0340030300911007201c0d5900101c26000b1134840800207400502026400c562078140d107402c038a18001040c0c010480c2100070958003100d440002c120380d89903442410039501c52150b03500d1251050021610410072a6030200404c00b2403a8100c5040b24400000502070b41c80d14069900030aa42c00000a2440301150813941a60000340000f821a4682900300c1f100390014ac0302103d0b44d014078941500ea4021141000541d29410391b510141810700103007410f10401118502c600582c00c00b04261803d980001800d2040148107003459601c1d03548000f903506000d011043c038485000304142501c2c0214000700500181e5045510030410140801d17019510004811807980003034101d00c0507a408012 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 864775701 1250 864774451 864774457
    0x10509010c11010c051002191115181e1903020c0d03050f0f040603061505030f0a0f0204081c020a0b04060f063501060605090405041505270303010b0708 67
    0x15040c10003502101541da02c5d04d04014041641481055010802d00181380d0545400c012441c1d00b070800311100b428680000d0b403a003500708261050b4581d0900401ca40c00b030090754081c8402414800c2c0c81d0950540c842c09201003002800001a910805071100c0d50300743c6240003c903140c2c1c1e00d0703002002c20201000c00e10120b510003080039014400140b08202c140f0410741c004048800140880544d107d003801030180845986400254a8041c0301c40c103261020f40010031242c002546044145c102d6031006404d001400d0394240b04c200850001c900041c030910001050320680c40a00d09441780c1c500c400108030307620340c10150040d0080d04d601e404240864095440050061102e5a001c50015111922004002e0701c04a0580500703e03c050100c409005900201451410900081c402c0c10701c0e146005003103000f2000c1c520710035603a0f400410f003009002c5840035128090420144060710f4003001c01c1025084080d901d200c89a8030040c3d9508050000c81160705035501c81075401d050108036280c045e4150 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 864776951 1250 864775701 864775733
    0x110310021629131401090c140a0b0d0204170610031e06060b04090f11040603021305030109060e060714120702160e09010b01030204210f0614070806010509010c 70
    0x85001d507400301200a805240c41d129529070300189522060b540303441c0ca44503244191396035199141401c00700001e03241041d11011184480100110080300400050042c1c2c41079000b400b52420000784604c1075421074020744200c411154a0414034a5070084840c3c4881c01128a04000c010f00513081c000203c07007540034241c0140102d458004171000746c0c0d80b113040300d000381c0050b250407501060402c0520001e000700761500c018000c00388006080702000c0681c0340110300890b82495000310310302241aa40d64a10802000c0081c003d201c205070604102008181035152428540900340c00103035468014000c180640589200d185c0c80c04010300034a02c4455805841181140940c814200c00d40405805200103030140041c04181401c00c445402c0c01c47d00c6903c01241418014403080017201d40c00166680d41a010401c0700f10082030340c1c86d000740310603440310b80100350314a0140d0480344502202c400d90f00c81c040b0354032190b02d00d85a032001074503203004d20247d482c0005c5e101d06e0382c080000c01560100784c200b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 864778201 1250 864776951 864776993
    0x50d0e01021b01052a0a020909010219080a090b1609061403040305130b03400212030405030d0215070804020603060d020616050307060b2d0a0b04031103100216 70
    0x5c861540184810789000750288900c940c4143e400b4010f6140c4108100e410800d518000c510b890400f0160600c2c40c80d9105004013844028000510805016088914216403000225503146000c141000b0500d50140000002940007100458918050100c03040c0da551003c030304504603900d5940403507007a07001800c0811070910102c1300040e0498043c02031401219200d8180c80184840180400d142c84122008104590050340c0f1a04c09130382c616001c0440d42d0181c3c1c100740c3c5c14079804010307840d40c8910360080d41c0500c40da5011322101ea80c0450518280808520044159126480c040b581c13044255130195000f60b041010448904d002140031003654800340c030b0705090580a0036034103c0a19262011f49a45d000025a501041060311840c0b01c039450846105ca021070f0300b9040140000000020f10080c5218400940f140307940750440c8000501c2181511640d0795202e2501c10681070400003054000d1244040c0a02c0710341417802911a09480468800080c20791616800184e01a41100765a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 864779451 1250 864778201 864778237
    0xb0f060405014202010507032d0e010e0604050a03120b0a05130906020406050d1506171302060d06090c0309020f1e090117060f060108010e1909050d0e01021b0105 71
    0x40241150b207a51514105038000086e0344c40c0208014040e1001c00f00b4079102c500303034040c0c440640311002c04588900300f141480058446000c000341d134018034142d61014400e1141c0801c00040110015024004920030703501d90a04e015035a80c08002c2c0c0c0c4451800c10b902c400360850602540c1400f901008012095810104500505444d254202c8e4401e401c480002980010070071a02c0c002030140d0f10300d075000e100700ca1459503e49040100140b4100f041500246204400704001c1203248281180d42c6400500050380c860f40301d141440140082d11507071007401e04001740f26403200d019100350322a4a03009411018151000300410842c0c41211488a020a05412000155480d00142c0f03d0107403480e001014000740c81c144041d0700d000c400400d208206460076040041c131780da110446d41e04641c1d20b8800141b442d25280a40141a01010039030740200d403030508020180320000403045109202e03034942c1940b180482004a0710f42301803845015041c2440c10252034103501c10401842c0403e681d501c4094 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 864780701 1250 864779451 864779549
    0x9031706011e1e0201061505030405060402060906040906060c03030b010e0a05091e09010b011404030c05040c050f311a030702070f1509050108130b040305160b0f06040501 75
    0x542c2003030f141c1a4070040c0c0d56004148680c05407804011015040e5040160652800340d5405607500700c0240300038024140400c807503416456050540300038040119082c80044c3d1518401003003054040c006500003410034010a100b5405440403000400001d01304174505401c1c6800d002009002501c12401420180e40110082d516400c901d4011440440082007100d040000105042c100100315000d8100c20441040003400c900d02150444106131004200030700c240b1400c0c0d50b00d024006500401e20000143da5082c1c41002c07008070703c03030810b0301d043d145908500907080c0203854081c00b4010928078074035034542540304000e01655001c1f08c40e1040f115501e8452104203540c444030782c001c11100c05a1140d0141c2140c01c00b14950141c00286007001403803605006d0080b51814403480500303600c000b98049410715114404480e101d1000000a203100d810501e04415900b00841c0d1050625420780d000c5001458a801001d04842c440350030105c03940304a40f041c029240f20b84030300591402800c07007416 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 864781951 1250 864780701 864780737
    0x90604020d1110090314120313050c0603041b090506060a201204150219060b0d140a05122d0904050406050603060a09020a180b060c0109031706011e 65
    0xf420f80c881030f0745008256103903152803846000d81101140c0560000440d00c40c8048600081d20740c440c40600c1c2125580040741030090030201c454103402d400050010070031050003080d00c16140004034442c0b907182c1c40b641e0741c1c07214411100107844441d801201042048843d500c203002100101d807104002c60600042d4007821751070030104000441c40c8800120b03042100c0321503284110031002542c009032028245159080c401e0008103400140807640c0c50800d07400700c2c1c8403000151140c90307202c4448060307c10b81000e81d66840014a03011111841000c2d241c1c1da03480207100a0300c40b200c1c001120384d2100c0049680d04400d801d441141d000000d07c1c01d1100304141e40d02c0d40202800317180240c10002c3e1a0526a081c50308007040100809015070401e440c210050312800090811035a100000e14404038134000315002034000351b81c400e0b80c00040842c41c102400d1040d40304000d4103202e1784507000401000203500048490071182c081c040780110b0042c0d040368140030501000410780d031a00094003081c604042e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 864783201 1250 864781951 864781969
    0x2071e0f17060f040b0703050a1d0c1c0f231207020901060e010206011403030c0a0b10051e060304020d050a03020106080d05070506010b070f050a0305070b0a05090604020d11 76
    0x84501c05454110020065200b40881500443d102030001003d18054441103203008029064a04041d940d0001a01c00541503102070841c0f40113101070ba010080c0c40384455503440800a0341881010041005020f500540c0f0110b26203951220018940910799101e40307404d10780e50a0506042107010304528064007051025010520350b101181d91900b4a41c0140105100141c00003824025402000c4401c2c0c3e80011f18035044410320304d440c1d240c004c4030802080c04c40c0140c47e05044a407040000707010402991807021849035036040d2036543d40300d03600c00c100701c2d100140550640580c03805107401140d6041c444015503010f80090320080700c60845a50705880d10348141c200382d0050355940700c2400308100505c40d02c0d50f18941840c20700d003400244e80780c0c00c0d03c4400604c80d007200c1060000301c00c810403003032602d45801990000191003d800039400d000d85a075012100c100c885094020001fa250045845110b0064104130b00404080e074075a03003844030303441c104d80302621f1001d40210425080d540d00504c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 864784451 1250 864783201 864783209
    0x10b09070504033f2609061303090902031003080403080904052d04050c040207080307141e090103110a030c110d14031b040f030302190302071e0f 64
    0x3410ba0b03079510b9030501c0854200c04c1c4030494280540c828024040a140701240458008848040301032a83e0104003135409000c0010400e85050750030a80784803a0500d2810948030781404030544d41140e585040c00c845280203034100402140707001d082030260400a5019550290206404904c8691a910740b040642c02940c01101c1d0448002181c45450070720340a220380155080b075012030080d40140158082c0150414403c21040310000041c0600c442048018000c01d4040c0c001c540d5818942024805d036402102e408002c948110034102381c2c20620310440740e611540303400c0c83d502d805e61200308548a6211081950405480c2c1c100443d42c1d0482e00001e05000d895a00e000505c0d0419040182c0034080942440200c0e810031840d081d000c603040b429407089010914074242d500d644000c1301004d10000f40c079a1601c0301c4404140450540c0100388450107490082c1c00306c4d01404065000c00f071100021800050050300051001c2000301d45c10348034880c400c883c444048a5883c0c642d5501004c2081980c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 864785701 1250 864784451 864784457
    0xa1403010b07030e0409021e04020f0a022407140307020102070c06050a0329010e060f040906030212061605090a170a03170408040e0a0b030604050d020708031c0e010b0907 75
    0x182c064205034010b901c240f0300040c2514284281912500011400707140d00044000f550035015442402e561694115006081c0842020b9110302e07035604002c2d80c844c040e00d82c00e100070540c06c080e0f940808a1002d043e02c6502d4990b030701c46a0100826000c4140e810140c5031000359034082c040c400c00102000601c0c00a1b00d915a034168940b521034400900342c44a0300c05800c01a14a1003004603101d0059074070b00d80c10602800c02e0110038880c280401c5251082c01302002014a000c140450700c8400c07500440100c03402182e0380d146a48440113001d46030b1400380d0301e400070310b0606407aa918060003400900001040100391170141544e030314180380b540c016500050141d0300045c0b2110b08054000e13090007030200c10008032850b546802e6640c4a42445a4020f0810030f40d80c0d040003d0b0644c040c0c0e00304d40c0403010090151540c50900317241c11580c0b10b464017604070241c017400780c001ca668100042550900145140c2c0c0c508101c6030b6807050340007007074800f102803095500d61112880c207071601801503000b610955 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 864786951 1250 864785701 864785707
    0x8060f15041116060c091a0a02160f05090c0a0516020a170c03160e0c0319111c200d09061d0c040209060306040b031e010213080105100b0a1403010b 65
    0x7180c6841110f07062440c1409006c4120014020508007840028241d0706003420255542c00b0034105900e841e60100c440c0003032110368600401c062031303640459011140141d0741c07859292a9606086e00600410f401540010010b00c8460b11500d09507840ca210b071790015003c210483d40b01d00004040700642540c01e00d15a00407480251641030070003071581454001c4043c6030074207041c5941003441440c041c180608a400210102c6c0e44c00c0c4040c164007c4070f004e1030401704400b0784404d4240b09a03400c220050302c103005031502030115285480c060f550651680101400380310840003440070781900101d00c20080d80c1e56880c94040000c1051207a012000310340b0030183ca8408101003214541010020018003890052001c16166200d420640c3d4100b041180c001c5800390b800c00200c1e150000c040210019040150312920302404198000c10303242d00d4000012551360f0f12031403500c1c26944107958105400000704410880214800082c1c100304180703140405021100201a2040e07400030380010003551000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 864788201 1250 864786951 864786953
    0x1008060d14250b1603050d110a0905090708190c0e060714120a0912140109060f0b06040305070308030c211008060601021c050c03030406020904050108060f15041116 72
    0x800c40d0b250040400b9180e1a10300042a0011210a00300341401014410040307001941030840e60040102543c200c807019807034140d210320080140c00306204a5024840b070741d001c00c01e0030f41300d01c1290340b1890b810320a000202000e01048030040c00140e002200b00804403242c0c805540e00e1400800c40340e130248041004000c110921036080031183c45210186040030004084003541050402c02100d842c0400b0590b45485814840f003048070f262640c4145510701082c0108100043e408000c1406184208200c074007295014048240b04d0307400080c080ba0b00c4188200001100c50f00103581c0003140040503410640c1032240d1824012054201082c6031100702c04102c1110200c1d8070880003080341c20b005000b1414a500040d488000e400e514040d1180f14070004940c89016204031000d0469a5007103039030340e2a01341002e070000d40050040c18400d9041000015071203d00103022401824011500f0f201501e465802900e03d940e400049038105407100c1d41d90351204000301c090038103040540790742210f207401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 864789451 1250 864788201 864788263
    0x315010b12090a030f0e0f04020d0c0f02070308181207030b091207030f080a061e080d0509030618010b0607050319140702190504021605010b1008060d14 67
    0x1040102c403a4031151100d0301182c0e20800319450650142070130040000000003081101079030114081e005800025002181d50b45580592103000c280e82ea42d4042080c144000c03070b00c484642c4405004070000b44160701203222215104c1001d81e100030712510840d4615a8503908210696009403402001a020001003c406201c21080702800c00b21a620f40340b41c5690180285c0c03907101e01c078410044140c0c0069400900c2d030b441500681003102844100f1040d10802580004050080c3d010358043d0381e00f07074012a4001c000366440000002c02602e400d07135a00814085200060017036211079901c40e95040320988034000100100360040340610b50f18000901c0036028407940d00685010006100582c80d4800c030010141c80b5070550407240d10403410f18180c0d11710402c030050f410080e4042e10001d800400c6480b21001070b0f50191054000348120108841045040c42c040307103001000c40c0080000900915005004c0c0a1aa200342d000d48081e0100000c2e032803400481c100b90390444000e050300d207480300d03070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 864790701 1250 864789451 864789487
    0x4060801050402040b03010b030712320c0a111c0c110a030201080601112506020706050405060711030312010902180a030f020105210a02040f320315010b 67
    0x4054030103500d013900c3e00160070864401480740c5144d103100032001c180e1103403140c003414140e00e000d20310a0109406500300b480d440f001c1d02c3c074135091000d1103890351081c0468080501c0e10542c070051140c1e00700602450192840d8144030100c140a000d0b030349082c107200202040000c1c84070016a1800c0002080c0c1c0b80150420b482010914400c01d0b0039441080141e90220140390f0043c421f18150911248030301c1180d1030010050f0709200c81ca440000e108540c0440309071482c04868041d130032181c5140d662241520340303120301d0240b507401071070811000700802c001d6000d0000580e8080c08481c900802d03034080c130090200a8003e0048a5000541032001c910f21070341d60810010b046500d0640315203140d49143c440c606c0400000d05000003c2208003151440e010210059a6120121000c519080031200025400741c0a2040a003242c05008240100c1c40c4800f040c0c00c12040354040d012401c080125900c20f1101260180d161040b0101d01303604414044030786009011214219894032646119000c8100e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 864791951 1250 864790701 864790709
    0x160806040b0306061e03100c03050705070b0f04020d061b03111c0e071d0901050a0b060a0c0c2c0a1e0b0414070c2d030302030901020c1204060801 64
    0x1030809410035503542d0040348081c1c0051040b07401d15440c0080b4800304210480d143c0d44668140266101c020145102e80c00103035802c100d030f45c0c0400c801c4d62400b0096a4900443c5005844081d440000804031010042d01c1c0da0480d000801050b0150010741e284400d8508100882100e1001d4020300da4503030383c060281d0100d0490140302c0c2c5041442e02490540300c0007039090380003000c0f6111800a40002014000ba20180c54a904c508072864944030940d0109141681c98018962034400001d02c040c80d2032003101c2d40000c00502e05407420481c084c0c2200e030000781d00c031300360b46400600a00240c0030b0891500b01200b04584440413095100718880102400720080c4608400e50400e440c1d040d80b0501184050b022119071400001c0c903104240c045401004980300781c0400201000510032240d8101c00c4140030315110742c007090031000901d400c00c0b48221250180d40c1d0b003d03801c2140500041c1c02a006968441c2040000604220100d0141071411154841548800d0f0001a040c00010352000d00b0368094 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 864793201 1250 864791951 864791959
    0x1b010302180f0f030f1e0703020f060315031b190506070816170301080f0727110a050319020a0e01030b040b0d0b0a18080406030c0c0605160806 63
    0x415040c0c04000006003044920651552408140c1c40e50f41564601034214050200c07205c4400d402130495484140c20482a5012401012a648000d00060b4a000c1d03981c050800d14450031142c003032041e550000750203180103440c04811503101d51810008110700c4440300f180344000e001d8440c140f103a0f2083e80104481e4480441400784441d4942a0032900c4103540420382039961a001c20110006130310604009140706861041c50301001ca030940518103a501d281c00343e510600c40c0c1c0b5240356655600b40b04240a2542000700344807004507000c1c800c015001001004606080c20084030400350313021682c41800301e5070110912980b50b15a10401041c11f507891030461a1080d1060085c000d14128140241050f44811084505484039007044600302c80107448807003003c40d2480c2c07191001c10221a005a2070341b40007440c502c0080c03e030300150070f074503000300c00280740500b001011009000451030040501081346181d80000d0218881c0034402c0107542030840520f0040c010007040050301904447c0f00d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 864794451 1250 864793201 864793207
    0x2120a120e010518071d06010c060507051e0304150f020f0d0c2c091909030e1009030201050306040e012406090b040806160908070905010e10082116051b010302 70
    0x306d00e021301c1210b070301100c030318208216031b944610040780c0c40c00c9076580041c4600e003494140302030075410801600640089281e4803c41e03204ca2682d40c2000c0c0411280034040003010346070020740e0b000e9a40021004e0300c0d070740e4025103000340e1b03001c4066241e03000805501c4840c0d41c580d41d0150702c0e81d100c020b103256080000700780c400302014090340841d40562110410b2150700e9020100306498128481d614800c146004140001d681c1410041d0400c038410303c03110b01510007507510a2030148030704049007e80c0d50584410b400d45d181c01d01440000c007000003c0380010340d640c030306d1001105000c00015045c0c1485041172402c590501c440101200c9440d03102c801040701c03e0106100110001c80c82c00e601c01100054054a071030301c81012200c07640c03203510a084c140034105001c5501d01954120304d05a485050f05446a070700d4068155440e5041841190140d4010851058058264042000480f880d54206505158213034105507044205000e044400d540308109502c034031685002d072460003d000f401c0442c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 864795701 1250 864794451 864794459
    0x31e04120b0a0f02162414040614240f04111e0f07030f0e0a090905060c03070c0308042a09050a050c03011215091202060c070302120a120e01051807 65
    0x303410310200100402c0b02400c1014400310744601d482030115286c01c400148013403002e06540800c414410b0760103039100c500705200c8500488071107103554003500c0503100361032000804e03c080104a41d03032606c0c10f81c1d00150360f00c506907803a44c4500640c80000d5505505554920046543d203188d400d50b50781c0ca40d00c0a00c203000c0040c40b03054003002c0e00d00359901810012102041c40d10101e4103840e054504d194402c2c084032000c00c01244c81e82c04408403e12a404461080e1120091035105001c00c851440002e035581013400300087c4a001c40c1600144035013044036403404105220422030400c5910415424040381c0300700031000e404c0c080e094001c4000502085182496107000300c00b0f2005003d90040c90700140d80f10420031240034400603030580341d1780c001c01c24030700ca51504101040c030042c0210700512812000c076254511440c1142c2c03e155040d002000405c10340100c035542600070300d90070b81c240104c000150841880030b00448030407030403420000505151000c0c45021845100c07500f4030700c5900110f0140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 864796951 1250 864795701 864795727
    0x216081207030809010e060106120b0108010e070c170309150c120c0c0705130209032518090204091202120403051f1d0a0b18031e04120b0a0f02 63
    0x500068142c43c10070a00d075150565540034240803000011144242e4000080e1207a0180012800c1400c081c428000e24022800441d0410320078010140510140c80c089009035025400c58040c0a118140100041c012034000d0042134204a40c1600640c1021684481a81c2e0706041a0b038801025900c0f1800c1a10001c3d17000092207004003106c1030154001a4010b0000c0200540030050600400381c20303060001d20b1a800294007e8840280203111303051117505494255600d8081c25140620360840c810310701408501c0340328281c1c071803505440d95001034a0250302c2c0e070300403500303d24003941c000e0a85a0740c0d4a4001c0c0340549008401c4a1a1401d201c203000040e0042800c0c00100d0080801c0c0781c903030070100d21400c0180308440c00311018a40075551241c000c4000300c0c0b4107a6681c0900480341e22582c8590f0030904001107404d5120300354201300403034810303005810341484003104030840d198103203a19000034124010109130155400b1318400e0400085003201d0080f1040d1104007141541080015810300c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 864798201 1250 864796951 864796957
    0x403180e100603060b16080c010c05040311010c023a06051b04122d150e060f0402040e0a0b0702010608061803070f0f02090f0a1b0f0f05040b0a02160812 67
    0x18030720610901b12041402103040c161484c0d00302840023000380e4101100b016009a01c50720044400c1c101d6549c0e01c210365030041e004e01d01c1d03864014080200004120000c1907010150b6000006480321100480410840c800e8080c9001d0780310360000951800e00c41504a481d80e030202c490f00e1a504c04001c2404032a40d02c1c964a04070940c81b410480517174509414080c00d011102c428080c140180702e41210031300003030b500300f204403081001d4200302c561001c00c0480e440d940100d5102c003041e81540d010800500703141c0d0001c41e403811450182c41e40d60745966602200c1500a646160060f91030b180c042c800844107204094000706070188000d10051007079610b036141e01554070058908116401c0c41f00502c59110807800441d58024000402403602032080f2100a00a031031030b04030603203800518840458114100c21001d0fa481c3c480340103003403040070102c1c4e611409898001c100a424800060b601100304098050380c074045c0c0140440050304140182c0849551340000b106511214407200c26200003812 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 864799451 1250 864798201 864798217
    0x80721140c031b010c1101060506040302060c0309091015050702100e060c0d0f030f05040f11030322030512120109020a03060302090f0a0b060702090105090403180e100603060b 77
    0x400d0316501d564081504601811541c44003072000340020459844042d0b1203c840540c0c0d64881c9841000036243c02401c90340c081c0141c0790400c0042100348054600700001c1c1c001002c0d0281242d14090074240401c1d0f1910058034400ca001c05810f0003484520004041c0345032031540c614000c0d041009940016541c0030f1050000410300400045070322803a107800c2c04445050480700c040740e04803d41c3c003400800760071044442c2c0300080e142420002c80712420703002d0203000d8ae40001042000211984940968505403007031241c0c548800c01c0744000d500d004607198019507840707450102e20507285050182c10150780703000c803007034282d403c20420a8590300156080d042d2041c2c00801a02c1c3c100945c0c05500609807a0030295120603078070100040c06402544907846040d803100103003d20425401401018042c2c200003d41c0000300c44010710183c100070312940e600034000d182c07207440c001100c42400741c800703460340000d00b03641c0e28881040f80039101c4a00140050810b45010019907103401600100c600680034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 864800701 1250 864799451 864799487
    0xf0b010c02210604080403110906060702010e03010b18010306060501030c09140f12010c1d031917040b0a0e030703020904020f01030f291207210f080721 67
    0xb1407035400440c94418050914001d0080750702600f000d0400b44140d4209102c1110709560355500c40c10701d030030b14034001c90080c00043c206900b00034156005590014500440c10342541d80d4111000c421390b64030155500d4600841c2d174907841c550550810000307840c00341e0400e0f070616007000d061503a4258050070b200100c074000c03141c00840c65258400104a41004c04000354080e42c03804100c0403c94040d84a01d4600f11951a0302c10b0b41c1c1c0515804040f04601610940c0c0d040d04020040661000421554051944202030050b000e40300c2d00e03004032194229400586e20208003184000500e41c102800c3c01c0c40721412002800d90078655400a83c034207000a000074040d46401d40c1104040c0d00036080303103400c1c4000ba0800c1c45004124080c0d038041e5007070708080d0050140c580a108865080044070098507580b00d10181c100c0303504252884201900c5a406112180c1107414424007090058100101c0c907842119001d607542998208142ca4041914140e0002e40f03072050313280703485070300100041003c088040d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 864801951 1250 864800701 864800719
    0x1314060d0b06090c0d0903172a0c0106050d060504030f0801050d02010c051c0e0321090d0c1a041a2802030c33280b0418060f0b010c02 59
    0x950310741403070b00450410040c845d00741110b046c105504080704880c05055000d070003225559800c0d410000c10409100c04c40e94108180f140c04030f80341d400e00100000f00801001042407507550b404035904951010050b10f005d41e40c1d034107000c101540264a0310300d081051402810765410100011584036891030006e041c010000030700800c118051010405100840c0c0c03c5800c82982c130800680481380e80e9040c1e502c0790203461004902801c4a400700301443c05105000c50600315403100b88000d04a0111080e1014a13071030760005820a5040514180c003010b903d0041d441e42d161608944c508a1555900654000244808a03001043d8a00110011100140c80c0ca20b680244410ba082d48124000105140100c96000940c201144000b020094909101d42d030b030418210742c030906141c3c0070b5801c0d58003c03455103144a1a000400b020841f843e07510700000072413101043c001030844520f06080d1204003203555620082c007600d4441c0769052082d01009120000000c00028125400014028400d80d418 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 864803201 1250 864801951 864801961
    0xd11060403024201060801050303181c0503030115030f0603020906040c050d020c03030f0603010c021c0306180b010908071404020c070b031807050117010314010b1314060d0b0609 78
    0x1046042c260302e10660f50083e10035000d0041d400e08a00240212008110301c100006101c0c100041100c091070407003142d03d50040d03112000c001214510a104c451071802520448010940034401503008080300000c0b5224520001006015902c2a2804114552071721030b080001da1070725140e82d58092000c035030010303011901d0355080e600703070040000b40101988045070301c0316000d100000460040304100c0581d1950307a00c0c0410103081e05c0030905800c005820811820030707625400083e82c541c1c0c0ca494100421540c4d1104000d50241200e06040002c49440311000104c558110302e43e00080d00400000e86051410202e081e42510041d4103490302481c0d00081581c0c403a001400b842d070190150148443d9a41408a9610f00030700004421840d0b90098003000582d0398001c000300d4040c1000445040c520741c1c40d5455000d1903440c0b008240701a552240780d001c80e56a5030000310f40607051328540c005000720503c01c0200712003100500e900d009207014080030020807445a0495401003044442d07030300726610 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 864804451 1250 864803201 864803263
    0x8060915041508250f1511030a080601080f010b09010e01020a08040f031b03020d060c12140702010606230c0a0503030c07020922111c050d1106040302 66
    0x5039448040c00c408000c602081a00d004103408840d501400340400f00022150413400d400716042c4204111480c1c81e940030440b952000c920000c4002540c10700350121460301899a007958050400080041e504104002143d80c02140b2107070040d00e07025000b04c1541c14000d45801510401d00002d050000141842d4881d0303208010118020754051034064489560301280f0941c2d406a020480307400d10a800648261462040800e046a400500c070070301010071900c0300c800900100300ca040410400394a001070404a50042c1140d00f0f9260a42010360702d49520001c1c00c450040c0c01800401150301004039603a681d40c0201c5219a074090856503403846240200303803a00c03080580040280c040442040f2040034210081d261850098420300b440c1e80c0c51403c5070f8060b0341ca170701400c0c2280c0d080400002c0494000003900c0201c4101034a400400329400c1801d800c13960a45004032401d41c800d4591443d0b00d540021001102016a001401c0b41d09007580c2c040d444103c03060b1280000d010181404041c0a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 864805701 1250 864804451 864804461
    0x3030513140f060105030a08030103120c0b10050108090c1509010504180603020301060b07241503230d0906050c0c0d120e01080c040b18101e0806091504 67
    0x1070310800074110981002542916010501031001590140d0000041d20382008076580101ca40c4c06401c0c10300d1682940d03581450071254019500402950300681000503401c001c0c00e0f8001c50700c001030144040c0c41c05000400c1c0c000020a05259900b00144040243d298822201682e420101d407040d161141c40004a406006a82c01103450700c42c06440100e602543e6800001a20f0003540284422503c64040222034420300c1c0300100865110b10540c4420783c03100c032003009034000d40340700851b40c0c14000ca04003604110540054400c520420342c588aa12130a000301c40341e441242018043c43c1144103c080d00f2010184101c0741032020008200200c803038140300015000000a054a001c01c95508180104001030503900d408103102007400b021541c0606205440303028040c03420b5280c00c0c00c00488500c1a0041000800f441d0140c8850300d2030346d501d4441c0e0400c1c000550380c0b01f92020084039842c80d00b6514200f406401d1142c081e050019607141d480c100d80e4400303409503003060301064810109000301 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 864806951 1250 864805701 864805703
    0x6111e0f0c0715090602061006121103090d18050303190306030c0e06040507090b090103020f12070c0512030603030304020108060d151a010306050604030f0f06060902040e07051603030513 82
    0x401000404140043d800710094422100b41e5140030348541c4600003641c1e00c960948540041c01a40c4a040100358440c03e140c1441405429000c146004030744000b40440e001901c1c101280d070840c00000c0c4140c3d5008240403580340100650100f0f030303464007001c00d4a0b0701c500c882c0100421000c1c101202003a000381c0040c0011980080c01e064180d50b034250103a500c41041c0c0365580b190781000040303140548902684401d03102c00761003041c0751115020040d4001d50218601064010b01030090122031040703001503d229100c0354954107054503070751400f03509101d00e200c43c440d4014420310034070280361000000d0300e50040d82070800e2152616110001100f403018004014801c0c0e0301330b101510140410f8000e0442030a9803595004600c4580e001501900c40074000e6a4024000b407000300b0100d48a070307045c40c1e0a02d000d05224419142030f03445040941c1c25503000841c01c20340020741045a20070040a056001c55145001401c040300b00504091035170740200060f007003640340e0700441d001b10548080d140c101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 864808201 1250 864806951 864806953
    0x50a0c050a05240915090a0605011401030c0c031205060a03060e16050307050f15040f0303170105060f191b150612330f0906111e0f0c 59
    0x441d103012583c1d80340c851610030b00150404101c03400c0c0000e140199010700000005031492100310281280318100c01420103810f481000c1c6441e0101798540300707980c06490b842a010180142c05000075054800d100c02210405c1720700180040440d0f40a80c018030303641c00d200c00105940d102e56000507210a02c41d040900301c030303103001001d0410076000a40c102c0070211946d403000200e6561810503485819074443c8a1300302d0130595010f86a86004260018042c605500707807420a0f07200c5183c0c15051101c0d41044001c50310128480c010f2842c1c907400603005010031981c1e503261016a0f0841e00c001c0c001c800e40100b8a06003492603d08060181000347c0941070740c220f038584e06c54200e0405041800d640f00000d28854540540854026080c650101c061070700001c00d81000900080c1405842d0f03d0022100c41030220850003414550003409200d080d550803000225001606042030f50841d01d26180414480c8000c20048541000f41c4109080c80c0c24031140a6446100c4d1f484c1103004c902c15880a2070903 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 864809451 1250 864808201 864808213
    0x17042105010b0a090209040b09070518270f01091107110307080303101a03012601140a06060e0906010f05070201030f02040806040311150a0b0d050d020304091119050a0c05 75
    0x600884d990207031880d02812541400344803040c0040c003c84001c2503400c00c002540400c9912400807021a01068006001e0105200c15828072498400c01c142e284482040c001c503c070030300103920b1169505d6070141181e588100b140b07c204112000c110311500b00c0040501c0d00f41484050644d0f400e004a4005003004426244c0c2c910703061001ca0240740c0d1500404200d0000c001540306900e4080702964140d8003001c010741d01d0359540c091481800303181008070040c2076481d9141701d201c178200074507000d005200c2c01001203a064103000c400750103c2514080130b030051700544200005aa0300c5480c00100242c0303402e0003a03662030180012406015061034010316a070000400061185000030503034445c4d800382d0396180d40c1080b51007840d51200c00d18039a40c7c0d0b40d102000040f44030074ac0d0302d600411610300014005c40c103032580e559600b41444041c44208016800100301048100d2071401921529001454441d00e41503044404c2c90015070600b03020f0b02007010210300c0840c094051052400c0c0c4a810070100e40c0c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 864810701 1250 864809451 864809459
    0x90c0d03171501030c020304030c051c050f011a040b09011a040506270306070503040b0c0409050412030506100801033306060f030b0d06200705010917042105010b0a 72
    0x102d1180200301140c00a8644481003085510100960f801c1c1d0b0b5000440400c801d1500e000c00080d24a0300708030b404044809011940002c0d01000314880000100700041222030441c00710046080c411002c00780071f6030801d00304544994641c03200f141961401c2d11b4a0321540341203c40c00c403490050f0b82216400c881e00242121710004030b0313805c061840320301800c01c0144c04084414541c940348107a814101040040c00868005940b202250b540140c0d280316941c1443d9864416400f90350007601c09441d10642040480700d41a410f004180c0d00c10f4040d0380d801c00e06204454001d009180511001d0038503010f88540c1e1690f8200040004e41180168207030300c0345445020704020043c00c1601c81c2a0104292540801c0d4103402405000c001810041040941c1d00481e22100c001e0800d41070300480c0c1611b0401401030414400001d001c52601070000040c502102d0b10309095541000100340f9003024050000304280c3e9003d41031000040425000440d8041051400a000d0010106400d82c0f04451402c082 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 864811951 1250 864810701 864810721
    0x5071a030901050c0a0c12050904060b0c011a010c0305030a061a0a020c04060302060a050c0a15150914060d110d03030b030c010e0102060c070201170f010e0906090c0d0317 75
    0x14000c01d580340007001035846000c1861418815a1000320201e24031908410109280d40540d812191a90901d945070010b4440040d04496031504840207242000c107652004440034441c90200d14103009107011108a400300103030080c80c90100090400c44000009041034030250441070080c807540b0126041c80b12040c0c02001580c02c80e00c0d20f0f4006102e80024440303180b4040c02441d044075000342440b850441e6400080b500350740a80380c05020f501c1111003050014508200040c07491151100000312080c81518040c0d110895600280e5481d0503c58a1311041c0d440100c02a045842140c0904400c2514a011801d41c042689060741c0024003601d40810306425400c44407800b031044040c0c4030b00700c61810040d0381c10707403020b10801e0042e0302c460005000c11000e035004100807801410080300481628130203403e0500201d03a445010350000c801007014220b031083d09500680d491018100320b280c044d04095030703154208c001c1c03445415210501010b00d405461840c12640c03001b50a00c020389800301c201 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 864813201 1250 864811951 864811957
    0xe010b09090f15040809060a030b120c1206060618030f100b100f08010303030b030c03070b0d181104050606090907030501060e030d020709020703020c03060a0f0b0402040e0f0405071a 80
    0x2000035000e842c812407522a81c03c00d4051155034496055424a500881400710b41e82158086405042d61495100309a030786031250baa8481c0d541030300074030344032260341c0501041c2c240d4143c9050007640004240000350342d07200c0c00d03034941e0410750081285002046000131b16180a071842c44485001d5100032441d081d21541100d100c0c071406490f80f6010340540318084031001e400c0b900c0000019200e200520010340319800c000c4400b8402401c94443c588000300182c1040401c0e4480e11210200040c3d0011f00d050728003622a0f2070125504142016030651128100100cc031050305100c1d42c1e5490004505540749410f480500c40e000d4103006003840c01030000390007003100780100404a1a60603041304246800588041d83c5030b003641c09000c3c035600d040c07000c3c0301039044008100d00358099096080f129031400c1003202c4c4035442c0750300089407600301d1040c030104a5001844103409070740100010b200c680e018521031a0056241c4004203001e5a450074003030b040c24580d40005440c8031030020441c4066000c800a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 864814451 1250 864813201 864813223
    0x230a0b12070c0f0b071e08040506010806070507110d170d113603030304030f031b0c030c0320150f060f010c080f0d0e0f06010303020c040e010b0909 65
    0x36020141e00d40580c25103602449810051200c2d481c1c07464000001c210b814002c2c2c0103206401c01c0540c5440443c10000000a20a0940300190a4501300001e001d010030610340103000300400780145007060b4800070440e01c40c1034006803001c0860702450b0250b803900c19580d802d03180c00529034000715030300217504a03050388101c130017078520b41c10010030a0900480b2022140000518045050124240101d5121000c0c0004501030300004840040d00191000d00083d80b10302d00c01e55400418015040b40941221400140b01d019000e101440340c032100c0c3c201036110412038250600e8900c15803541b0382181d2102101031300b4110200c00c29090640c240d0000340c207200c01c0100781070b941c034140d603a4a20100c00e08800c96510f50f00c00a0348510b50441e50050800849050043d030700030b450404020582000365001d07008400446681e042d00c001000b00030f110f200500c2e038100010744025452b40d2402992001055081c1c0e21655844104001c41c8000350f200310304020024003409140e1806026541c0c4400350300704 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 864815701 1250 864814451 864814477
    0x809130c11060601120906090f0b06010f080415020c1e0304052b030509060d150f05100e010509242d0a0516200301060603060807230a0b 60
    0x42401070036404039400707114042c180d44082481e01519205009007041c0c16003502c01958941600300410b11109034400c07c1c0d4050722142c02c076420050001441c00000b0341c179080030040100c0504c80020709060040129407210080540c540e0508600035090408030321400350001c00d0b02c030323850782c04503000b1026000b1120125582250000d8a12004400356464842405140382c1000e2100020740142d015011448010702458207001010510704211a14001544030a261101080210110001c0c5840c040c00080c0c1e003074034134031401050140c510030070382240505200f404100746c030b283c0c1c0361010007051040d0020082c40c030428007158000503d500145500c44044002c000c01d40422050443d43d0050001c0e0b03d80403842e0803c0481c0455054100d03a0f940c01c1629201c2c031003040456000040c0c42c18080006254000c1400104105400c4034980d41c0820107150500204005808000c00c80ca0212a015001410003100f103046071104203d4a40c00030f5070201840801080c2800302001030240009030709 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 864816951 1250 864815701 864815717
    0x60a050f1e1c0f06050a15020703020904150515100c050f030714011d030d02070602160b190c020a0305031b131505090d08071704141f0206040803040809130c 69
    0x390f414094902d140105900007021750407c016100d03000d41c2401e00e484051041c5c03548a030b180d034001910706009840c01e40d0303407442e41403c40c813266445200e41600032012803824520303542c03088040703004601d44284d844284560f919801080c06018820706001103569816a80d6800c2c0621b048210580368031113910f0150304e880c5400080c6501c298501c1d44c0c40728284010750034100d080301d5100196108490842d0910b1b024400800742100c10031004c41090320aa0390400140f8003e0391003a000094407600140190900198000342c5402081c1d2800300c0d500362820a5807540c45401c00f020140400e504e000e030120002505003c0c907440c00151800780c480c2c0207000740c0d100102800481e814018400800d50240d2051f030340728001642c070002032045a1180c40c04100100b0120018a25a00140d00007040d1621481c1119410b10700307940c00c080d815040e0791494515017405200256074940c014002441440c0000116007031081d40f001359007215070010404102d8618003082d580181c0300d4086d03000d010030b0280c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 864818201 1250 864816951 864816971
    0x5090703110607051e0a0606140306070e0901121704121502030c0d0906090c03110f06180607151803090e15040b0109030b010909020f060a050f1e1c 65
    0x208003255400340d0000300a017000d032081c03001004a03d014488807030151194118590000e00300b13000d648000e0001560401d040b8022030149801c02c50001e0145e0104090013890804556400b0042d6055946021146041103c24940080d0405500c0c880c0810030f40b01040000e04080c01c01c10040310356103d0b01c07542c203240320f80a2041007640005d4034184115038040c0030702400e851813940050300140c096100416415400d85a4130914034080d00f003034420640002c011500b50808050000c0410320076141c00f841c100c4415040d170280c500750021107100340c1000441071b0a208410080380300e100103400e02040356913500955415600c25254088022034030249002070300130b00e00d91489110f005e0711129040200d0409003040000d00c104001c45050060070000800482c0040d55850b0207448000d50008100c0504d00402804840b464145c92050038100640300751180d1040c265400d810360a6203050311200d200780d018841c00382c43c6101e269041c07808034081e9582c8002c070701520a41c0044803010880c04841c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 864819451 1250 864818201 864818209
    0xa060c0c090903050d1401060306080c09041b0b0c060604050c07033006080123130b0a0f020d1a1002030901050d021201060f0e03070501090302060a02010f0509070311 73
    0x100100640240040c280400c40c0c0d907002d07004a90210300c240352185c40e08802c100914215440c0200c0200c2290107440141704d880d4051058802032b02e5810000d0246200c040b00269003a07100800003009051780c104a0901c40900700401e001822400b5000c1d5207507865444590781da0f480031565144540c3c245004101c4460a000c2107907095074041e0b480c603a010b4409816200c0080e040074100c3e510b109800614044050607108250191055800218020341d190001c0d6a60101d42a1a441c4a19130b02e03041c440c0048050950b110302c03a50100301400c10b582c4008800004120302c0110996160000803030884103a010381c0b005609000301000c000f4000c4c00042804400c08466008602580c020402d091040d130140f4060084981c07040401351501c80c4469640d040c03404280e111a00ac01c031980c48881900c3c3d0480380f1746010403019002009250300e0800001c004122610010b0300400c000209942154400c2d0046500010181014003050505d400201c3c1d0768030311484203644500354201c0c1c1d1801460 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 864820701 1250 864819451 864819467
    0x406151701030c09230709080705090f01060f051204030521092508010e03040608071407030e0415061d0609130c4b1409010516080304020a06 62
    0xf400001ea1240c8a082030900702c020020340d000140495040e0011030442d210001d0550f01c60f03403441d602c0710303105031810041e035140006030340009200d4043e002c100314244640a0410b81120000d240c4035800c031180030001c1e901ea00c00d4401c85106404100100802d040c1c100d002003403103288400d1740c04819910768488080d00b14080c3c58a0850390441c14801c1000d1078003008080480800d0042150019a42d14001d03007100c0c49181304009540020404000241d0081c03080359104040e4284802c8502110004131074900c5203003402401e0010403500070038142c0317503030307000a44c00d54890240301040c0d80c8802d4090070751052081d0b100504661000210302504101042c0c6510450140c8a000705c04800080d1300c02500340c41085c1000c00818800070381160b070030000c03052800c4440c401c9030b043c414002114240c45c030601900f00c0380d03201d4641c800000302560085c04210810b5416405d20348487d00080101c8040c0304201403001031b0b101031041d010502850703a00440c0600d01c2104c030220041d44d9407a00340e5044c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 864821951 1250 864820701 864820703
    0x1120c0c020f15030f0f1003030f0503070908060711100908090d11270f0609041b091505040e070b120919081801110d0e0303040302040615170103 64
    0x15003180d0008005003001c203100341150314001c0c181e01501c0d1005041a01c1c58004942000c1010659010b0181d00319000c5144c0e9003081c0400d0506082c0350858034050034412681035030004100c0000009100c8901c81c0c000300c00585101010f80d00b084c100042c0060010005815002d924000e00042c0840d00742c02c0d11030911a194800e0b286070515110a041004c0704210b1081a5182d041042900000359182c506c2501c0c5400302c0e0b0075014076858010440144500000c0c80007000030b502c041807040c2030780c80c0d41095a01c00e40c002c0540c01351f0741c1e0f0b0f800059001810703130b031014600604001000d103808441c0083c983c140e03a01510100080060544c40716514000d07403182440c200350401aa441c1081d070300002d42e0740402d06034101d4039482c0103809a08881e2800740c0c015a060799010a022071460411014130b1282d140c2460510403100406051340e8441070070030007101c1031082e585d103008d004c0d031004d04c03c1e10001c40c3c00500400c2055aa803070b0401030044400c40d544002a60002e0780da400282d482e804074162 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 864823201 1250 864821951 864821957
    0xa0b13020a24050f0412080706051f0b2110050310050f0610050f070b04060c020d0522031202010e12070807030305040f02040f0e070506070206221e0501120c 69
    0x11510031100b40c0e00f41e8084401036801d00c00822001c02d0301512072420380b1486100b400e00341d9950300c1130b003080401c5a0300a0603815041048845001200d08406004000d882c1c0e0012200d0741e03080078a8035806854141d0030440d900780c0c1d1400403c5144002c10a0314801c855050702070340c031084240062032040340c40c215980c869400d04507000c5401420301c001084030000043c01c0c03a0b403500301d01070320344403198001841c101c0304800c0a41c100400c00c03045004114403031801d400245903580d014107000c1d2081c01002114602a4100c40c41c4d0031000000002da07200660700325450812008030054000d0191400103050310b010300c10a9045110801d202007240d4499810442c0181014002d58040f0007425001e4000d40724044c1002e04c41025036624840c80310541c4910100154501000b00001e0070007042d5800b6900c541340074001940503840300b81c200e0b0211410405090402c2c095040d41d07000d40c5095402c450340091202c2008602d00329080e40c440d0640703001b600ca865581d5202c1d00c88006448030100d1400c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 864824451 1250 864823201 864823259
    0x1701110301080607050703020f0102030a060609091404030e040f110310150207031209080d180f051c02011103070302030c072114010204180510140904140a0b13020a 72
    0x5005d201380040c01986100384161845200c048640d142640c00982e030201001c2d64800c1d0400050380c00406140040c8001c0c0000d10104184150150000000a00203002c0c00303410800007101d5039841d0b100c540580c202120800a0480022400900b900700303d0382201070052001c00031484245c090b540c1d140c480322960003400001d0465442c240c0c06180d412001050018001011030140001d1102c48911111755941171011000141c260011002542c010621611180d0f024461505da180c0a259100c1c10085d0307441a51807a0310040791126242e00c6451014080441c0d032908142e40403004101d564255411102c0054403151007440b40c15003080c1a414400d107001c10f4400182c4040182c2c12000c0581c40014101541ca12100805000040d070301d8040580e14401c000000760f445220002a184803214a2041c044c000046803490801800c054085038414100480c81441002449141d503400020164079042101c110184200c0402080b4410544513a012a10b02c2002c0d6040527000000d250680b2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 864825701 1250 864824451 864824461
    0xe01080c1014041a030f070809033f0906010f061b03030b060f0c0601080a0c0e0a09020d06051e150418050a0b0124080106030203070e040617011103010806 68
    0xb140c8014401c0c201140c5003d120000b003207000c404c2030000c01d0401e1519180c0c0c0b49081450b100d1050f000406107001d1245013014442040c00c00820350315044800c200c40c480c12500c4e00762010030884104000d01c00840e10751803042d030101d800301d0200d018030398110403035241e07980b0b54001010030035490252100080d03441d590a004c010b10360141040b00c40c000d040c0000d080b01d00d000841d107594807040034a50400030008400420f24410040e0f2801098000003a10002d04190355148803085540b094001285215001c00d9603480d0950059007850350040040f40d0950907840c01c4000b50400319500c2c010300800c3d120030140f00181d001d95034450072070343c85401043d00040c41000001c0800c4207190100d56010f8a0210001d00200201500d00b030040c0044169076150551490050301c0d00949050071524107412290201c1c0c00c201c0036415140c0d503040258036aa1102c000302c0c0d00c180c2c03421035994420f09003c000074200c500c4140e08980b445101c002405541076884058205100a11a4183c542c0c05400011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 864826951 1250 864825701 864825707
    0x1e030b030d0e0d02090c09182509090504200d110907111009050118170306040209060712080a090b0f041a0a1b030e3c01060e01080c10 59
    0x322064000b020105016516000b00d6a0141c00312249050241b0000e40c4c2c070340d6460014a170008850348008005020302d095000408448299402c07403e1100c0303104481010b15010740710210251818810030041482c150402040064401000600c2800c0401c80b0070348a0810191a803405904150308210840f110424003100f460002c082c00100001c01864500d03914041c00000400860440003040c0c6c0c0040307091190865441982800d504624403504400141c01c070b8210780100740420b030103103490341e4407034001c83e02034411800c006a00580001c1c1150800007c02c06d01e151690783d81d616802c4955030800b240080b03410651001e440c000e505030005190000040707041d9071052050324001182c030f041107a49050401c2c00c0e6201d509403915945d02c1000410b08800c4e0740703030003d107524050025018840314135841c0c420403403c1002556445030310068402015440408000c0c0403c0d140840d08290081c45e03008280e0b078000c103c00303a208200005440302000892078055100240844904c6103580015 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 864828201 1250 864826951 864826967
    0xf0803040611032707270506090f040b060a1a1e0405060715022b0f0c09061d060d020904050a0b03030a0516060504121e0815150301061e030b030d 64
    0x513548510403030301d0214461000984c192540600109a1401d15918851140540d0130080c1b609005900c000f0400c0f0012005228843d000b43c2c202d180c60713a10751142c1010a4501009410007541d40081180612102c01c41c4801400c10400303682d002e0f41100d0005007400038174421441941d0f80144140103540120300d02500c03582040d8010b00e80145801d50100c400e5098003c0f503504244880c500c0b0134001b450441c0d82c012000d240e900c03500c003003248001040004d082c00c41c01d8083e0b032041048031070125403072600d003020007525010300802c043d0315251a800240c001e0740c8a07a40321b0340100d04080100e281604c6d20702130000011401009581811001c0404903816041200d83c0d0541c200525a1200420080d00c10540114000d80601d03120140036180640b41c89448404040e0700341c101d0281060281c0c0c020300e0746401c0100040d1201102c01c3c0040042c0b81e004003102c1d90300700740c031000000190a0707401c10421300603101541c43c06840900159815400c507021020100d801d03420030110588003034800c00034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 864829451 1250 864828201 864828271
    0xa0504020d02092815050f0d0216050606030f190311070b0a09210c03060b01020c0a080606031e0c0105090d080309060a0b2d0a030f080304061103 64
    0x8014105101d9400189180001000080c003004d104280b0500907a042500e000c05440d44000c940d555215202d0018620f10960304000105a0085841201a600c54040f90301c03487c202080c04000ca940c6041458850200f82d4115119109a2080b51000308005c900e61700300900d14080b484030011561419030355011311554003109801060804141f20107a01c0162100c8442651114001400d0000c8190f550300307801d100320149600f400390310001845401c1c0300d905413a1f000d200442c4074091680140d00e044644010141d01030880580401c46a42c0061000d108141c00c504032901d1402d03442c02501710441500a1900303e8025401114041d40a100100403040d00500400003588254489440c0c80d042541d24038129044603007445040000350280006210707044a0301034541241640d2040e54600c0041f00790345510301204503581d10764807211014007c1d60400c01c80d140480f5946007450b81d51340304031411076040d850020160300c3c45d9040c0d01500e100d0340d07100041c580c052040103411400c00741c1d1280 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 864830701 1250 864829451 864829477
    0x6090819020d020303273c130e010c030504080a03050618041a100f06081305120a1106040c2106020a02030405120d081807210201030b09060a050402 65
    0xc4031030b006840401c010700c0204a4000c00010100766a413080406030641d40c644d034442c1d0310400da1801e164006e42c031007407102c01e41040c801040703400d022070300e034140c5e00f82c842250b0707100c07000c405141c03207441180d00064003150180d0001c1180814482c0c050781100d0044c3c6024106902c14485044454040d078002030b01300100030400300c1154140130303c03485482c40031101290000f042c2000400459840c1e541d035a0008020082c0a14050030002a50074584080c03140030300700f02198000c9010400c0200c10415000d8110061b41c800381012282c05045502000b2910b000521004011801714000b20f5002c5c000e0794031447d90045580703040d08010102156090035505104d0380301d15032000034514030003001541c1058015607191072810003041412211903604010a0b00014651040da90703000d400150f02c0700048205a107520500c0044a18000403504004a00f0540b002c1451180251a1401d00c90300c1c402d0341d052104825600c00d12200c2c0105a40241d0041100c54043c019480c080c2c0290005800040e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 864831951 1250 864830701 864830719
    0x4060903120504091a100801050919061205060105010801060c050a1101052101050109050901081207030909020a030203270d0f02010f090c060f0216230405041b0609081902 75
    0x141c1310000c450200501c507000285540001c0c0031420100281c095002c1c40e803d21803040d62401000c102403940080c405001c401036540c900e580f0042c03c0e07109038007800001031003841e4800079143c0390756241000e0203080d0100e403000000049040c0715000d888100341e4880090f01e0484429a2201c00e07076140d0102031030502000348604035803200c2d490f0025a045e1170a4000c03503259450b000024040125581003680a200150014082803000085492004e822041c0307840d0f50702400e0a00f21440e0031030f500401201400000d20340c0c540b41e4982c000d54000c4000240100e01c0108201c40c62140c0e01000c4421001ca0300032880d21100f00c2e00910194954549900000c103003003c100403550300b210f40c5c403c0120740c80e4004503003d105699004a004a01c007445000500103234003401000e00d80e03001c2a02c01c405003c0103118941000014881c042c0c40c400d140030304180164200ba2a204699907184144c01c89250360701d0900050951154120808603100070700030306813200c18860b000d0040c4030f0110f01a60080021 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 864833201 1250 864831951 864831959
    0x1051b0a0305060a230112020c030414180a060e060103020403020102300714060f071d1908010515100525080406020d1206060503060d050705100e0906040204060903120504 75
    0x780035411030fa070f5040c1012171101400c4005000340c0d412460351a107007881800010b9142d0000011103080e20081e918030804400c000c7c0000e450351806c3d020004400038030f03006025107a041c41e0408416909041d00c589000d0303450700300450403800381e072002a006034000c41d8a110100d1030a02810541c20a060754505c07500800441c01005500c030f0300d0202e0b40c801c0c0c00e001143c0d90105c18003c040d00000e4000c0b000d0390305d0404050062018a40550400b0380701021010028990780740c45050441e4803410b00b407000c010f0b030754000184c0204170445803124024274410b41058249000b030020303828084e05441d440e08181d21101480041c483c248220618800702001680c04542460080e01c01400c807a4000d154846103c0310040c5240e0107010706420007400c201c014441c140c7c01600b92580300d8001d880045590020741402440d00b2055400700350032158502c41900310a42c00310040322504410b03030344c154003a00d498061100720300c10380c46064005041e0a00c140000340c0710880800742d4010a10300582003d4032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 864834451 1250 864833201 864833219
    0x519080f03130203010c051305042a030e0706030b12011512020301090f080915070c06030903050d14061905030a0609050a08360d02211e01051b0a0305060a 68
    0x6c60300301d80c804a031000c03c81c25001400c104480015000680d014082ca500181c403a441c03074904003101072521600ca101502c0310511035400480c1c0700c5000070840e5042a560980038000b0002d0010260084049081d02e0341e1422050040c681d625031104010003440303191040301c65000080c408200e0f4195200c2c0c0d01c08000c150880c0a2254042c010f91030150b6035001c01302006424840c2032000c4d4010302d414042a80842e003c2d42c7c442003140c02d2401c000c6a10f41080c602162a403058450341040300c0c0c50558922100040c0c24400e41c8a12820f8032030302081011581c500710042158490b060303141c0c3c0f014820000003056034011900240c440d1040320002441c41e503800045420a40300041c40511915901e4203010350080b10503c402e2150110462143c81c4a022841191401e0070103030050883ea003c4440302014528004044017100080d10039805103054800524811546908c03115801e1101140180b503500404404104002c80090718140c2104416005230200602e0390354890100d103800590005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 864835701 1250 864834451 864834461
    0x8010e1b1324050a08250b0d05041103010207210c0c120c120b043507060501051005040303030903170c0c06160903231501030519080f0313020301 64
    0xb9203199820040c100310786400b8615800d61081e40b04035110b400401510201080811041030b584005a248106200300c02c400c00b01c19a1110300d4046c400901005600031560215018a105481a030441d110041c10107082c0e014264000d4030036039481c1c072110101a440380c4140b05040da6410404d451460b10380302e80801c82507c1e03000c003030348581c501e81c403404200d17a5814a4000c0c1004661b10400c2543c5a2a4009010fa00402c01000020300001e4078085420404828040794a00d8174860800303c520400a65640c1101104643c182e01305400414180f404103055008400706030307501410940f45031001c60181012480c00e40500032120020040c012134481c019210303140031a0766994900082c40d8507850070748018205418a1510b00001c0c5503503600070480307022260003d06682e01c02044007007180c00201c503240082298400c422907801d4461180284d54103da0003035040e00c56111044040c4201d8a241d46401400d18104120b0f420f004251080907542002040c141c00e002c2d8000d5a001c030b82114 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 864836951 1250 864835701 864835721
    0x211f06020a0506010801060605040603020a0207080f012304020306240a15080709080601140612040615060215043003060f1e03080304052109040608010e1b13 69
    0x10700030381201828003404010540c010080000200324148c0350040041141c0074500403182091340000390394412903c200100d60240c10f42800303452280244140b51402003e40c5408199072444402c0303040000ba1000c0c00039480340350060003900340b9540c0c4005010039800000c90384000080c1c68101019162034941d512005010304c40b0401000b804506d001406500d40202158104071040c4400d200d12900811898112460007407200402d01a0078005210703802004407116451440708100424020207400c202c882d4200e84501c10040e41d20380c00d0880c1c842d043c1d1600d41843e241500c0118000694005406011401c500560400f03034500c4201001052464208070f00069101c13002400816029180c1c48024405103041680c1c1280c0d4042142c2502090322020b8003020022000406000046c045030b400070007000036081121805030344a84094100c800c2c024000c528111001c00c2c220b01c14801c045400034110000c00c403001210301ca411020b4136042c52241c000c40d03250340ca04001c213802d003d5440d00b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 864838201 1250 864836951 864836953
    0x19050c01020c0a151506111509011a010f0c0f0807050312040209091506041a0901060c12090b0d0c03060504020a27030f03120908040603020703080606211f0602 70
    0x40f8032401c0031800a0700050309180c1c0c061078020030b080084d1000c182602212814100510740c03220b0844c0366030800b03c0c90202c400d0503c43c6042080440201940181c9110a4400219444182c4038004440b0040180c4030400440e42440809002c92031801c05428414490049a440c09109540b03581c190f0f0420354080c40e00100e031034240310443c070701540120b502801d050010004405c541e0400710005038090032032800b8a90311450b280e0801c0d003800c41c035070072440080d240111950b51014001c019442283d000e0b00d40c07410303103030380440742611849502c4100c80d0101e512a00b406550540030004104400c403201c1890350721300c030002c3c1a495130b001a004400d03903034440003c038441d045c603101c1000c0d00c120145141e142e417006003800010300c02c8402c042419054645101f86841c42d50202005003181c07103010700000c0c0d0201c1d0000741c0b580c1c50b4006000ca148079646aa55070b840b45000d1040a010b5104042c00d621005242c8210030340c5084078495010001c0d02c9040c2c0d040c012000706112420381c1d41c01c14001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 864839451 1250 864838201 864838213
    0x1d0d030e010305010902090315060d06060e0415021303060b040f110706060b09090c1303020607121701080d0e04090f081e13090c021006060f120b0619050c01020c 71
    0xd582c01d842070314010042d10f5001e41c9441242400a5111100e1074240060b040e0000b0115900703895900e11580041c0e40020204045a00c0b50380d41e19030008c3c1120122000307807608040460100f42c900035140e0302c80d0410303100031030241181c0e9090050010a4140d5400075a202a0a0900310160040448100c00120055611078190800340706441c00794000700c0d901c040810075036110380c035000c40566001024140041d02d071400003a50300c040038911390000c1e5001201041c13480901048201581c070403a1a92102d03145260020180c140784142441004001d410a001c0005140e0240b0b000c8429090010000281c000300e41c0e5036031307040621601c1e081e2411500802d064104038048541508010040c09485007020095000c0c031401c3c044a004000303205490b40611200035000304200d130750030011000c0074403046480742c40040c03950340130100c0d10f030005030b00340c1040d880c02146105141d65014040d010a1528003844003074050710460005030020000c01f0000079080780c40a10103480c032264904040c0030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 864840701 1250 864839451 864839477
    0x1c0f082b061e0b030a0e030f040b28172e030215030c030408070f0618060b0a030302070b0a05070503040602070302010206061c060b01030b030733020d1d0d03 69
    0x2480307400c00350a8140d0760081100030f0194482040669074465903c03040442c080350b18107004c5007540a80420204003180200e40031492034081c81c05411a20032801000c520300f000c0428210340342c120032100b180810740b203080c041c0c00420804a40c550043e080071603407081104940031008025500040c0c000f100903400c0041c021481e102d146840c00c281d450164034294201600300402d60721002d80000e00d0000b0018a20040280d418510300a098028808205211080710420214054284101d907132a150031210754840c40c0042e2000d0550750164010501d6030f080000c607000c0740e80600020b50905c0710a1254400081c7d0410003400a01004d5014210740c41c0f9500c0068685080500585e2003810340f1103020b2a4014503221800700c042d0003510201d44500041c005030020101640c0603500350140d800e02103905030344080d00841c0070030948419100c00300e42002840f4844101c40d054801a08440111900c030b030304c100d000d140d010144c641100000c14032035000440030942c1e00c50032004a411480c0100b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 864841951 1250 864840701 864840719
    0x2252a0905010902040605042903040809100504120201030f0902031903141e090f06210f040210180513050105031015062006010806061c0f082b06 64
    0x42c01411072060541c142800c15030098251b0186010341628100c5069214081c1c0400ca50f2100007410300520b03461382c3e070a0909017000b540c0d203d41c403614010350503160030750702c198883c0c012902259420342411400840e00e40c011000b030303d003030071840d0301040c3c890406e02c001d660140b2222904a01640700f01403440c03807903c1c000d0410440c9540200c1c0005040c0000046c1c3c5151064610288003c08000b50b507540c03040000903000100160510781040c004104000f10300051604281007140c02599440140c1c0c0d001d42c90307040d0f0002100c000390440b6a108120282d40e028010000c101112103c00014013a20794010a449040048034104100e4595004010b141010b00144419104082d401d10805035941e03d1080c2800e81c600c00c1c401005080c070700b84000342e10f13111006002100c50308151412942d4600c05240e4845090344c0c040d10411100c02580712903103684001003002d41c1c0c01440720100003255202d19060b50001c9440d064000f04400c03400ba4000e80b04490480340014045c00000c200303050504179 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 864843201 1250 864841951 864841961
    0x1b0312030c0c250504110c010e0c03071e0b07030c05191a0618070c06020d06050109050a0e010e040f050a0b16020109150b04020403020613051302252a09 67
    0xd1100c03e20352901090200901c40f018003070b00c0040c2c0d4082100d650f941440d01c2988114041c0f031006528180d410004500d004c1f4241040c0300d0114112042c40d80c0300c0d00c01c514420060880b41451072180081002802e0403840946031003030281c1444c01440d000d030f89a443c208451001e4158002038084103c800300310700c2c0b29008084044007100202c034cc1c60084049403a080d000568000d0480d4000d0000f403080e8490300c44581d078258080c0d8250348132100e0804400141400d4002c00e030204101810119640c28aa19484100c50460612481c284d00c0d140e11030381e08410180040d11041c12250040002c960100000900188200d2102d405482c0c0a0394034034800c110240c20004590403c103042c2e02041802c41d481241c028909800100d00c040c400010340244a20fa20003900480082022048409440320040440b48250b039002d540e220400105800c81c4103030181e48400005c5544a00703c07080c1c410b01e4100722103110348040c2c900d070b24200021296211b034160018946e951a02c0c01446010303210b01403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 864844451 1250 864843201 864843223
    0x5010e01140108060d020f2101110a0504060c0204061205030c060c1812030705071d130f240f0f0b1f080907031208150a0501021b0312030c0c 62
    0x180c00c408030692000a040700d0000d0400d034440c40d01500c0f10780556030b47d00d41e403500248000700400d04280780380612a03035542c078200d4403e00315460704040c0e0030100d040500f101c400d001d00c1d0341c5041c41d2609040c029950405c00a006076001903559030045804071260f005010958001c134000c1d80c40385041c84083d4034001c07004207183c40b82d40050007004214030440c072a90580610072140b4080b404d07a1030184501d14092090054030b54400d9480000301c0b00b80203151184070301c5203005840c0590b643c9014040c440b054448005000070340701540c1001081d980c8ac00c1c20498005c880070b400201c20b0891050307061710803c040c1c41034200d0341c0b000c0c03801c00032007a44548244260250f828040c645201a810403808a00741040300500c840070000500d649001d2195501a591043c103500ca07190084800420803030080390f908401d0a0080301101c814a0150541d60403107005074001d210340c03a401200d41076120780006040c3d40510070401d6181c0c00c080740c00040c0d403082c81c1003500c007512404120012887c000c010a1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 864845701 1250 864844451 864844469
    0x19060c0e0901090e1f02041a07020306180c180105041802150901120c0f0f03020c06010b09060c0304081605060c150712090f12020304080c120102160605010e01 70
    0x16049140c0c0c450001d03050448803502e4000030340c0c00c1c1d24686582007113501e4040d0325024032a00f991340498a03030765014005446584500303125084c4401082810303031181c0080a5410703402000007810181040b01c4041c203944031402914400c200890200306002441c1c5080403407104240014070040c100380c4144801c005102c3c50402d031140164022600303103040d45c00008041c100000e0074000700e90066002010f041c1e0302c01c504100d0307401c8940340207158250454030400010083d00410151a00c280241c417401d541990241a15918221907043c7c01c1d404182e126030000410311011003800c0e403d001070001030000d0300160048000781040038000100c0b54010300d100e003a0521440386200b0002416012241100980d161261208001514905925850100a41d00b000b0020003003001d03590381c207951a445038a10000c08030702483c040e40c03640113030b0050a10991155042c01c4851402002c00310100f854040014a031216190f203500d41c0686140c0c060380c40f10303164001006100702d010181801000000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 864846951 1250 864845701 864845717
    0x60405010c0e040c0e09040204060b1c0f020f160201121401080105011205071401090911120705031e040f05030f04080d0503010302060f0c1c0c0605010e01060e1e0319060c 75
    0x143c0c0c00307805c0d001c1d00600d05000d86440ca001504648466000c0c10180000d806e00d20303154546004004040c1c1c2031103070110034071420051840190305185c000d9842142202288a0a0280b41142c0103e8080c21550590402520b11481c20000c0d419200d018903040eaa60001c0400390b0400b448a405c0d00e4042c0e11205686c3d07484211100400c20114031481500c0e031a00d05028a503001c000121000091038200d491003521703260f11a5021183c030700050000d001803507041c07950350341e4020040d2040e0000710b5400e0342c013035000d4440500d0a0040c0001c035521030311070920016400c034552100e40c5950050b003c1e0303110082c40000c06005210b01000135500e0720090b0315100c1e00e1981558045800ca0140200701104141e02240600480030180b080c2001004816010010800e89200c0207050305403424050b10054a03000010800c200c00c0a8000d042e0340032074541c1c01d41d40350380c0814000300c40e1000020081100b42d209c0c500b900c654042c0700642401d8030141e10b41100b0b1503141800c80450f8003014040c0e060082d02 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 864848201 1250 864846951 864846971
    0xb0d020a0e09061005030702100212010801180c0b090d050a030e011205041109060f1e04060504020c060417070b040c1505030906010618030c030b040c0f1421060405010c0e04 76
    0x44c40314035000c030085180054907905c803414242e01e000011003080003540d0010404e50701e8901c4e100c2c9114100c56000c002801080000011300700c1c40d60f0b032800e018211005100083c841035404400401105a01402e03c3c180f540f0760791a10f500342024290b0807000a5034141d504043c40d82e2005010742d03107240000003040b0a0816070f48100e0b503060408170682c00b1ba03000100185040d92000c10711700c0000d00190003042109241c491aa64201c18600014400e80c135101011489041030b00c21786565031609002002584c03165218004850102c0c80002840c2e40d04225840008031084400d502076407040d111090703110b00b8481d811420b14000a0004108141401008400c03c400524141124058140325500702003400e1602c651084a410162503101c05000020402696440032485180281c0c100e026598842c85d070000d50030340038410386251400c2030407018003610300714280780d10105400c6003099448200c2d00c0403500b4000308840907503c5075540c1005404094100c215403030b60f5901103400300299096 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 864849451 1250 864848201 864848209
    0x4031a040b090319030513051b090709050603041b03080c0a231c0504170703020301060504050c07060e011401060210050f091e01060e010320030d050910090b0d020a0e0906 75
    0x102d42ea07013104140c0c0f15408148100c401080b0f4811032900030013507454100940000d60a90f01035481e025009280840014005034883d5a0500c10b172031005003035624689031500c41000c41c092200d1010803058050320000000b49001c4000c0111028001c05041c80d060903040c4071601c0028020004110b805414100752030000108000c01030814002e03240315501c1148000b220310740100d401a40e40058107800c0c0740c00e400c0d0001501c0c01104e100302c0003881400c0e00ca10901094601c10b8038807003015081401000c0004261390440320a22805000001d08488107903002c10800c80282d1109000d078104140800d080c441a0243c90340c080c0d010324101d41c01d424003110040e9540e1038140694001c040c80c0c0c4502d84e0350352080d04040024288100c1d040d1442d41c50f030500340004044c0740c5001e00c1904c480303400c401007802e01240b07513182c11005403030742030805110034280910f0207113410f005000c10240e184041050200c4402420740c281078402e0040e100d501030440a40711010100c9000c3c0314644403400c0114580e1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 864850701 1250 864849451 864849487
    0x512010302010807020a081303021c0302030316050d0603030305150a0302100e0a0306090b0108070e13032604080c0d0207051c0317070807122f04031a040b0903 70
    0x2a0a183c503160390b555600b02241032924400e0002c0080c940003484d46515540941d0b4101680d008980b650503070240780302e008030000b407201d00080158206000080d01c03060005404e10180a03c3d0411500d0f24100c040a12f084680a410031008030740c3c0c81040c802e210004040c08226500166000c507001421900000c1182d842c00b00010208001c408c02ba110b01c1c0c440ca03c10070700a60b4405014071109890b86007070741103008240595201803107000b20008120212040c03480c01802d034880f00604108050300e040700c2c40248891421414140c000749030340411081c0100b00c3c07055005145d110340f510300c804582403e01c00300b01309410456100c22424045580d9005210500c807402c1104400d4180441c541511110503040090132030b1034104003007145903a0402145840740c0302960701c0c0c0900c2842c4252500c00c445000c1c0c60800442c180c2880010500c01c0d81c1c0100491081c08840c503803c1c980d9940d04d503102e10700c07a004802d03071074010749051204100880450740c3c1c00a403c5030146040404001138920808 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 864851951 1250 864850701 864850703
    0x27091d1621050601181416080609100302090c04081c0e03160b0d0902091504050a1404140322080f0619092102061b03160e06040f0608040b0705120103 66
    0xc0c41e031400c10070b4070319186d03000c0c1c0c0d08540305100c551400c1c074110b1643c0c840f21449131141808600c40c000040e1051414501d0948249425084c1c042c0d160304523020b0006c24003000380f809859640410020a19003010003540700010110341d500e03c2110222100207096035440104a8040c0d4803412000b280e013007109001c0300603a86440740003034403420021141c05c06020100e501942048600d4180148070196000120b00500705403828000d03902c038216100b08564021004010961422010800042d03200c1880e90300b40b006542280d0821815444904036401100c0c1d400c500400c11039400c025503101402507145e003141c42c80280120b45880c0540c50042c445100403551501d580d40d004100700b20034040c440f8081d51492544402d13220b00c020003c0d581c0c040650700340d0384404490302e00c2c48140b00180c00b10303441143d0006841c00301c0c101203541a1949000f0080d1a0340c0300c102840040342d44607034030600c82c1c000e0206560300c4045003080c0c10304046606010f09a00200503040003603540c60680c0302509411a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 864853201 1250 864851951 864851969
    0x903090f08030a180306020a32090603070306080105090334030f050c010204060314090a21020a0503030c04300215130f0627091d1621050601 62
    0x1083e084c05280b61600c0240d000240620701c0410351300750590303110b080c1400c0c607a8800c180d0301041041c40c044139204264582c1c440181e290030001200942006009143c110300d1604003c00c07500d403100c0350142507503070445840c141da42c0085040c0c3e50704007200078032461002d0403202ca810318510b21040c038088045410000741c1070015180ca0600c94510503422103036007840d407034000c40d1226156203000780940070340702d01006e1201d040004100709140c0484c2090440c4d030b0001c41c0c44100100f480840c99007241ea0302d079481c02d501600c01c50202062003030008601c9008140d45941e035960400080710010f11254107a0002d401440380200c41040c241c034a20355455804580303030403008400006602c02d80c4101108010341c01130110303000416a03004111941035031815107440382d04400c8200d9481c581c0b0049401c45d110b5015244041116520541c0301c0c1700c414012210500504082e4075031140307000b804030000800c4802600041000c4000d03981c100042800c200740104503000e150300c4042c0c1d54001030250901e030b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 864854451 1250 864853201 864853217
    0x61504230a090c0507020406240305090f12090108070206090606010c0809030a03021c03020918040f02090f071812031107050a0311040b06032503090b0108010903090f08030a 76
    0x941d44041980004081d030345010300c5141c1042d94010926007041e03500300c0c080c504000010400140083c414108002c0c070426078200c0425101c0b08030301500d0041e04500aa00403c012111140014442405910701da00d501c0c99032065828001000c21070000d0030a011500309005101c044100400c519801ca442403903d2003d807036a605103082c0c0f521490600c140e040c0300f11000b101c109600454008039080c810000d03181d2920b030304c0c8425802e03842042c0c1d5860b8022000d03100c03403a42100781c015858000d402020b40c2440328041d42e0110f00382c8001030340d00448842d00c01007040a00b80d840700c80190780740c00c0c2d20307050001c90b8588040d0210340d100c0c40f417004007480620042c44d00102c600300030440c0244001444901410390341c0c24040000c403401505180641d051010f086490f0a0050440380143d62240b014070420f800581d00001d0110f60300b503141e0170180c84040300c10120b0b0040300200d029040322800010700d91914a40980680155802030301c1440603240100440e180110580e90211003608007006 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 864855701 1250 864854451 864854519
    0x6011805060105090d030e01020d020f07050d150c09090e030a1704050f030301120506060604140d03020114150108090d050d0902060712050a020d14030126070806061504 74
    0x1804d002e040700940e0064210103031081815840030140d06030000a0b029070307400c401201000c030780751880f00402d1070055004040c100030718240880d040000e940180d01c0c1c103050301c07110741301e5406403070076020b5180004007024410f00051241d8450301c01c04814000c01035140c4000380601030a0202c5801c4a14006c0300d40000080c14028140058034480362840f094aa40350b8507082040032544052909840c50700c90400064207a04100c0115030a48048e0094070400080c02420052103c4007c0401c904554880d54480101ca205180c254007034003002800700c048130000000106120402402c03103c9541c400d8040d000d800d90458100c07000001c0c01640829079281a0000c42d56a2240e2400100303003150110340400e215901c0703000b5004280d6030b0f90986101d10051002200d0450505042c0c024208080004120414260496450003912840c180b030a004600c04003604024207680540e075250890b41c20001d452400c1001078210700c2c3e150070800e08090401200104492068004184400342605880 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 864856951 1250 864855701 864855707
    0x9060324090501110d06080609072d0f0e0c1c0c0e0d150509030f030a15080312100f0f0509040f0b090d080c1c0506010302132303060118050601 63
    0x1100701a0003000031312428180c0c031203018140c0d100342c482100180c0380020220b08181c001c20760794007d04ca0680106030f007074140ba20801e8160031118034040d4034618000c1040c0c2282c2d030b44a840c0010402500c109001501d00294199280d0008140343c1100c0c03400c0001e92807028807440400382d80d094560300052050111344045d2840c04484081b5544055044100001c101000901050020784c104080c003e640325042c2a40c0d6a0182d40c1e1300c1d031084101400020024a0154880d102da042710292445143d680d41412a00310703402030b6842c0c21800034103010070901c920040d60b201b004041814500e000303a031422500b42c100007802c0c092507116046200124040c0441c1c0424072030b00c0c80c0c10030840410341c1091441a079840d1b41c610910008100903500148641c041d00c2c0a030f50800c84070680744010070055685400050070003c0030903050607424000c402400d40c1c0b060400c0094014507030303c0900d1061703001004a9200055250382e00c681c1c404c50042c4403500700450055a44000400007103040d8980500503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 864858201 1250 864856951 864856961
    0x60c050c0a0b01150e100e030715122703080c07061104060f2618070801020408070504021e130b0f0301092f130b030c07050709060324 59
    0x103035007841100080c078188001e440c1854100c03080f1048200203031348254004e84034181803a0301950710003c20040c0a00e03040c021107181c031002c1001002d070307040701e40c07901c0d48440e104101050b014000f94078074a0807a840c0d51a0320030342806c140000308000c20f9949403c120180c02d040120020304010403000400c0700034605000b0f0703440642e4030020902c41c013030700542442461703005072080000203062045540987c0e40181000070f90300c002c0d41034034032102016100c2090803600107494511400200092290101e00c180300c6800940915000941c0d07480c07a004641d03152000580100d0320851040000c5a03080400000c6417121031550a480c0741ca600c080c840110b040c034003d52007104460380010f004072075002588015414ae45e42d011040100c00140400034011414103484844c4008940d442d180c20310001001501130b001c030790130b0071000c803d4403202c0b801940d80040e20946600000481d6402c02c1002c240304040242c28041c10401c03a852039500c1c1c0c03200c002c8802d00c0d075070319000d091508102c20f00d2580d004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 864859451 1250 864858201 864858217
    0x180f030a21050f0406050c0d0f0c12020f0a110102120c03040303210f061a07023313030201110d09050d020d08120106090506120c03060307050d0311060c0a0c060c05 72
    0xd02d5072113a6903140003a05607840704100030154025036140030821070140081038010800d55880e07904501c0643d9440841200004804c03044d4851001c821414000801c0305042c030310702c610b039420364945824001915241d0030300000c56a40a00344102400404000192412240c0500c0c1490101800c20341e44480e03c2034001540c1c80c05801d140300c4008554060f04445e00b2102648180301809210130b40c0034140e07025540c0c0c000d600800e2182d0f8a25000c41000b103030003800848124201c0156400310444410f64059049006000d040c08801c10a42da00b006c001d003000e802a0000d083c00344a103040040c104440c074003440d4400c40d00f59000200b9521002860340096522800d41551200c10041d0054000e200f449148002440504003040d541172860588100720260101d145203038846c0c4040a8030740e0402059150903111703078800094580c2e54019850002d5020b920b41d100f0b01c01c01c1042e55811b010340141144000241044034001280c0d0140f03146421a4001e400010880c000d240101c84500c60940 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 864860701 1250 864859451 864859477
    0xa0e12030618070825020a0b280522050312090c09071d0a06050702010e241e090904020f040f1d07051009050904060204030602180f030a2105 62
    0x10000300b0f68000d00818092100d0b400e140a41006400030400d491042a641c0c10050708441e00c0f50001a500005080d00310012001922140d044103a240c0c010078425102e01c3c01140e169014880d00750441742011801d8885107140c44c42070314180c2ca444c0d40d03912a101c1c181202c0301840001400c81081030120300020303007008094905a040200d4010710b120746071040c89100c00401003c1042c246455040030040700d00c00c0c1c0f11981030400940064803144002d052098110714a91905540f0340c144050758807036081c2c13010303026031591a04031550261a1107100c604078603d80406c07560b0f4440d500c02650f554001e504481d15804544036001090192109025883e501402d20401c071040509a0400e50207820210040f5612190384030104000341407030007600c002040519400b803106080a03030f0115403107802078038090b18040e941c0c0c0c3c62004990000c0085a05101007425104a51802c40c41e09080050200c005207900074650b02c4c1ca1400035040d4000a500641c0a00380380c905e280148143c802c00d2400c3c5e1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 864861951 1250 864860701 864860749
    0xd020d0c03020d0c020f0d0e030c1309121805040905010b0a090605030c0604180203061503070c02130c140a020a02090c040e0c040602030a12020c010f0e060a0e120306 73
    0x30314090065040040580621401d04180420061000540904041030300000300541111000700750707810b8a00802d01c1e034150054403100c40321030b00c441c1c9901c118600302c2c8400140450090a299034801250601c450130131805061669048480c41c10000541d0000ca6002030703902034519090340148820300c48140c00590145000441450300d61003071084074400d80548010320005010032520744154000d0804a115411181202941e1a40a1680100040c0288280da490166200055041280c0850024015000400841c10500e0100040141d2001d051204044864025058201c6203225144407400030808401c0d0380c0c400c0042071031040e00070380140780c5410011b802c02d9865001c1c3c06180e0340340014a01040c0d030b0303503000001c03a01151481da016604020311a07200316003940d0300d003a0054401303409100c2d0ba010a04203104042c0814202d003070010340c102885401605046005008034517a5182816030316503c0c40116814103051803050070540d50390380d0000000e036120501125000126040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 864863201 1250 864861951 864861971
    0x70c121803021903030206010506091e0109050a08030a0e010e0907080c040b04030302010b1516080d110f0702030c04060b0d0b1c05030c07080a020f0607170c010b01110c01140d020d 79
    0x45101c43c00b540e01960a4940c680c2c3c8660621240344121142503410078029000000450201c034903180505005141c8401c0300c565410008410b020b41d50000846c035000000e40302143c030382020340c082c203000003030810038a0402c0510010f80c540c40b008000000788800ca00001e01e0207000d0b001214080e00c50617a4490f03c990b280d050090007007040c5c07444a4003610491080719400b250020544641346810905c02d98a001c40f0350301c070800b980201090202a0b41c903410b40f4514041ca01015000340b079410024251101c9141c010985428046182c4a0003245031031001d11003000044103d0f1064041c00038046484400c0034082903a90009482154505101440e03030010048003000a0400c15842412180f01988820400751030328240ba000a6001005403001d000c9401c02401404034580100c00105404062115043d01c036448480035510595407400c0e1260250382200101c2c2d0f0092140008101340302084c800a0072810502d0759203203410f27402090300700c5c1000084d012220750500b051001d1140e1030070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 864864451 1250 864863201 864863239
    0x3020411040911041a0d2c150702061627030c090b010e0d05100903020607031a0915120109060209090109021206011107031a010806070c12180302 64
    0x2a010b40e080301810201e4069600c81803c041d1010b54100380c0a81d021540354000d04501c030341c03155207905c000d2604c440b1294048000c07100048414004a2012055072030000030060810304d031003001200d641130540c2480400e65001034070303075880305841a01000b00c0700410300030381e00c105200a03044000a00b4175080e0010f01d4140540c4e100b00d85c4200d8007410019141c807603440c20f07a0600b20003035000844044029610b40307040c1c441d030801c4901803000c1c1c03010084a46200000d070341402d4016005031713100d082804001c80e0b140c42012a284900b0011401081e0028001900c0303100c00350400d4042601040c0e000305a5441c0112211095000341c000c010002d1586050300280d0000d40c1c80a00c41e442c40000000d8a499038000c0711500038000001c41c0f226500d440c015502c460f00c510003d0f03060b200700040030000401030005400101e100143d105d0656240003200b9140403001000c500402010342180e00000700714210034691500c0d9400c06400401407e07010840805955001030360000b240444c1d0905040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 864865701 1250 864864451 864864457
    0x705060708091e0322030807150902030f0d0e0103020705061519060807021905100e01061502030304020f1005030c030c0d241a071403070f0507091a060301030311010603020411 77
    0x900198066100010501041200c0c41622004d40000808c0003044001760f007d2000d0440d00c8002600042c900344560003180c034140c050005156a0391020303074540e01c0d058000120f0306c080d003c2460150300e04030300c664440b0341ba03d401401e07182c00e2082c00d00c26140503680c0c070380c100080c4211044400f20034503a1244014035001094807040054001c10f00301034003014940100740340c0303d900403000f0041c4400a4501c1c82c01040a181019081d550324980440c1c01d05400f001880019100c5e0700442d1241414010000800c0c400002d96118000c6500703121426a04441a20b501c555410003c07034803580c404400501c0d503c5050200e210041c5010b00c1071118050215650310101001c1c5c24085100352281808041502440c40c5138401d41c0c5c00f03000b44e0300050042c40214544440749000d480c100000c598a030099092103840441c0c41d82c1000000340710001e902d219111405c50b00401d108040c01540c0041229440b06000c00380800c64132206005400e01c5c250007000040d0360103041008080c0d244041c484440d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 864866951 1250 864865701 864865717
    0xc0308102123030a051806131a0304121d03060703020a17090c0d0c1215241707030c032609060f03040201020a0506042004050108030a0305060a0b0310060806060705060708091e03 78
    0x40780b030201c10800109c0e048150b91180e0781c00355030b51040c68122002546c0c00d1030090310303000402c42c501c4814039281c1c60a01c5854054030454601603142c11400102401801c03080c4c0c0350340318500c002c404200341200005109a130111003901d002c10100c201d4100448504070300d07040480f40620000402040086514081806d0f2001c581c04000c0c103620500e520f1054100c40136982d103080c0271008184040b25103c412a901f07000c007603040301c031004d5a9581d5058089001e600503554850000b503281d07a528941601030300c40b18000c401682c0341c0003403040020040e0240300c0da05940044048002002c590080080d00825604074040b190300703180910b0b0051066600c480e241100c03140c3c00c00301204508060044030b05aa81200246051481c40f400032001444004c20b05540103000030400030b51800715800460140c9018a02c00d000c8504004018003940c501178160f900800081001101044002c64101c0d0000114a0038074556224a41c889144c100002c07480a03101807450007104901d407002001701050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 864868201 1250 864866951 864866969
    0x120e060402181003030e01120e300a050702040f0218011b02090402060d1806061d06130c02010b1801030b01050d030c0308102123030a05180613 63
    0x1001182c0741d5520042010756580450101c4000c040c00001d001e01c5100000765070600d04030744501c5000303d18900340e4030406800c0c0c800750019203902e40c80514101164052240080b440d140440034161101c12074411241e02070300308140861440115980c0c2c0e040301002c25800301003551540303001c0d03941c450001058480305000c180164001004180c8102c024601c40d500240808020707940c41e001d0081c29484403a00c03881e0a55207a62016090340d01c9141034007018094032000400c0340c240b054810b0b000c160303031401040c1d0104c0d080403c1081c5c0d8400d503083d25241e071030010104030741c1180340003079002d44529034510b6441811400e0555241c04403240ca00d040700c1c010344103e0741c00d0f613881052041d018008403005e00018041940100030070f000e2400a500301044c5e80304225416a5891200e442d4446965040302c9500741c2042d0906025040b15075020090b031800300680c0100c080e40242c0d0340e900c134034250035003031000c0411051401b00c0803200610040c2c002410042d901d01c50361002e076150140074004c1c4101c1c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 864869451 1250 864868201 864868219
    0x102030f091609050901090b0112051b0d060905120a05180406030f1e0c0906170726031b0a0203060703110d0506060c1e0712020907050a120e060402 65
    0x40c0140005141c6a40c0c078070a602c001030035041421600140078000d1100e01590f40741d0345c208002602155442d070007814140180c4910a05a00d481c80c103006617600f044541d060036082c8000c41c0e035556800140f0b481d62014001602c04e420b03240090900a90842541c4c0d64140410f400010b0342c1c0103002003503c0091480108422801e184c1000212a660300014210407044007000d000961500042c01010f000c20b640d2403c011110368860104071002e41003403240e141c0360b4a0400642040c0d103003920000d03c0d02305c080c002013402c0070000c0c41d80781140641c140c1d50701030078202a0794078031007882252070581019001c4101103000070990750342c0d0452440128041c0c4260800035041078402d1048407843c0080b008154580840301c43c0f94005458043d003010b900070030400a41c0440501008600300c00303103a00c41c0c1340e15a4031100302605c5c200285588030030152a40030f01e108005076a180100c81e80080c407800d20740d44030f4064070000c407410443c0300408a02c076450440c0e0b4050000000601d035225a20807200f41503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 864870701 1250 864869451 864869461
    0x61026270607030608030301080d0c0c0b040909062a031a090406021306020a0f0803060105040509041101090b0a122406030e0606120c010e011103180f0108071407230102030f 76
    0x21b6644000d01c2005950740100c0c1010b030129220b8100c5191090240b0482c0c448180c54096048036603001d035020440d41030381ea402c04e80030400390b0301480714942c10540c8480052220004540103d20400116400f0940d5400700e0640c0110742c0800070f2507a1314003810103030240c0340c50f19001e00254005111111701000020000410714800160109465400030540442c40420707901d58402e030300050041c03818048184400700c4c068543c80c3d0154401c41c010302e01c0c01201e1690b0400034000e40c80c190052402400c0401241d01c84640125034185034400c04440000c08880c001008403406480e410b030441c11160503400080d29030b905802100c031140075042550015100c450411400c640075004c00c06041d00b081c2e4241e000c56020700443c80880106043c5600c401e403094141c075056030302189084c07011b820b4810f5010480c1c1043c0d58440c420840070700700300d070140c1013035400500300d084038451000a0f10320003d101801c1090003020f0007100c00011070541082000030705224040d4104450030804580c00c00c000036 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 864871951 1250 864870701 864870703
    0x70b061c140610080304031719081902180d051903080a050f07171f120302010605032811040c0809210d0914070608061026270607030608 60
    0x4400c803003e81d0000c0d0300d4645160f03038804011a0080323981d80801c0042c071207411099420880c1c1303070190500d0340d14100d0626003004034078603040094900350304a5105000b940d4016080880030700040a04449482301c110f0286019071034049240b41e402c1c4103024030313042801016003040e20140a168010b40503c001d540c1d09600705e640300011a0a8000100201d19100201d40800130403900500300700d601e18114900385c0004081045158003c2882d0303024003e418060590a01c01c1d41c020300421400381104e4806908104505070f003c405041c51080302d034890108102902c03a2083e081c21001c1c0060102c40c1128002800c000320031150508507000304058640e02400003c00001c05e131b044c240c00c96040ca031400c01890000c000d0803604941121240303241601c603850030071142004104c0303035890401c0c030300e42a01070240402c4103001d101e040c1715000c0b5042e041058030f0414014841100300c0f0450b0507542c1d01d605001d0250414803502c0038020f00b107030f40c01e002170004142544100c2c00d5850912480e65640c2802e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 864873201 1250 864871951 864871981
    0x70305060f01030c1209030908010b0102030310151e08010905060906010f080a020f070f02180c0732060f07021204090504050c09070206070914010203070b061c1406 72
    0x841e034850100d2204001640c0a580046413003c1d607031400844480351807140308201d40407030703c080d404100001c0c4c080040403000d0091080d07081c0b00f80301560139414114403048800005000340d002d0b4940e50b4544003201ca2152100115032144480c1c9012030021849010b0842c580a000390f025450030240000c0c01428103d510030b00411040c2c0d03070170200006140f030484079000c003d000c3e218010f408101da40b2482c203009010340b41d20760041c14003402c000310b1841000180d8800c1c240c03040040d1070f070004006c3d58441d0303041030780e8485802590001c0440c2d107241401c000d81105280140070303d03100c0c898945000800082440c403d82030030b402100f80b600e811a003669038a0310852891040b00e001c20090060710031a405c9980c202e44a40100c8482101c03034400138080e100200c5400f401a809401044000d80d03100f240100103000e031228070010b420034040000c2d100d100d035071030140050783c1080114400d911390701c0c13281142c40702c000b114281405062a200e0107041103802d200d0030520074500070038044a000040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 864874451 1250 864873201 864873211
    0x1002040b09010305060f0a0b1b01050601140904060504061e0509061c0c0503012f040302061218070b0904050915130c080303010608011d0f15030f24070305 68
    0xe81030400c06040011405007034002c02d09900001001542d84903900e503401f42e030000d0100c0340070715600d0b181800ba030000e04404050300c00c04c20740c0c1014180a4503903003003080ca1500300c10751a00180d41701e1031310000c1005414103170f03c403a41207440c00100007004030a215518040c403880b0840010030581d17900421084030380a44103650f024942000c0356100c03d04581030f51104500c00d151041ca510b035114002421100c1003055200d03a091285510403596441803000d038103500e104840c080c20242160041403041c06801c08180e02c210042e400703d4655180a03265031180303004541200c1e4290b490301035640c104c2c1c1054034900c0c002d0b81014046070321520b01040011108110078410f1800b650b9804044560306c1900d0001d0703030303164010741c07010038086401e100441c041c10258442e008554903014000d0711030560b030076805003240806414080791000040c480c940041d4040c04200070f1400e000c0c0044d0401c40d6143c170480c8030348551000403040c2684502000c01141400e0541d07082999590b1043e410b8a4080714 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 864875701 1250 864874451 864874469
    0x160620010902090a0b150c06090601061b170c01060f15170a05040218310302061f0b0d09020a0518040b0c09030d021e0705030c120a020a0b0408100204 66
    0x400103081d410035901041c80d00c4e40040003545001b2150380c80f09003030f902082c04040380b03030890b8042000c0458108011401480700d864106d0201401d00c04400c5a0042101d004200c0b81c01c00220301c0607001820f00b134981d0304034981e00800800d903541003e01200e650030700c2010380340d060008810349528040e0720a003128083c000b184420355034500c20403100906008004a83c45464541140d2216400c54011072207501d400d8030400c0f80030440210700d406010b450700a180103601199803803000a42c046807268014a0380058507081e003081a480c0000341c2d42e0340d00060b11401d070101d0f0018003003425400c40388402c0e00988402700b0300f0b600c03203041c0814404580f482c040850b9080011500103003101003c6903201d8024450242040aaa13000a003400c6185407a08010380c48040320441c0310204004050070022150000c000c0c5a14280c0480c0d2030707081c00700300b141c810b00001500d00002c5105110101c05140e0040c03c07003a01c0e83d1184a0411560014080c1c030300c5602c610351002c2d035103212920884068900c240 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 864876951 1250 864875701 864875719
    0x30614010c031b05070308040b0403021509011707050f0703030b04050c0405010215060414240a120305071403120403030c021603020913020312070302010f0501030201140c160620010902 81
    0xa40c0d620380d100400c840803941071050705c000001185908000e040540a5203100640d541d185004011100301180c1c541c260f5000e0810021134540e0300b0049a14031101070720100714040d81c0c0d915050f1428020400c7c040e0314280d001840f0020142d25600c869000d141c1100c0410842c2c85040b100101401580101030140c0c0c0006915082c140c1d84c3c4054a602200080001c42e04a0044180c008010002e41d08d00091050f00c074071403103509000368400c1c803181c2c0c8284e442d110705030300c2c0c4180000506415100a014840005803100a010043c80200302440d43c9200700c980e110b02c8e00c00d003800004012a016400240752a82c2006d050344081044074510103c2e42c0241a80c504540030000d481401401030400d101c000a6041e0050714144004019812145081c0d5200c1e10103040184c00d450100b00100700ba50f15050050005070703081f01c030148400714004001ca848080402401d45080c00100341d41e42420501d503000034109a00c280da07030107480d083c8442d6481003408481218243c400284009500003605 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 864878201 1250 864876951 864876977
    0x309120a170d09060c081608090c1c0803040c030b0a06030809040f0902030715120b030d1407240f0b0307050105130302060301172b0518060307030614010c03 69
    0x280015052100706081d000031844038070744c1c40c8421100300c0d074142000318144a0821604184036016200050300a080240e102e00e010007c064981d0342c0d859050344076000ca61f04c4d03520658408180317550410381c0440e401e6502d040504041c41000d02903c0100c0300e0001000000b0780d040354502850040300c1d0300001c55410031020704100405403803003c8609211607605c3c0d11034030240c1d03006c0240e6001824000e80e0092414002600105901c41e12000000c005080c104510542d80307001484c8440d411143ca0310010200184081c1583d912038400d0180c00050154403207080c003020340709124085110f0303110802060700d034600100c1c16240440b0703101b40e06800c513440820207035004200030010b00100310401209181c40b9400034003190401c1e0400065008100d601814504003045800c03400c02d040345030800680403081200422034103400100040100228a2181c0c0208205c210008080e004113055200d250144e001001001c0c5846011120390405920400302e50280c103141d00700503010b603a010002103030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 864879451 1250 864878201 864878243
    0x60e09150624030712050601030905120306060c0708070e160e0d020a090c020a0213140a0b0604051e0102061b04030f110306010305030a03150b090f210309120a 70
    0x782111214400481c40c10118007010b0001180f02d5205030311042c0d074440c0240d01c1c02d02200e000800290625191680d103074041000000c5400810303131510706075a9640c0c1c558000c80c800380112480b100b464442c1703440c04a100b41010404505640020b40c02c94119524031010540344a011002400800d003d00382000b01820305401c4034100d00d0000e010002200e036142c20b60320440b480e41c1c07811401070700142c081c4000c6160400900f180200c0d000c1042c85400b035a80307885d0361102c0e00170f08207440103036a0b000180e1103602d84509480040c4801021802150190440010858140c001060060041c0c50000d40e260303c0c42005100700c240003420003402d00f411582c9015005244180644030055401014403581c4d4007080221b000c0c501c61009580c40d5903490401800341c400c80341030032035036150ac3d80090111100c1e480035681c070741400f20745038890021030b000030500000e26054904155401c01d4000d00d02400000f000740008241524400c2d50307410540f00e5607849601001c001440403e258280000100c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 864880701 1250 864879451 864879469
    0x31d0a0f06031d06072d050301050d030c0204090b04231c110105090a1209060e040906090f031107140f0d02190e10060c11060f04051201060e091506 65
    0x1a550f90f00700d81d082d0514103070b82d1900310115a1100040c80d00340b142c00c412000d032500c4014410b0a05610b01c1c803603000d160050b100c0d01050003818025080304c031828042c5880381882424440d0007410802651015041489012130115010f50b811411050034001210745032110f404900b0000c00a8205200c2624041280b1644801c2003030400000802003040010b080c46050f0156203000d0080c600304c0558502a0714080c400003d0509001300d000c010010648c101c01907103041501110001102400e51030118010032000c2c00141401400809400826070054038070704801b0740c0003007101e940d40e03590704041507258403040c2c8084c3c100c20400001300d00d509024034406500381c802440903203401340d51445c94840d120305a2015425050720420b100001442c441003002500c81440c107034800504540b60040ca128118030701c01e0080310002840c030319407001c203000c7d02d01071304006046500c2c6070040c4940a010306010300605440400d5940420040d40001441040d10441c80c410399109039200400c00c40081c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 864881951 1250 864880701 864880721
    0x9130201210e030409060501030c0810270509070501120b01170c1b030304030e0d020918070503100e06010603140f15090f0a3e0f07031d0a0f0603 64
    0x203854200c00c001042c07040c4041c101030210880700243c12031402d0001415203207001d01c0207041c0043d0006020702c034400881d1507015180c7d0042d13035030558040a0035070001c47c142445500c4000c0c0c038000501c041b5070008180300c421180242c4c0d030103500b10451003625003150031011580307002c90a01003501c1e100301112101c1540c4041031131030181c10041d0b03a0002c0895001d0030642c1c0100380d0070020411041640055601c10302c190161040d484508041e40419965180500440c40b840c00503142070343c40070800c0115402403c0098240c40b804600101140082c00480a006525000340000030a04503c2032103406440c00032043c5059179030315680d84030700440b200503050b01e000c101c0501c41034119031222860b082c0a0903000c01580003d2400001c814101c03243d00d001d040005107911624204000352040038110302d815824071410340707101c0304130084071407041c007004d03e04081c4003240344410325803c000ea01e04c0301280c1040114220140204100c4d040c46a03003d00140d510042e61f080c0400c62003540514010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 864883201 1250 864881951 864882017
    0x9090203070905010e0117030406051b102408030909011505071a06090f040201020309101106090312100f0b0c01091a0a0c031a2202040602010b09130201 67
    0x8580302d00c054070545a090304001a1111910010010045c4d000100940b0f406008051802d090510b24020b155100d808205003228a1401051070000014408110f00c00d0078513108002c403840d483c00c8080d20744103520040010b00b6241c030000603040000700840b00350241c000d1154070780f46c0c2400811034490300c60140107010008140600070000344503000d018410705450300a98224a01300c000c00a04a400604c000c0b0301040400c2440b006036000002e2718460764041741c0985010401620450310700c9182d990410b040e200c1c02d41480003069002c0010951000b050b0022084d90b40d0328401d039550300035648501015140c600304200030815600d0080c1c868102c0c1100041440e10507a1074141d03031112080d1307101552025500600404128074412881d882e4020709060018200c0705c80003010100c4014805406581448080b0b400e20300c01d0700040301d81c0104018119245c42e1541c4000f402070021030142d40c0650140400300f900c050400302d040507080c0d4140d4464501091002c4000703075114008c600b00c030709 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 864884451 1250 864883201 864883213
    0xc0a020a080d0603110303090a0e0a0905072619030c030e0603190b010905130f2c01060f180f112b09120c081c050601021204060909090203 61
    0x50a410041000ba016418042a040d00714200307680e0001822204600c05c1c0d03c00c2010b40c5168451600070f0301200c0910102d01d40700e46e10151040b01812101c80010700314080d0800c0494480701c0c0a4880c4840d40d1500d083c00c060086440310256a84d00140710100562b100c0074060f00040e10841aa0b20294840c0c544020789034055408604607401c19a4401039840302a21240000201b42c070490200c51800d10b400f80241e8504004103500f04e0351040410011622507084581601c8150006044c41246550710f110441444540d0302d407894810403004055401c2c5180041c3c0390102c40103107000d031000500c2914214540c00780f01002000ca48209a82c46c50320340d00f11401e20071a003400760400188031103510840d00c030040400450382c500d0b810b030303800003526001c4440089982e10000d25102e0080d07040030030584403281001c140601031a2241180301520790048001c0d07001c2900b0240c080c1380c00303070200c4104683c640c1d50986e503401140280d00005040c03580421910782203412108140340080d041e12a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 864885701 1250 864884451 864884453
    0x12360203010f09051e03041404020708090a0612140f060108070e120d1205070c1403090a0906060e040507081b0f0a0206090f010905150c090d05060a0e0a05060c0a020a 73
    0x580f4030780d150550ba80d4008800100124840220400e128000c40340598036150400b9265070b00c11342c12095203405903a000c68070504022004089581f0404000c0c008440d850b0f031024010b006403810b5040c402082d04002401694070204c0400d1800340d150400c0d00780141c3e40c1d0364011100c0c031b54000e00010400030403201e086810f40b5402c02c00d00c550b2a9040140c204c00c012004050909070301c102c5c8000c10701d89050200b00d0441d50160b140d03400310b036000d81c8000543d0300d8801c406140d80501c0d100a54884c2540c40300040c00b2440e58001c2d4102d4426460303210b17408805000300012541c0484609000c00c84000000d00003a50120b4500ba1101410b0216030500e6904203640801d500b0104112000d03900550500110600804c40d401e00d445101000b401400000d80e14142c981e80e088000180c40c1002c0e401242840010030151100c05102500001c44441d040c10181c5d0354138419901480220302e040361010403440013144c4040d900350800010300107601e80401144c01c940c0810750001c00c501070001070340 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 864886951 1250 864885701 864885731
    0x70c020f0d06020904061d06102706080a02130306020310090f0603210f0807031b02010b19030b011203050c0d09030b0a1b11010b03030a1236020301 65
    0x40007502810006880d010040180411a01d0942000b143c0443c0d14128001600035100504ea01600603245082c5100c03e1407020350764140c1039040190800301d2405046500c0466a540760121045690303000520b032204007500c8100d1107a038900303409220b03d203007040c0003042c602d4000315003000ca881d0300041c002d59202689000c03075166010710000180c0303828081043c819201501002491f070031101008040100381c0141030500c040f040039080c080200006007103180130343c7c00000d060111060542c51203000010080c020b2071201c3e955846005070408901060a140c1603180607240e005240c00c1c01c0ea424488210161102420120100241000624101c01c030600900c2c56104554030740180c10750031444d012450b0a0010045031040d4613100d848424888419170307480302412030303040c0203099180d07101065002d4420b11030f20a03014480011007062050740046031300e2210005000400002c245601803044c51443d020b0845030410213011180800c007009075841942a100500008086840c0c0d0110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 864888201 1250 864886951 864886969
    0x150311180d170f041d010819050a140a05120901021f060f03050d080106030c0e040b0d050102180a090c0c0215130b1801020a0c060e030a080301080604021f08070c020f 73
    0x10030f07000034004c40d00b00507401c01d001c1c180c01d030b9a184090707000542d810310550030b41d01c8400365410204020a0480d0006218050066210719900450f40c160162000d0040c41e596011388202100d40b407084500d40011154000195a05218145d0261503500d00704000002403001c07a10b88804015607130f1000044413a4100d00140003103129034040e1861342d00c1c4801c080d1240ca01680300009243c00c00000351030b0b4503802881000f000c002140e0028902024601241c41c190b03c0400080140d071000030700c076074105100c3e0700b00030284c10125158000240c0380c0c1203100035500c441030b0210100e0070b010402d100500e03042980424401d4004030960511034600840e01c040d07080c83c0e1011700c1c0b00e04000340d42c03500d407c45100a142284400c0c0020854200b4075501e60340e18984038030500081003513a1507400d070117503024000ea0701650307008481e454482d616211110b407540000c0d90700b2841034a0001010440346d8117a10700c03681d0450300b500c3e1800142d488410954800310180c01c00c80e0f000304101e4001c40c036a9144603103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 864889451 1250 864888201 864888217
    0x11e080303011517220f02041d070501322203020a1712180a230901080c060307030b060c06010603050a091e0c080601150311180d17 58
    0x9503240d4105010f0003901c00c1c55000a00c0384065100400c01c2500300c0c6100c01400c0902070741080715100b03152410052000380d10404000c0d8464101458606a5108269100e00c501d1444054400b0941d44600540700c204002002402c10f118640c201c41d41c002481e94030307801903222001d04525000c1500c0310000400c080200000904480000030300540c10807840b503001a005c00307107080c02c041540258040d6500409861203a0198000500d00c0c102094000d0851058a0290001440644644a00d4151074042c041401100c01c0103000000510340369021038101c2e0100c501503c4061102c00034440b044d400180004249910b0b600c546440784c80c2d54000f402c0884940300900859414250001c0a65402514440301a4145440704012a1a0070301100340008140c0003c10780c600d4034980705031071400c07561210440e8014403000046c161104250044000e540e0b90b01080704804e82040c03030007603008201050302c915440b404000a607042003124081303000e0050005845448034001125416406046 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 864890701 1250 864889451 864889469
    0x504061d07061407020d02040f0209060d021b121605070302091e09280f080c0f0609070e0f090106031b05030c030c01050901081509010b03150a030308011e08030301 72
    0x101000416403052583c83c01c03801d100c0c04a4540000c5070006000311710024400307449182d9440780c1228419a03541151400f1102070100e41d1189d041c16440b8000b500000c054509440c0c1c054400012544049440321400b440107070500d05112a80e040c140d0b003038803900002c49131485140c1c40400035aa800407140e00c6040c4561044410002c8021044003841024115194035400030091060125091200464444443d40010603500603810101c280240481c0060143c1100040f07400603444042000e4019002090466919490340c014650307076003c40b80300300b0403900d090301c2c00316003482180000701c5e41000402002090007a05e075210b00b0b1119004403401001980d003554200b1450a00780888001003c0480250032940c02074000a400ea104298000e410054014002156103c2130000c1182c003840162070701001d580c54020403107007940140d4540c1544040544020100d280c01e607507940135a58950f40f200c005900e000341040c4410b03290405640340b02d0300b00d200499940d004001450080a00c00e0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 864891951 1250 864890701 864890713
    0x72106092906340b0f0a0b0f01091503110703180e10050906063c1e0a0512040c1818080901020a0605040c05040e06090304050d060615030e0105060f130504061d 70
    0x35100d07000300c1c0c200c103040f24001c231b201048500c0d0607a00144103c0807619012080032034242070301e034118001c0c2801c120981c028180850000107256121041d0407a200c0d41c404244d021641f01d0350713002c0800740e0171150709072a9aa4140107104070306004502e1500040060052400c1c102036180f610690720440c3d51082c0c08000001c05443e0402105215005040141807514608074a61800e40c0c0b40d03032460320340c0c0e000110000842000c114490812958200d00d55072048040d03003043e03e00207200c8802803040c840c4010303180c081072040c1802032060b0380b506004094002103650b49a552031310b41e031b08105030302c5066014256010010468034040c0038840c80c400d0007400101c0c5d01b814208001c9400a840c1459542d100700104031403440d0000c100c03000da0b07200304c4116030818200e281c040050503040c4c10024640c50100c1000a45942580000014000c008028080d982e40c90303050105610b07142c01e16940c415500d4280700c5203142958460b5411a000e1800454001820045801c5600d00443d40c411558081 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 864893201 1250 864891951 864891961
    0x5090c0f040e030d0506030712060e0715082e08010203091b01170a020f0c0c03010c030b10080406020d060e070305010608072106092906340b0f 63
    0x1600045408003801c54040100035406952107a403401884484400260f60700081209558101301840090103002d8a000c0c940590b03280203005488184240794152113043c001154003240c0300f448800b4075629079611000750380d0310040c901c0b0b81004101c8200150845404643c0c41142d89003842d0043c003004000940e0368200080901d00d00000c05a038518080702c40d5400d5000b80c0c0e4455940162643c0c3c1001003007241d140d00d900e440003442084042c00f890f000000300c00200c110042150701ca414001c130000c001c031452a5038254252041407406503031141365150400c01c460b00414440d600940213803401030415824481d41e1048652075008120880c504208110300980c0c107009050144c0301034a820740c0705080c12840a0481c00c00303125518121a00d6881c10007004203150701501c01025000030034000184421024201d03888070b804403d20700110907101010a007812811102c0720b07100500109c80c0200300140d06103d04244640c00d6503a8079880c4252004a42940d455030300400c107004402c03c450031300c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 864894451 1250 864893201 864893209
    0x171815041a090906090901020c0105182122050d03051309090507060c1a010b040612050105090411190f050406060e1f0908061f120507030303110d05090c 67
    0x341090007045440200180348103a181d03801400d4216a082e01c0c00d11803510784004881c06801046413101d2603610304401c128000c202d0303000046100b0380703040944001e900c69130a05207841300e8040356144003460800440c14a044516000719001c050340c035800c1d036055221170000f10313200d0f655001900040e5012522000c3d0f40c044968002c01001d00a400b00100c2c3c1440d42d07020340f28440351141c01c0510265030340304c2c014841005011006055010f80302c3c105580c4891440c00c080d0400d01403030001950581024600103201d20a0b20305a81c0d000b408241640d840c2e0740c0310440e1030079840d445a0428400e0f2006081203402121346000f0704084080070328014100818802202c465a204604009030751880c880c03291604441c00d40b4030b82918410000f106024042580c070ba40f200e522a007005d104042c200b005416600c445e03812501c05401d0010103e554900300246000c9000701d002d4102e4101d0442040020700079480764808140382e80c203641c01c0050903607a03501140c02c00c85041e0020740010350803024610f4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 864895701 1250 864894451 864894479
    0x2b0803041b17192102071a07050a0f170f0a0e010507080d0e070f060507020a0806090d03020c120d0c0e010201050727090c11071217181504 61
    0x24401ca03420145251850b0a607501e40c2d51070700f40410f051009694000707005808100c0759034a0050310b1441c0c2e0050700c0e0031000b555104a171140d090448810600d400d078600d080003c440c13195401500504080e103c07619282300c40081040112a2960b40b58a02daa0003454400138080503000c1c12845a00c40c8080c20002c2c100151204134503040003c03c004c1c42000405c00020b41d0100d41c864080020540c01c0f01010500d0006180c03c26200c42c55001d1001880d035074088020b012170f034030944001003010355695904e581c42e64281c9081ca0f40381c000c00c103003c4180744030340c0c0588161001a0111490300410710340424066014416003901e0648a01150b006103400404003841c007030083c402045186001c500c0200080300c0310728500084030408102c0818081d00d0705929000e81901c0d0bd04200011070402d001e440740720302e0740d0001c0c164000c9040c00900c00c2070011032642415000300208418001020b40b03010300768010303000c50102501c003000c20107040d214420380504184c0300c04823299907181003014007480c800e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 864896951 1250 864895701 864895709
    0x6140106082505030a060305102c030f0d0b10080612060105101107090f050f0106090602120325050d0608060c090919090812070804022b0803041b 64
    0xe604407103810b501490041d14030180d0201c920700315880c0e45445080d40041c1c990b81d071001e0000d11800c00c624406200740d81c020300f11218031140c41c5c8200c00100c44082c820481052003114107400c1031028841890350300000780707048010160b0000d0040410b0002030811100c00003c140003441c1d290420560f030415642c0c14800c8281d150080200f0f614000014903070fa08001108420080300030401d0703072100410030501003d0815010240615410402d080005001c00c4610071204912540001141801074034a642612101c2c0d0140c065110380041d056030a6002403d0700ba580d40030407801000c010001215884c10030f20b181d030740558480450f07924030b040d6003183c1c200300021b421050500c009170324200b08441050409880c1199a039640c092408051400500b000c112181489094420401c412008040c1502442d0405199441d00401110000411100250810300340c80b090b61850703500740310290803016000340c07110643c0d280c1d40e1020f0a0b50810784044451000c6071030425000c848030704030403000d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 864898201 1250 864896951 864896971
    0x80a08120703090f080d0e06010902090a0b0301030c03030e1818060a0614040509010e07090207060507090b09042703120b010e101409150a030b1e1c0614010608 70
    0x202d1071540b00c403034a0070f0030803400034030171640050f00c0a42513110360040710a91b20408147e0b035056079104021300196000c034440368450184010301066403500030041d03034140c3c2d030002c10140c08141565025605080e0f003450166000d40400ca080b110314810510640c030584403041a030001c41c10300801a403038800c02412602425040804c140700081002281056619084038045101e44918031010300601030f10260010500440340041042d04094001b0308445114444c200802d03901c00000b1207410103503000f6418510f5041024601d50325040e00407030003410b9282462980c1d40766210580b465230740c0c1d00001b2404900b1440050469142c0c61252142185080c200429111540c40010300340140d40ba0091040c403809820104d000d0703661405440ea480e0001e4170742010b1002c25882d039102d0350003012507480003a0811400b0155402e0a45088102202e1030a503482c0000c0e00c6410050010090314000701040c95400ba500080780c0140902d5510ba4055440312102c0d50600d2002080e01000401d05046 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 864899451 1250 864898201 864898211
    0x5100b0322150629161e0b0901060605070602071103061905010e130f0311060c041401021204090903030f0501090e0f0d05030103031412040b060109080f19020109080a08120703 77
    0x1080d80d16021410542c5460300d155555031850a9082d0503150b2048406000c0d102039030502c0750702c00315102102e080c0600402c216061a0b588c1e0b41010300b6540680604c0d8002341303050000400007003250300541155071180d03605034903035851440421f140c102c0c00c032540310001289000b503000841c02d1303210303450142004400e4080c2c5441e00082d07d0500d00c241e0000103000301d9450b80c500043c903200d0700a500c0911010420390300305040c17181c500300e44e0750414095490140f085403482e04035076000041035544452180340d61800c0510b0701051200503d4440400d81c01c1c075031500c0d4100078480d01442010b000c0c00b9828800503442d10340705401d43c50440707100c1c1c2e24a0303d644883c96200c003440c2c100741902c0c116941741c41c00510b40c0c0550302d0021914050039840304542000c0006020400001001c07a0340300d4902a83c6801c004c994800b09942c0d1600440700d84011a001262408a201c00c032040050a0a006040518806035240000d625025030902c0c10750307001402240c00e040740c0304000c05040e0003600b50304d01404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 864900701 1250 864899451 864899489
    0x120912020304170705060414030313030b04030809190201050309010f0510140603011406090114070606080d0203130b0a020705030307030f09050405061320040806010302031005100b03221506 83
    0x390900c11f501840c480803880045030760007a50f04100b10341c3c1d0110f901d602190310a50300e10341100c00c1030b025282107000c41c4c1501c000804401001803d41d00304bc0840210601559054006490782d900c0600010341c255202ca00b0000030040c940103940c0242510754407030750040d01d0506c40c440360201d008101e42c4190340810040200f80960319205448080880f480c40d40e8a11b2140107079268200c07035000141a840c0400c400b801e1001c0d1758800003c84503003100381c4145113010a401c0b0380300d00c208102140a032084000c140b100694a60141c8007504080c0101e805d025251070000f85142c00c03600b01100003440f0034210140e02948464070740020441607a0a01480c00d03e1000603440c0b61b1200030000303609a480d40548400c1026a00103840d81c14843d040c80e0361592152141501d0341c4090106a02911030102800f81c034007554030401d0310400c1520200c461540c113013034403059130b1b074009410102c0000164240350280384403c481e841c200c5225040c8a08000704e500c51000a950b659072003a07034401012a0505 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 864901951 1250 864900701 864900709
    0x339030e0d112107050708030405010516060b120601060905300a0c17120f03130305041a03070323150a0909121701060e01120912020304170705 63
    0x28880403080e04001003041c250441c1035281000e00003600301e60624051645844030200c5004203184c501500c1643c4140e0384924000c2c1da02d10440c03040c82d000900402552813250803008405c218244100d40c003040c280a80000a201c03200b18503102d21154121000400c02550000c0380f400017000165146c106120070f195143c03d03480440025000c04410250801e20812803d1040c1019140d001c64a030081b103484a00c4080e445940507448182e0381b10700c9144e0418480c0c4517040d92402c0c01100bd100b40b4660b42e1140300035034541c420000b10140f00d130a010103d4064020441d1001ca003000096094a0b8603040b0401000e907a040002a4644205821031142c82890502c88a41c4280ba1601d5018075a00a101140da540d02c180c1c0100c140f503203003603075140821030380391003424100708169101101c2e10350410341c1480c14142031040ca000324800410541c00d65004111152030405003110000742e03000c2c01d449032005e4110b000c03903810040e0800901408814a030000c1c0000300c0b0540e00060154030304040c042 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 864903201 1250 864901951 864901963
    0xb010207080a020a0e0711060405071802030103020d0f02131b09060e032503060f0516110606011b0602130315020c03041e180b0405010518070309030339030e 69
    0x11104104855000030300d1a40205d80c920391047c104411100607180900782540c6942c918061342c50040a011008a1902d04a0082e01e050b641c00605018501c16680d445041c07240d042402243c100d240c0300707226401d2010511450540080c0d48040108014a210b4010400071480e0000010300920203141c0d11103440c0059030b000041c0800c184204002c440d4403444032041c4643d0310081c162400d1203030810020a05820003402600915890708400f00e0207042038540c0c01c13065160310116882240080d846612400641d408010b00301c14072940174165460307641c180e84c400341c0503400e0700794813000800810101c0c003585584400f094504604290641072143c0c0c81c5d2060340b01c0c4170039200d450081c1c0032003421044400e8000b4412404c00f5041c01142d440071001030700d40c0c018164880c92601d4000035483c00c00c5010100b64845040c01c0c032002c2e546250741030b001810450401e40c10150342c4c0c5041030030080c10110301e06504483c824410100c480307403910700541e144140b80c050101405c142c6e171030400e55000615 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 864904451 1250 864903201 864903209
    0x315012301080915060f100201060807290d2a0e10050d090512030712050604090305030601180b18130603110607030c080f0d0c030b03190606090f0b010207080a020a 72
    0x1032480710b40c440c44001403510001c88481d50740281f03c15a40120305805511400403505090240e901d81c0f5510000d1421540c07000072428048803007940030840d80060440100b03201d0300d801d100080c0001d00c01d0040c00c08100b41928802c0f240a42031411407481d0b0b040203031400c6a000448540c4841f80800c0b00080c85401107008992810340c903810140100f00061110300c1c9c0c82201403035150703200d151109004040d05508040d141c009407402004c5a1241080c2c050702d00d10036015118185182c4485004490034041d1089042915148081c08515202184002c2c0a110000d407601c00c5400c50b440108416804150610685603141440404c0003c440800303000202e0022030301d060b1255502c1c10284d0b609650008028844d202c00035044081985580181c48916076031102002107415030881542100c604400c50f6605a101c102c0c800002c9044030a2003182d00d10590010403007507981c1d400b0348183c410108407400c000d512103144c00c0700340d68100312040c010241e14005002002d25900400c1c1d01c4203450003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 864905701 1250 864904451 864904483
    0x70906080a111602040b27090a02060a0f02031317010b24030402150a0306030b01060c0b061c0204020720060a08130204060305160905090d051803150123010809 70
    0x10101c0c013550364941c0080b0040402401c81305046800d0030708003241001b8040c21400f82c8000303202044207448001744614000ba80541103034640684005e007603c903102d51980d07441c00c520040084c500075803000516400106020b17151102610300c000615800c1d6110100900e0240e9401c00288041040ba2080c910800d12140000d59403a20341d070011410141541ca40d0b800c0c2d11200050400c4010340c141e0110703003180c4c001c6000404598880f1030171652003c0490001e807501a40b030000c983da85c07601c00384c075650741c002c42d01c441d9405003210b0f030100301641c00054085d541011348115040104103a00f4409040810403980640f4051400001402c2480040c00e84204000070440031700440d10350780e0000c40a1504801102d007a82504101401c0aa9107406410b07851400d10f00824440a13001456404910040c1c507130302e040c1b4030f9504040c4550750307070b1165060703051040c140e0454108041c0720311503018100c040302c0c20259582c81100402c01808607070032a410020b05c0700401008050100300140700405001d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 864906951 1250 864905701 864905737
    0xd050d0b06040b160519020f0910120302060105190503030307140702090a0903030e0c011b08130806070f050f0703030e0a080a03020703021009020f0909070b03070906080a11 76
    0x44089041c40c0a6a088540344410000b00c0ba49510074584002c4a824400d000701c5030516958a90482c142c0750b1024000d42001160010302001c2c601110403507400070005414030019541c54041da40b403d501c1500950158010a0050040c1d080150070242419800d618a403503080c5080c02080ea2884020090020407202d0b02028590382941002c480079250020010942c5041508102c802000410800c4001c00d20b041c1d1404103a52001c41e1140c000c101c144c42e4003840092450000d5401c0034100801c68209804000e04120102080c4841024008071401040c0620f810580500b4141c1c3c40402c807010b00c81c0912025490003c100100c4400a51514010817a0301c8a94410762802d40880c1c4001c01c04040460b000c5400e56243d4054035401e400b83d801c4070b80a20320010814101d5248203c0a034001080403030f000090300380481e00a404c030a401c81103a000c1584d80b40a02050340090307410600064000c03608000e20350340000600d0704038034403034404c10605400e0a41403072140301e05d420440200c0d19072 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 864908201 1250 864906951 864906971
    0xc1e060f0c2415150c0203190303091205072612010e1905011d090a1208190c0c060b01020f01020f030604110c0d0c110d03200d050d 58
    0x140d01d0400c007254400102c45030203104950401c680c210324202060818a00f6407071101c1052032110507021210240e40015800d10b84902c03c8030788407462071040e60148102d1100610031807441030f40500c0e0078042c0d0780024a80e007851501001940c00c900b03000040100074080300d00400c1d1034440d0780c91510313040414500c4031b22075000120300e2406101500340701000804000105102010328881c860941c1c558440352003901c156215040300c8003809126401304401d081c0028040e4804030142c2c220107620100d400f98556640c0e1013510582d1206882c0c0000d40303290030b03c801d21b03443c080c2c080000600640180950144504000c15140442c94043c0c0500d8480d0148240b5034000d020302d0741800040c400a66465681865a000340d60040d5aa10300542c68048042c0d01181d5200079107211101000103006901d0a0f4070b4100d92610200301c0c00e480008281804550b0b56480c0300307540c080c1078882d44880803401c402c4400300724100c4d0384810000161b0000c0005041c81039005080307036190f40c603050340094003c1c03107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 864909451 1250 864908201 864908207
    0x140d030b06033112030c030c02280206040512011e0903300606050418020412030507050c0918010606080601020a0602030a0e0a050714040c1d030a06180c1e060f 70
    0x4200000d00301925040d90084c41030f52540250010101c962070500c07038510140d03002c1780d0301c00b800229007a440b1030049101c500f2032114141c3d41b4038180000c1041d411b007034445000403200701400040c698030740e5491a4120360301807406885541410035020030440c900b1640c03030141c24885c0c04101c2c0c100100c403054144c60b21030901030103d400101002000c201d425203510000d840356000303005640b0503001d5440383c0154003419000b00c50a840c001010031102481c50380d400d547d81c1c0c00206045442c5d0003a00354041e15a12580e00c06c03840303210f14180c80310010791a0b2914600310ba048e078010104006049007005501c2c0d8000900c1e2188a622620050f501d41e10036582c02c0042140032201c2805002d0301c8480c2084c00400607a5000343c0d4407008030320f8883c0300c01c4410407084403049241c400110f03240300300290905208540c0d40c5c01d0035401030103403180349401d5640c44080303500300c403001401a05a01c12050a022150a80502070182600303003a0403260f01c80c070f40341c00980d0703188107807070810181c09110491188 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 864910701 1250 864909451 864909541
    0x30c1b010c021e0a030516030903021309020420040b0d06090e0307031706091810090c0f081203130f05060a09150b0d02011b140d030b0603 61
    0x100000c10030140c001c0c90003500c4824016141d89500c4590b02001c80151011030f1070b4001c3c035810344410745401ca80c40d10720318030404e0181003a018080c050f0300000141c0ca44012505d4060300702000001c0e440f41ca8410041282ca40103c00000f190200b4031100e030441d04401190203903164409260340b81c1c00040c140350b01506032504800116400c120006041410000c041d20159109498130f0010b01851099200a0b0000321800d6074000c003280b0208003144c81c0756285440307541249042d2403250ba40300703108009940407c44221800500c00c00c080041d10a0b1044060240c0f04400c007411400c2c00521288a043c000035240d0382c110021611010108101c40c442002c04592140a40d04185440b00c0c0c120010015294141c2d0300401e405054150800b0602c100b00c034484000744011958001c80c0c0044031381070386c07034070840581c2c1814900000100341e008924180e00ea000e80000d007400c00024034010155511340d003da50081c10141f050154500300858440c039180b150881c00301c0603900d01c2d011324001407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 864911951 1250 864910701 864910747
    0x6120b031207020102060618010506030c071407080c0402040b04090f0204051008060307050d020d060c05160809120106050109030b130f0506040203150613020c0123070201060605030c030c 82
    0x1105281c03101c1c02120000e000381508074000d80944d940b60380c48a06120846894800502c03403146100300600151420001564110103403000c2607050400942d10812a100f81401d401c085500241e01040000c104011b0414945402d890540c1064075050b0501c2450040d405604009600e0340b04855951903542d041c1c07001881300400d0614008070004001d00034010a03103072280640165800481c060030300303a00c190881940038080c2c4400c0d80803a10381100034080c50700c54808010302080601c0b0040303a03a8803050025402000080c1da1142000700300038490341c508403000c800d641405c00c2041181c2c0c009003050112900160101190395555044a10901840a0081603503514180c01010b100d8001401c501c00e92082d01291445c03241ca0b000c40060702c01c102c86c05640030104014908030a8800e801a1240404040010030501842c00480c800d041c00c02c40b948052201c03010802c00080da09000e5400201214103002d0b20b1400c2520901c402440000c00101441000140b041011030101ea03001c4145 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 864913201 1250 864911951 864911953
    0x16060c050c15030a0f1109010302090a17030912010507050a1103040b03070c02130e1f180f0b0a0c021b03030d06090c03060e16260907090e0d0906120b03 67
    0x50307282c0c881012150000e0f182581c2d0145011902074281201d4800c6260304045404650b081420720001100654807103805150000031800002500029102412620072000400395840b030300c44c28140448403142d80e001c803441da81000140038109411004861582e051403803e00455603406c1c139414603602c6030394020301c801c0000008000362254007024031450144202c4108002c2402c29184006992409035880855040b0030040b0b040c2400c4501042401c401c204404201d0410813428440000e4003004107403030724100c082d400d20800191510340b41e88403132050010484003002e600020358990b41000140c5400c060451420300340e5070108150780d081c03900da107014000d1645644000024051345c0c0d46610200c0c5c18074001003018816140c00364482c0d6108a050080d80c12084011201e10300044660310541400900950041d000103803120320828001c0000d14003240b400303602c2c00848443c3c4880001540112640c0d444066000a9036022501545482c42543d007000007210010072040800f540c0c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 864914451 1250 864913201 864913219
    0x130801020306010306080a020f19030b010306020c010b0a1d0c0c01020a03150623031e0408040305060601080601021507051303110a050d081903020712020f0f16060c050c 74
    0x5010054004500c41c0800707030f9003480400e581d40f440700e81c0c80c902080025404000b00d603c0382090704103200321504060203010004007440ea40e0300c916490030020782040d02c01503000a031002d44171800b4003c106c0d9140c025034191812a2500000d061400400d0149909103060b042c045a4442d9120701903d4007040224002c5594140c000303400b90003040382844041d0300001c122800a0303030501855540400a050f0140602001c0600f5881c0b1800d40c00108401d1585481c9402d038404210403103e041e21541c416080c203540ea40c00d504015242c000000c1004e0304100e40403042002d079981c0425281c003200418a03a0840a4075540e070141d4990140ca08030600040014100109004440c3e50300d40380300d0419600804030580711000e02800c10a0340c880542020800c2108841d0f80e40d00d50a01c8480710010310340142016411ba0f94047c50005000d01c1c0c80c0141e029000e2580b01810520207403810008200040100b540c03048120039024607284681d90900c5080103600c1c050240501450100300402000c41c58 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 864915701 1250 864914451 864914459
    0x606020c01030608010b0a120501021e130806040f020d0c031509060506030f15040c09110a081807090b01140a2109050c040c050d050a0e0d081b03060613 67
    0x140e0380c1981168a800281000c000040f00013040c403680c01c00202c080c1100803100d0038440d401d50030483c0d22070300300c61944d800c100c40d40040030500700455071000c601c0c84469541c20484850200348100d80c2041d40590010424000081c4007100c45204a0b68103031101c240c0e890540c00e0a10303401c4000d070710150104c94441c43c1e030001595190f104111040c4141c10070001600c1d0f040034555100781c00c500a07000303548205441c180642d02c00551a0348503108601403000c0ca52218076a20030756000205001c20510b022030244902e40e040001194090340c02400010135a00024010b544c030841c600c91129590340c0c9030500f05069228030071001c5c0c05442d043e01079548244150009080800148802150707070410076410324089118003811110315000070042c007026094504000060500c41d001c0010722404100b4040351821500804e80f1542d40035400084444008020a0030192240c8840040085210801c2810f0320aa85a0014008640d06403500c9546040c0070071428808c0f00740740380c442030045074005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 864916951 1250 864915701 864915703
    0x3020a30150509011b0c0804050904080c0102070807140105131707050307150b0901060504091d10050906010b0f0f07020607300914040c120e0102250201120519060602 73
    0x19a17500060600300d6040451840c007201d050141c5e4500031700300e4508000c1080685441c3c1160b40c0c01c2400344404624102002c120107003203910241c1c0864821001054440c02d11500d0889002d503500c890009101d03a2601d00103101103803060300c90041010300400c104041079801d50007a10607082d4884100ea41e240c4050074524070501d012803c0c0305e80c250600d5170f80095814210b000078129007060b01c1d0181054102071500014000c1c10b4184015480511542000c26108009407603021b98410030001d040c0c1004400c090070aa4160040c0210320000c1041500c490340da10704645166894504440d2202e41910005101d8030038168060a0441d003015070351106480d81c00213040c000c81848414440d01d168440660740280d207071151240d0702d0445044503a05040640120f00508001d01d4800079400e40000840101e48208080078070366903011540d020701c41b5400072b841d58001d0b4249600c00c0c080781d89500007801740c040c0b601c10604041d15000414044031080c410340b1790b54a00b100041c000036031074403802 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 864918201 1250 864916951 864916961
    0x2109051c11010b010507031218080f0c1c05070b04020418050f0606010c03120b0f0405090c01031d1c0e060708071a04020f150f040f03020a3015050901 66
    0x403450035403074841034040c598000c5e03040712020740c0d05464082252280150341002860340c0706a022180000f5141000040c1160006107100302940914580b1084121002c0f813400e5401c000a90804641e034070003115094122080d0392096521400305800c0b507456101040143c0301d00d1104190181200d11018208200840d140f541354186034202c1c0d4150ba10030780111040303c460440074000c50058403400c1c01d41181d68103e6040030401500301001d13200510003182c1103881c02c45401ca421341002d401030700c6c1c0d5070349801146541303440c0307101c0440200c010b910800d850b41320300d2a00400c482d10200301d509019000342903001d44200024540c0d40c40343d01c1414408042d0384402c41c2250300c800c1c222030b01ca091452a460f1580a982c01502c00103000740e8031418050080d0040001810450080c40403040f620343c50300007040940700d0a014602002d180d481440a6100250005800c5a071f0701500741c80c025440305081010000c0c003086109030040c50781031152081440a10751030405062000b0400300c42c805401c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 864919451 1250 864918201 864918227
    0x41511030c0f0f0303071e2309150304201513030c050405090a23070f050111120d05130b040c0501090b1216030e15040201020d2109051c 60
    0x15100383c680312007429522844100c822a001c01e120565140514800103090b0003e0003007400c0080c401012118603d00003901503010f0154028001348101050408032219542d00d090680d01c4e41c2142041e640340e201c240302c03040c0201c2c1400c0c0c02070183d9003a036580d1a0b0229407010300241d04c1e0fa4403203020010500c4800180070681c0d003e05c05e594001440e003070511502c0e00c144041c2e806000800c80a644141c2c0805000708aa0380b19002010042800c102c103001c44001054444250034086140c4000544080807800b2540b1701900300da101198014100400c4030f120001c1400e001030140e41e440d440726941103c0000c0904441164004c0200308400c00781440c003035075426200c068040e03555007140081c51095080d0548070401050200d4038405504503a60009611410042018402d14107224030f4203007c104480701202c07404c0700740010740d41c06000386000c1650500d0150841110f041900c6824a054001c18030130a98a68400d001c0c480c050003002e07050301010741d0141210b86400401003095901541c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 864920701 1250 864919451 864919453
    0xf0606030c060c030c170918150d020612070504090903020303090f0304180f0905030c0d030b03030a080f040c0b031311090f06190b12090c0102060c041511030c0f 71
    0x940403450300d008070300d040700f5660303d640c55100e600e120782c0d1107107056146040c1000e82d201303007480780042a6403010882c40c6806950301e24440245010f64040d510103460307004c190300030b41d072040343c0b4005600e0701000c0792880f4158107801c1d2941c2d01c1c2c601c000ca40c288982d90055007030f68600b019400c2016404001580900005000c843c610085421500d490344914807550700802c00c1305010000c4503c83d500015500310034000005070900407900c0301400e550102444c8046078000d1514603466540520609021843c250011400d120703003104054000000541900c2d4078400c0040020200454100323507802408a8034502a264203103144010031030130790310408440c802d00138803564801341010305030103110310801005506a03890b0b1406105000c2c070300189044611407400c03404a4060b5058000b0440742d440000d86d0030300c1e450000c05075810001d107038486a04540140042c408c54040180a03601690700c1580c2c1c58200e040241c10540f100342100e01030400720b000205503440404404034008002c024010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 864921951 1250 864920701 864920723
    0x70317190806030304090e1002070620043501060e011a0309060c13030506011203030501140d0b070504081608010c021c031e050f040204061d0f0402010c0f060603 71
    0x400207031404482210899015402400100035244180d00301d80b260801c1401070324241180c020000080e031740048420384501d034503454030b48842001c103880d054007505903d0007103003020b041c442d12181c10521541103540c42d5101035040001085502e4504018500103402004400d646a0301d0710080700b007d1050400701000c1c50060103282100d542164070481504014004a0340c400740ca00d0f040760880446060003109136180480000e00400a690281c11003451800c04072909141c02020303100142c03c15240b5401c00359480700c0310740300c0000407002180d0103040c4c1c040c0b6503a140f00856483c0100c0d0f0001c891403152840b0844001c81102c01041900d041c4c9009001412680206982d00c00000c0054400503110261341002c1500c264001030801ea00c0400f0244051328148446040d95800e88411200049c00760030300c4218038252107244001d01c0c1303010203101c1d0f046220400341400d1400801a8100040040002e81160b104550000b0304d1588860350500030816400c14400410721400116a01501c1e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 864923201 1250 864921951 864921997
    0x90207120206090a021c08040803040f09050c04120201120b030a1406060d02180403050712020c0103060e0702120c15042a0f0512011b0c06050606040b1902070317 71
    0x8140003403e0f0303801506d003144c00c5e61240020700408480c414107446c4a401408040380343c0c0810300050005103407055031102801d0500d407082c800c40b00f0260006034404001c110802201d03002d1201c1c14401902402c5c0314024184458000d80640180b2069503418040c490340c900802c1600010307452040b0416084900301d90301c603024080707000824076020354801550814211081d01c11805181e201d8800c3c030b062410840d050791540e00c0c04010000d03850158014031048130303131035a06214580c010141e002c500c1c5c10508201c1c40181d11a41e0184c41019142400101c008140000300460340c1c0e020406034290145160901b00501c1170b0709019084c4c15041855188248501181d124102c1690104144001214a407104205003182d04050350589952070f08030f60783e0740800303480c118000510103884202034182d45150050440d64001d195510603101440140241601c40c03090702c0f081c4040702c2c0c050306c40101c4020305078641000c641c8014a0805d00551071481101031402615941d5403200d044100c1d542c1d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 864924451 1250 864923201 864923203
    0x31050303041517060603190b0402070c0e2401030b01051e030106121515020a0b07090602012306060906070507120c08030901170703110d060e06010513090c050409020712020609 77
    0x100303481d04d6a00c04001d20105030482a0010500b10340d03081d00e4800644001c030340c80410103a800900703007560f4490101504001c447c45c100400355202d101500c3c06a0820400c48403400403000c087c4800d0b04165070f030403440c02e250340540202d400490007040401422102e4500082c071540c0309001d4400001e044800001c04001e1500604a200ea4000744e030700c1e81343d41070500500d4580c003080050340c02c510030182c95602060b00b20380060b000d00800e69070010114102500039003501c1d501c400710020b000c040040c0080ba0401140801d4210b0400c80c0c0300c03940d800c03200c40010114007030548040c195000707044001a4000010641105051050a2900210b6a1070000c152a4017034141c00d103010541c0d0142d003165216841e00800e40c80f00b418280003d500d284d000315083c0580200c0c01c0d41c004103039610401c0c00340403080880b150b03018800b403070014903280146204480007450307840762203189174842c8044143d00e0301a1007550090030202e44115265209070a00c294900d4042d80f441025005540100d403070400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 864925701 1250 864924451 864924497
    0x906050d0305040927030801030b1e0613110a020606040f020405101110060605121503030a0c030318030c15200304080d05040b100b310503030415 64
    0x9007580701c003410b0034a00070000c4080c00101503040800d00500320b60240101d02401c020b00c56500981d038440c155811850540d503840d0010300f41d00203501c600c141100812441c40c801d80d500032026901640c0b80301030440c000010b0041c54000c1da20054000c24007101d555400148148941c0c411581400803211100b0404224421030003816000010007107000c822034010640a443e1a0752103040760030200252002c042212541d40000c0300003038000680c042e441802108003174210111071503801e942c04403180001d0396441071010180501040041d403009140c0030340d0040c03c01a1021030210211281458003d1034182d44120448681010540030750f1680c8641c071901286e480510150386513010302c0a00204650401001100d6400c010003106d0b0400829020301c0340502d101d905c55959904010f00241c401c846c03d50040f140180041c080540f00c0d02800d0b01c90310a183c06007010403c0c1c030707814640b401c040c5280c0d6089641c05100000300001d50b2000300c4016484440c00303581d413104c070f0000b642c100b42c5240d03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 864926951 1250 864925701 864925703
    0x210050c061b0a570b1f080610050108010e06030c01080705281706030c0112090c03380c0304052b23040303030e0a140304150509010903060b1311040906050d 69
    0x1400f030304001a9504074121b07211000d0b203407403103000b06404d5036407481a2510408440951603081c11034000c1000d035070801c3ea81ea0140100000540b441d1610901103640c0b010800e45c0a81004220303408034001c42c1c0540704582902c45030000c1d06060314a070382410310840000e8030106000403e20902140308420741c0401d0350040300028040c0251030700c6100112000d020903070400d14419950075500c00002c00114a0000440c8101028920050480c45940e11081c0b20100c07071f4031100d1486100e460032803406130703215072001520401c0340d00c0352100c0c14600d26103410100300c03440c682030840c15050f41c41175004100c041041e05550b02000f008840110384020001c0e40f800d001510070521050000038080d0300400786044555045900010058980c0c01791041010301980882d040000c09200202d045070309007004850070708000e0f2426044c000000c0c503081d828803018202a6032500356910301d68802e6000714281007000404d0140c481240e20014540c1d00600c58000801c1c94a01c000034181004030303c00d800a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 864928057 1106 864926951 864926963
    0x7060207060914091506030901090606120c050d26040305010b0d1a0c04080a0804050a080a200d0210050c061b0a57 51
    0x646030000c1c400c118a0031020300107900e1000f0745480f1040180c2d9a100d40d0740d1604100c01c00c01340b84c5080745a01c8400002400140c00054201c00c4109008510400c8003983e2360074401244203491074020850f20f0500340803c044c1c5072900d454014140511080140140440200d41550100440d82101d11001007024410320109201d000c1b004003094a44440d840c41e203440b04060040c0d00c11102402d600048000341d1000c0320300d026a401000c08800315003c121032403514600d95041401442d00810200c0c1c0300013005403000a075021170a401c00c103c013204451380280203814921034000150010280b04118005803120207180360801690f81d10a5100c2c828000d0243c20101c0c05880d03020f402d0740f0301019510002d0b80004903000c50b4200e050070722070b80c8003074508940125405000301c5494a203416846a03112030142c200c01c403210741c00c013036009079040040b00003001c1c05c41c0700405090 = true := by decide +kernel

theorem cover : BRFrame.Cov 864748201 864928057 := by
  have h0 := BRFrame.cov_init 864748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 864748201 ≤ n) (h2 : n < 864928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
