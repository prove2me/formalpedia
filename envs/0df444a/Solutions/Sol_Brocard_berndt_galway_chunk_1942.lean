-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1942
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:14:38.752988+00:00
-- url     : https://prove2.me/submissions/53344e94-1840-4557-b714-035cc89ed26d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 349100719 ≤ n < 349280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 349101969 1250 349100719 349100747
    0x60e0603012916060c080606070215190f090902070c17120406021501050301052a040e1603050f060307060302070c09020331030c0204050603150708151c080307 70
    0x290f0f0341e650200c0010207003841041d0044842501d03059010381001e00c0707205082d00030a40104120300e818a10303020442142502d4540004100c02000a00c80f24608000c507070308010129201c2180620707c5480c0a4200c06041d44007006060040101c078001407010081c03c2d050341c0d60466200c050034000b4088500d4403261502809414200140128203240c001500d41640e00d00405802c110740c0e00d4005150a07107205450641e8921710000042803489403005030207560096009145080950301d210b001c2c00848269200006810f03500340c40c2d60301d070780d05000b03941d4001414600100703242018000b2030b0759040c051088404259002c41c0503030400051305090401000e1510040d52681803102c520000e602d141200c0001907a03040b00b00c050420028201642480c0d010f8444900d035000c0e0b5002c2c0f0028140040445502d40500880500381d5440030500368040e0025039910b410038a00000c0c00007111004042071131003010755030216843d40d80c81500c0c8000d010b5000c0050790302ca0301d4403a41030307920140080352 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 349103219 1250 349101969 349102049
    0x7050904050f0a0b01210c1b210203030421020f150907060206071706060d0912090501020c06090d03030e03040b090f0607031b050c060d0213060e060301 67
    0x3808102c5221481140c003c800b084002c0045041210054a81c0390244900700380700361072400d140600c0991580b007a41403401e68146490043d0300140f02040e20313141880200c4034001b001d0010341c800103801120138800e0350f19000451031803c19403140c4480b425040c00ca0102116040c02c1c01190384e10070b1080100e03254001040340d03150700c10812109150342c0202d84030070851165042c0040c0313151001a542c1e024411644821482d03041d009601d407500000246003980041d01000300600d0300a240c03281c0c2c10254050b102070000b81e280e41130001c1c10705031180d00450440d072000c0100841c0d0b13900c003411908034903401c4031103414000325440d0640c0500340d1000e6941c4c1c64080843c001403c07200500040101e0002100e00058400c42c03101000868040e4000240c0026400000c0040d04000d044404204601480448412240010015000794071548211039682c1d0045095001c0300f00c840f4403200030302120705041a0000f02107001c10501d0205220b242140c080c40f00d016581f0300d81001100202d103401d451 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 349104469 1250 349103219 349103221
    0x315030b090606220b03010b0d050102030a05011e061b0204180c1508240a060306030b060d0201020a020607060b1f110a020a0614040f090c08090a0302060106080705090405 75
    0x600800910080710500c0d007600504000a1483c5001450b070354020306540403403480c80125207007450051440c1e590083e00740d961110002135903940c40700c00c580d40d41c0c0305000140c1d484ca000458441035a90690095906019801103034031291298a00e510540303244d0301e03208980c140200c1c60a039550102c510040e40040c640a10340e0801c0d4400070081d0019401401100150307a910386032488400546182040000c0100d001314044910900d40c10109480100c004020495020005141540d070756000401080d5541410402c102025103090b0380610210360346070b4850f41c5c0f0340003c0d48400003d00002d2180314006a0101001003a80c02141d150101a0240f5041e6084091044214820300030050200d5001403054803454800140510303050782c09003200110510306081511410040f05114020344014080452009241040070000742400e035008200c45402501c00781185101408030700e002d4000b00f5002021980025126045404502d0601c444d41c0d82c8003c101c0c1e09002c1c40c3c4039203a101c0e0500f8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 349105719 1250 349104469 349104473
    0x3220504090606151e050903010e100e01060e01050f091015020c1219020907020102042103080f0c030c16151b020d09151b03120605040209060702090601031503 70
    0x3c0c2c000e5064640b8603194420503c000c0d00103135600040c807450320260702d105a01030307164988124080c142c802e074090004500480c3c402e0310142420300b407808070900d00c1d5544203202c842c01406d0195a0081c4900d001402480d414900441c1c42d05c0f0030b100b00c1d9030180850303001081d604005589420018844200024034000200034021f4940c05020136551080380074201e041c1072540e002c207000d04421421840307040ba402c1ca50b42840900c4000422150a41d5428080000c0e48682c503001d492860407668141251016a40707000340900c0000b501640e8610164010410b42c080340c4011a40c005031f1003049940c4031504000030750192890100001e01c6042c0310f09034119003441542182910401070012001980a10f01040365034641d54030f1118000f070740c0d0340f03c1000704107800418981d4600e014601405807565201080880b01c4e03062038100c00107100c00c16003050345032944c4506800b50108071800c0d0700c1c0203003402c00a0203502456001074401c81040b40803030b00300e81c080d900492880715080000d4001725628 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 349106969 1250 349105719 349105721
    0x50c06062107031b0905060d020f0415080604300309050a0602040b341104140108150109050103020f0418021e0a090b0a23090f190e032205040906 64
    0x41c2d00400404030195804114800745d0300604d0702c02c80c00a400144462010303000c11686481c2d005546402c1507a841c206041e21900307454110240c0f00402c000c0445040c64034120710b08100e9100d00c1c008080f1081540b00c0307542418480621058094500820458500e081c07440c102404260700424491001800060f9062240c019110804182800c81c11034034038009000c001600704802d048100c1c090141c510001a40c0c144804050f40d80504000381000110910445010080e00200f140f43c0c0140b2482a46501c1081d80f1405008050b2081c0059495a03010804071020740700702c64810ba071034590040c1502e060b00d00042442c0c1e00280340700c0e0358440b07203044004039181024007240200e61000002c50703604018058440c6562020309580340303903480c25401c10011000e400d11040e0ba01c10b0454a0350141c0d032880401c0d80039150810603030816060025840c280141c101d069124403e0030509013140114002c001c1d1032440000c3c801001d280c0510b11080d204140d52500001d600c1440c10301000244011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 349108219 1250 349106969 349106993
    0x60807060905040c030501060905010513050a0605190905030d2001290a0513090201020304120b100e07140f090301060902030a050709080a020d020d0f050f0c01050c0606210703 77
    0xb056404004801034030401318181c400900401000c24416002005294030070740c010001603000440b8202d80c642c6070381c00108414034640c007c0b800520089402813400034441d5102da594012410075411861a00c00840d4441100f140003409020401c001e030500062401902c0c2e98030402c080003001350102c0e80040e052200300b400d034040901e015852000d1740a003450741c1d14606559009250990420441d55403078060000900200d04501051000150b00d0404146006800740b28040c11225851706414a94192007140d0001c100e1040c0f40c0b00307106903790841c0a540445450302803131a034640700b01d40d074020b6034071541070b4032500366103081400540141594080d5000d40000d580034030407506c0d00ca804841200c00c40c02410030b50b4108551403001854034407091611907202515000c86005c4039200c1425842c207585050b500ea40003611400c05a10040c040d070b4a40706d0007403c0c81e40c2041602c0d40603950340e850003000ca60041c2410203091603412180c00c4107588035007610342154070480c1c4915111002080e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 349109469 1250 349108219 349108229
    0x1033809070e01080309150d1116021318021002120406030501090c0c05100504020a03021309030f02031c09021201020307121104120308061203370c0b0a0608070609 72
    0xc828000419130b00004000c030740500c00024445800c0c0d0841040f03000507035100710041582d440e51412810003e03100b00028041c00d512130807403481091058010f11918823480007011300142d1074003880c81c42e2520034902c0007000c96019100302c201d81a510034180e00e0025403858409403035401090000300c0e542c1c560081d074161140b403141800703c4d0411810a42c0c84031b00c0050f00820342e40168080b60311364545a1302c4a94424001041503204640e03a8000c102c8510b0303d040c102a0713032500c85c0001c1040c103030030611541c00401140300851a005000d101d9101c1200c0c50040591a00c0c0c03a00c91803010340d602c080000704070000c90701c02195203081818000d0700d01020308007554082ca0420400100441c031000c18ae9040746e000040d2070070b402016980445900f2002440d996001c405000319041c4800100058003402c15528004110016200d01c10040a40030300c5a0070b13400c01301002451122940b142c1c524007440d600c201c40841c241c540c43d00e050701501603900076086078880e039440001d0440c1e02c001c3c50801c0f18 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 349110719 1250 349109469 349109489
    0x7020310110703050319050403030209090f07050313020303070b0a1401120b01060302030903160c0503011409070302060a02120c0c010f031406091f0803040603140103380907 76
    0x2400c44000c0c01519420000a01c80c000e082c888100800e00881c02144d00210001c424a078901014203098212039007030f2400e0b8002070b400f080500c0c1d03a0820030160b540000340c079a40b003141881c0c680001043c07440010507030020400350f1a00c030000c41d2400c10a0304c0d12030354891032900440c54201070100003841c407984c0c040300034a500800040d508401008028005800178000c0f586d580c00d10303030150701079400a05035813851b2104020740304007260301d02101c2c516144070b445044c2c0c000d454001050b0070b40c3e62000f2201c03441909901400388690f40051a80308699050316900e8032032400d80c5040c0e040c100110185068001c0001d41d07040d0600000c40c0311801610241c840e900d4900311a00100c081740c4824030032403200d521080100d01d44c0d10b8002c040b642d01008240b01e4161044a400c001803030681c10758000350701640b001c20107102c0703650940101700080701c00014140c603a61464690011400d03001591002c0c1d02601d0b81c1c0800d003501d4601e00e030b404042c5501c40c40d110508008910036940c04103403041000398 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 349111969 1250 349110719 349110733
    0x1110418110a0f0810180c030509031c0f060509160201050115120b1201110301170a08040b030a0207080f0a02100c020c150c191101030209010c0f0204150902070203 72
    0x109070310300c040d41c81c5621240c2d1410b00c180503115080d02c1c0c604003d0030701c1d091805860800540b400584518505442a101c40420340600b10040513050718400351081201d0382061280c03002c5414072145248007501403100100380c5c0b0403000000001090160030180d0070501042c01c200c114454144c01d82c2e415a000d070300070491a0382e00d0340c101c109107070790a4032a00004c507041c1d07400b964500d0075048442c520200030045442c660310a4030850131951403142c007680c0810080010086482107403498000f4000307400241c20b003085140d84070315140c800c5014048407803801201088600c0d42660541c0c8003d948070700503c0d51490310802c102141d400203a0090010701c986101144030101d540204a9018215002000501c034802c0401004000b00359658128203001c2c490004070a40c1004240400c06040b034913030301d4810071350070303c03500c0003044950803418940108044002640d201003105005500f01c20702081101c0d20b880060f000d094481044a04060f020b000460171a00940c01400510701c00c40444800f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 349113219 1250 349111969 349111991
    0x12030103020a1203030609020a0903050601081903080a09060204030606050f01031407030c0e0402030f0103030807030207030801091d06070e1215010e041e1109070503060a0b0c01110418 81
    0x5100900000790002695481044011000c00741c426030a482401c2c080b41450721400c240c2c003240c010960000c00908520020000e00c5824003040707003d42224005000d03d1035807040402e40400c52480001c040082e0702001070b66182c09603000305031241d0302c04c50941d680d07566030070300070050172080c0a490304c11096400113445035806823044aa102d01d07003180c1401c01e40d407484800c2c1e008000090f120b00a1100182e0018074a0341c03a4401103104110010b1100815411420010b0554500401e0182458410003804002c2038010a01b1411185442b60204045101041903075003071984031001141841650144400d050300204815002d000644003600c2c010031305404290f8034040c81800e8050058050018009030740304403c2540e01c5400f480b100c8203d240071043c2000300720040201911019504207880005140ca00000c6070400418500581035040c1640040e05071401d51144580803c0002500703a280d40d003e4011502c1c009009a006807105e1b91000300c00f40c4102c0825818102c5803804040c030780 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 349114469 1250 349113219 349113253
    0x305070614060307030b13061103070e031f05220605070806041802090c0c031b060a0515090a06090c030518060c1c06031713050108010513020f13031202 67
    0x4882c0750024014000c0c5440e54a41008128002d0040700206100c84901000f10b21513000340040142450308a5a4074a081c2500400c08442d24480074400d82044040185111160342c041003d554202c1c00000c540e00c1d07034108080165003111402c6446441c0e46d5140052040a9000e68440c0b00291110318096650500708011034100b03aa2055450079000c000c0300142c10036560380b030f51040d05927079914900140780e60b1507890f64210441d80d5001c030301c914110900d8041c050010750f4111281400600650910a00660007074180c51409401003124000140c90400d141c0c216900424480d0020041c0000307200c8010090b003400c540700700401c1000060b0311046040050355071f02c180c860803105810301e2110741002e42115000309096036000c1d200e4501102141c216240420300e100070741000ca0fa10301a1061015240019074000c3c0e050140500040015881d11501e0222040323420100581c0c90a00040035565800fa624902c01d0030005040b001c4200400401c2800c450081e45c1c00711a0813000d5050444 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 349115719 1250 349114469 349114471
    0xb07180e01080d051819080c06090625061d19030e0112061a03011707140105090112090311150112080901030905010c05091302041a070203190305070614 67
    0xc80030b5440b04110403e8988141d0191a68200d90800105610072017400110141491030b11941c550440c4074080106000800c0307003000000080c1c80e000d007002101d00000d1001d00865400c06804400038a402c001003a035001c9007100030390f00201c104400018000444100b03191175070f0742500d6201e43c1d0311035440c0881c00340020041c960b05079034045401c003009004403024000c3c20708a0203070740c0d1070304804201212108808900c08a4080c2c666841e589401200c40001d108011502e905030071680e000d1102d141d40010804d040e000c00c3c01c00b20f5545451030012604420610314200e08585000c00b0041011303440256120145488011103805020741e180071040f2040a01c42d5201e91b070003035502c0780006010f0001134a103c3c01d05050000d040c0000f5201c450035200200d000c1c10002d100003072140c0a900d04108003168814000c181141804d080256183c4480d42c18200c141107410081551411941c0410114001d0035000c01191801e0702c9900d40034280b038108460803207500b805d007021142075000c610811 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 349116969 1250 349115719 349115729
    0x50f1e060402100519030c0306090212061e060c0d14040e1306020c010e0601060f170402041a1807021b010804060905010b030a0c05040605010c0b220b07180e01 70
    0x600441e468942c01c1021603202c2452180c00e02c00180144800300c21906841c00709038003552808608882a102c1c000d04807411500200b030940d02c1407001088146100200c4c590101c020b5641314114810190001c00c1024200c00d80b40d80301000241c0c403481850f01282000b640881e03038803410341603061b0840302e28440c01280a0031100c0c0410100240c9060384070102c5030b8069004143c014901700700340e80b01c1820b55210040c00301c0950320500040001c6640103e00146405180c50810000c1ca6900419182c003c400741c8080e1045031a00052210316181c1c06240b2168440244801024541c501c20300c000040700b1210500503000d1150304030680100c00d0641240340c03205a50b0030391583d03241d589002c018500c03010140d0b200c1d0f5854041c1051501d04101d05001c940c0640c14081e0380c40d00d800104425600d90743c11682c10400094002c07c00102014800c6402102e880f08003003403a0040504e1030a03140d40a03201a0550421800348040c1d1904420303c0c05000c02c412004010f266182c24040400304028411 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 349118219 1250 349116969 349116973
    0x411070b040314090a0e060108240607020a0f1e050f0f06220807031b0b030112140d050301090b040608100e0a05030a0f0206070306030201050910020a0f050f1e 70
    0x107400240303c1c50000a0081015480c542000b00d800c02044a078aa540c1181c3c000d0b404030b0080c8585513801c01a42176110018040035412602c422980d9818100e0415070507000e64008201c1504540e10308444802600700303405000c100c2951940060b0101205009004456144217004981400d0114405200704002760551510048443c14070500d680080110401e86408107c0300000407500928040201480d08c01402800e086080c511a000c4d50000e01000e1542c1c0707032908100c41c5101c0e0341500c0c115030a000031040000e0041c2488107031400001000100f9004038103926a14642003005581079808011082080b0508101800119912405402000d03070090182020201094018081c121565015100506050b0791681c0ca5504400c6201001c500c603c42c14815203641004125070001040c07801303001092a43e00040c0091054000c01400b030203111031150341c2d40d4000c00060075910391002d2420580c1800e4103120b6214450412901c800b8012080b148040e8481e0403030358102c280007000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 349119469 1250 349118219 349118221
    0x50c100302070b04110d050d020705040f05060a121712190c02100b1306090203060f0307031104020f041503060f12030905120f10090c0b030c1218011a0411070b 70
    0x10b804c111004120217003540001c074649000c1c00038a0510580b40f80200c01c1d0010100c450421040100383d40c80319510850075840e01040014903035440c1d0b441002c5942003110641094039130308040102490b032150015000382c0004014880d9204000f20512070100040f1401d48050714070301080a413112030741c800d001070740700350491a0b6804080d0b0040b500d424009028080041c0750032640015540d4a5100303070b800d039038040300b0000320707007041c1c0c01220400350120050300d000b6007181d491101811400003158012503022610b00c01c070581d0740c02260040c0402a05612039000b041c80010050308940c00b0f05c3c010000c20500c009021001c4d0421540c495906031294007405081400b4450003400070140340c0e9a501c00d03900020100c2c42d05019442c61288164008038058946050006901070359610181c507803801041000400210481512186450019000318a480d620011061800b44001041d1207520f0700030380000c818250041000540820380c0d0034001c6600c200301e00511070041c510003410031100c280c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 349120719 1250 349119469 349119473
    0x30604051b1b3c100c0309150c1706061303081323060c07030c030b01090b010203120c030a140a090c050303090105040b0c0a08040902040305011410090e1207050c100302070b04 77
    0x500703106001c55036040301c403404d00c0003d10b0310941d2002ca802c0000300b6650903c040034030000c54041c01c0303c4842c003101480007040060000703040d640c405200000495640d0301007680342d078480007151002c1c0780c410f020840a40d22400e090005600800880019940c048000a960312030a034040c060719888214000100c0072010901c0440c3c1d0091448603802e000d00c10000c40068540d400040256009410208a03503042c19140303821900480c1e20141554810721260b0400300a2001003984180700407a2a5140d8417514800c0002d00038a007408581951000e04221482040354051043d007406203a0b080704c4103035100c2c1815204d1041805407800203408000512401c1b00641c01011103440100445010011548920040340c0181d003211034680e0700002c04100f8454240208510350051111386106800d1000a0607144204ca01c2015035264a440148282e04014480b5007a081001c0380804d90307a038583e1801d56102e2004080c820310850704070000402e528824400d5070ba07055030100d990308942c2c6540d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 349121969 1250 349120719 349120813
    0x50916050706020a02010903020d030e031b16181416050717030a0b09071814060421031107060807030209060904020d0906060614030604051b1b 63
    0x162148040c0801000400e002581c01c0c401841054040d03400054031300b00ba071034005d0800880e15181c2c01054204404c07e40400000700840b0450400242850408900382c2c107103500301101c0103d001c61520081c0d000003000c000540509208006c1c489040000e2669007030040d1006005a6416607201c01140885441c1030142005128082c0180d400c00100040d80c07501d40d49640c0300311000c0408548a003584000c50921803070b8180c0000507400c03d0074860004d402481ca20015602c1000c1c0c441d140e080c42c04030b858442c4000ca50262456040460070790402115245102503880e2040f400140c24184030b0b0340c03010020911400750380c0282e1b600455501c03420070071806904201c050303545c8540704000007517090b9628401000c40c12500c60010559007810b040450889000354040014082c50401c0400e008100380212036010500b242c000865441c0ea6070a1160718143d070031b8000e03d00e01d00107250741c40c03042c240c012210700220090490b04071010144590810304081640e0076600c0c012120036002c04261 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 349123219 1250 349121969 349122001
    0x6030b0610110f070306200922060b070210050306010807030504020114031f0e100306050405030706060f0f05031f090201020c09160e0303070b0609070311040e0a0e01060509 76
    0x15151a959500561404900f020b030104201d03a415800300300104104002406489544080400da001002002c284400e0051003603d034458420321402101020003404400c1e08070400d0040e1008000a81c0c0b50400304146502c00002603104d48443d43c06949450303c41c4080740d1141d00306940d09c40494584210603000b46c940580304130305000c1d965540400d070b054243c000d18400c0c42045900140d40c1d2020487c90f10110898118501c00c06181c002c000284101d4601d031411690b01000c001307160b80d103d0500d5400c41c058244d0080c031807820301000003000d44040e46d955050361061040c15800b60350301c2003055620a010902203102109655828036014100d9100340c5500d4018019a034a2031607200008001e04001c440400b0041d035520713007034135015038800c0d030104a200017038005606e414026114035482005c01042244124081000507200c280300b034000d00515200d406400340c4030364603140003c00702d12003202e40030006440c00800803281c0c00c2c1405050115400608908426229090600000b040d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 349124469 1250 349123219 349123249
    0x21203071a0a0f0606090b07060b03071502070902070b010302040f0e0d08070314040213020a02100207030c02150304170901020f0703050114010b03090601090f060b0c1f06030b06 78
    0x1400320401103640762000c2410840c4122a01c00e0900c1d00c50085070032526a0600082d10914100d400d11817107801c00440000c0d1110380311116220103007850901c1c058098014001e8042c010030b84001446690302e0f50501da481c0751902500e02064488031820120700070b101000d400c0d07601c00d000410241c1032030303070240191040043e030202e1a0511703140d80902d0714a45000710000100180c0800000c40c1d418810b0b68401603040205078058286a00040c19600240707003454900ea6000901500e858000c111003101c5c10000ba909649070640c80c1005000300185500c26402031051203501c070303000a0600304032407140d64807907101202100e540f0342c000000d400c230300b1816040d441100301da10383c0410204a048011440384001243c0b101300141140c0d40124181c0c88500d031500306005001d080100842c4160645000030400241c901060361450040c0c841507015024644000503d803201030404280e0040c0c001c42c0c1c1c95090701000c00224070000f01c4546100283ca0142c0520116030070345402045220b07608 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 349125719 1250 349124469 349124473
    0x702010c0206070b010906120f080901021c0c0605010b030c12280501180b01051210050907121a060d02030c0c01020406050c15060d021207030b090a11090103020604030212 75
    0x112a503400702e40719038003000c01501d191442c000100314000c000c1c0101c4004d44000600050383c400980d40c2d01e18490004400149442004140d00b0600d074401c0010520304401822589644000c450020380200c4a808041c3d03981d606040011845101d0784040300c0c000ca24400c00c02c1e103004102c070f158001000003d007216003081c202c21024004020b901000b02d10011800318005681d504d0308501080d0542c0518250031007504000050840d6038020040e508042400218094141d442c00d01c03243d0b041c522908010b501144000c240425194460340a15104469003010040d040c00004c042e0400d0055002c42c0d80d12650401c2400015442d603005180c000b03566140142c201020344041509a07001a0001000245e02081a0b0140038080103d081c95842c0e1958050b580d007449004211a5084a5030203400f8000c800c01d065000d24080010700c0003541c0050030069141006c02d003503500d070111800b00782c802a0411000c0199407405021003812264001c0200786031900e507030309001ca030042c1510010298 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 349126969 1250 349125719 349125737
    0x2301020a0c05330a02010609060b0304230114040201170603120c030903030c031207170f040f0f03260c12040c030f030f080109020c0c0111010b0a0b040501080106170c070201 76
    0x2501800d104003445800600f6161142d1001800908640c031560000c81801d09010701080401e901d1000c1366046030b0403007d019070310b062010b04030000520f100a03100d0150302e03040c2d4850944128071402c5005030b1003603a8a00102c050282c41680070700c0140c4e841c0340d00d038102840e0540180c034104014103000109000b0b4030308002075040040d00315040001078504036000014410100120148241e50000050404c0841d0707003101d0802ca08004402404651380038090030225040c0401d0843c8103045d1680320005425512031071030011b007a02c601d5103000006140c3c5100f039040b461407001040d446030400a40c02404c01c0c3c0b00d00c0580d1203071000900292541c0c1111940800499140c090003401030b40a600c9a80d40801c800d0002800840142e1202d081140b05020034800001d0110740000c1d25002480c044070b08040c1800082e005040c2c001c1001d0340494203000006400c6862400f500440e482620350706043e81e41c0f02010f0300d448200300406030340c03140341e00d00146002a40c4001341070a140180340c10420 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 349128219 1250 349126969 349127029
    0x20306190306050907050d051203130602280c0b2d070512011406090f130903120f0b01090b03070c06050106020f0d0302090105070b04050c09012301020a0c05 69
    0x2144035550002d03102507490b80200010b50404110745802860700b0b4524a1442100351980c0351641a00d043c10fa413005000800308421501071005a018560802c07411540c034050500c46038100c0e02e044809a004040c42108507854a008031346040e44c568026079640030710795542120440100c500405082e44800396003a40c0c544041145c0064803603030303890319901d43c0c1d500c800503054000c40059000e050620b80d00b4003031000b16162281036840710001038441c0040c2d0800d540014920313102c04103c088400d40381207520028154402c10568003100500c07010492070303440d05114400d9a01c40745106001c200d084804002581c2c000c4005c503404495440e005211000ea59110401e03100c080e4401001680030300074442d680c88042c4000d800d0020a03040440c6440b082c0c45c00680140207140c0d0262404207800006005d0000c1071141043c040d1000700199010b40e15000d00c103402107a41c5c28038075055003445048404075400080c014501640001c07990054610301400c101d03e841e030044801c001001c4640a10b81 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 349129469 1250 349128219 349128259
    0x9020414090a0e15010801050c09010909050711100c1202030402060301030321090b07080601020a0b220209070206011703030f13020319030203030910150317040305060c040314010e060a020306 84
    0x704c00b440050030725940d450020224295000179000709440c07032081120008503a0004184000c0b00d2102001040c0c0382c0d9a42d030117a808207542041d4a146000c0d000c414441840c665020308108411515030030301d00402c000120040b808200c4000350044c90404c014408240034000550002c24000c0c0c0100941e500603841074282c519492080ba07030f03140120144041c103900005e000381c1c054803c2c401080b189030700782c555526414000d02554501003410340700b0710518a00d183c0c00100070b038000d080c03500c490070710b0403000b56161400d00c03400e5600e482d490031080b40c4500101c100ca00450014880785202d490310311421148198007681240d01d072043c095003460b512841d11500041c1c900a0300603580f0b905d081101d1740e082442d00c0b451045200d103088014125000940c1c0b1200036603810107402d1980d0601c0100304240343c401c9810142c02881564200046490b0000007882501d00c2400700d10b610744945a000d5080c1c940140300540c26402c960002440442144d01079540910010b0800010250b0603072891 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 349130719 1250 349129469 349129483
    0x204151208040611010506010e0f0a030506010803040e0702160603110c011401180207020d1401110c030406030f020405060d05061504060c2102030a03020304050111030a0f050109020414090a0e 84
    0x7180804080340c00c004081e00f104489400402000080c8140d117800000285162210f154a9100d0340d14818aa222501c5203032001c2c000e554008215816035840d040c010780e03a50000d00c145200348075a2000240400d20203c0d9902002c07000310700310705a00b8280f1500750058240c940340948520320034407501005e40000d0094420100d00c6601c07540300e9504003a084502102c001080c0510140100300d00f80051303c0302c1204040c1580c102c80c000211420901c80d03180900000100105400800700d5032508003480400104116865030318104011714158190f2026400b03280300303007548281c084c030000c00e8011242d0411030341300c4001440c4400c0703145080b45104583d00b16400c0070700014040340004041060a880d601000c0032501300c0c8111603100c5a078002c0da03d01c141081d440c10180c0100208041140942024902541014a840e1a490a0b0050078028014100c0100700e036070900c4000500c00d0003520803101520b02d15070b00d50b0a002865030522103150000392552a41580d101c41c070034010f5074144008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 349131969 1250 349130719 349130723
    0x5091c0b0603071a0a050705030904091b05040603030f11010b0306011401170c0f0703230705010f05060a050613030b150a150e040e0f0f030c190f02041512 68
    0x11210380d04024080c0b51038510389030050004d0680300902d8200640b403040030307266010745501d80300744e030360105107070080c2507001d041c014907005401c050a0708100003070109510b0104008260b8019200c0d500c000b000181e030510701c0040e0119000e0200030003001e1091b41440d60b01c940030800410b00801c81408a49043c00903406060b41030350500c5809405e40e407000041851210b80d0b9000e000a09001d84415081d104401c00414086000940a0308040c01131301031310201c0246070b42846030400e003c0700c02800e690241004032132651815415003000c0340030b1b1081501400000c0d05e5401150b046c042030040c0d503480722050010707000b101040040003601d4010510700c035050003818800b00c2c1d40708030140002c070072850704003802d600c8802c2032148526070710811180100a08840c046500410170800300e09000c041c8203194024051039100307080d40c010000090541510280445841074201140b05486d8203a0100060018140c10801005031900c0d800000b0f810b54100844104a40c0e10150848510641502 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 349133219 1250 349131969 349131983
    0xc150c020f1e030604031d01090b09221803030516020c06090d06050c0915180108060f1e01020c1002070b0c160609050112050c0304150609020c060a0614090705091c 72
    0x507e03076800c15a59900812000c080c00e00f015001d0400c41b010f5010701840c40c00d81e0103141c400c0c0f0b402c0d000a607404290400350811600400840a41e03001c0700350a10403420058011a08002c00700d80003465030f110304003941e05594060304c0c505050404008140d440304103156400340081d04e8640124986204150141a295000c5c3d41d0f100c0486091040200454401c565000310512445150110700c0194900e861750920341540c5580c2c6000004043e1b12010654981080340c140780608104241c00505c0c0310403000344c0840e0174401c10313881040000c0c0b40d40c0030b4030401031b04101010800100c03c0c401400e240c07032000040d02c845007450198007092144691004000500c4c8050810241d60012001007164428079800d000900d00004440602c2c4000f5000a10144100d0622810480d855004c4e0006c1e0185200a5550350400440c0659525003503c40b403007111315002d0000b80400446410f82c05414001d030440c06030303640d180030030b88298002040e0180c00c8520b08a070034260b41260360307030789490034400c00c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 349134469 1250 349133219 349133237
    0x20318060705100f0b031b030f070303080a050601170109090c1a1e120c03070801060e0d0f050a150b0909060609070c1113020c0d2309011701030c150c020f1e03060403 73
    0xc101460840d030340d5127a04e0650001c2c0f2003400070030742c0403101550220b6500c001207482c5c2c46040048075004101c0910107440d4500740c0000c00d00c2c2c01c140d040140c0c4a8001e400d10420151142407540102207000b00d031020072101084504001c08845546680c0120200c01843c20070a10540c1c25030341100c100c500d40700c2303441c0005c1005902600410711601425041c503140341c090311840045032814034868005000301e21400d072004100308042104901041d07014039685500f070f00c290000005854545620380c842c80c0390000141002e41c0008030f15100b03010003010740502d5115000e003a41c09581e04001628140c0380036280350f0503a112421a00c810340000e140040c1d691002c2c0840e181086114151042040705224010903110b541c0c6000d032800758080a003003a5140c50040059039894020509071b200400e001000005205054202204441c1000c025400071543c60340c040707411101411000794040c14102c446121418801602410741da94028410046050703078000070300e0280c084174100c0c00103030102 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 349135719 1250 349134469 349134523
    0x103080c100212041401020d060e070e1207061b050304080a0b070c0302070603050a060905040602040501020607181401030605031c18030804091503080703020318060705100f0b03 78
    0x415440c0901c49044110b0038410301d888140c0c80001c01030070140c0041500004031206010030750458020760348036101001890b0365123040c82d41c81c120494032400482c1007009454583d04001c00401520b8001034040e0890b1801c201050740c40f034110b109c90140e00316048541000181c4100020000b030701032400206041d00e0b080c41e0081c09190000c1c229810418401044000030741c00041803003d40d825801c010070300d5550703550050300030412984080f2000303080c02c040c8424412654000d01c291042a402c1d40c0e495a80c01c0d000351014008062020102d0312890707410400e0600d520f440d05000750051401085643c0c0c7c50000900c1c14071800490003400d000314146200b407607000794042d14520303602e40110b030500d4919152260540241c4c42042034254a8140003e404005141d55902441d03115071324544403101130600075a6500081c406065035815010b0b0010b00c0d1511409a4944a0b40400140f601c040300c0d04844018040410648500780e48500300b00f903840c6d805006801d05010004c16040d8280b01382 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 349136969 1250 349135719 349135723
    0x8060109060b09030a020120070b1306020705060a050a09091a101112031e13030801090612020d02130609140a0515091515090909070b0a030902060f030103080c 70
    0x1590025980b02c0703082180764069100402d000300d44035024203115105801860103202ca86414075a00b20482c021010049220b5854074040d1211b03c481002c001c3c41c25403902e01c16a501c540c1d034002d03181d1021092044072070081c411801044041002d24203140d40302da4801d17421080e00c1050032030391110b0100e000c80c0c802d241007140b01c0c00c0310102580741265880042e500c64903240c0014011807034100000000003102c150802d4140d10400035800c55020040c50501401090910380450890024445000008014005006940c103842400783c1c4400c21680e50b908000d4247e45005007240c000142018210011600c2e11801d0000c1505801c0460004c0b08a032680d00c2c910780050080b02d41c2c81c6080c0502c00d6210901480005408050300d1205803611119042d00300c0143d4a00f40c44d40c050b02d8141d00401103c0c6d09009401c21000c1a02c400c04035071100401d407a2580c400e40901405a032092019402d0141311f1b802c0044d01900103451107185c8041c004421a00b5030090f00140e4007041c2c0019115842202 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 349138219 1250 349136969 349136981
    0x60507030506180408031b040503030c03090117040b0c0a02100e0304050f220903050d11070309050904030f0e040207050307050105040c060903080717190c020f0a1809050c060408060109 81
    0x10400e43c0c00518180d40d41000070f00010b845070070301c0c02c80d4022043c80b0000701c0b01142d01800009003220b4a403074107200031aa80354494080300c0d0003e0207034240d5500810302415524051948990302001503a501c0030303130f44166003104070128114403405c8803001c001c3c1c0480c81440410740604000d182e542c1d0034a002e00003811448001c01c0d0044d4440006006500c102840c034115038462564081005615414200c42d03c1c040c039410904110b140404249030507061000a00d6510300c01d803501c4140540d2107040003040301003100c018010410b42c0c004070a407603100305010406c2180c020300060901d01d89448a07442c5801c0b080007191541e648000780001d01000c0c00814005100624082c150242595101c402501030000000e03c4071144021601c500310b80c4600b61040c1c4070200011110020250320000d24043c00748009a02030b501c05c203042045030600041d560181e07a1b014948600303a10000c18030000074082010156150700070390031668401d9480030700620080004030b000340704a5050444400444030307 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 349139469 1250 349138219 349138249
    0x70c0303050c090a031127010906090c0c0605101701051008070605040e0a1808031519060c020607020409050303010f09151e0e01080109060e07060c020d0609060507030506 75
    0x18140319003241561100668004c1d00d500400c0258208502d0b000f0408410085c3d81e0825012280005524800c0031514010f0480304182700174000c3c0fa40e86c007444400c0b00c052920160006504041c06004180700707400460b0000d0308440384190742561000322005065024400e4200e69440f0b10034480440a82c007040d40c058101132014103030743ea10f0490081c10070310403032141c01e0104803c5400a10644a99070240070022072290701c412942c0400e180880090b4011153380844041c203105d001040e0412074450546244403001c00207429040c180107075250138041c0802c90303104000b0480000161203074010010311070710400007991039505082400c0009e4045030009817100e882c0424078155a00e00101304c1003140c01d4803900c030520400355080d2428450b410380264496510103400024000b00550203548494001c000030402250100c08558654a131840740200042001c50b0000c058a0610102e8915070310602d8000b83c0f000b21a0380714030913504103d030440003203030783c500410420b0f08000c0f0312610100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 349140719 1250 349139469 349139491
    0x160c08031c0b03031222030c02010215071b0501110a090305070b070201210b0a062703020f09090f011803080105030d090603020c030f2205060408120906040e070c030305 74
    0x202c84032000c40d0762030041c4010403030001407440110b0a1641540c560075483c1c0c106180c25451420541000380010714054412070041c07003810340900300c2070f0502d640c407800f40b600c5540d00200b1030300c943c148555080e13103108190fa070380d56900c54a0722212451002041084490340b101005645942809820030700268441d60500070304100c100c2c0140e82c0801205915080c2690141c0b42c51030408600c0000c01d0302800507030f006200c142010906580005c120f02403409414030004110682070132400a50f11144802500002248903002c410f16004080e1a480380540d41102d4055045140150079a02c071039007810101c0691000e41003c1c19400120513024080990083c0307094283d03a4002061283c1c584120702c1010750100d04850101418003c071500e00380800c80068441c001202c2c00e2880e54032100105c5030400d40308500042e1800c01b042503401f11030409018044040d02c064503807107140d01c9001041e03401f402c10400403805040407980f035406500c46a41e0041c401c2c0140c6030240484001410b01341c104 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 349141969 1250 349140719 349140731
    0xe062d0a05060a062613080d05010807060207260a0c0f0905011a030402010c050f030c01020d180c09020f12131109060a030f0f0605071101150f0b160c08031c 69
    0x144005d00362941c903035050200491556035242c0d5400300100034048020002240041e02141500381030300598140c40c10102940c0c4120741d203403016a540d06262040e0010714484000000400c8020856409081c4640c015110701d00700356907400c010108550049480c083c0d01d201c0c01c3c000700e01940300c0e160140c11010f1002013810504c0c80f119020307000c000d000a0401580280c4001000000e02c00740d00581a201e0450b61030f94003040030760303000c1c2d0084501d225202c0d141115002e401040b5803602440c20350086c0c030101065007803180c104082c1d444011040322014080100390420410f1035540d920443c14002140540311562a00401079034405020511829008003400400c1c0d5400c0c134417004603a80304031264907010882c989062007a0381c0003c06004140341c40100310a1640050721064200740e800020001042c04006151403032245001d01170383c450f454030342480300b004568020b18000f100740e441a200c08500d0754894003241c000307400021050b0004101c100394891110161411124804000d000e5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 349143219 1250 349141969 349141997
    0x90703030c111219020324010e0903071205070209250e1809010b121506010e0301020c0106030525030809010806130c05120a0e062d0a05060a06 63
    0x7807400041c001e005020b40c10222903650795a1110120104402c000b81d0f00da0740d1500507034040c03002000900764001d000c0d03007203000c07900c0a82d940c401050f0005201001d403141d007401c2181003d6140106034100780d100800450000c201a0041050160142d5039500e0380c8020078818071403030b11800f50000810000c0e020034030b204004208509071a0784450b1a0001c0014000c0c070000381d002400c2810503901c08a038005002c00004190020640403400f51225001103d12a02a598440030301a149010301100c0010030721070340c40b178282441d1100000700050f0030700c00030300d034240e007182c60503481199554801e20b1243d0300c456510566100701114003d031000c1592039900d0f45d01144c4078504000b410801e9090000b40142c0d5840c05000c1c500b6a9001c08201c00403c00b103019280e5131114014180030501200007410ba02c50600a0345607040310304024118a4540344454000e801524140c12248400e41a102c9542c00c002c1d20b00b10b11521503650045124101700041c440603c6c0a0b4101d00100002d40c048064 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 349144469 1250 349143219 349143227
    0x207110103020310032a050108070203031f03120905040c02010c0804080703050708161e02030a0b0601091508041707020108042a06020604030206090d0e011202131d09070303 76
    0x2444002820056901da48090320103244500a4200038400e840503209100c40303850b98204e00300c288140f1500298440d40745c3d001541c5040003100c1c250010303401040040d140e010008640200c210026043d020341035100e50742e0211005170407008000051142d0700802c410702d818000d01066085a000800800c03d400c8001810404001c0c40600300d451300085c10010184110102c402c031030b8010001a0b02e803500040c0b1940d6149103010705444920078421002e01c1c02414000c5801400d500234018400c1040030f98400e981c2450007404941030003000a40040c41c0f51810809001030720880c1c0c3d5445003480c0a20300314011058882e0040d80c0c02109001030700060360045001500103401020100c1a205002609a20309288169962042d1022a800100e21303400081550140344281c0950f205c90743c0e10a04030307a40300001281040060408491407800d035004021f40e00503501d0009000d407078010080c211880c0350a141e800701114150440700c80305806286001140c11a910300d000d01a507900d1520024 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 349145719 1250 349144469 349144493
    0x5090d1e02030f091302070506070f1701030f0f05010204270905031b07030501090308011410020d0311040e0124091203030b19090203011503060e04030e2407150207 72
    0x2101000c000139030b404581d07507078040048410007251020b640d0307907480349407040d2100001e42e140804038480500090007213010b0100155011510720703014165070f1940d20b9618003001111415034640305101c1801010840c20b00090002d000403814155100080305182c11305500c009101340c0d02c240c03401d41c1150000e030b0088200d1b8038200d160300381d010724800010750141c2045080d5000502640c80d2841b240109074104400314100e603950305080c100920131030f061212200e119111000140c018403240045079000e0740c0518901160502c6072810551905a0b41036504400c2c8c0054142410602d0b042c11103640114483d80501e10902e44100300038030302122104010f000420050034141c41c2d0402c1c00740d03a21042d41c2500082c41c10910040070590780d14030800250b10038041c480d2a0000320040e00c03c913034040e0003500111507001d10404059038031910708854025200407281e0b0710103203401d540044070340740e110180119034104c02141d40c0e848035484c2014907400b401d900e4440741c41c0103020350300101301104024 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 349146969 1250 349145719 349145737
    0x90a05030313060c05032b050903071a0c0d0905060610020a0c05010c24090303061406070230010b0a090504020d030f0201060f031b0506040513020a05090405090d1e0203 74
    0x100d40b80c021340d180c2103056010b002c0030408803d00d49030403c203040c216041d00c540410344107182008551690780c00c2a8892180d6000584a05240705900383c0c3c911511100c2503000c42c0b000c0d10542001061b10142051321b900910030798496001c04240700305460300302220300b0300c544240000d11b1040c1113513541d055461071501c0758906103c0912884024803200816070408550410003419001c5410030001c0014030101005400003441c0402c080381b03440000c10f100c40c20240050001e4240196a8204004001104440c2e004800d4440440141c01500700801c003004255038000701c1c1c102d01030400d21031000055405030110a00f404c1c24031000d0380380c03004031034041501803a003460001c240c40820707409403c1c558000c60440c1070624000041c0005001480e0540100204420b041ca695108005160042d40a010362001c0d071010600d41c103220b1030f401050550003508102d414254900001000c640d401c66000030950442110310788001e910003040742c0f0322400704100485052043d40000d541e8000c020b44 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 349148219 1250 349146969 349146977
    0x11a0c1c020a02040f05091e0c120307020a0308120f011503020c0a0519051e060606180a0b040305010e060910020a031413050601150c02010302030403030b0411090a0503031306 77
    0xc1056024400e002000b03280350054014001141c07040d0810000309001c86107000300d4050040482401c44443c2c4240508070350320002403036400107441c10032944e156107010700312440c401003003a280140c4035180c00b40000d601808015440300b03001d424407a2806001030401c680281e00e030005000166400f10410105d00f080d240c01a200d0110403041d070319018805001424078802c103039a169410030300017419640f0034070410607030359440c01c0e00820605800001801124903000040000d4090626901620307a2000d4152101d20407030b0b596010824101b00c5401040400e0f0000806105006003409a5062100450300821140c90600304440e101c00ca052503140000c0d400007100f10609110b43c01c00f00100f8070003032204846040180100b00018448141200c05029103000025641582e01000c00744220700e81700c81c140c119060f80110000e50004004400f0300d542c40303010711203903203441c8911841428941c500d41c0da2212001c04010510358580d0003035110381c1c001c1000319083c8603000c0e1f20f44102c030180d0030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 349149469 1250 349148219 349148263
    0xc0f03032703021b040b1915020105011d0601020a0c14040b012c06091302210412030507030f02071104060f1409090111031006030507080c0304031101021b06011a0c 72
    0x1300040117440e07030082c099030005802e0b8030b40707d864860800b0242250407030740b1000b06820070804241d003681c400340b0a541c0840d032040b4408604040380010242e1245d0144140c45004001e41c0c0c0300140200c0c20742109103000354084203040c20b82042c0c49010780400d424206016102c0303082c0300d414003042d1807045101c4540c0e01400a1092922403c00ba201c1e8088018103500e900702c0080c1e445d1009401050000160640b20350b5000075400c208843d030b0f802903400800ba0680d90b202c00c4c6091303001c1c28001d00721400701540c5050395921411301d03102422685118a942000201141c2c0030070040c0c803100d070001034410700929402c212032144101d03060110f4206030b51259840e80c0e1012180c0c014027030204140b2411304004108807004000c01b228206482860300c0c10800c50b21605000c440565044039900051070080002c00c01280c043d07018110101070300d00000d4908038103622220018401c808030412141d0103200140803c2141203007515045000600701e501b0614180800c1d56140882c00420001e151000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 349150719 1250 349149469 349149523
    0x8010e24060c0d02061b09240403060e0c0301111c1a04090305030103060c02010506060702010c061116050106090209030a0201050c03070803150f12100c0c0f0303270302 74
    0x7016101c0402410095541c03031682507030069140c1108542c10014500c0003055580303040e4503003050b41d01c4100041c3c03880480400084124119007a04214860310f82024400000000c466000d910708000124000c2d125903d044401d240c02e4425900400140e120140700310600880e500c009841c1c080c03948440030401a060700d40f0403e8102c2030000d03141d085801d1440390300516070840000c604a03442000b00f0051298419401c81c00c0740d0042d500907038806020018800598401d5034484e01075070144070300060351034010b01100d0450f4000d0400601ca0300300c550f10071050182c203210307400c0101209103054ac5011600b00010791101a1746500034140301c4045454021014200142e40e4160f6100d0121581c074188140c69501008030501030a100c0e583c29080005182000e10710710780c50842e4000100a03040792088101c0141100242072010007000c04000004151043c3c0444a21402501d00207400b000a0314100c045110102d4600341d0055101a0390000940c002820710f0505403540c0081c03081c00b529 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 349151969 1250 349150719 349150729
    0xe041a10030905071502071203020327130c020f150604021e0301060306050405220b1e0f0109060e07080c0307030906091101030b01090506161b120308010e24 69
    0x78001400c1032013000e0020a02c00005400d14150554540866150707950b500815654803c0e00f840040040e00103001e200b6200d00f40b00440085508010625035a207504040415505549405070305001916400440c9800360188010741c101501d2401078100c00c04803900c40781c41ca83d8040d242c2801940c1c00205d1450007003044401b200a0410400100da413942d5982d030082c0034005601806103c1d81c5800045800d02261030148060692203d598458140c5540c9850740350b040000e00f40030300443c110400980c0c840c0d1407060075110b4865002c0340411541001c10481c200d400d0350b00300d16401c0243e0802c1c0300e0515000b868295112a41107407240c2d40e0307503402c0021405441c83c00d600400300c40c02c080b841c404002104101801364142a0307000c1050769490001115052200c0c881c494100d80c041010040021030600000e00c100d00908898500806001512000039015032100c00b200e16058031403801c15034025a21713401010340380c0110300c03075085c059075050808803900020b0800c1c0355142c034110071540751 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 349153219 1250 349151969 349151981
    0xc0102070b0a1e230301061b020112090605100608010617060102010603080705100f0501061403040c050d050703050d05120708040515070909060b1810030f02040f060e041a1003 77
    0x92460034190b54044540040c000c1c800384c4180342d0310380f0101d000e01401c414010b02076034101c07101c40c3d0701e0300701e80c0c40e40540c500c6c107501c152441079040082c1100c244000121130b028410a0b2840307400001405c0c41e11091801c142c44c6135401c120200b203440d81c010003200e98880d010424620b00300b44601e0f200e44800005030700405582e4002480c0340e80c04140c0c802403000105010000c4510708006100000c0c0203140d2074125031007401010003040354074404140b201001c00243d0b600c00d200381414110700c1d48401c00070f134840c124014100d4940d80036036000e10400ca41402080400d001d14141141020449001c80e003503440e00600c940204405100000d0070700608020051042801695184050501b81d20040c0580d90a024105020b42441400202018110221031880403000750140b503010121040004003501003c03031030704041c0c031106031260b000000d10080008109443c07090002c02c1c604400900300d00402a0301c248100e203411010603070b0300c40411540056050440307984008450080c0c0c25402410703 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 349154469 1250 349153219 349153247
    0x305041e05130c171006030c0e030a0f03090f0e040602030c160b1005010c0807081b2e0b0904240501080109031b031e210b120c0102070b0a 61
    0x1400c01002c0a00401d96000b007001d41e085a0711405810440c1c3c1e2082011002512280c1d07180d00d02c45010003019129512200070304d001403030b281152443c050002803529094940a5800320441c610020825030032080f2140108503030910b10301c00525004a103260100c00400c040c00f107a40020005508000401c119074100c04280c080002c9910242007950800c10100c1d051114038445100205040d800b4508003180c0f260b000c8841c1d840c10409a451004d10b0300300e81016018003155110003504e0210901c40e043c0740354000002d5041c09203c8400c40e05519110804025026103800301e00c2c0320940320b900342c956015070480d0f80002012a03004800c82c000348507842c1101014a41000812002010740042c95054003d56403002a800b00f411110190318018a0043c0400d190981c20304070000c450201c0b404542060070044c403610b00c6110300c440a006001500c107141035450201200d1494680480f22250000340001e04000030301100103590345d100c501608141c880c0200b0300ca44100c0c410310b01448482 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 349155719 1250 349154469 349154479
    0xa0305130b12010e130803160201150b0c01110906070201030b0a09090c050901170604060e0a02040f0c0801092708041d0702060717043c030e030a0305041e05 69
    0x8006168080355502c082c018212050520380c08a0520651060140c41d80d6030004000713441c50300d0b1001301403581054a40c0034800d5540365040c0c48c520006405400d030041c1881d0a480e65208035800590f801c5030031401c2d00d07540f1032009000c1840c158441c40305075040c265083c04d00043c54441c1c0d50010300380070050f0340071074440350070900c60760300300f02c0d008940348201e43d01982e0822860f40c84084082c00080f0a59142c6070651041000901040ca01c0c0c000d1904900070b00e0503284040916004038094a0200c800883c0650300e4186241907150300015880c0140a602802c01142c00c201a0b039480803c0e84c2c20045501420710354400c42808006021540107207000140e0141d4080600300e90100d01e0030854811004d03014080025400c00d000d4007040b10404104901d503032240c0e69035601c2d0604260b004003210300c1054004180306542c503650f070020b00c04121a5540c1440180a031030010801c0c0d18071600c0714001e0300700040704000a50003200b40c4007964000300345040e0800305200d6640340a952984141d0b484 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 349156969 1250 349155719 349155727
    0x603070306080f3f0703031116110f0901060e12010e0c0a140a0501050307120c020f101a040209060d09030306050a3503072415080a0305130b 62
    0xb51800103810900c0180c112401c4c2484401d4aa070540c84c540c40b40041640615001c1115040c0c4030180007400c0d8207109080000d8000c407281400ca4960300280c82c80a00040d07241000340502c41041200751640408075100d418500249012039580302d0184030761803c0c0314001a04a466944070240012500c40341c00007001500c82c214541652012500b000901800f0081d00101e0841031340c4800e1203500d0000341c03600160070329107001100e207540700429031410042d178840485122845030040c800d50000b0350f4010010500b8070b400c00c90802c140c011150300c0c01f40c5468104250480300f550018443d40d0200c8005840740d101e02c020500c01d12400b0750a0400c245408025802c16030103034408400e65505503840c040140d11119021009a03240c0200c2c055001c80c07244103e00c02250403a000c8400910324141ca0401650f6a108408940c44040c0d903400c02011600b401d045461510a450b03198003641d610b1042c5030305e444c582030b4441d007406801a08001e40059440d0350701c203804901c05c00a1075004210303580c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 349158219 1250 349156969 349156993
    0x50409150f090215040e06010f0203040315230601091d0a0504080c070b0d05060f091b0d06030b090c030106030b040b0603034f06031e05040f0b071805060307030608 72
    0x20b00d5115001d6406c1c2000c400011603065446074600702d44115242d00158506815521082c402d1903a00074001c5c3c003d5212658034128036421040581231194074109101141003c00015203014595007140d03d04440441c4a034904864900e0100e800a400910020b5980c603241071030a000d2096090418592080f00300c0015500c80e00802400c1e008a03941d410015a2a4070301002111001c980c01d1561115601001c1417070f00360046201000b42c5007900c105071411145000700343c00d49210780c1c01941d254081004010081c04203104c1a002c5850803002003041c0c80c1140ea4040705244040e1010307000b03444000c0011382584080003129040307070f204041c170708400c689400c60085030b0500000d4079000400d50303a0840d00700c10f0507042c4010b88542d54400190210309282d8210020451a0707000b05040710890306042292085101d820700490048183c07107000d10082c20b012486400141c80d801c1000400d540030169900609250f40507200d0440d00710b650b81d00c41c6ea0b41140540300d01e4105494501070000c000724 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 349159469 1250 349158219 349158259
    0x90812070513080607050a030b0a0302130209010909020325113f16030c060504050105071103041404090602090405181e030403140a0b071701050409150f0902 69
    0x4004039428007440300e6510760b10b003c0d0b1514015540c03140880c40920010000c1ca000c1c0d0024101c0c04009400341070510340e25000030b0210142285214000b56000400700529648010107001404e152882549107040c1403122420011000c0c40017626012140c89000c445031181140e01d03541928074003154131598030140c41c0080d51071441d855895030f000030326125095444d040a42c0b6011040185524105a0140a209400d0341914030841c10041c242c004140015814130807940100d000e10300018140c501034a01070803100128130890095842400100021b4100a080a5298109480100f0b121049107041c501a0044c0d9000640c020704101c1008502050701c2039000c00ea903600821aa0f00d200144200c2d1400340007a98070700240c5c1c10810043c40868074505a4405d811038010440c2c00c050b805865a508a640507119100065240003502c6003140350b81503100d000d003808583c108001072165a50900081402450304c1c1c5c05501e9011b00301e4041d83e00d178400c02c1200e07000340c09004007a0307820403880 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 349160719 1250 349159469 349159477
    0x3190603050d030e0c030c090603070902073903030c06090605090604020306061c0206070c0b0c0102090a0b180f03011e020705070806010e040b0c0d0e0307062d0908120705 75
    0xb00041c2c0380001d00b0400000010f042d040e0001c02602420446004005021443c0002403d0b07070341500ca08040025111442e2008100c800d01403840c2c01b008035030301802101908141c2d007030b03804940b66019031031000c1036909401400b100c0c1d15040c00c00701105603140000c0503010f20300c4e0140c0028901401c20501050100309240b003030344202e068843c6551014104607074140310780790504008007030038541c01c01803d20714018655035020340f00c042340f00c69407244294003680c0311072100445650041920034440c203040d08030380c01034034101c00aa42000540040440f244405404261290580ca80e2402d60b0343c40c00e5001c281e200d84011f004241000041852101075030041d0170841e0740d8418001c000404480100d4920705880c1407541c074007020f40311621100b0807000081d0141e10301410401c001c0340b00c000c03980325a0050110b050091034455030507040081c102c5465424512550074494001c810b507000700d6107486401d40521000140343d104504005641d4001c02ea10056408098030074020b40541040c090 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 349161969 1250 349160719 349160743
    0x6030c1404140c07240623030a210306090e0d08011203020a0f08130f032109060315051c02100903080a0e190308030a0e0f03040b0319060305 62
    0x34007404542c1041050911021109075a4500e024052100090b041030f10072800c02e030703100310120501101040102c08032806548114504002203680f04e8214182c04541c01e0b1009084028191014003512804c14130044082c4114007054103040040c4101d020f54001800390100c01c20070045c0300390304008241e82c0c8042400c60408200c85000008580107841090404980e15034090b1580c002e00399a800c0c045200403904032210401401030811300c0c04c074808800024103901001c049141c1c59810610001c06a4042d6240d110071a001030310052a04181c01c40e04030740305440e0001d0003000840300c14a0441d140d070004c1c0d5215604452248208501d915410090b900072903103520302143c10301c001e44415400f0321008004041c14040d440d442401000b0b01840c00d0800f030310414403071030308030300308200c041280c1c00c200d408000100c240809803005105145040400500070600c0070460250103030b44e4061441407040e9150000002040c03580048003120b1150b14803401442816143e02e072141d1258140d40b00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 349163219 1250 349161969 349161971
    0x30105041d06010303120e0a020a062016092f03060301020c0f0d03060b070f02010513080d030c11010618050c0c0a0503090405070c02090412030b0d060b040e030309060c0c0106030c1404 81
    0x50050b000401050407032031549e000300910551403400c40160340c006425144845005906a480c600c1c18105000040f20300c1d440702072100f042410311061804507503031b03041002601b0010310042a80080583e02c0c07200700c0c20070500c0080d00c0f5503c031000240a4850000d48080b03030701504440703400074240065840d001300041d841c01d21403140c4880e1900018058500085c142040000140000d540100c00802051500b907420001035600c42d4a0715141a414804840000e651601d038080f10f1544403140341d0445100a002303125462500748419140501101c1c29800740365140046141000300c4000c0f26500c08030340c010303070b94180c031f15042c01a00c9405c4415958010340c240350018103040c2c4564506084d2950082604509071520303283c82107095071300400d52081c1569000304491070359400c6000c0540c18403a140214544144505010540700941c401e244164418411b103e882c3d80085510340d4416014030030fa5441d00c0800008501608190340040c12110751341e88041003440b110715410a2501c010b0310 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 349164469 1250 349163219 349163231
    0xf131a0108041e08070803090309040f0b0604051201020c12130602010c12020c10020f070204061202030d0f0e090103121b170a02010f020c1f0b06030105041d0601030312 74
    0x10054521190803900100303040c02000e9441105090422580030950103032413090f0811a01c3c0da01d4409030f0303006482403403441c2d1000c50702c0b214074981030261164036000001c0c140b203001765001c0482d1043c000c6000b001d1086201178040c101c400b10941c1078a01e070140c1d210881d44040b00718001108036500154090b440b5040382e480c013080041c014002c0207c495181d6441e40b20314000e010308000290002c1c500900940542d01e85840150268006000702503c41c1c08182d5403421640304002c01c1300e00d00e5009841c8091001081400b681d00443d11a281845d541050b00300c903268050110380151000c4095540141d603200088203011844038402c01094858440c0212a180c8645d40e1004a0900400a1080c0d00c01c84101048201d00e0010b040049400e000101e00b20500328a8030b010390f000710010000070751200d002ca40f03082181d07500401412800c0c030401c2106c0500788011030524441405158000e40c1c0fa590885020302d5804024110003114800b545c025503140d2800400c044c9109012170f1a00781024 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 349165719 1250 349164469 349164521
    0x5030309040c172d010812031e0708150301051006050f040801020708090a140d03030f181103060c1201030807150c030501170d0503160323060114270f13 67
    0x4600c13103050f04d44003002410590160408a4015840103000308250003d028161881d045120754847c040c00e40c940398100203180549405015120120380c0d9031213a81800b0078050343d500083c961000faa08146002c540d1041c490140315490301c11907100f0010b642c030000c0c2242c140241c0701d014240c084401c48180a48550315212041d10812404000707074042101e24540c00043d00961009111120001010624003850849541100d144d48801d0300c03400480707040c8056519091000d990320000c000c0f80380d41040c03c04015400d6034801400024004c14001802c00248003100000380c6401c4d07079800d002d0100520280004001d89020301c40c03d032009444001c1d15250007400f0404c001540003564405082d581c611241e030b1415031000400300d050554a4102020040c4200d0a07400c0c00758550102c2406820410001070980a034007040c0c0c1079807034017404480c10f00c403100c4040b565002c690815400190488800152259090204040d1b1000d01c81080040603030194008002c0710440c601142d140103045 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 349166969 1250 349165719 349165801
    0x3040b040215071509020a0503010608061e01060f050a020309042c07050d1e0c290f1902010b0a080109170a050301051009050310020909070905030309040c17 69
    0xc0f04010800d01a00c0a40352060895521807500f442c0010007002c42c0c00da50303070003007800c469180e0800800c0e0b03048007041003182e80d1940e000305c403089420003442405614045004014010103c018820008000b640006142c42003041c1ca1034508018801c1050030b520501da0514410300705090348008240041d641040039011460200312070008c0c1050503070300410758814401c44c04100c80080c0000501c180c2c4004107010541d00c90140940055000703109140010f00c2d0091180450004005c4104001b075030400000403007901c00c0c1d0070340c1040b00001514140c0c0180e025103905800d150b080040e003640020802015000a403150b4040c0000002d040d042c07040700d40e098414a125034000c07032000c1004111a0070101c00381000001185040702e03c0715214000642803803a0103000220098001c0b551a01901d4550300e030130341182d4103080040c420741c58803022a0310b9000315013940c3e201c1e0f5500c183d20068a401002c0b00c2c00c2075810603080078031030324196883c0980310410000b441800340c130001c5014100880 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 349168219 1250 349166969 349166977
    0xe030a08070f031a0411070f1103060a0606020a0807081c020d0b03012003130501050403050301170d1e02030c0a0606080d0503090304090b010c121e14030114040b030303040b040215 79
    0x6048074100800c4c10b1113080c0005407000305545004071000704015804143c11958021015109602c640340401081080500e864030240094002d145000c0d0100101a0001405c9000c03603846500907071105150f042a81d400d00500e215000180d0500070500720694650340240035071502c0c2c1c4020016064040c05140c00c8a0300044800343c201e410801c510403002c0c03050003469000c8103540300003018102c503659590a5400542d012400300e0030120052000350311400d032600346000c440000f0012601500c0c0000e200030010007140050f5070550000380c030741c24802c1c011902490140c4003200c901ca44540b402400500142c41840c40c41c2c0101d41c0780c2200e4511a80c101d80c0103604c421300440c242070404000038020716807009150306100030b42510340e000404405005220120f036403100811040d0000244150461190280e010804074070780c2907403001261403c0c3c078195844a200300d0104004880454001c203504011640d051001204110030010243e130b03181e2045209588070200c05911885c5110540a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 349169469 1250 349168219 349168241
    0x30601120b04061d0c100311270303040b0904050609061f1b0507080d0206060a0b0918040f1101020c0a090b0f0a17071d010501030203040f061107021e0a06120e030a08070f03 76
    0x504219491100c07270080c003184848034009914100c100c0f100760001e85103030f2180e80800c800600c00b003804141e278a031610030302e54002c1058941c844a8584000095400b0700c60724074103801c00e0740101c001c040d09441398021a80b030243c480446116803003142003103940d075005031003050f2551242d045089245440811030600a040241455805034109500c41280d83c1010304038903001038099200800d862051510103001d5401a01121641151800c00049440d030350742c001c0381990303c14076013211540c41d4008808200d40351100c000608005440000d986080d58001e541d40c01590040702040000c405130350070050074003040c01c0321801c03640d0320503007000d10340d65482c2c88010b06520301c010401940650002c5606c03501c40d102540d45600541e880c0070844501c03003840c000014000c01d509046003050402c4117000e05610404000e10745038031000072181c04540c01198200150840501d12180720380c1c120380c1d48000c1d5201a2501c524001c00000c000e00c2007115084005810142004031840c080c0c030070320071924 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 349170719 1250 349169469 349169501
    0x40e011e18151b0e010f030b0a05060f0d02030a020a11060405060a050a02070c08061501031a0103110c06090c090105040504050d0318051207060b030601120b04061d0c1003 75
    0x200316600c490842441000b8003505154540040c201e20198070703107803044100160388461a40c078080d50001048065403503080801e162524110f034981c0e640b040d104000720360f03088500719642e0a0711002102140a183e408519642c004400d200ca42a8607402401c0308070000d41e2213400904010490941c2e80205507005407d9400140101d000110250005940800711070405440c0c0790a0b036603503080800e16940030990319081034091214610610a811049040c246000c0c020180184d4010041c40041040310303040c03559030b801c07228141d914041940c0e5038030100f009441d07840c500b074010981c4a004031160540b01c1e904110010480f803510340b048034003030307a0000003d005070b40384103009030014001c03180201100f544104c42c000005a0801542c811030700c05000c88c1c1d4403441c0764a4003400f0f40e412005064070a402400c01803004031116800200c030542c0000e1440b0b07082d01c580c20104000c110341c54100b040d100e11110345801d90500054000460b0724103036079180d4203001980e000c404541e00186e0b440404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 349171969 1250 349170719 349170761
    0x10f060b18090f0a0c031e0608010b030307080414010e0d05012705191707050708010b040b0931030f080703061a0f0c0f10060b04032d02040e011e 64
    0x1201c03964096400110903040005603003201201100c82482007c051080c6076840d4031060010400030300801d0080b05050307008500785040b9554180e0180a5030060020000159403640074036840751511825000019028600c82c511230304266004e804032241008407445400d00100d005000503c2e040c00c070f1034200b0050074480026a0600703803c6140f44901b41c0b40106501c48bc1c030a240f0700003004002c20341c450070040c01001d2900c07a0190a440102560b0f5124a140c405000b42e6511040640d5901c00e50041502c001a1918038003040320030651002c110411072500d46030002c168110900e05074030461a02d54225075912034a0031016180140030750030400c0c81c981c90248900340100c01601003c1441e006150034000c5000c481403920a044402c005150700a0090782c4010220340f00d1032000c0c01000c00c12620780350031034480e00c3c000020a6103040b4602000c0344104582201c0c0c28010461950081080c06034400400905000c0c107503128020118003100d00000100c40b400348500f40ca4081a03aa0303450700 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 349173219 1250 349171969 349171981
    0x609060a0302241b1203040b19020d060603090b100b0406030e0309120601031a1608041505071d0a031703040c080a03050316050c060a0e010f060b18090f 67
    0x15441c18402d40c040c410401c0314203c950421100150801c3d1440300050b90943c0b42100700c00d031600803038050320304600301c00b0802c0c170004c00d0180f005164046880026101d00c0c260700d4003900c0c009c0c0b00e03245030403034000c0c0b81c054086101503140d0410121140120241a0310b070311590b18103160204584a1103402c1d180411003005010f0081c0c03c10726001c2d000d407003500d0800c4022404581c004405c10482a081c0d080b1200500070484040b0b02c9040d11801043e020742e051070583e17412260701503101011024072030401d000804000242008a000b80d82d000300030300c414104000050140440e009003655000300310984034200341019100f180c04c6035004803420480c810072240c142e000d5400500152846030035004040354003c01086641440392081d41c1741680d03440c0031200d00200c0725940300b00340c00700070041020f0034950000048194106280a00000e9201e01e0781c08914014120041d80c1c4610704d04200002520000c200b014011140000381c9030781101814408200400200720b40382003109e1103600100d49 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 349174469 1250 349173219 349173229
    0x3010305030304200d03121d030a11060403020a24020c0615010c0302031e0403081201060e0a241115040606060c0b04030e1305040b06040b010207060905010c080d0c05070b0609060a0302 81
    0x514805040e00007c0c82365601c41c0303105030f42503049110189580300040c011a9a54081031202c00d62554001034195400c007660b0083d243c0b00c107543c016090881906061480200c0844441c0040c82402d10856441e881340e5a05901c0c3c01c008c540702c4a07070b082c003032100c031380c01e035014071b500c040d150f6810303400340d440c0400d90600b000695074203200e9210f002d4010b00c404070024640000500600354112038030641303907150041c000d110440c04a4002d0207200c01c2d001c1008001c00c0d40401c1e840e00305001e410b01070b054140d0130302180c00b000c2003240045d20303114100c0012410311104618a0049000d45400c1c090181c80d080203441aa0105400410320402c02000501091088250603150440103002d0401c0c0e40041301d51000703680c01541c003030713880180c4142030000300d241c17904c5006545d59080c006080064603240001d03228114510605060041160103502040324040450b405080448410425101000ca004106400100c0b0440e48684201c012030712a08c4c1000c6aa03218400007050200150308550a04c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 349175719 1250 349174469 349174487
    0x30605190207081e0412020f01120f0b0f03010c0e2101090c0501030f060302090601030e0c15121008030912150103080c0d0804020f0603041703010305030304200d03 72
    0x20409642015461440c000398001005080d008961854850540d100c503d0200d100d02c0741100f940c034808100c1007100420f00c00801640c5a01125414007010740040161680842540070b400380500d04110745034000307040d6200c0584010305441300c0000c86262800c0c1401c841042c40c56801180f060708040f109451f0000b80d484021107104108000b20036944603503801c2d10044d410454094014a01c00e00884d41e051040300c1e0319a007803900600ca29032a580200e400203c1c040d090307504050300e0701c0134031800140410100c100b010010f001540d042041e000e00f1229034014120494201e0319040114040004010814060318240030141d441d140c80c65003084840c1005000600c034a0007079804402400b01c502c2d11141c02140902c007401e99800c1400b910074104030929084a06202c608010b07c005a00c4e241c403001e00441080e56060703a01c1d151410400030104040c1031058850348004008400c101021000d140214800c0c80d0401d00381e41ca00c445a00884103041d007241d0001946035154020034410b040074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 349176969 1250 349175719 349175731
    0x200105150f06040918060606021b010c030c32100c02071406030406060306020d09060f0606090e04140316020307090e06041709131508062215050f091b0a030605 70
    0x3030b05031704490f82e40d441c4c290b5000707500c12009a000958101d24200060282c0c419000702440c004e00d0a042950b0b001d04040d240ca68044c01441240001604807498041004070070107041500e52652008552550b60b0b0b806210f802c00c4200381440918035405000149078803e41d0603104901c46400d070800180040c0c0d410062081e24040d445000005c04990184018400004601703000700d0304804506000017611440f11a4190705883e11301c04000712030b40a040e45c0240c40d030003103198641e81c990341814000070030010743c01318540c00006480003080041e4401800094401ea040d10282c6584290190071114440b207680825082000007a000416082c000d1110702000b0380014107104140020815504400e0f2081d6002c07a07850515508038644250900004e00d05080145814a404520403001f402c0c1c82940c0000115502c81c041c0c10014120300301440b5856000c41000103151072421075216880940d0012514020b04c0c00503500341c0141a41e4004140b0050701c1d1f01051481e6030782e41c40081c20000d001c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 349178219 1250 349176969 349177001
    0x7080403030b060a0806101409060304061b02070e0a06050906190812070213060803091306120b0a1b0819240e0f040314030601200105150f060409 64
    0x10310301c400c0c1d882c1c1020348a0b0b1001d541e922003030b0b89441e005100c001e01500d050072023400f0321a02490b04213400d100c00c41e4071001042d6a203a88903103503441d100c40a0000070402402c03000f0107a011a001a900140006c1222085489003805464404680f0100c41150040ca90000c040400080107800c04598105003190341c1180c8486040d03440c24040e007080901580e0104240000032030f10254a4110f50800f821080d986003000840e14028a1030b80c0c0b48038289110707002e00320045c60008601402e40c0410300806070444006003003486031070543d2440800301c8401c03a040e403501003504400651180450300c01e4460703031140340c030035140c03d140c020350510740d60725a902c0d10fa11080c401c0c81d003442c094010f96840070b100e10700030075103800c1a03031000907030b02e0060401c5000d03c070100030080031a40c00b0840a6081d503004145680d66101c2c100100c480f1061116005003003021181c0c039800f400d40560195101e46d071140219207200c50345e10308002040303c0e80040d19a0142c41808180b1000103a0780c0300038416540010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 349179469 1250 349178219 349178231
    0x1608031602120706030c170f0f1e09030714030a0c020120010603050c032401060f0504090c020c010f0e063705120601050a1d03010608030c010222030b0708040303 71
    0x482883d28085402510002c2c1e104c80450305100e420481d0740304840c0940c1c0d912040c42c078014800482e00040201134643c00120000481c1d225048501c5480f400302c440c000c184098688200c0243d40c2c1e52080400f01d8003c5c2003104045040c4501000342d91000c0c00b641d855040103001a001100c4040c0400000b810f9070340040d0320a00549000d2094200039803081020340901c84020042504124404203c144101500c4200981912004514505451042c00d10030b801001c401400c603198059a000b88100c1441d0070390140c580340e00080c1c00300100c0d0702641d404403044d0012400311000032841d0100d40d044030081c040000c0100600e5982e003906090000c40b00c0c1401010000d64040380000c204c03042c0420170000b10b24400031583da200075400a42800c225143c4403000c80000c042c61900c0c9a10741c8041a102e58038400c0d40c0d420b4102c040100b031070404894480300c003444002c1c002d5110a0442d80b0601c45a85190303d51610758110314202d030703000481ea098a55980c80191604a8002c1c0120100740d0b03111 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 349180719 1250 349179469 349179499
    0x504030203130f050f1c03050a09030b0708040b01090c090603110f030c0d06050114030a020a030605190602010e0c0a1a0403020901150f0305040b0a0c050409050f091608031602 77
    0x294018004028508020181c2807414050011001259003403c5c06108184680424581754101b10b511055251401c555035180341c0d802190171000e540c20040a0f031000005000f004c5600c40d840a0280c1e02503014501c07a80d80c4c0d0f0241101722000d0500d040c001c41c84001d000c002c424080d601c0107c95840e0401124034254a074400c0b01c409178011200701000c150089401e640d101064480c08000d803000b030801948c01c0030100400541d5000c0102030052180d00013829200c0c00d0300c6900282c00800c4003410741c04054000b00e02000d402ca006004a40c010740c030745102804074140c0041c168549050252500101c6403c2c14820420a040c00400c40c9040d10704220003c0184c07545043d0030b00030070440901141e421f141510041800c11348101443c1014101400c1c0004912204007050300205001000244845906da09490a01840d4000d1100c245480104028661005031480c881c0300407500355401c3d040b5402d41820001018010581d440d48140080fa8100500400b1446001d000414030350b080c003040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 349181969 1250 349180719 349180747
    0x111203040305101b0212030a0504080d14090d080f0430021c0c0c1503061706060f0d030c0605070509030307060b043213050601031a01060c030f030504030203 69
    0x18030030407282d80c2e0304c0e00e9003044003048445503120060244042c1c00640e07500075043c0f01c98000903003034a02d011350f01e001090402240348104c5200b80d4043d1028082d8021107018111901c804440107501800381e840c0e0804442c2c40307400000d10812814441d8541510745407100354a1003044032a5078116250118042011242d0f88410205400180e0041c284101d100c02c0121101024804040901802c0440b010005815030a510250343c46001c00400c10640c285048000d011258400c0240280c0909094110800854a18031400003a551a80403050300c1050020728075070307540040e0008460740702c01c000289035a0441500441c05161040c2000741100000382194066041142d0701981c0c1c00d070034504c40c10b0902400303186841034801012415850110b01050b100c4e1000c001b0311525036400020b400762107440c5070800c0580c100f002c48400e50303102c1c900444054980307001c20a8021010000041c030301d1003954050b06290b80341c0d03100b94004c810160b0235000b905000c1c008130298002840120002006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 349183219 1250 349181969 349181983
    0xa1a030c0d0b060f090f01031205030c0922090b040203060117060c071109010806070206241210090507060e0d1505060d060f0f0e010605090105090a020d050f04060e010603111203040305 81
    0x280c03046ca025254511b24050381c44040d15034206007480400d03c01c100451b0b048000b91032090700c05803010400030007842c100501c40c00c42c8080072507410345040c02110521149140b5144a05c1c8241d04991060745c0711140162141310212005000368031150004604c0560311000d446030f24825441c800d400440f036400200051403d0700201031940c001d00030019000d904101d0b8640000310098030010707203240309e0041c0080d1071140044501038540c0000e1030b070461504100c59002201e010400700001441d91030400c3e1101818030030040003402c1c0d690080854030308450703003106041d405001210f440034005440809454018940342e44180203a80b403201040b003a0003660b5000c0b450076030004403124142003110031165540c8e00707081242e01d03003582404643c440c0000700741500d0045a044050360382d98849030f806032040480d0b0702d943d40c0c2000240220001c0140c1c80c50b0060b445150180440800c0c40c108a00b212454400031b03007001c0f144681e805e25401e015080b140010020f009032460107869840711403070185 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 349184469 1250 349183219 349183231
    0x80304120606030609200d03050f130803180a081504020f01050c010e0f010c0203070f03030b0607050d0305010303030617061605090603040c030506011508070e01030e060a1a030c0d0b060f09 83
    0x26400c1b021001c0c071140300c0325000341c17080f109001c0b540c400f503c004002d400f5031031000502017400180303025240f025680d2200103118204c02c0b40d80da542501e4070707460000c000d12001e5004549030507000c5949440851a002c052070f1003600781e41940e0b0740c1c0e02045500040540443c1c1484000c0140b00c0c00564207024400440c00c1f0000245526402000550b003114681d100b45811504140070b1040000c6091460803050b0750545008624000c1000001d0300511901400030054454001e0071141550550042812240603440410020383c1c2d0302c04462403042e00a81c2c8403415080400040d074070403d10384080c0d10341c141030700d840c5051501c240301140017540295000d48001d86210020400c11408000781c601500101d00c00e1010040e604e14090154480641880b00340002c80102d00c1250340f107588100018582c0b072084030003d050041c1048020017881c200d103140c1680c9240801c20a090000d0b1a0b61420406003ca0b18079136056221000720032405000c9542c080e003240250080396940c81d4440780140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 349185719 1250 349184469 349184483
    0x21801030506010515030f1015030614010f0e0111010b040906050a06090b012309100f02010c14180a0b0c100506100804080913050109020c16080304120606030609 71
    0x15040d814101d10304001640142c0c8103001800d0100da0604242d01500d4011541c51440d0009880d00d401010303181c8042e4100c00c4d0760855031404500320fa581500300f00e08540081d80c408102004000045601c404152011404114078640141d110352103004481e03d030350100c40c0002400040400001d044d1110588203440c05529002440300b190039510405004209002c1c003000449201c00001c1c1c007181410031413425440c815184030100482c1102101e540c000024411210f01d04605000340c89402070303a545c2d4006610b03282c8286059030140b100c0200144610206500780106181e031800d85c0411000705070340000800c3d01c0021410001c402a0041d5018400980107030080c0301d0381780d01143c0009000d5072052045651014000b0742114009821507000b6a030a65076000c4500860522111640d1a1544c03c0c64240001040502980a813600f080038805a035503d9081c1d4500549508050080f02c0568204110400003aa00794000c1480700e03102c0c106c0802c0b05076803502c43c0c00444142c0001a01d0707407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 349186969 1250 349185719 349185721
    0x60302030c0f0a0b070f060c05070b150a1e0f0b07170403020a05010804141606090509040c060c05160306020a0e0301020703080103020103020a02070f150201110408030f160218 77
    0x145424004071449080581e03440712201d20000000d02607034828442c408500b20005410424000711b00d6100c100150080c40602514080c140003c160740d0240c030083d24908100d40104101040100c3d50b90500e1100801e8502c4c40d44c208074622540302c00c419403041c154110510006219880e8401820007001042103858070b4400346c0c2401c11f6024014060005510820441800166108112002615401c0c45c15035155940ca24005400700b0b40940030400d00e00c100019140003c2c54900c040090b281a540c660b62a207940304144444654140e400510f003a42c0b014040c410503100d0f40074010a80e00881c1142d03c0101d0060940c0131501950304251003d41e00020250681e9800c00413442961500340c0c004c41c500031068030001c0c804201800f0007810990002003c200740d6108120b1800501044410f10f960113036199602c1606500994003032002d03500300440705028000035410b80381141c4545010310f18280415422040300d9202016101030011170011400150316540098040e55085281004e01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 349188219 1250 349186969 349186973
    0x280e010e070e09070221070614070e0612150a030c09020901090510050a180503070801020c010b0406080703030c050111190e03010b03070303051303080a12230705030a0605130603 78
    0x62400c040d400d05026850000034010513a90018007100304000035010760070f035003200c05c0c0b0102c002c0c8950392000d4103c40c24401c41c070541ea032144a0042c01092a500c40744d500c079501900780002400350180b05120800b811001031048034541c160b14407004401482201d04903100d41c0c400c01c2403010b6400030062194040383c2080c4c0340d6004078424015000450740301100405a5200034801c3c0b09104e440800c008040c0c0c1070800f03000344001013001800d8003d040c2c84400b900c40145900035001a14040055030030000707956800d052610a400564641c1c80140100d141951016950304058032001ca45940d41d451420700d1020340d80000e09a0f10400c070200c00d6110041600007030411107031406083c032903494a1b481040035600000c0400031260706003000b60b1215003200c4495014101d0381d1014043d29000210880440e502c40b5407120001420041000501c1601d185045c803828031110340c9441c9528400456981da0007a805103511200b580c40203e25140c443d4003050220038901d070302c4d8801d2500c0c0c0f039042c01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 349189469 1250 349188219 349188227
    0x108010b0a0f031b03200406170309010813060624031b0f1806022d07032301060b0d06061403011517040308040b06010c02280e010e07 59
    0x80481045840a41c00ca04048031007941d044548070041950440c00110b5042a070400c0b00b01d40115003051050801100c2000140054201500658440e46c0340900103d452a46115218140c0304c07240000c508105416005640e840320240030b50600303044c03442c40340340000d5642c0510030181c4030640300c2a484405094020518010641131502410f041481041c0201c001d0103004940300580d2400d410464908003041d07030000c031801e1a200220050580c04181c10b500069400c4085210700c1c2e40443e0b2800807200d40704424051205120250400f440810119418161a20001181300160001503108400503801c40700346034480c1000140100c5e490600541da44240002000075080040410100c000c008d60507101c14001c401405031600b4080c8203032031085640e81080100400104240e0274103081c09060703030b00125030803100c20021000055155101d48500e80d46254003410600c4000454000c02001900c614802d074104182c0500010780490a081c1d030600a10a007801f2207020708107110018 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 349190719 1250 349189469 349189481
    0x10807020303060117070509130b120a030537090801050c040303020a0b0c0f03070c0c0f0e13110d080705060108060412050706020f04080c03010b091329040b010801 72
    0x8025900103108000250340c100c1050305611480307140d800b8041c4c1d0781c400180c4841c060440405d8105612000d0340407591029440f2750b0a2020071150555409a07030340c01c980da41c2d410f4440060003d0030500c50b54003500d8000d8450300810b40e602102d90407040010f460140010030442e04980000c407501c03000c010300802886076a40002c000b4484902e4036086440280d5641c4401c50010541c038198000a80c0880507401592401e20001100c241d036070804440003051065108001d60741c10411060015035010740d810010116442d48020010310b59030610b0724804d100d00f4034402d454102c031152861180760303202040c0fa100346102d80320b040d88900385410000c0c5401416000f02d000c590000d024800403074088005110104981d20f0a26a01c001518060000e80980034424802d10b402040200c1c6140340841e041c0c4040f0001d9008000c2c180c145000c000980c032054810360105091040c00c400450300400c0c18502401d03d001080daa0600300c0d081074101d5030000c07a4155206945200140240d05082c0180 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 349191969 1250 349190719 349190731
    0x50313050a080c0d060e01060618080a0308130c090c09030b010807120f0602090405040b06010305090c060405040b0f09070320040501020d120b032a01021b0409020109170a020108 78
    0x4107506007482c2a481d621010f44441a04c1000004044010045079400601e10104804000d01c8920382c0c0e0400079003000b900b6010b020b81d01d505058040340b01c5400052410400341c0640c0c9907000ca480c0c2140d0403031144008030043d10003a07286500400c58021500410902140e241d5a100e400d40ca9820b08221880060f0000c501b00d41010904026003405a03416500254100001c695100700e03915200d4000d04c07415019a400030304080400c8103000c4c11207802e500c2144207803410300c15030303803090b1100d40c0718003042d442030b58401401d0106000c1424290300038412014042c02c01c42d0703416000d02c0001e003410b00899044001075140c0c5200c83d6008580302000314003d00b00003c050a06041c080040d49843c1075101e40010881d00c00c0070090b060761540c21050301d070780340913040e142d00400b00d05c0e45c019000c1c00d0100035204011000c240c41e01c20f51002610503c003002d03c2e50b900c140307004400104000b8103401c000903410000702080104000740444030f003a00005c80080209202e44203480007506052004283e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 349193219 1250 349191969 349191979
    0x1401150c0f0503040906081c03021c0612020907080402030d0809010207060608010e01060503030c06150406090c081f08070504090c05091003050c090c07120504150801081203040804030803061c05031305 88
    0x3207400c060b03448640b03021100d49079040150b1a6980d51000d0358404620800000bc41414820000f9004c401c0320101c1406034001d8400314a660364664080d120140b055070029010340c048000d003c0441d01c100803945e000348402001500e0180b541e00c0c2c11054800703035040038601d655200480c243c001d00034030501006000c290051030a1803040b5a0003516040020308540070340741903c42120032035440740c3c40103026000c1c1001c10401d0580c0310a004041c00c400325608046852141400641c12590307042c200200c4040200510304603061009010292103a0403007241c64032030142010481c1c3da00c50501c1c0d84034075610300d03c0315003061550034a03e15141240700d2850003488503209010030741e03040c0c5046400c4075402c0700c80f00d0742e080c6031401c0881e214410380c0e1001c00c03030080e000034103902c2540c0204518100c4a1300012526030704140ca41d03084091005545c01010140c0812042001801d0380d40910b62240000b030105054007001007003070320a20781e6490300321082d03000020401c5150788802c42071409041c0c1995 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 349194469 1250 349193219 349193233
    0x1203210a150b03100302040203010602011d1c111912031b0c120c0512040503010b03010612030804330e0c031906090c0e01030212011401150c0f050304090608 69
    0x1019003080350764000c481c800200080043c1100011080310401564050000c540d2581c0d0703280024001c1820034a91504894200e00403580c403100002c23a200c814940c0c00c0281085080390500740d4180b16810200c0305180100903048010740c00c1c80014401150103000780f581c5181c5078240040c100c8001030071214203449038400020704da690001000201c194030141a071a011100070098a0954610400400601ca80401010b8421348039014104451054009014441d80c110403d0f082e6a8076000700ca004403203c20510000c00e200e080c1c01c0c0d0b08103019900741c0c42130000101e1050348294102440e040f0141264982c52880303041446140c500000c2d03000600500398280000907190a00382001c0310145481d4484c070340a100840d4001d81e1210f07400100c00b4005642c031203811840240901c403d0b07101d480c3c0b01201b50761032001070040c204660501c01010765560f003440c80312414801c07020404001c0114882521001030010f44020030032502417001035484034902600c601c196040380e006005980c002070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 349195719 1250 349194469 349194491
    0x7032006010819020316140f030105060607170f0307030902010e01020105040b0c0315121606020a0308060d1e0f0c060c08030a32090c1e010e1203210a 66
    0x401e02c00c020b141e0350f0f80300200b000400d000180c900455009541c40307458580b0000034044440031310040000c94156901c121084c0c0301e00c209030881c0c0d8203d480a0300284100400c4001408a0240404051131240c8040c2801d5028200300b8541c2c0045030300300302090b41d51002034155a041404e09000756003d2000380944c0c946a03803480c907440c02c041c2c01444000e4020020820310a02c2c14100400000050290141600c240d009550307920001903140c03001d1035003101d010404a1010540b60802501510740a4494450005102c2540181d08081c0c800702c010403072181c2844460b00e180540315000b26031200380020341342030801d08002d00d41d0202042c0b240c00b1859800003400c40060341e43c081010440092107901a03942c003039265000585074107000e071024598030b8181b10340c100d289015440c144101c42203a044001070200c40d458928090002c43e00f03a012b40007003584580340f01d02840d5006170205400c055001b01d1103155401a60041e41007480301606030300701e03000a443c103035441030710003030b050100702400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 349196969 1250 349195719 349195723
    0x1081b070b040501061205070f0b0a050304080702130903050306031501060c140c0918070b070305040e06010c06020c070303111501030209090f100b03100e07090f0605030102070320060108 82
    0x30036801000c446812001509000303082d4407410081800d500c12411829075440e2640e11040140225642c5c0c02e004280450707460301010a0307508203403094942c203196840e243c43c0c032281c41c0c0144c10202d90103214140150700461712801042d507442d05c60703100c4640328207010b02003504120300b00c01560200700000004110036580030a41e031031a15000b0100c4045031051a0016040032a480b005030740105080052140381d40c21808070240d1010b40c0010703502c5c01910360000666502c102d00010b00052400c0c80181301b4188010401c03900050705043c01d03104440959a00c01c03d03030308141000c2c0d40b00e801980c41002499080403d450700307a65800050805040c0c01514803a021006020103802075041000142c401c1008101d400c40c100500b00480300611000300c400b101901c0100c035254060701451144081d05030090090305c020400c1d01c3e01515011b806c1000400043c2038084c04003825640b501e4000400327840a10090526138081d9490b6140d4541c01001d405181c0b580c403809245079401038004024070500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 349198219 1250 349196969 349196977
    0x4030602190f1403060111120a02030a2303040b150a060e010e06040e0a05040807150c0905030604021008090c040603080301150503040816030e031501050f06071a061f0201090201081b 80
    0x2420100c00721011211f11a15106842010403014a800210410760b1500000500070803212951900080d50740b004070f0804040081031081ca01703d60520104001a4100000341d501c201d000c0b0340300840c940c810002a00c20081d42d80b000300410000c882c2c01c0a20b5074041c600c050080000e6410b680380600c0c080c0081da8003800100244012035a41c0c01240030000e100c0102d9003000e41005909191201c0103803a5002402c0a0180201141c1d0007000003d05003070101f400c61095400600b40d4000c0d4640200944440d007004004600d98005c1580280c02d130fa03030382d02c40d040140d0f002e40f0b8a59125810880c1030441d5803d03210200c0c091000030300c200800a0b4180d000c66048098a0000c018401c2c42403606070b4641311791202c5d0982c940103807007403c0804e00c9403105c41e904881048032400d4000101c5806e200c128403031958042c1c0307444401c1504c0080c91140c0100b158200e44068400d20110700c91351380480c000c0704100f64280040c1d45418207070082d5a44010050380ac42c028109450b650b646440c124000c40c45 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 349199469 1250 349198219 349198231
    0x1f030221070c2609040209031507030b180903070b0612070e04060501080a0203100c05070204020408010507090603020a020d0c05070302090108100c03180b1e0c040e0a06080a03050f04030602190f1403 87
    0x5000540c111f61501e05000749418007003160000c01c41814a00005400b804a0360300c924024104400c61801526400c01480d0184050601841c0351070001d0b01c0c0c1760494130000700030503040441e20103501600b41c400c001840040c298400c00b041c40f400d1a2074a03d0a03100117034411015903003c12400780150b50046698402204410400a0b0301a10021305507164000d01201a41c0180702140000e0101c4040d04003030710990781035850b05120303912260706908a0007050a48030069114000102c10280140c99062420307000f48203e98100380d032030f0b000440d505c2d000d80020001c3c0c1c020582c048140d500b80d00819010340e000782018840b1415400e002c811044a400b00a00700c08901e00100e86007401404c1a0100b08a44543d113100d00c1c6008281c0102c03a070b20600ca0000314002d2500040c1030303241c107072041700244c0703110700054000004a901e040380c4907001a034220880c0b04040000000241013480100365901d1100d007000c502d21034154000c1c01c1548400d00034828400c48003070400003e0280e03012070398098 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 349200719 1250 349199469 349199471
    0xa030201080c0732010b041406040e0a02060c07061701030f08090d050a081c061214030d0e06330105250c03111f030221070c260904 58
    0x500c18148540391054030800f000d0884241c0c400c11510b2410816144c2444681c48002d1290804c14414001207400e011100701003207413100e0100d4040d07e003d41000e400410114204c65411800b9000a4150b82c454284418190f010000c100704041d0000c08404907080c0740181d41c1c0b0381d503265440300707004100c2c0c84500815250300004e54003040d64451a100b8400c680000850f12920018034000403203074810407440c071404142e1111600c00c0106800b41d042651050144611018100d0f52171003551246910340810b030740070520a8400e03c1d0345c2c1e4031600504241c184000d098070300b06180c6548414115040c410601c035056030309018508610044104552003c0c64807665039000d000f06031240c0c24030100c680503603204802800d818403524410b01c07005c0d640500d8100200d07190b0002005600010354850b0309200a0804006840e6406940a410786008680d1004812070740c03c9040b0a81e600c041302c189012852043d5040c05008560700d00340c1412120001841c1031350481074800140b070080724400d074410f07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 349201969 1250 349200719 349200727
    0xf0a060210092405070207050d0807060507050417010f0f0e0c0904020609040c0e040c02010221040c0e0403021e030a020a020609030a0614040302010b0105071106070501060506030108030c07050a030201080c 90
    0xba8044450203d1280f0341614102401807121500500825100c500042c03241d190041020710305800440c5115900c00b815901d015039076074950000e840010140420321505000018088200001040c6e1351200d83c0d000103012500181340d90100d6440554103100e4a14108054094203030002f03d0800d20f41048480c40825a624800106140b19540c4441d400c181800c003610003080d003050b544850404111010310915030b041804034201e009108400808950b50280484d814400c1880b103600300d40150b80c108292910345021078040d04c001e40c0c044006a1248002c0e2044007107203817500e00c548040c0703030185161070421180250749600050029100d0080040e480d0340650b0200180350803030f030f8030810500c5070009092168507046401c0b20150099424400e44c00c010358414400c4480c110740c005106040c0070038110a00c54603400c4914211141c0d942c9120101d095911380004d0340c020070b990f4000307565401907800c1c51410b2510300e5114501840c2a8502800140e07001400e04ea4408854860f842d21 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 349203219 1250 349201969 349201973
    0x1406031302040e031c1805030a050a0c08070c0e071d012001061403060a062102040905151509090c01051c0c0504030204060608070e120109020415050f0a06021009 71
    0x503c0c50010000f4144800245101c4c504000e40c0341010b03000e0001c01c100320036000240b05407844d0340c4207100102075820811412000c07901800141030150031a00c2c0040055a80342d07a80c0351998403074007095400b40c425010070011450a0251664030404500d06811140c501c24094038401400000040c180320621420741c5450480c4012141542c440100030300140c1e60720390625800c2c2080d0040750340680a1000000c1c0094902d00411040f40c620441c44190300702e1003285403810a601140480c1d0240e10f5407035043c0801d40401c40300b81c038012102c600c2e811905200c42040511a150805079003d1034490003004040708001c1030344806283c0070f081c410764a511441e481c4198200711252200f500e231410048043ca9030340030002d0420342e40b0035030b0204a9140c6946081d51000d100700c91580014034000408152405c0894a040740002c00e900080740728070b440ea0006003540c42c1044094a40301800c00308000601d4100030030075005030142c0300c0002c0c560038108000d4a6902c0f02903101c85181d15200c0c1441 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 349204469 1250 349203219 349203221
    0x1020a06021806030c070501050f040c05010305071707020f07090b010804080304020d1719031415121b0f01050901080c0304020a0f03050303040b16050405040e01021303031701140603130204 83
    0x20b00380703000703000603600c0c03600b1000d0004981140205460540c68600065403a48400040c503000d65000061008528580b00c0110047c001c014042420801840e0a41888202c0045614010905a000f07003510074074003001c05103412180d911010205091040308000c41e6008603261342c01641000c503440c8d80e943c45001180b407088074140010003035140000000061101c00c0d019120924035500c2c4003641f82c1c0c0c82182241607810450520104c0a90341000c5001440381396050b840104029040708031214003a0101030502d1032503801403501060104003021145050380100ca1403082c242401400d010760300300021300c414002007004011403400004207007035540c0e6440300d000600049500c1102c40d500c2e4500107441c1d41050301e045880014050100b00001c60750402d02c0304000c0039988490420340340c1800c00001d49841c11b0010038655081000124410a000b25040514040c2d141d040308404420200c3c15040b03416481400f0319501c008004c940c40e03450300101d94000b068a0900707003008001e800060 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 349205719 1250 349204469 349204507
    0x10b150d2a050906043303051b0702030a02060d0c0908010c020d0c1103061302040e0705100e120607090611010e03030103030f031506031b170a090302070f0b18010e01020a0602 77
    0x401e500c0040030b6a95200008400300341e602c402c900640e880100c200c8034107070241da105854400c500590300000108603c030b00c83c081d08ac020b0004080b150348c14000d4000c541c076984240c001c85080d98441b071030030a880740c0280c0302000818a1800070440e15415100080d150b41010080b4000c115442d2a61070510044461024003100d0050036910b0605001400c410429a0410100c0c0182d080400f40e0f1408c1c200400c0e03031012107401408200141201c44c81c1129440365030611182d002c0418a00903840365000c102d550b2080189845949009080a070050238402d5680008042a03041c220f0030140c1000220a581c110b99060030584050044110260040c10301d10028007003c041410340069100c0d4581c01030006028201411040b01406c00300c00c0364406003400388040d00f0414440410800e101030b90248007100d001c3d1050319001602c504445070304602a6200b406100d5000c00c1c100303c01e424140c40548481c0e03090038021150351012001039103c0b8403500300504551340c003241441000c41025280 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 349206969 1250 349205719 349205729
    0x901240303030c050c2a2205070c050f03070204051015081b0a09061413050906030f1f06060306081c03020c070f2c010b0309010b150d2a05090604 64
    0x1d1690340304104d64401d403030a845059002000e840703036030f1070125042c00000490440d4041d40042c00d41d51300100c47c00041c2c507000c2c0801e001c00825044d0140402c20501c070559103600402c4c0650341d5403205004000a0ba41d01504031140f00c42c08000411110241c00340142c2c2c020402d0400d2403043e81c840400c0e006803860310105985410300000d206001561064012060342c1203501c5918807684079030260141405810440001c0c01700608051060740b905240d801e80c07005008041b202c00c1503072429418100070000407801d0080d45880d410103200f004a00801c000791030545002c000c01171414119583d2005c0d03006032265211404000c00280078071a8040300c1c0044002c07c02c80310f90700d1b500d40c1180407449851180d103c00d0310200807140241c120700484480702c4900000b10075543d900345010110b56602c0a004070301e4942d0380e006181390a48400440c207840c46c05c0c40705141d4985e00c808000c9008d45084501c1d6002120102d1035101200701d0940ea40200880c181c5455030700c40e8158408518035100700d03001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 349208219 1250 349206969 349206973
    0x10603052d0603210f0306060d061514160605070309061a01020f03030f04030f050712080103020310060e1f081005163015030b0901240303030c050c 65
    0x4481e0004209010307a0090200b501143d808840100300d0003241c00540c1281159540c0402c00301c0c40e80c0741528040c542000c0002e01c0130b4a080403004220f002c90320a54048074504040940000600b43c10107240700344d610b002c0403c18a4900501c05004000b420350100408a9903608082841a88030360700c48200643d005030100058422020010174504003030030365500500ca011014102c820000c82983c0c002c9007241c48044190325580c1e03040d16a0b266042205040090901c461004241b17580c1d0f402c0781c01340c210b449158140d410740c01410709200070141d003801070500b0f20300300b003000040314040c0720780c01303130442c8001c0b01074402c2c89401000315521030b44407186512541c90001c400c240b040e44500e005404030309000c030007070600310010b440115410701c1042486102441500000d40e40020041c0d01400e003100000310240d42d040700007400c0750190810386e040c040c200200003490109120b03000c1c180055202000c0014001c602000204400c0c0c0401003c041d141c4c0104019580900c050707030131000039541 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 349209469 1250 349208219 349208281
    0x40504081b01091205031f091b110c06090a0308120a0c0903081909080a140d14040909030e03030d0e07050616060c140a090302030c040b0901060305 65
    0x4021409400140030150500150405403440070030502c5801d00040c0d004501c80903880c2c4800c01901c8a400041034007004010140303584aa1050714200c00300038101c00f8400044201218203040d100c20255043c50f014000740c6401c8002da850009229400000c044548655a010450124100c0f50450b0f0000f40054800700b919644203400c040c02b603208110b40c42080160408401044034040d480d4440988510820051990070b0020700c101107008082c1c9050210315203039074510680c2740005011080e503030480143c50203010047c050082c2c52400f0014031700100c1000d000c1d10361548a02c5280f0540c2c20250707640711040701300341c0940d0440303840000040c20341e44c583d0f94651100e8050030074406404400d024a203404982c61800006031900148400c224114240545e600c040c0105008500d940034051f103c2010403030307503514400801c14682155201d0485a10b90b1061600e41880b04140500c240d0401202117902d0b201c288103681103502500d00403542d45c03245032111034811456041f861200140e09 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 349210719 1250 349209469 349209473
    0x90a020904060b120610090603150e0f0906010e0c0912070302060f04030c060309110111150a150f060f081b03041a070c020f1509030105090c030706030e0d03020d0b040504 75
    0xa000340450442c5a100650306542c1c010070002c11303448a01b83d840125044410038424644664070407010040c0b1801340c002c280b078881c0354002a011048841c4034001c05244100a11903006000d1140140101941d10007141800c00240690b03008103801180140e000b100e00c6054858200003480c01140c0140c101581c401c400c1c4107003002e9a005000c103807500316411000060b054400c0c0b04410781103801244440d82c11030b502c0c1c011a9003041710000781d60a44223010440650300b180400490244444810001c0e02c8820b0f00c03881d0916110756480030701d44d1031050307004201a0f9004200d00021a0007490502e0045ea0745031640100040b4503c8850301200000c01000204019620501002505045808030640c2c4d001e00894000310b0018009420440c4102482418108815042d0044042c82205410001c220780481c0c02c50328100d0f119400c1c0e0b8002150400d0a0a060103403001900c2d43c2d1030103100820007900300a50352103460380b018080642c0002d620000f04107a80c01608011001082444182058 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 349211969 1250 349210719 349210739
    0x150f07150e1207020109090f02070b01060806040f060f1a0c06040501060512060402010c110f060c01060303140a1d06070519050105010b1c0b01020a020a08010c0e06040e06090a02090406 81
    0x8001c401003441281c2c01040c82c202c0a509035011030790305950f00d0b441d407800c044c0703544041e041c2115040301350f40d001e0000b040013451441e2081d010b0100e03a503071295103140c0601000140d038000c11280000d00c0c0f07410412300c000441e159500c001d0b2a0466044003902043d507a101f5014400c4440030285800b17030400340800c1007019040b0208481c0100e4540b1582c2481004050301c9010980d4001e020400f0710005400040c0c0300b020404500d40300810010b80841150f004c03408031740c0b1241121031a82d545210902c20581c110020451103090b00007071505148c0e0b511409059a000c003e80c0700c980c4298500004540d540302c208458550307500209440d0b0700811810640b0091040500c115819400c20001003101e45054080c0c840c20a400700c42c8030590aa00c000c038400615494075031504601864070250050b0325040f1000d0024000700b00001071440340902d008268030b80b4441039610601c0c0800003002401a01c40040350494000c48805200351112281c2030004e2280b0680b640d003250030040300040301092 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 349213219 1250 349211969 349211981
    0x300e0f0117190f0605061e0408030412120201060b0f130f030503030f0106020f0c04090507050603010f060329100e091501090b04030c0e07111e0c010806150f0715 71
    0x8400b8061000d81c5115005109a40060040541000d028043c651450380b80c00118001032a40b008501e00d019112211103080d0751154101000b0f080720710034500304004440b10780514019541c4020412107007060148040c41c802c40740c1b503c01840d0041403141164001408080051805a400c2e8422a65074a480f83d12a0421200036000101d9040005141c41c00801e10b40c400d40e50b40400780008140311810000101a03002d4150780038401d140010a098071100d000358043e220751b070b081d42d6019181c804000d05848000080e100c40c0420310482c0b200711103407158412051081168103c000111032001202c0ea103200a182607808003800e03046c8040b241319a10309081681083c0e8900c0c407280d1319410111810b2242e8803004010401211003080300301074500016400c20b900d446c100c00c0d01b0612101c818a050340c04640814070403401140600040400c10607808404802e082c10051072400d2000038140440040a240f2810000140c0c188002c1c5010101c07003240341e02208601e007446000c038041d801042 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 349214469 1250 349213219 349213261
    0x10515011706010807030905010209040f091515090f0e0d08180a021311040807030c0e06040509060c03180f070501020f0708060c09010912300e0f0117 66
    0x55003800e424070452280c4074288a60411307150340240d919160000c074000c1046084c00d0303581d55400e00c40c104007565103000310b54a1101c03a81c0041074680483c00e2985a420082d030700c41e000240303060040c040151400c00c8060480e00452000103410316911590381c0644100881d01c0491b000c0d006189440c0d68000750b42c9809009a5203008012a5000b50100e07075824004002135800501608400700c84410b5400114002d807020020500b000d50321810707203107000c015030812240c0040004050101900591a00340e00c010110b4092001d400c2608580742c17100005001c420f28183c2c00800101d2200c0f00344000049401030030125549401001103280c0c4032a054041d40e03005000321a0080071808001400c007080c3c0300c040c0c0c0541401d0700d0b902940c52496004d02c00382c2c0e05010310004001200b00740c24000d03204044c040d5209a0818440d41001c030f2008501c242c07001c2d1034003800e0a04d1021907074840e4604203200c40544680c3c1105030400010b036070525410110030170344401d040c01c004d09603404600d00031610b1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 349215719 1250 349214469 349214477
    0x30609090f050d110604080c2404050105160c03030f0204051810050906030d030b01120204140907020f0c01050d0230090319050a030e0f0109150513080c030c01051501 73
    0x1866030f0854001c03080101042c080d0b404100800c005c64110801460840c000c5400c4811400f60801c04602100030b8111180c808250700b001c107c1071100130300071981d0000d04201030604149824030702800c0303000801d001804040d030726030074a01032400f50b074120750282400604808041e4a010000752100c6c500b16021084400300000c00606410442c40c81070003900002c02400120741698001c80c0100807a50446041280d81c4014541d410480d100800c003074a05d01d2841034003140100180503039044064200d8045520100003001848400310308e05032250001d01c3c00507591803050740504041d0142070550010b0703600d0401c4140031103040d006001d01410b00e240340e40d2040c1d5245000d0039201d01031a5205149960140d91001503035106030001e000c003c01034100081c1b20300203070300038a01d0200c088440381c846a540b0034641c400c0c410102c0c43e204540034100e4041c450341c034101015450103812104000d0002c0b0000c00c1e051b100620604c2603a840c80c0c501c80c000c120320b20b80390022458035003c15942038082 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 349216969 1250 349215719 349215733
    0xc03010e07060804120905090403080103110901060f12020c15100603050f04030318060f060f0b0309121b0102121503010203070903120e0312040608010b1303080a030609090f05 77
    0x2403202041c040100d40c166124528169507a4641140609903000c0050400001010100d540d58950f9082800745000703540c2c031105503055180600c1e101400464662103441903000401516901804401c1d110502d0b1400610901c00801c04801a00640009000d00d000380c00140085103101d4032a0f40c401c901d00100340c1825075031403105804483c030564004101101c1d4a00040109001f504800400d01d03640e41c4a51213101d4075110340b021200311030580200c950300c40100300141c0d9840c0d85140c01500302880e1040c6142000302d052070782c0d4100155900350065000c0ba80b03100c03100d0402c841740d03114560240250340d0f8400c200700c141881c45040310068403a03c1550380f082a1401c0510a59110310300300d0311181001c90030758503018030641c04010603808000900f00d221401ea1030a00081011411100d0001e07281c508040018200030b0b0141c00184500d001030211020361a20000c443c0100c82d001100c16944043c00c0000f240603080130340058000c075041100c0b40c000c200b44007042c441010700580a072218 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 349218219 1250 349216969 349216991
    0x60f0b1e03190504081216030b03010b0105040e090c0604090b0316030209072d030204030b07020c03190203100c410c07030c30020a150306050a080c0301 67
    0x2107804240c840000c000c164008460000090350721180e0400e000e05051418420344961440080500715104400b9200a14000c407445805005101745140101e000f44000c0020200003070950165106140400c50000085842154103000c0800070075400790441d81e80344e8880f16000064110a0640d50203841800c1d043e01c0716106401d20041960740c004c0c4007003000c1c0c0303030604215100c81000032002c01d40c803100541c2418619052000d4603401c402d90f240540c480d031031801c10444040c8000c01440c2550004414000c0c65074020594030302c41c4900d00d044402c080502c0c0042460490b9808090004501c1c0406000c2401c2e04034a01408441440d01491210705645a103c001403030380382c008600c422410300d0b51026002103000078010b800036100c21654856903030780710710420700741c540e0252055035840c940380145100d0300101d2080a244001c0c9000700c10740198082084e005141c42162044604200703003079003041c485c0d00210010a002400030034010740325840c3c1d544942e1081c903414800d41c80d041c01350b84 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 349219469 1250 349218219 349218277
    0x1030b0112170a0e1c03140909010308030408090603070c210e0111010e100203100b07020f0d060b0d11040c1d01050a14220b03060d15060f0b 62
    0x820760340e1000c10044048981d085201c166080300c1c40ca80c09004840802004986a141d558060500d107110140490382c13260402501802440240c2258008108007822498842e401002d04595000481d503581f940d036410190124040c030714409900817000400e214400c0c2d03101006858860240505075003281c0114821000000300302c0e8982c001c1280c40200e14455030040c0590b4175001521400464480c00c141e131a24284001c60040039417040d40802408103001d0055074110117021190000ca29202c02d03500060601800d2100709441602d2603c422000c00281340c03c1391800040143c9014210314136444c042ea82a01c0c2d0b0f00c0d04078011440e000580c0203141c824000c40502d1800c070f01e40030320201c0c65540111001d03405900407800f80100c298000c44004281802000680c0190103032030040c5a4907030301030351052030661100d2a202c030207000380b00f050751700c42c07040c0f44c54281c8c88441180c030010903e292030042c01e4103500c248840c1c52103113070020b94a50404001c140c0240540f5480100300c015008001c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 349220719 1250 349219469 349219499
    0x140d0c0f020c030601230307330203040510030902090901050601021002041410051b0f0c0402040518060f030703051e0706021c05310501050406050d09020a031a01030b01 74
    0x80d403503070048004001c6c10600c0daa00b0b8103030b100000c0d01c54042859543c00300b440d0a05640c0199442d0210384181c01801600044620031008044004042581100070080d40c9000314080d1900c40d44d4039030003c0303a8442c000d9005100c01e9501030001c040920b000c018080c028101202d4036400b60140700041500d0000714400c98094900d00c44041004440d00b4080c841c441b020710130280c023408000c1000502410100c4041654901100020032450b1a40440e071402c2c00303000d1004030302450050105020950303540000181c25607240003402c50070b1392902d00055103043e0b41f0891540502031040040107104000c52424141c54112800c3c60b1202001c1a07016034807034443c40b5950040e0000811980060b5400ea41029003d529160290420070142c01000c41c0c99220012000c81c0e00c0c020503184080b0200001900c0100b0090030004d0500e40752050190881c86030118007080250341e28040021980c1e0720280340007442e00a0102c080d480b80317012000e182d8100070300040d41c07000040800020130700701d20745c1c0c44 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 349221969 1250 349220719 349220743
    0x2090f04150308030a02250326060103090c171e0f030901050d092009070207060228050d090326120603011805010f11190c03140d0c0f02 60
    0x2001a4a285440f0050f460b000a080c0c8800d25408116510440020942c51900c1d206002154140102c041c6406821030b06c3d00c9441c9081032085420014000c00c0c81204154401420300300400e04004902d8110822010354025900301404070500f2600c850f00015161800411a030101e81030340c0442c1d41d056503c0445900e580c03000e0b40100244089544500c0150a095281c8000828407192070341c0c0e61027420900c50700b21404032040200050f010314140800a0b0480101d0000d03044a0b030801c40001d45510503883d46844400e01204c1e02090074280c4103141ea07019403c20117680c4810044c1d0030040080401d840183c1d2005803859492450f80031030001956000d0341c0525035850468019120070801400814103035045d5030342c01003d1420440282003100c00d82c8581c000040d9042800700060484012056016002c40288094291210760300505882c51b4902d0500e00d0051184e49022100c1007a0704584814007400480c0450460a60790002d80c407104240d2101c0c003007a240541c040703075180d03050850 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 349223219 1250 349221969 349222001
    0x30702090619120605061302070c050f060c03040f0503120f04060c081c0e070614030109020f04050d1b05090402061b0c040e0c0a0b07020916020a12020102090f04 71
    0x4100c20b881c11000c06161000c40040600c0925561806844940000340c0107454094941007001520302d0203503411032043c82e404400b141801c0140d103911180040e0f5005090140000418001d02552902d060b154080c40400450356210784481c4440e218015600c1214003900c12001c48101e10394038203050381c1c141e01100c89404d040034134050084410043c5800309949103e0100841d11003046184165800b503072055402154504614000c1e9280c246564862400c2145e04103540ea10241d8801c12281110f002c1d050150702c1ea0480202d1042901c103035481039a000255120301001c01c40d510b003e00d0500328040040f90501da0350b5109014481b402250004d40c0403504000c20316144402074449445211540d089400c0c2680e18008202207078202902803c240c1e0120040d1415403605118040140c50b2203402c0c1c606048059011900c07000c0003512540a40100c1c20503110351903c00c0000b402d070107410004e02c400c40342145002034000e501010140c1c0c02540744403103c07a520f0405000f80b18005d118400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 349224469 1250 349223219 349223221
    0x8090310090210090819020a1203021f0204080d0e1801030b0403020607020628060305030d060906080f0c09130819120b060f070f0204020d050708090109051009030e040518010b010203070209 83
    0xd0099601b00d902c62080f030744031001c0003010071135180700784a42c0c0c1c20921170740003003614a5143c0b03521a448030000d0310708400b031801000248190180814580604041c5041c4560b01c0400ba40000c0d8808210041004002039a0b400010500921140ca24080d50186e02a00c5240d115218100d88410040f00d89428a102c0c0c43c2040700207102c1c04d2810046480001c0c00001c0280c2c8a96425080d40c0c41400c0818529445460502c040d900f544984002481c82200803d810315040c0c501d1912900b0014415109680380310001e031240c007111030048101544408e4283d81c0c1c0700c00f140200e40c06405442588002002014140105003180c8503e0042c06001090382d805c1075a0242c4c5149140d220b058201d8403034064505010050310342d0b001030086198070078004503061802500007070801100500003409a814600400c010500c0070030381110a0138583c6000c240109c460806940a00c600d500050300607180208100c0c0c88410800540c40418802000780f02d022280001281c0c2c038011010003941c0490424 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 349225719 1250 349224469 349224493
    0x503010f05060d0905100b04060e040b060904080d06090f0609090507050603090717031815070605060a03080d0b010f050a1707180f0f051804020409080903100902100908 74
    0x34140f6008201800f14035030915a44940c00c208500411803600e030780341c8003890f019103080d019071805009006c0c10001c05180a444140d41c0c1d00020303000c1401000300d840800d050148410440d10701c01da01c0a07040c89003d41d20f1042c18001e100a11050710b1151070007101240407400740c05106600d68009008103801c0d410101000242c2c0c1c0050013101513489041300000780040d07a04400031031003204601944c0c4a915000300742c3c4200507140d10301403240c5860408032580f9042e1005581045800c220002019549ca002269401051782c0000e05040d201143c4400c0840d191f400685060800b030b41c802004585050040e1081e006400d030602c045403604100c0b0040403104414180d010840d45440300044c1c8074182030034080c4401b9000016010040300060210303810001038140184800d0342c214140c01072001542049400203172000303108685642851007803003108030130f440409c00d0040581f581407080111800044c420a00304074002d180c2098001c0c401401848018100c0e01c82d02d0140034214002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 349226969 1250 349225719 349225729
    0x30b06100908070b03010e0c04180c030b13090507050603060607021c020904050a03020d021c050724140a0207020303070b091510090f0605151b03030a0501150503010f05 74
    0x303189100d080196024001a60010400000000b4184060000c1ea6541031000b10140107000800464411074104420010070030707101e8407501d4a17184030600089201001c98110007401805201c540d10520700c08003280744520035880070080c0e52107a0111201c1030396410a104080c08102e90883e4049020700c041d00150905008901e50104030400d02005140903a001031302501d401d5500b5a032640c8061061010190108907481e024061400107000c0d0a0785070480300002c4c0607003200b803801c0090100750442009074000d502c103840c915000e5500414113044a03828000d2882c689411800d600b100045071b82003016100300d8505640150140d031802e4060f450b16070808401624405191107402c0b60514410305503660701c0d00070b181281e81c24950f50b10f0074003d001544c00320344184da1250b14100080000369142c1032b0842c04040ca81480a86403a498803244003241016400e15580c1c3c00b0001c02c000d50143c0316403206044e640d000241030900ea84961003214507010902a014004014500c1030040d4500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 349228219 1250 349226969 349226989
    0x1805061c020a090203090606031005041e110307180606030b2809020f0a081528090905060109111333080403020f030715050a0605180619030b06 63
    0x6400004500e503502001003c0f60f2045644040e02c0d00540e041c0045864140a6024103a551050038002f0341030985400050701030901e008101601402014010000d41c2e03e084810507600030140c4180c2a5200720030710482503850840c0c8440c600c1c3c0391010075840d002e4443e40b088518054001c81d504000f680c880200034141103c0080d06030360300e402c00075664a050006054242c140b94500e600e40f04031007030143c0100d501a0800003c00040032120b09580c0741c1e50420201901c000481d55a9904400800810f000380ba0300a000700d40c1c148086201404000140141241d0703d40d0010400030a030010344190318016071561102c41d19000c0d2013005400c83c244824400340010b00080f410300c103d92495802c141071450841c0c0042030003901044181f40d018000c1442444403030f0061031030001295240e60100341d80c44a0540341c140d490011070544882540180b01402010302000188107400c1e210010140d41125103501c00c0134141080d0f00e01e034000350030746401c40764007400e07107500740c1c44000c2003241e0104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 349229469 1250 349228219 349228223
    0x607050304050d0804090c08280b0307030302241b030c04170a0515130201141e041a04030c06080a140c09040e01020901271d011805061c 60
    0x210a100104043d80d5486480826502c074012482e601e03032620a80d2401d90b40d6903082c400510146000700320310620f160a08840300c1c894965005082040c241840c1c008040c651703032054140c81011004410190005820640074a20b000d0064400ca044107002440b0a4200d0b107206009541c46c10146194422401644e00704000d44944d07800d040e2102d9140b1100038200c030041441c9e50040c401d402c14030a05001c60003118010848000d2640b070b10b41d18404804441010007030420072a07949000760f0b80000003e5a8801c64090810440514038560700c0c0210340003405400080981402070308840d8a008007100e04076a4004024100945030510580b0301c0c260081c041c0d900a40c0b41d6a030b030a19a000c1c0d01c59248210020844140c4030315081052104680080c80061116071040080c00300e240e820402c0124580307140003400221002d80d000324442100d13150b00403c3c040d4851140806100c0503c0030090695001885070f500c2c00f00d8030004241911800d80c0c4454102081b452481000203c849494a8244c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 349230719 1250 349229469 349229473
    0x3061205030901081e040f060b090714090d0501140702060903040609031e02041104140a030f020904051f0b010e0405070f110a02060d0917030906011e0503011401150914060705 77
    0x1400d81e404d21742000c00121401c96071100300c0c103020800c0183c0741c0b01e031142c0700307a090310584140d00d40000064504910340700c821580340c00c0480e1b400740c9aa50414052626580040284403080203001600c00b19076003a030704c80c40940070341000600b40f19000019601240e81507030318013001501d161241c1c00070218000b1826501643c244954025840724001c0080c4221900f07101c6941d0b520304449602c6241c0f20401403070ac65240e0700c03020000301d40c00c2202c541e4a1901207a08a910b9103903850294030b00a0252440b00a81090841000c2072045a0740190031409003030f217a20b944e64848104201c200e0740c2c12122080803031412404d03070100714402c07a0008000741c00310080307030550002a000078156820140000510790707101d200c1c01c01005010031103510401381442005007182031000c0d07082c0e1114014011129202441c01c8011032206034141c92400411002c0d008001600c3c03d9a50b100a0020900030075100180ca004202c1c0c1c1c0342d01c640881320455000402c0d91010300201000c0040590111105407194 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 349231969 1250 349230719 349230751
    0x24030a15120c060f020d0c14031201030b06030c0d080304030e0a0f0806090f0106030804181b170702061330050c010f1a1306080714010306120503090108 67
    0x24180c504040605600800c0a0302c03603507142c420010180813501550034210740203011040c99643c2c07c10075a4444030f070311024910807000c00114061640c01807100c250168401c5000000c14007041117102400303110160291125411582c0074440d0f500e006200050030814200000b90211780704560358002480d005205924050f600c05220b10107044980220425800c4241407040402c002c00c20413030445586030090054600d581c03102103281c011343c8950000c1000e44c88a0061500e142e900a000030761050f145080103400c8034100a1900300e840c07402440c0d1015140104480d1800040c01c0d9104001d02076486401181c2e0f41c3c1da02903c40c0a00800125400150b400a1041e02e0381e4135000342c6100003a6584d44c0c4403402070514a01b0340303107050080e0710380a2610078850720020402e410350784446070603520340342c1d04507544d00082c0c0141540c2d4840c2045001f02d020110f4000420070804020920990b014031002e078a40f03800c5c140081c0d2011000b8143e078000c0100151030350140b0380323079644045001401419 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 349233219 1250 349231969 349231979
    0x8010b0a03110f040509160c080c120406030614010c120f02010b060d14280207080c0a060605010e040203151903140a03080a02131e0306150524030a15 66
    0x280e40c210070030740750b8003c2c404a42070080381402410503600c507201100154110205007005801c100083c0e601a040c10000200241200c408112040340001012040c40d07403503aa88100030020000f0740035032000f5881a448502c2c10f50320805000d072003e03402003001c60044c0c148a005544010001d02124250354031100c4203e000c2d9180d101402002c040040c3c08111a4054a4603200c0801700a0183c4101c0040e91003010710303804c0003041c03907028419003e00180d81e420181000f00460150040d62a205d12448407032004204082e0411780854100b0780b10309505040301d10420040e808200e600044001d10110316820340d2a001c80000c88a00360805100b05803902d94448880401c404401c880b055805200e482c001c05a12940342039004101200841c2411111a50102c4ad10f516110b00c00c0e4248040c110018003400d0114000c00440d8403e104000250602d484204801c45030b100c0d0301e11481903494110803030750703692001d00d640460300c0d0f54a0b4a1640d0720000c00300242001080d603090b003043d41001080f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 349234469 1250 349233219 349233251
    0x60501030b01080d080903071e3c200612010806071e0e0907032c070602010605090a050a0207020a0b0d271511032a0a08010b0a03 57
    0x8003a50040407481c0840d8100440c06150030010940407080041c0f2000700300c204032011050381c074059481980210070320310000c01c00e59803282e01c0e28090110074410000200c0341c0d5041050210038551762581640707209844007030f0703a8034000c0e104000e450070190b1445010072004130b10000c030710054001c10640c204100b04000740700c841c1091304154180d03400b01c0d00380b00781d454001801001c02d203002d00900c404250203210042c00c0e000781880342c4d0300130000e840206640f580aa0031080d520049070100301c0c80055407454010181540601c812914003424801154951041c0905426524050b015540079221046050000e00c0e00600a03003096900b40070040042c0d40d40c031442001004141c0e00d10303442e55004070380e8074219110007088423050b8901c0d2045009450030007041c4000c4941011240c1890615980c00b0000350841e10282058420300104000411800103200e02e440c90241407c840c074442400382c1103150344514100400811202001080b40000207001071040380c03103524011401c081341500c844 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 349235719 1250 349234469 349234471
    0x2040306060b0307020118210c140a02090603011103070c06020903010f05010e0a140c0901090305010c02070e0f060a050f0103090506010323070e06090709030b07020109110f1305090a0605 82
    0x42d00400041442140c03582406500c0ca120b0310046460141e0425542c0d403814040018200b07400e800d0814050081640100360700c214403500410511561001002c280e80c640003007040882c82a004070000c1b070003a0805118101d6600d02c4144079a1458440c201d058680305000d10045410f80d80800980c40152001c0c042c0091a014488010540d07506003520b4801c244002072841ca852494481c12042000314065080c2e00510f800c0310040c0d450b405600100d60b0b000c030301d030000b814640c01c000085030141e900040c840119842307c00c0c0c03140aa110740e0700360108040309171003095005139600b005100c1c0e0701e0030010890313000700b05040018440603196a0b02e810480300340d03c141c800e12004003040f0f0b210705240c4204068800c408000d8084c0300d02700b941c907044641000d0400c80c0640d000b0350000315414055414000616080034540400d8504103000038068142480125029041450880d00741d062603d852845060020004040d070b1070040c40310380080500800c041020301c50b2003119800b05040d40f01d06 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 349236969 1250 349235719 349235729
    0xb06040b0705210c0a060b010c0215040e06091003151d0601140a06021b0d02030f0f0c09010302011b03051911010b010c0812090703171e09031b03010204030606 70
    0x80e02d090043d400710904680d00c00c00d4880f01c0c8031000c000d5619810030204a00c01126842580024480d406400403100461840da009400c2032584840300354000c030b024050812203003030814540450b91501c06101d9510300540303070920f070812240b0b07082c00001d044070180107810845100000f1070f02d4098410045400301071500710000d4105400500c1101c0404e18000400350080e242c1d0288546481c00003903482010020f020202c0d0700f1007000a8031035840ca081c0901d0a90010200ca55440c051040c050f1125285d50300300c0301500c82e40c9000c60701801c1c83e20105040301c2d01619481d03080701071038402da80d413519151003c408114041104c1d008500d15030300c0054500c4543d540f121000c40d25182440d08450081044034180010032102d00009124541110f041c031071040d06100702601c60000d090301d27105007030700f00404851002d00d45154139074490f00901200c4180350406248002c401c0071512180c40380c0485690141c000f0584812803001e09541c9220301100540010315003503494030340c84120b87d080d03004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 349238219 1250 349236969 349236973
    0xa0908071112010608100504081902030a170f1f0806090705040e0105012402070315091208060f1915030501082a12100515030f1f0b06040b0705 63
    0x1c15140c60a060b03562090700d4002c1402040900d003411a0199103441c000d0944007141d89842c00102041a00c00540f01d207010fa070380b40c220f031000d401e440c065140d0304407914400010701d4170704e080072011500c61441400350071038003078003c16500e484034405200320501410145140401c90006038800b0101300247c03040050350050190039082c282004143c44c81c0700d00401503681410010301491209034000b011a400300711090803e00d1200f00f00f0f0b070408a5a5002400e810890a10500c0b02c2c0c843d44c0088e50b6592040300054001341e1542d406031001001560f010303070000c00d04080c0501c40e003081c602151620310701c114200c0d02160340d00e152606011010050b440000e03100c500405c0007007410003020030601c0d503071481e48445030358000c4c60820783c01c040801c5512030f070456282e5000ba400244500c82003c840d100060180e490041503030003980c5620301042c0e010340b1840041d440407040c04100022840b0903440754a400c0b0070f002441c02d01800301307070a030725500040c01c0100042120344400104189485200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 349239469 1250 349238219 349238243
    0x1503070608091e070b1c0e0c130c0c022112091c050c10031107050708060a021206040902060c0a110103060b04030206070308150a03030507020a1208120a090807 70
    0x8a860a00803601c0052082d540c075004031541e440741c049810320035182c0a0342172545405c0c103803100300500c102c05890074030305918007540c0305840b200c01f050501c03100d60180c4072500d4018100d00c65104a5259505240001d86e0254100700180f600255640031000e2809140019601a00441382056403003041c2c62848000010160042d052002d50903c40398109c0202480e441d2582d2140c5440300c01a58640303114101d4890b03040a010b0084e4408156a0305803890f0a481e50100d14103a681c82d1100d006240c0f103441442d0018507407a44500858003540e10012245100fa00c6800511029205e0704a089a2155007400650384a0b1400c00111200500518511078050104070016085415641001c0c540250404c418005a00e40c0d404485070300e0340c585084409940c42c10f600c4080c880042c5d81035544900800400014141e1007400780031858004c913000303500a6510052280e00d07503d0350100604181061180c04d500340021000305e54440b03015100130845c0d00503651440042e91040350101c452022030a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 349240719 1250 349239469 349239481
    0x21303060617030315031603051f0209010e040e010b0303030f01030c0e1303051e1902061609170118060c02012405041d120301060f0906171503070608 66
    0x10040c00010300304400b42c0c44000e10381c000010f883e44401050038483c0c08502504446540b4104003020740d95000d808130080c40380d10780c9466a264101aa2403440d20510729126103042d038002c0c402c5503010341050311a19442004801030002800072496642c001d9580ca0703458407482e4500b0300040d40308041d83e190b00b40056040d80f030081c20520081c0c0001001032180000c10600c02010b65200c1c500c1501801d1803512050f201e100d4080f0300418204800c01080c0118011940035001e000c41c0d550160f0903003c0d0303102036513000c10110103100312500c03010000b140440c0800220000c04c0801d200c04002c03000102c3d45002007188182210490503088540741d0780d41c0d84444a4030b42c280b0402d4260038415a180d049140d26603c1c1d501d8012060054030b100b0ba80d100b451b101c0c200c2400849851010161080e580100b45459501405400910404000c1680c03803050b64001c40c03190800000341c6203191034004602c0b03203104a01c01d5119004001040382003110107a01c4482e542040013400400c5d46641d038a00c00c1c0b40030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 349241969 1250 349240719 349240721
    0xb01021903020109330902090a020304240e07050d020303090910080607020703020405010e0411040c0302070605040813051921050102280504030c0509150913030f051207030b06090402130306 83
    0x15019040507606c1c103107817000142d403024819034101000700805601c9481c0c5003041c448280d001d4811000b103040f03103c401c1c2802c00c1282c004009085004082d1070355503031388000303104030b01e0100c1c50020341c190010000741f911460102d03c9a9001a040078040041640311070147d07140c61015a45803025070f101d08020804c600e0b05015850150602601c0c0080c05e0030903590b15105411b0a2030703252f11031500c5074043c0102c070703100383d0696007001d4000c00e06015506140c10300102c1a403011b268081c0a01c8042d2010425061080c00400d01082642c0c1030003560389801020001c4509034070030802071101e60746020010407001d0016000030420306900c44c1e80020610810032000d80214150414030105101c1080403c090822040c115002560020100d641c2d2958214402000404c0c8540c403410b03e10900c03a1031020132402d03200c0148071341c4965140c0c41c0303565425240c902424603d408001c84007800201160f1003a0030100680c01d01a1003a802c00000d4000a000da8120b0600000301c030300c0b41d0204009004e12 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 349243219 1250 349241969 349242053
    0xb0c0f04170303161b020409031107030c051801030302030d23040602031005040c170613110309060601171f030c061d060403050a170409020703030606120b01021903020109 75
    0x741e814170020340c0c0342c405e8041c40989120361020b4030842d03131030040724185402000f030700411032030f0354055810a64891038a41054056401214002c864035559180520040300c240e505030703a010380045040046401c10324003e80001319070a44040712038124010640d4400c020280200d11a01d0056103d1070402120109500e0b180e2149104e42c1c101046c0c4a40150480722149050002d071514042e82e50b1a03e01007034841c1401640241d045150100303440811084801850041003402c0a86079241c48690045501e1031214016210f00100071011461b10707052500d159820019000c0d00504866894540703c078040100d40c03141c400304c0e0450152980e0035020b030340c1c8039400c1c1c08115922403c1a0440c0c458681d1002c02c180c00034102d1070303c800d50154944401040c3c074000e04420406550721812850024041c10b014031882c0d02280030290100c4544455008034181c003031041c0d006022205541e07035003040b4103d0008096003555a6540d294010039045000b2642ea0344100c032002d0b6494070503409110810203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 349244469 1250 349243219 349243261
    0x30a0504150b09070302180303030403030e160f0902090d050a03020c010e12030301090b0109030f030306050a0b281701120308010506030108070b0315100e09060301090b0c0f04170303 80
    0x201e0b008a29525a848850480e00302d40ca40c13600507120001e25a80c0c120106c0080385c090750520004c0301300410142d0613080b00c001030b10144156070890349d400d014580b41041da40614025180e0740c0d88140070108042d405040910001800c01200f032180d0345440341441ca015600350016000503601224a50704400041922507082d9080480788150a1800361030b40410300a18034a2a03c5100681050303200701641005507400038040b003881405403401030010610b80c81400d0244158200004d5034511a030161007c4001e40842c880ba00b650b094829588070403100f0349203052107618005034401c080c082d545280a80136190004400390396a040141061070140d00443c070400301040180f0510740041204400c0f03580f0452260b489031545111714007000e9180c3c07421500510710410071850150300900d840313100f03601559000051b4441c00c041c1807d94000c82c1000d0250140f00020890b4086a00002d1507000880d010403800d040c0c403000344058038040e0707a80701c0d0f40c20351006c424400c6008402000340d450741 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 349245719 1250 349244469 349244471
    0x807150509030918090a14010f0506151204020402040b040806041112150903041a1306110a02150d1503110409020904240501060c0c0506121b090303030a050415 70
    0x900e40000640c0c8035049198242c0d41314418004509044404c100c0c2c980703016403040584e6844c1e80c80301e400328001c0c9141c44000781d0150800c4042007540c10400381c0385a403a1020030416140a5411150f155008400b1b0400c03038100d9400c010002d100c410120142c409425440050301c0b0030304103410060116090300b10300c2072043c0d4000700741d03107818071000640002d19a940c02100482e60740e60b540d8903041d40907584c00120390410405203410450b000030000c0c0200d0017242d2100b8442611000d04880744d01c05890443d00f0340e480801c200000d440c24020021480d00ca00031201e05c0d21030481010700503030705d840c0300c0f1034000d01c803018007402000a003d0060421580a640030805010f81c0d4002a4020401500107000101c114551001101000c1c008c2d0410b080000303400d02480d6950680200030340c2c0b09040035221007000c54008103081c0340244c1283d1401200280c80e11054541d422220041c40c144d00c1e0211904c04208601d4a60352020f1014520980840600103103d24181c20f0806244c22300400d604045 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 349246969 1250 349245719 349245727
    0xc0f020405040318060f11060c04150c02030102120121050636010e15060d030e030c040903020c0112021306110304030c08011d010c0c060506010e0d15061d0403050a0c080715050903 79
    0x342803980b0a80c0c4c211080190bc50041c044000b800f59120154420041d4155000151180c1001c50100c2c64504079215015140105200d0042241c00660109001400c0d900154045803e903125400c298510701000c1141100c0361101c0c0208111b031400b100054042c40c2d44881c02d0003545a0203010250910b03001c0c41a01c0c102d444c0910000e40f9000340602d00a0510250a0491455440c100644030054401810820041c64142030195481405100d0390b80000c03084121040d40c0922402a00d01c5041502c054690081c1004026601c8000c28002e1490500c014000000802c19034400c0000801d84c0c10300000c7d118815540c2c400d129010031900b24200d03810081001e101c5503000340341c5101917410000021756501c51400407102000c140711256440f202c4a00d40303034203021901c80200b55030034005030100300c5c056540c040c1800181c609000c00410202070710002d004031340100000e001c1e880d824175100c040c401c000e03520003c143e00030402c02c0c7d40c0c0c4106d16041514404e6548103164201e03021400441c24 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 349248219 1250 349246969 349246981
    0x30a061509030510050709120b15010201021815070503040b04050102160602100c21060e0901090c0308070302030d1814071a0d0b0402030117010c0c0f020405040318060f1106 76
    0x10b40c24143e1041381400d55160001010a84101c290b4030151410843c101e1048403036040241207400d040e2100441842034060304021903005100303c0d09803c1c002200c3c81005140041017045010300b51480340c1035440e0401c07070100081c8080c4002d10251103214400c5407070303501b001c0009150400d0340d0b901030340c00b1130f0074001800615000a80c0152150b0310704c0c80444c1230f10f41903108440507250340083c040c040300201e92240860762150095004e640900c0e0300710146035650551135017603802d040c1016240c19070304001803001c9255031005024040c006d0048a14020b881b501ca041150040d54240c0c50081084044030b04104807103540503c910381d8900248961403c210301524144c40940c01704681007000104105c072003000c7c0c0c22280c008080284110340342d40c1d5500c030f40c1141205a80040311654039140004848901079444445980d0700030070200003c001d141d090000502008c0d00c181d0a00c109101c891100380a01c041d404043c0c42542e0344c4070030b0349018490292541e0581003202c03529801181c10452 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 349249469 1250 349248219 349248223
    0x60c080705031501020c1f02060c040b12041e0308160c0302071e05130504022403060d21230903061f0b0d0b10030218010f1103030a0615090305 63
    0xd04001440c2c0c12120780f00051005030b140c801c0307502c0711540002c0c90b10015109209411040040c8820640a0301c1950781d801003940c0d55842503020303000034036906200501984001d00046035000340b20720001200c7c5801004103040ca0703201e500d004c0f0005000c9008100c4803851b802c1c2d890704244a18140f0700400c00043d42e000c1d45071041ca0080c410649116104810500b404a031904000c4c60090180c0c40104003114144000c1d040c01c4400364040c0301440c10b01c80030a103120344c000141101038070070f650442e151901088411100840305684e407040e44d241910000b0b142101d0000824a15180d000c8152402c1401c541221040342ca05440168184581540f81d00e0101d04550f10100d5028040d100d1801200c010000360040c1e000000c12010200c0d081820301625401021002c1088800810040d0281012002d91044122820b10141da543c82510b5a50080d01984410b003418180324541189011402c1d05d10f400881d60210344940398401001940b8412030042d0380d2804a1a0010b00e140c150317111301d5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 349250719 1250 349249469 349249471
    0x40f1512051e0a020a09080a0b01152106060e030a1a06030721170301050607021203160b240105070b0c1204080702030f0106050a030204051506031003060c08070503 72
    0x4031240c072580000d2840e60540440541c00080d061001e400d810400d681c40001e4008400c0e14000c0b1703404d0640801c2041002031300c484055400742d40200c40c1d03820010b024443c80c2601404400707005940a25603d01d40001c5110824104800c5001501c1032502200601103a03442c034400e40617030030400c182d001040c0444105603080ea61030315075240300d84808011910300f50059000000c02d0840310406401c0300c6000940d03c084a00900601c41d2007401c580b4580c880303120138410686d000d802000090018105103000711124588a02900c1c01d1140100d02c2e86000100c100e000c48040300c262041264002c1200e400b184054002c031507180741d1140142c0040c100d44a02140070307148801e40d00009000801860403241c400c1440c84405000382000c0c42c000c0181c0d004110102c0c0f19015806103005015414032440f001c883e0000c006034102c5185da0203110050101030960a600010240d003600f40381c03990b00c0154001d4021640c0441e040f403035410594220344050380001d08000c002c800703001d0320581c0301c010b403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 349251969 1250 349250719 349250747
    0xf0904050106051806071103150f091507030504060b03030a0905040e06090706080903041a07050609060709090902060408030301060e090a020a02030a03021b121905090303120702070e010902040f15 86
    0x199a1b20101807c1c80c3d100b03041c660304496450304c40c01007441c260842d19424a8041da0410f0750303a00c040d8448080454440b082148000e004e10040000200c061740300307800640c2c009004000010320030301c840340803d0865008142200100c0c3c070b81c0100304404e08180c820700071039003500400341c90705052181030310703854074000e00c80c00040060307042c0840c503400c038180b0494006008441d0444a50703a01c100041c1c4c6290007801e02502c4a000f60344c002106a01c0c00710b40184541d4071a514940400d080c03009400c0103000d018401d80c0c01440904c80481e08000400045028010f96140c5111482c090f8040060150005000e2003020b4010b001000410790000280c1c0c0218825040260315505506103821a211058140f610248104c149034002074900000808818941c20904000341c00007120540d0780344980d1460303981540c01000194410040220700c1c07500407a1610554603281e540300c1302e4002c0030601303030051151a640010104008000c41e0280001010505445104060f0b1307043c000c0c0942d881a654 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 349253219 1250 349251969 349251979
    0xe030a05030402130e0604110103090f080d060305100e01180f02130e03030f041407050d02090a06050307140a090b010e220e060108011505090a020f0d020f09040501060518 75
    0x2090455540c2007900445109140703041006030a4421415030760501550159030302001d8800382506540b003402000bd1064012040441d0490b150741c0e44801507204480d000925661b030030000c00050014411518403501d00100844c554005041090031202210740107a8199400c100b44070000e00000c444e190100e40485510b0030354200b10300740d0b1018028400508060340400000c102140e0030030a01540254003a0790301800d20b0706030340420740d03413440385008250380420300461800052410380e0203594041d80311807011402d19661070200303261107059000f0b1841d100d0321400c0c00c1c003d82003030300c1082c00410b45101d0511090045a0000e13016401c191801e5000d501200c44910071141121810b040744500c4a000704203c1204003042920381200703010b4080154207103414080e5031644200300c90127450008248184070b80742d0340c141c1d50003503000c0030103030003400c80c10312201c0240c071010300c090010311a02880456480240604000440310b05810060a03c0340510900c095a8800070401481e41c1094030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 349254469 1250 349253219 349253221
    0x16031e02040b100507032a0b0c070c060c2f1e060406050d0e0102040602031b0703120305010611120d090f0213090308090c010806040b0d0b0f0115030e030a0503 70
    0x10801901220704443c2d00032280d98400f1001c2940840200a61402130340c2c1e03024910f021503802034211150005032054401001005808600b4880d00c0e240c0100c1450788107480c10039540d4420041d14000e5214901050340f044045040c041c030300c85402c0046040f0001c17a006056020405200e141070f15a03d9402084451a02081010b8607268480c100380700400750f81c0c80325600d041c000c0450741710303041c4012010b080640080c40c000f03050080c0e07016928903401031030030201d880310504180c20441001040500c1070b42d200002151040b100c868442d02265808181d47d81410b001501a04548085007102c0d40040796200f49081403809542d251513040300c01044900340e40c14660016502c00781e02a610001c0c01a40d4043d88160354400014188a0740700c0d0083c03903803140e03509606c1b60308080e5814003180800000506500d03103136000120040300107025400301034440e01c0382c40602c0f5045400d07101c084c030001d0042c8810052041c0c1401007a00c0381c41c1c24460f18501e400f200b0b4607400f400701401c1c1407200100c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 349255719 1250 349254469 349254473
    0x806090a02091902120a05010f0e090714150c0d0305011d06100207091503030305010501080c0717040801021605060c0f18010212070c0e0c0921100603030e0316031e 72
    0x44c0440380032032110808903116003091000e60004040030320804103920b205100006280c00e0700802c0c01d20400f1441c000d05681032030a0408140d0403c403400042d440750481540789038007070310070015101c0c006e1484c00800c1181a803540140840d101a0041c812810b111703140620f1909030701e134845502400546680d030016003182000d070320380703c0d42d500720780003890030080340701814801d4001180840e402950140610f9a0790001500c01030016940451030207020007011011900710340c2c82613410003103401c8130707803905a03a40f401c1c50898118000590403141c940320110300b4484100030340c03500310842500b100e20b014200100e1043c3c5115100800c04504614078016185a00a1060090003100802c0d4581c0d00c0503a803800084a44503801140c00041e44000490400d141c1603080d15200d11002c1c00880b44003801121104501540200381090b034031030080311107100890303406568010762184d01c0300014507041078105806d141124050600c1c00be0031803c10008217030131000301e13450f0400202d21448100064 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 349256969 1250 349255719 349255721
    0x3020f0a03120e1f022d1c050702100c05070f1d09010b06030c04092f03060f062209020a09210b040c06030c0306030c15030b18010806090a020919 64
    0x191002c0701ca1305003092100780c01c003500030555501070080480c052020800c14000f4000f01001d4040c80040c9500c0400740300c08841030ba500d075045000c0c640c1001c038144811580002d9245c40b03641071080c00180d14100a6042180400100c2e01400380d001554456504150007410f001c5109602c560036100d5420110704424020360041d405070a000c2c0c24640c2d40d00e040c240c1c490580c0d010b4410006031510b042c101d514900151841c0b000100c5079003400070780d03240c40440a10042e030400351046510070740310307000c0441c141d0b2084018604001d42c0154056011170031181c1c0341510246a11481c0d179540100821400c1ca0760158019040d178001c0714035040c6002c03005141c280c044111010042c202c5000c070381441709000c0440c4454088030700a83d400c0c010409502c10441c00e0b03510f00d210080c400101d160081c4485c0c4070501c44092409020703d00010f50304d0b5a00e000442082c50242d1550940301d00700014403102500b0301c00d05a2203440ca0303000300791800d03507640801c1600c1c41c01001400207010900300d03d540d40b111 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 349258219 1250 349256969 349256989
    0x20101d090103030f1e0504060c140d0905010e06091305071407060f060524090d08041d01061106070503060d02040c110609010c1704020303070c030c03020f0a03120e 72
    0xd0211003040d81c4a01e0040c00800c2a90040401305042150142c048035448400f150340601d42c2e03031441c2c00d081c034081c000d60300c03074220800c202c8020070398400c6d0824041c0100031415800d807071036a40c1c0d2b511910780000174200038403007840107000742001c00c428400c07502c5545050b6010b00d044280002c0c240c3e280c10017100c08034400084075161702400261030b418412560024480c1a130107503410080e09640d0780421510f84108a02c06d21421410208034103c80000f00c09071001600240c040c1d0b5505016a40d440c620740d000d5040b071400c0d50740b44550211140c0000d601036001d00100c0c180880ba040c030344180207940f008001c00250801200000140160f01d560070120302c000d07030240040c00400760000c80908241100c01c01002030b88112070014003e030405000e043e44201c159203031840c502d64005030104034204024001d0340c00d44030421590300040d042e040d040f0011401403100501079800e610400c001d20507a80141d520400d421201400800c45032482041d007800d4a040085201e14428042030400750 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 349259469 1250 349258219 349258277
    0x42109120507050316050301050112030804030f11030c07030b070503060303180105090619020607030b18041707051605010302090604120c03020a06031a090f13140601122010 76
    0x144102441c40071041c0c10817401034503022402400603070703206d0350040c098207048500540010900404903010030700a880174489004a46048100051a94881c41c616440b00141e4003041d84900c204106100a000010380c01044600c0c00520b107042900c00a0754034001c43c0151310000c0d80b1b10402500c90b03801041281c841c100d025007003903100c0920041c440000300845411303102501407030000680492282c031822940b15001014021442c0c0207640003440620000d000721205442c60190891244040c4060074590303220f40000c1402558444854800031002da0000b4140741c018420400d960717440505540568460100701c0b000700120f400e0404030340d01e2541c0041d401004044021070210b5054224032541d403400300341c103010454980140a0140f00849815032843c4030b801c04100264010000b08180c2400b8010441d041c41c20040503074140781d402c1c1d000c0385000c028a1800d108101d41094a1103800140c0e41d0079401c0410070360040356007031410380400c4080103c903003042d48000411940d0821042 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 349260719 1250 349259469 349259473
    0x705010e090a0f0609140702070b190203070503070c0501020d080609070806041e0506150304020a0905090a05010c020c090906071d1309060c080f130206090a03060c080421091205070503 81
    0x1d40d0317407400c1001040c0126521400c080303a030b00001c90b642d0000510b030b022a00148a010300d0b200d9903036104850b400b4038082d140c003140410000c44001c1641040074000607805804200803180c50b00c00060b2900fa40940030300e00f4001002c023000495510700090f158088124206003180d9074031080002c005180140317a0107044005c40c2110804824103074400d9100e403105461000c1c6000440e0f0740a411408101c8000f5407000a0701d2050021404980101d500049000d08a6005162a41e1002d00751060b06280600580c41030103007000a1800d030404c4ae0f0007400140145c00541000365004043c3d8215803c1409001c40305000003205498030000100e49003c62402081142050302d0400050f082d1103000100042e0000b0100316410551446940907084040402e080c0300d965500303014030f0f40c00009510740d222100070340c000046081350041c0410208581e0700d4803103600d007a14046200c050719185159941c4180342901c0c40e059006080c8005403200f414a81276104c0785840c0c045d242003081d070031290f018 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 349261969 1250 349260719 349260731
    0x1303170f041d0f070813240606080112020a03020d08120a09031205041101030e0c270105030c01021f09020a03060b01030f06140d080408070f090b01050f180a0905090a03110705010e090a0f 82
    0x112152361010090b20401d40d031f81c0c605a6030380c018401d2001e045010282d4404141c9604100500e0082d807202e168070b2050300942c0c2800e182c030580c40d501a0080710328601c07035501c5012910405a0120030840c486400d00000c211302c4c20300c5c1c0c5030040752800000303055042c903544504903030791070008110000c0c003604000c1c00c0581c0030f0462032444004131441810409030590410003c00e0a01e4081400820420180e00400032400340003001c12011035000b440070304140d0340d0400540540c54118060010314081c6102050035104080014125043c031200110300925041061001513280c0300069507a11088441071000601c604020405200d41c0d84440c4191080e0040020803c0c6210040c40c100ca00109040003040800c0b00191502e20803880c085010460070001c1c0070200c003407003803a001541750142c109000151640b00c404211002a1170124856010300303015810964402c1141d80412011405440154605000078104042d1710060603c00c40c2c0300000618510317407030b900c5907190b4400c1c4d0000703001e8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 349263219 1250 349261969 349262033
    0x209010e1002010f1a060f0a09080a0f0203060f0f19021312020112020a0801090903030b04060e10080c060409091406070c171303170f041d0f070813 65
    0xe11001820f012140c3c01d041501400355189811885c0886000c2c080310700e40408450380c680e06500c11840780c011b00c200c10901054400c1d040101c10440d9114804410b5000c000e80105841d00c40010034604800960310100300f00000c140004981045540504415851458041c074000c0e024444141d007480300303050000500c0b00baa001d21102600d0007a200c1b4403052164403101d10591007080201c0300410041001000210480c0d4400c180d00d501910700060342400e807a000606464460788244d848000410034481281300066000005064500007050803041c0c0030b021511900841c414410125601c41c014030901448205030820805603805952061622a6000d050380c1411842514982c41c3c1c806070108050b01101250100801750400051741861541c1c0c04c10001081005a10001014014054842080c0c80540040e180304075010458822070054200c44490080c891000304018006000c030841d006020160001803000180986040c282810844101030000c06080350440c3d00074803c1c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 349264469 1250 349263219 349263221
    0x17090411091005030702030331030315050121020d110c0604110409051e07090e010b100503100b0717070303021c06060f081f06020d030f0c120209010e100201 69
    0x48441045401440d4003118000890f018003007203031004056441000442c40e000d5410030740c40d17405801d40300358058846600130140d0300303240d21240841c086902c1e02c2940b00c141483d11041d0b00900401e10f00b0070500794400fa0000441080c22003a410200d50000b00d40d588450b090b00814020b0003a008130355a80c0c030094044035510b02c411101515031081a1600080700c1c5403a009000086070010000d00340c02c8a1407003800140181b14036032071a41e104d40c1800041012642c02100e42000d000c10001856911080c01d01c0500d9000c0d4410904000c010000c002243c5040414401034480e40e80380c550710340c402440c0202c10715940b003000c1540c52034045445010140e16400410345085441e41c41c0d08580e80342882801501c40c0c90050901241180c1d980300006407003040718580c0120f1102d95540c0154490030039441024558018400680140c100080e645809d4000c8a15480da502020800c0704181d1200810074400510054140c43e00007d8110440c2e00c10303030b5801e801000080c0345000100324100e02034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 349265719 1250 349264469 349264477
    0x14070503040f030b0c09090106050a1701060e030601290d02090409200a03050c01110c0d0822080c04020d0f060f18050103120305040201090b040b04030b0c1617090411 73
    0xc4520011100190504442d217042c0c0b0110080078042d210143d00b05030090b43c01c0d820100c0b00c0f000b000962041100c206a03070301607050003400e1a85034004000c1c5003030309060034140147c01c1155a2020b50348004011000040790800811142c0e03286615801c5151211000c0d12038500c0d0306038003a040c1a4140c0034042200c600b014040954007500351448405800d00c4803542044c8809807003030f003000254000c10b50040c0c0e6080324250808055848103040200000c0d000128000b05071460309011851980701c615000051806941e1202641c26191808080640d14000454914003a64010603d820709181c5500040300c051180241032000b5a1941c6080000034040c0c441c005009840a4440700c04c11b51901c03420303050b00e801c00542500d0126014040e005810040c02c12810081c04034030000e88011b050300500042c0015120035031703403949141030100700c8620160503140c020100704141c5c144500000c41d20302d80c02c2d500240c0c0780403552004060b007600d03000e103242d41c68000d400c1414038040005208014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 349266969 1250 349265719 349265723
    0x5010602010516210c03140103140d02071a28080723030a1a0303220f0e19060b0d060e0c09010818010b0409030201020306010f0503130314070503040f03 67
    0x4004524040c0070445580001e1501c0320b2032034015840030f444050303042e00000b0b40030f441c0b0300f0081240364038440502441f0314264801d07185400300051304110100144a040e410000c2880100142411702c241c070b4003030150f47c2c0c03042d000d99500011034404a10350490800768081544003c15400d044411024000500c122005d00006040d801d40304003115404050304524801701c0c1c0b010342550765090101c00204507070000000c01c40c083e0206003411340e4040004101c0000c2c00f010500c809103810307180e400d51054507004000b141d44a5036003031050345200900154095400c401c1600300c0360281400c0b200424668106194001001070924000c411580162080310340150568001d50754071800f003a145c1c01001c812034002007807040030602c040c0408070454a9150030b4800002c043e2040c000040440d03c0c492000c5015075004001c1044543c4c00141d40f443c0090541070451452414500d0226560f00320350004041c0804500c44044448a080a603141daa43c450100c1e9562030303c90820440c0c00790f2610003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 349268219 1250 349266969 349266991
    0xf0b181b07030201240b12090a0b070c03111b041a041a01110312010315110a08090606010c03050d02070c0e09071e03020303070611090a030809010207061407021c0501050106020105 79
    0xc060241c045c83c80d085001c85120009041c1803d15070001718501c00d001a1003038416114282090001c2080100401c0c0200070342e0310307001d415204030328000d80383c280b0010782c01026400c4580e400a40c83c5071900e0f0450aa9001c40380021004e90f25403080e0050031042c02000c0c1c20515200303010b003503d6543c20f640740c0f21480c01d0321003c6900c6080070150340d8a2090b4100030801f011110300400000704140c0c46107041240310301c40410786c1c240701001c0110b180c0000706868000780d500c4041c010324210601c240d0f40c201e13400780390058102070141c030050114480e24550400455001911030244240851204080d0850440061080c00d0000c880740d512192800f4203041e002140c000c2518100c2c409807801d0840764083c0166003480b0241e11000e00400d41c4a1800e1a08a010450581c02d9034810300b9034400343d88900c6406e500e0303803800c50009141498a030810320038031040350101c16844600c0001c1e40c00c016412510901c0d80010020341404000d601d0310020003d44c201070020031030307a4040d00094030030440158 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 349269469 1250 349268219 349268261
    0x8070f0b18180c030618150609030a120207050109060201020c1b0307050306130501050610020c0114040504150612021c0207021f050a020c060304030815030c030a050601030203010f0b181b07030201 86
    0x6081968901c2680c1701c01c61400965070507d080c1c2840005020301c0000101614208840b544070856200701c00e084150068100380c0c0c00b48103540e001103800020f080c0758070086041c030341120701403507860410501d001c803444184008080c1c140d40400200020b00b4010b400d94140e03051040185081c00007680b000c07929542014001062400c16034481c0303a00e41041c3d4014034101c3d0b501c2005417540d1721034841c6d040300d80d0720070440821151100d004000398080a1081e00891901e0048000c20324501c4076800740f403640c010001c1540804141d00c0e0000c7d8034120041c0107030340d514180300042c118410201da001030301509070781020f00ca98005010381a8082c4980a64240f80c5a41c0d0802030303948402c444c010041200070020031142a90310f550340900341c20207030449180c0c0c8000c600003840d02e82c01802c102ca0b036501040c01402181000c2c01209200700c0005000c2c0030035001074000174811a94058113402880c3d0300303000140e0340e20741c0518030411902100112903841c036031420024041d02c2d500d10345c8404c0c5a4003407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 349270719 1250 349269469 349269499
    0x90c12052a0108070804031205011502010606090609031b120308090c010206060108070309110a080a110306070525080d050103021e0303090411090a080708070f0b18180c0306 76
    0x400c103408a1903050359000c1c030550340c50344180c6070703285e000e00190204070444a01c045801424801c82e8007a081080d9102c010f0002214000d0075641325820050070400c81d110f04124041d00410607000f5654085054465000101004602e9102c030358004070880051450400c24181c011680d14020324180d401e680e1421000310044e651950155840ba00003020200010384070f0b4070035408001081d00c0748030720722100721b2140000b8014032665000049035802c115007980401241c00c800c2250284150060210b5250901e0060058000c11403488187c01c4d00c1c20b20703040c5002f072100754190708035444040035032900d1215120f600145001d01003240a01100c2c0314604402101403c081c030b03422001801140380c0b030203000501c809840d40c500c40c110000340900415151b5a40c081000010b0b02222000700301741490100351915100361580901c940c850f00360000d002c25643d003021202d007060603c80d0290000781700c20101d400c1a1581000e034640300d4a0b102840091040301c40110b005280448082361400140307 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 349271969 1250 349270719 349270783
    0xb010b070203190b130615090e0106050d0c03080703110a12030c0e0a270f020706150e010306020a1416020901140f0904081c0b0307090501030506060103090c1205 71
    0x107803c01a2554078103030005103980100203440e2094502c51103001c40d141d140010041c2c50114190070059241da11411504449842446980014241210300e11400d404a071a00f0200010500000d071048074002a81028180034803404100f442c40c02084030700031405030602c0040d540b103540c014400241070110403082240324035026410600014520301c00d891800e25460081100f200a01d03480c41c002034a051044c40c110b20441c40c0e68001400d0250b940c1c042840d0010407107940242e078580e600c51000d01071103a0341001c1c44c01410f5036400b0340300590b034030800642559080550205e1200c100d000007a21078071841180b4600600d180f090310810744d141d13214003282200e4000d00c140181c000b6a14030250031207180c040c070031030741041c025602d2500c3d11402c000c0004440174a407100100070b03525403840400d03c1c141004424014041c1190401013941560385070340d168440608998101a210340d07a1100344884480e4a40c010300c00308c0c4000030510307a036140881d04ca442c121480d0031941c1800808001362508 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 349273219 1250 349271969 349272013
    0x15031c09080105010b0a05090d0606081002042603180109050a03050a03140307020a110f06190e030c010503160e030d030b011d060702060d0f020f09100f0206010b0702030a0b010b070203 81
    0x81c42d11118240240c1c01d003827000788403c0304016101c003525900d00080e821070901814507000b842080159032103042120403503020402e21081c0006503950660902aa42d01105958104030310180d040504036a4900407902e00c0c0d400d80002c1d41c80507641d040081000b0b40014601d000907c00c4e03d40d1808447c03004460189030000b100c03220301607042601e004000503c41d8407034881c0d0000007046504105d10401c040303062a00070304c201c01900241007840101c5650803540c0c00360900d104500500c0c100d900c0324002862400301510f40700030810401c024004c047e01a40b030b64a00680c0180440e080d030050024010301621440c0605404544254203107481e02e003044800e000081700280c481e80c5041607590038070031580e000002e10000160758020340d40000005000401201031116003668841d40907a041003041d60f074014110702480400390000c0a0150041016411500f064001544030710b000e0001c24100089120002e041d05103200003c0340c00011a4040c241c094003d50072101919101b205d00992502 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 349274469 1250 349273219 349273237
    0x50c210402090a0f021306034b0906050a02090a080304080a2307030302070f05040911040e0118050a0302060601110c04020901050d0e0c0910060815031c09080105010b 73
    0x40c0c1c00000940c072100c03507013280000385488403005143c00318008103204034000d03540008001986a040e00002074159100c50b014000c45109a90415040c20712203242c005800ca51660100d82250002c45102d02e251b801125250341200003031090b071620701c0b0481d009610005109101d441e640d00d002c41d03a032000100f941c0c01d6a08903c020031000c84c0d51380700c0340d251074500783c0070502c680d022103000e003d41d04081c84a0001144a500204002810040304050840711604824001d40c5082400c0d40441d020f240445034081003602c00050365100074012074090b2002c1d5000d200c003521081c4142040110004d007000010b40070b03900b51080d03516907034011943d000c020142c40243da4130441d060070140c078040d80104541441410200c0c60610150328000586980c004600e56903007040785038041780d0801010160344602d015440442c02800d00c480030b04000380c0644000f24140114004a01341d440400004500192034070400d10b4030400400c0c018070b40400c90043c410b4035401d1000004051b5158020784800355 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 349275719 1250 349274469 349274479
    0x140f220e1905190f080a0302040602060c0f0d1e0e070305070b030c04031202150108060a0c050a05040b0d110c071e05310204090c0207080f0705060c01020904050c210402 74
    0x40b101401c2c41036030304a0b050040d00d116100050304c800180b0140024511554280c40c05a10350f490008045c0c18190300a040385190310003001106841d5124004407060380c3d0341e0750b10000303810201d00302e400030031242006102c080034540390083c0c02c003100001c1d241085a00c02d40c121368503a91500c1141c80180001d075145130301102c09200910005210a0310700c002410070f44104e42c00307040702199440c45040c083e80b22403115080ba4007807140c180c0305409161500f0200c0d003040351502c3c81d007140060070b40c4074920a50704044030204d0141c0005020b50010503110f4198108140c55001048602c0d884a05502ca8160080e4a941e00e11520440740e82c80d08040f1240100380c074103100e6409684840303000b01681c0c1e80300e059028070307410151b074000d03440a00090442c01c40d000586000252000c1d00d0310009030001d110903801840305232220b66000500c0000d0310703801d48102d07448088140150b401390282004da6030b80207041404001040201c03401070603041103e00044810792030301d1038807ca50140c06036400b03504a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 349276969 1250 349275719 349275733
    0x131401181212020d0501080d14031503070902300c120703020d050a1d060c032a0d050a0621060203060d05010908090415140f220e1905 59
    0x42010408200c810740309030b092440c07400302c400151000300e074070920641020954690050040100070000c00482000c1401e0105441804c1c0c038200607240802040b45c441c4038034842d9442c11035101070004500400c00d13501d0540d1640c01d80186021300b03a19200c00c91400c80c08412035030590790007009002d0300504c0074221891903d8010501c05a84050043c400f206041d0200100441b400c0e80f403040302e20500e2a403100080308526018840100704800040c000240d01943c14071510203c294226600554040107100c01c0e1025140c0c26800590240c0030400b030110f005c0b4844404400580001e403041e29040001c011480d1140c64444030485000b0003882848040c03400d200000c0d0440d401960030150040400c07004400e04e07512103081d9004501c007100d00a10105a40e4128181030207542c02c962071600245441d113003400303031541072850184407081c4a52901d140380c542c41d88421610b40c10407203a0041d040e14031000300ba804006071242c51106c405512a02c104010841410400c0398443e9a00c6400740c205 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 349278219 1250 349276969 349276973
    0x706090e060a121a1b1b0a0203030a0206011a0414011d1c060c0809060412030906110310050306061302031b070b040302060f040b04020904140613140118 67
    0x11030310004003420380191015070040b40262030440ca00d0203103485100a24003036040040986411400585126201400784103240f503052520705c1510115800d000780e0b4509810f5400380c1c1440c0c00d80c1400041d4140c080011242c280f01c2d8081280d0b816544428084500c030004c2208800b4207114510a00d43c228440e950304900940c4030350281408520190f00e030912000d42c80300044c0c9102d55000c41502942e6160510350100138507801800724195090524648614040300841e80300c00000340010502c0c1d00d0300307651001c103e001e60b000130340207900860f0400a010100c9088101948142c0e11003120880700e8200107000e203400501c007031142d10301078844526440c030b1560040103504042c1440051003041b455600300707031440d98040c00d074031400307a043c0c04060304160402a0610001500f108007a040c0d2000300004038404038165500a0b13030649082c1034566540c24852025501d0f04107000f014064103080c413940c00c48445072212814000c09001c1110019071140c54200e4844035481d490320003080e164540 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 349279469 1250 349278219 349278239
    0x6020102210925090c1803140c060a0c03140301051f02030c0a03031a0405070e06090d05100c120504170a02030d05041101020f010b37031a010803161b0305060c03090d02070609 77
    0x810f82d0381400480d40208111800982240c0028000400140c5210098cc05165024400c0000c401c080d1040615650606002c60910708020410004a03e129800350309024401c2044600c030310b40d1031058880320102442c2c0180900000000c3d80304100c0e101d5040e00b05458244203040c02120903031103124800d40d8080c14422582c024040d80ea90004545c81400003051b418000004490074159001a9001c3c0d1258080c00341c00d140840c06900626203010000068040035030580801181984651070f004c0182e8100d2440c17003409405d012107818501404104801031440c8641c8600c241c00f07803110991150403050895008040455000c000608111031890203138201c1032006940165a0102d8401900d030800342d18482d520072540c000c0b560006c802d1510f4902e0b03909000d0095003002e0361800c14081c0600d114540c01404c06080416400c03c10002050b50b08030340c800641d484000c1d40c038189400381c07810915400484640030b160003101605070a5500c08141c90064038050303114105941d080c41e040d10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 349280575 1106 349279469 349279493
    0x30337090e01140a21030e010216050d0609080a0c061103041208190603051b010806010206040b0903090604080c01030606020102210925090c1803 64
    0x11040d400d0711012075045440105410140340c00c40340000d058000c0c0c542c08807240b440c5561502d00300300c09030700c0c4200056001e503c03428641c00160005a132540c00400700b4a00000440e00c00f1300c2213103170400042e00c41e1800b500001030004100e40d601740c0c41d030b44800d0060001c104503c00100801c402c60040c03803405140c100c4582d007142403d80e500c5031078078240144801400000f4002655082540218881040d500382c001d1101580d01e08207141c840c540e01851060032035160381c0d82c05240d40106109409200d040c2c2c010030443e642e58803260941c1d94090300c0c1a069010411140b01075a6a11010f040a0403042025210207070340c0d0340000d03045900651000066900500c41082904490f84c040c9500711280704500c48582d072502c0f04c0c9403d0841448840800e48600b5464048880c2490903074401e07070303845482c20013170b007008840c081d1110380500e03a0301460180d060b40e060000a250100403 = true := by decide +kernel

theorem cover : BRFrame.Cov 349100719 349280575 := by
  have h0 := BRFrame.cov_init 349100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 349100719 ≤ n) (h2 : n < 349280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
