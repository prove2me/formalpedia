-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1400
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:47:34.368979+00:00
-- url     : https://prove2.me/submissions/b43b89d1-0f72-4336-b3fd-ce20e918caab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 251618705 ≤ n < 251798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 251619955 1250 251618705 251618707
    0x2d0b0406180506030601020d2307050a150614040c0e03010f060609230d05030717030402100c0221160b04061d0a0612090b0703270b0114011202 63
    0x1a4110140c9610140d004070014115001400603551501d20140ca00c5138a040e005866500c0b1041001c69140d201486032282c088000f4201d8896200c514000d0700c1260b02c140300404010000c0e003010503d07128400d540c0c1c08140d0801c6401d0100740040210140c41c40401c0d031703001ca060882ca401c103a88414455907000d070550f00c0c180740942c050342141c0000e01100e00545950350016161800100c0e8014100029921142d004400002c02e090aa01800030540986c0070b490400c3c41300d42c1c0341c2104004c80700121140751000300c00c0c0800e51500c0a006140ba0b2442d0412240b402400c0d80410a07255450803194080a100c08584590f031406125800680c5034065018214984605030f00000d82c0003800f5800015115070048503900c0d11310540d01101030030003801c2c0d003003ea1034514201ca0510380040f5100c12241c45507d810b00103101110700600a03103050324003148148508004207040d1200d07445242008003144449008036014004007815141e04140154001c2948001601c950042d0350703450b0031a0344 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 251621205 1250 251619955 251619959
    0x90616030905041104051521040602190305090d05030a090b0108060412090308041203030f0f0f050702030a0804140c0d0b061003090b130c0815010518012d0b04 70
    0x1600c00c1505099030b004035010010303a1800b980810440c042e500a81c2c4e086400000900401c51004000c0d04104410310140c600d082c16101c00100e1600054604a44040d00403d012106044404a0180a4850b0711b003c00c001d02d800b600c2c0555a841c1c000509003840000004103c0d506403581200340b8982c0c03c00d0010085503075a01905584010448041e600c2007070700001c0c00c1f6454455031000e42120341200f0140c1c2450305144490b50341e1f0301c9001d401c900341550b4000c6e605a1003030a014a1045601c03c1c03d000400d01041e100c001c0980d0302c01040301046410070004141c00c0340d04003000c1a08550003019031411242145030261801101105144e480702d0603012040810010346d102620944c419922108180604403054059078a9400018000d10703038100000c00405c600355107071110a005044811030350740e80749900c3d0300b0401910202c130440034001c00184954209031007001619202c10000e81d9442d0700d000c940041880c0144045112660f491441c03080d6800c001c20b00c2c402038101c50070031550304d035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 251622455 1250 251621205 251621207
    0x2120f0d0504442e0e06040b0109020a12051e150d0b040822140901032f040204080708060114060f030c070503131401020f0304150507060f200301030203070b09061603 73
    0x10140c035240d51001782080b191449108021845600507540460412816400c00009401a400880500c0c0c10840144150f1940121070f00801d0f0041036450f40348001e0b0048914043c8903a10020075600b18001d1416008025856000840c00150b402601c5481c0c1d9403564685000d00380b141c7c4807142c44001403800481d2801e41190341c43c07400c94074000d500400c07421000d0144540c0d4402444003034070500c2101d040310340b00d108520800c000104c1280c9440a41030f8800f0005049802903040306c802c642c0300c40c00c244107810703080281034094000d14003240007040c5104001072061144001c500340c41c034800b0002c42c0c00d0400c801c054070036941d400002d8070b449441000504050090710710641c3d500b44080308860040754008a04104805c1c41040a10302c0c1900704940c1d15030b4003980c110a0700401c030701081002c0120320b140c410718031041212400450020310356515107201d0a0005001a0705410030401080160380025800701110042040d998841c0244070000d50240550104851200e1032503032608109 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 251623705 1250 251622455 251622523
    0xb04090c0e0603070807150c0f14061909170a0512010308190302070308041101021e06161103070b0411090412030509160302120f0d050444 61
    0x350310180c0444030415550301c05580c2e100124440c6100b08030108114120300381c464840e140703423140510100201200b1540c1c42c1018a29802c400c4a55030f00000f05101003245030440484c0c0b91002590103020a000984900c40c0704503070f880600c40e01d020001021444036000358181c4e080301501c0300086c01e842d0307940e06000d40380c3d92181c41124841541c200c0b100303400f903000f40701307640c070050f01950b0b80b00c0c8075a2240d032480701e844001c00f281815845000e84403a01030404408c0d0105404401014104c01c0c20700911055820303000202450034401880410b40140d0400420303600c800340c00c00c2042e4a01c1d2641d00303001c1080c0c8000441d00f034001d0211001c02007444805e42c41110440800d5604105640d55014015158052912409002046030300d0800c050b20380065245c00d451510000c1d07410302010100114a805868442d1801144011808000100160032880403003c001c2241500c0d1520040706456016041442503d1140c4c10324044032165004000c0345189101c140c01c590117102038040503000c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 251624955 1250 251623705 251623711
    0x230306040c052704020f0a09090804081209030a11060f19020c09060d0609021903210c0b010e1003060c03060e0112050a020621070f02010c03050c0d0b04090c0e 70
    0x580385040418440b0700c028070341046280c00283c0103107458407203908005290100c8503200754041038540000c40c414072603101c0c031802140304852050381d40780b401d06054107024203202c0242c0e21400501480c14151400f14000d90815840031410752280c01500009a10303009052035181c01910109550200d002422080740700c0b07201c5a021030741c3c41609101001f04019048400e250008121200000044c044c0e0700700c5400e042c801490782000c1c1a5480c0d40855007016a807050321000301c46d000c00c80c0d20071403501c041c801008952411000c0400603440d00d1306040703018411400d01001000020b1740c070314080d0100c64003440d808541032000d07070000400240030340b2442c09086142040080001050051040743c1c001c0554800b02070718904406400300800354000c40d29000350000760782c4d00c460300e21b070200c6a16441030515489035102c07007481010090840c0d128868038024149402c041c40459000081030382c4580d44e22007030100d01e8220513000700d0050f00200e0801814811000c0e4007150b40d440720245148 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 251626205 1250 251624955 251624959
    0x12030c0a020c030718110721080f0907030b040206130e060f010302090d02010305100e040606210201021c020102070506090d1403070905040f0b03031b1015230306040c05 74
    0x10b198480081016119419032040b00d150814840c507003d041c0245400c602c0c14101034524181c20082692a00c0d44441104146220b44010b41c40340b4481c540e4208499a801400c23200e5410858508140030903603489081c0405000c40e0340c2e50340000d0855440b5021106d0303508552407101005542d50700c0c188040001503c000c0d1088184400c0000154400c5c42502e202c5000200307408840e00a58006400900700500340d1000d0b40358190b40801c003050307011041d42c0070383d02c107000c0040c205281400791400d080190510328040d0010103056000360381d00041088132103818030325288425100348002d034024404c41c07100806902401003040390619020494480050094907440c074121400e03602010a4842210f861000c11802c00050041f41030950000c807210070305d100d00082400460000030b14580100400c01c0700400e0210b99851104002c0c045100c02e900f6000c400c3c08005840c0c5044d840403042801100011440001304a07400c01c4107014011131440c015040c4d52980c107060504260404c95802901c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 251627455 1250 251626205 251626213
    0x1008190302010b1203030a05060604030f2004061d070332010b0c060703020313021f0e030102192f151026070305031819030812040512030c0a02 63
    0x114509240c85401e07540708856005d503141d03a8402d03680c180240405059190084400e000120018001083c0300c440140a0640c0c0c91800f81c54113085641110500030301401386040c8041000101c04006030411a1500308104034110355658008500600400e8410710701342110f109000d01c485c040446d070300301d241007590203499070342e8a0f401500328074400c0312a50f40c141d502100018001c148240e000d5900107a00c0c1e1030500b00408240c00082040145900c1c40388241040c1c03902c0540c00b80c0054006c1030004040d0000d6041403400020640406120100b000c00d00051039a401015003040702c0e20071407040c079000c1d5210b1282c16181b80a070703070b0320b551090501c08202c100003213542e4040c0c06c040c40040702c0c0c034000800c11506110324000c81404080001080c00d1050280200010b1014400751000c085010902120352400c8000c10009034080007001100900303040c01840819068001c4940c2d040a0701e980070441d07150b030f01c1c0180c5812460000c00d405210040103002c44030081070024610340c3d51560841d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 251628705 1250 251627455 251627471
    0xe0406330504020a1704080702150c0c01030b0102071206020d020a2a0b01060e0d0614060f0d020f01140d0609140105091015030b060711040c05030f0f100819030201 72
    0x111003248134103840000880d0100202d0f56412428070042a48140709020305402d04400c0d0b800705210f0380c800d44081400f440c000c5090007000304104905004007074240307801c0c010a00e0400020f034841a070740c011180c4002d2100912814080c45030121101e410f80320400319034a0b06050f80081000010017610000e692030a841c0017580b25000c4240b0b901c06401400c3e180032a46449030544480940141d042c2e00003800045d59408609140300d61904818801c0c1044034610b01801000001c04081082500c07500b400140c41026803900d820540030780d44203090544617111035a5004509000e83e44a185500782040b8000c90454481d802c0401320018080c460100303640c8034003c00802c1c00c0d00300ca43c0c1040e9400c1c1402000101c0f1280c506030190a01824001121000c40000c00c0d01c07680080b0040c5c0c3c00b0110941010604c1c2410300c03e1180514051030312a0450400100c28101041c0150000c1100007440020400e0f40704d04490a4004081d000200c40d140c10385451612080c981110040e03016510741114 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 251629955 1250 251628705 251628709
    0xd08030406060e100e13140a4103040b0301080d12020909310308090609030a0504030f0602090604061d0a050d020402030405010b03030a020f0111090105040e04063305 73
    0x4854016806510b11510440c00c1c010000c5c0c0c078078001417031407802d040b1411180011400601b040752445c44a80080c107821074090920342c0c20b0000072100d404144003111a0781c0c40e05d02000001400114045000300129040c1200c00391940c0588d812a811400300000000f4440e1b500103600400e0b900e041c1c03180314030180448000340c120301404c00810b40101d50a000141240041000b90366002d001003001103c942c0502c0e8079030204d12290208801059400c0b01380710385000c082102035448040c0304015460009440b000402178011848010000d07400440b40300c0402a00d6015610100c0b0050100313600e6030740c0c5800c02080b180300d01603002c101c00c1e440162000c05003041c020241c1074480240c45a01c0101c071940c24000203500090065500b035680d000b19032142d60701440201001949030b40105440031100d034900b0b01b1150741c11a4118032a608002800c02c50f600b21003624202c0340d02104001050b43e440c10030001501040c136010544000c01030406141c0925409406405401000010f42c0d044c1c803442 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 251631205 1250 251629955 251629979
    0x902040302010f050703030608010c0309021302030411061b1902130501030c170f010203010303081006080103020d0303110c0715090501021914030f0a0215060d12030e0c0d0803040606 80
    0x2001e4002a14044825109070184005000017442840e0016800b656049010708641007103100300d00081d211a40c02d0158038101744040411056090118958109a80c07060714039401903450358002c02c2d0104e12003030000c1075401c04613491000107041c2d8880c09900c0309480752000d20750108a106051481506c031002c0c0c040c4c858241a20f5202400540d614140409440c0802074001144e90030f10944010203410f00c82800034500031442070f01c8120141c1400301141140a4140c0c0210080017910001007002da62075590100354140c15003400500d83c607a5122507511840742c1d207011840c1c2d20450800207152040010061004071503641c603d2411b5480703100498070381241c203000002c85051195144082103400765141d0000c280c4104580c0f400010026501060b0010382c0d245009d80c00c840da40c030710441051031150f075000408807140041c5d920700e070f41d0301000389480360510742c10183d03140c0248000450400805458600c010500301c0e0403140e40c0751042c95030b80129421500035040c06000205800103074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 251632455 1250 251631205 251631209
    0xa0e12061509100902040306021206090403080408090d062d020901050301050f031903210e030a030b2404080f0607050a030b0a0b0705010b100f051209030d0507080a0501090204 77
    0xc0c48800d4003522040080124010703061a01c803440762640000e00c04c00d2840104002c0d0720071303000903071038040c0b0788030078809000014030150280003e0010400040d0388140900d6001d1780c00301425440d83c02ca000400c2c103854003980002c2200303240a40500c40e41915243c40d02200c2d550440450301c18100300400c40607070003911520350100f10700344014442850151031f104441407018007150f11700f42c1c0a0000000650821784154040b41111550000240da15002c80781000448070051040740000c4000380d40d0b0303129400a07402015594481000705039143c00c40100c4080842ca11109204090301540800da40a071080d40a07a05c1200201014a10082000392003040e01c0c0c1c46040c10000e031504103034040c00004511a5000080800228400031b1a8018040300c03801071000045103508401440100341540601c441031007000c0010200c40ca9004080301c00000004d40780d40515214020041e15600a02c4240242c19042a04000d1000c1d40b055a01d8492941404103028999071080880c080b88158 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 251633705 1250 251632455 251632471
    0x4020a0207030212150f0702251418180106050a05010503010605030903282c04020c0a0206030408070c0f1a0c100603050c01030614030a260a0e1206 65
    0x180e008001615000328141c0e03250b01c3c0f01060360340c50f5014445c0c401150000711000012541000c00b48402d155042000f85e070304400c0d00e0716410315440c0742d01101c408071001d8440c1e401580d418280702001c1d0348a008182d441148000c100a400342044100b9048950803d0510f15003036103400800551072604140c0c0600b1600180c55051540e402c00c5d4044480358801054086248000c00180c03d101c04010002d40d42840f182e0b00b00144200000d07070040c000c0881200203681c482c01c00c0f1901d0035034140c0e40100542c4800c21100180c0e141d090100d1b080c02c0c0740c02d100020b903208902108000a1002143c014114a032003150b01e45000c076200e0003105102c0c1341c54007600202c0580048403880500c07a03c2c00400042c2005022070f41400d50754050340080c1d40842d0421107140d004019182c805581502414014010480301c40c400448a0408269103001d50311000e030840f060f00d0813414050070f100c0c00041618940d16078203a910100c8041c00303032a22207400d40c050301403045c101200c10032031004120349001e5590 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 251634955 1250 251633705 251633713
    0x1a0a030c050d051e150106020d0207050111010b0a0b03041a040305030606030a090b04050a060c0903020f04090c03291806040209060f04060e0a0605040e07060c030513170c04020a02 79
    0x2001c0034400302c40c0e03007160211801d01c02e0140200c000070320845480c0c0d049000b48001d051211040341141d2861006a21002c259032085070f000c4519500840d41d00290f800a00c3c22551650050701d4031409000d046103440d41003070740380f070740441c0c109081c42c0114403450280c03640c481c0e0003e40148010304840100c8014000030000d00204800d89001c5000790b4101c901c071040070034070404076281c1c00242c039400e41d011600d0f90320400340a4200711040c025109259654100828082d1441d008940c0030044e81505034030440e550503602e400c0281450f0782501079034110700c86a681c0815a1048840c0820000c05078180c540c0303500000b00d900c203840000047c181c61890240c91140c4840e07007440342410005d032079983d04c40700001c007401d501c0c0c950784030345d03001454291140146401c02c040030030700b1503605030440787c001c1c2d082190b100d070310b1000001c40c42c2c02c8807642c0c0741807400510a414111214050000581e00305140c03e48005a0b624003642c024002801c0b00301901e10121000003004124802d0417010009071300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 251636205 1250 251634955 251634959
    0x7030b0f0603150a0b01080105040b060d1515090311030a080909040309030203010e030d2403080309030409090602040501260105060a031e090b0a05010e06040e010e07091a0a030c 78
    0x4034181545070801c0c4040c0c00c41c1c010800318240d109425104a0301d20004554134001070341e2560340190301a004220503a400c00c40c5105072404203485d442400030100005031501184144031104108581c000c01d141e140d005030000e00f00c100100146403510013580c10420140f0800c02600c0c01048840546a200200c24580210034092205147d00104160180080c001002015031004e0040001c2094078078099503803103404840044c02c441c8400030f480007000005140c114080001c4501c0c40940360040d1006899503180034140380340d071150340c0141c8400d60400c6842c2080003041d03005002528026203440501030040e142121401a90000c040813400401d0010826424a00000d12002402d881e011031020b5a0794401403050302c1e015a41c1e04041c1c0e072460800f091220420b03106030812001182800954900b8040d0b40c5a207801070004d52155580310b074041002c202c250b0000317805a03011320540b21115a9000f80400074003c4109a00020342800030882d6189464041c40040e01c0e030000c1c0c6520070324 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 251637455 1250 251636205 251636221
    0xa020f0607020301050a020d11190c020307031a010f211b0929060c0d0305060105040e07180506090315040602091f020c01030905150a0615031d07030b 66
    0x14285006811820400840001d81c5003070203294801c0e00308441c00741e956510100d81c001158001c10354044040003c0c882e0701d40f00105541d40302a0b40c0f080e0f180c0311541c001e030786c00001e0030a14203030301c000c3c2070503440658a1a025640c03901c090490b20b841b4414403445039151141003620701c51843d00b054984440f00c0500014541400d000e000c8400c00c562259000d03144e5501d4812503d5001888902076280300c140c584014821104205988058031b1720342c1442d100d100c5065403044007150300d030107050320340c4000340e00ca91140040e5001801d2001c81d2103071380d092414000e0824002400c07202d2494120040c003040da400c2c4801200c05ca82c0001d001400e035041c00065000c02c0d1f400150080300c18580811032021595261200c1141d6008440c40d20504070041d004042c0c600454008514145410b002c3c445001c50404551b03820461f0390302819588507944c0105950060426402c40051011105e00001031294194040c0030b41d104509607004003040d030510000d56900051000412100070800001c090f1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 251638705 1250 251637455 251637469
    0x8060d110a03030203130605070201140c0c0d080d150f030b18010c050c06060406180f09020a06030b030c0402040305030a050c0c060301030b0a140103030e06090105090901030c15110a02 81
    0x5005039810451600309a00003512100168001c3d030040c0c1c00410741c8040107030181180401803286013096031030a400e40e40040c05140e8076004103481124082400e001140d0709001210645000a00050701d880b02c80c0380c0082241c0005050505a0346072003443c1a92503040c84030001501d4018040d041440c0c40d55540071006007000702001003251000310101c2e4007501c2406008100c17603064a8150701c0b100701c10384440c54503800a00301c510540c02c1420070002039100b001c894282000064012500120010303100014000c4010025080304070114001181c590541c4000d000f05022800e441d03204a44000b00030903401a400090100d0704104200c4880900481c010004092184c051b03541c0169818000303030194009070f1055940812007010810148420b04c00c084425400951030708941d4155103000701003ca2001c41d0b140658030001d1981a907030300460907504942030007000c0c0c407810768403480c10301d038000308034070402d4103902030b070740a903007006004046190221250780e00030130400d180da030204850 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 251639955 1250 251638705 251638729
    0xa091707030201060b03040501020a0816170c2a0714100e0307081506010905011722020a03200916051612080601022a04050a0212090a120905010806 65
    0x643d90fa409000030800c00380c5001e1441079000b00c000585504c000310016140c50f0005240ae0145a1101c5200c1b120300d0f04000100f070461003d5685100c035a94074000c0899920803104017407846900d601c5009074142e59031a010003a4071075981036910095540052020341d540003080c0c0340e401651904154200c031710070481c0320b0202800400702c1e84415942c03440b0740e040c0102c1c420228900c1020104024165030130400e01380c0140020700e41101b0f4020301c0203210540d10fa005d00fa0701040203103010758890b100c03600901d447c403850700101240341955032480c0018044006c41c48501205a0b82182c0111170318103244014855031130712440101c00341344090200da407548118007269140e038034070201d440032400e0b448c400d0384101c801e5114039a0a04081001a1030000310355a1072441d82ca540340000000c20880240701000c032015280819240c8074464000068001c08820714110209001004181c0c2800102c0300115030040c0d10040005107040f00480383c1115a000d980e01061299000ca60207080502241c46 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 251641205 1250 251639955 251639957
    0x1a0306100311030a0504170903030a0e12030d06030b010b03040503191205130c08031305040207080d090c062615040b100f110c0d0f0305120c040e0a09170703 69
    0x151410389100c0b600d07041d082514441a09682c960400c820000500140c2e0300b078114042034141411408000640e8a124051020080106002e24401542c8038100d84004116086042d00c3c1c032421200c5855000341202c0c8001d5402c000e01000010714221500200c0f40910f8102014500d05255103d20072211b04461254908000f0441488641d03000c3d01d22849000347d48004000408003914100440c0825061308a8038450f0020490000324452002c200800c85a043e180076883d68090305184c100c60090300e00d02c407001400c1207500c508108082c0040070540360b90351940f65104248400030f43e170b6402c08080840071003aa84000c282c0820f440400e5403c00f904c000d102040c4003050700046080e040d1000045004681042040d1183c00d4000c08403400d02201b01c130041c00c1000312200040c905040e925009026011200c00310014584200126008002d40404800e0a03040c4071100e11030b16030280c481c5818101c03000e00412161901d60146501c0f141d0020101d0000000300c186050a0b940700e09800c41c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 251642455 1250 251641205 251641211
    0x40e0702030708040e070e030105060306130f050102040b03010503190209150616030203191d06031306050903030a06060503191d060103140d021507080a020c01020715061a03061003 79
    0x20300000c3c0c8010041c03000c2d0042810b81200c1742808031002c2c2c03a43c080c000410b4440d9041100304091768400150183d03110040304810782c4071032014200400444008440500254000100800d50000f00350056049680650403950040c10100450507c4031094000a6001e2503d6012030b04402d07141030301c6011200300620030f500c0d041c0318801c41106942555411809600701041420603501080400b800c1c001c1181013980724030b000f5000c414012000b20941520a060100115030500c0c01a41c03194241c5520900820450030803a42c1c1542c0e9400460758454018101040415a1813040302941d0042460242d002d40d030202010200b4054541d0f681c000c00d80b1181e400400652940c1000020300035401b6400b021003103101c04042c0750400002501b00400d5520484115400c56020031507594070542e07510307004003603444040c4094060b204840396038443d0360021a0003000e002c29000044080c203840402008420780d00c18181044003514800c40c0c5070300c003003070000400d2070034048003c01860409103400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 251643705 1250 251642455 251642467
    0xc0d1a07091206141008030405240412050d111011090d060228050a0c06020d060602150109150b131e180203010506071e08030705070b10050105040e070203 68
    0x21042d88241480c140c440c035813940500388450f09059810340d08000008905203d00d81000100340d56842203125182c0100f6040329842440d0000d1445400000035460b240c40d9140d07590000840d220b42c0015040e9050701680d018608498002c06000c848040100082d01e072902280d4a5200240587ca6000b034071b05104000c01c0c00d4907074410452035803d5101d18001621f82080404503541c0c20b0007a2403000258000c01d448410302c68010040d034010545616081c5180a03151a000000e400340b070243d0400c550030000c020564580204540040445c0d031440401c00e03aa841000314191055503100391000d4840c004c06100040400008015003503e410115030034035560400c262038241c2c4900001c15a28026034180941010003455440140c0210030641c20765040030300088107403098800040840c02c0c44007242200001b03001a16108039001f074400c0340c4a00d003415028200354080c010443c6d46c01c04050001e40c028142c001301005445042c5d5900b403c050420943c00c00d618400703000f5030250710041c021 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 251644955 1250 251643705 251643719
    0xf020705030d0f0e042f041d0a0e0d0e150c030a0807020d0c050601121e030305090106050405010e0703020310080a030c0605090606360f090c0d1a0709 66
    0x8450b80c404032540d5100e400c41e41030b00000309485902e420407441107051603520003441c1c11402c400582d504208141841c600001c0521076042d00c00c42c1c0c0700280d440303000d282d031851145107115001c4c0f1490f40c11200303004074a082c2c22101d441c0c0143c034000c41c1c007003618070500328240e007495619001140404490246011840080b03289560044844400007034010401c1010b56503041c09240c0c00c0103103074204003070f00101c0d5985098940405004500300c5480503840582801940011403900f40c44200103440710360007a04005028250881d40740c1010741c207000001416040c0b91051504a8809504045d42a268180d044000c3c4d0b002810060303e10003003803808103080c08180642c0000502c00c2d158407480a180d0315003001510300040511015400010401450740c60310310301b2181c0d841d41030703e144050350400313030a0724502040c000c800c0308032042c64010400c1d00742d100c1c2d6030b45018049040885201041c080c00708410782c103100c400140b000780400c40b00c143c005140c1e10f076140c000480c0d0402100745615945 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 251646205 1250 251644955 251644963
    0xb06130509070f080a12120920190b09060307110d0c15050108030714121201081504030f0c020d021302070309060e0d081809040c17060609070f02070503 67
    0x401900d1a009040c04222289650f00002c0040001401401d070b078240d95100c18044006c1140c80318140030704d03202007010302452540242c15481c0d000840041240641e1030802c4c0400082c10024002d040d542ca441c0b101c6c1055041c81021181c9101c001444c10710103000340305003a04094142c0c02408050b00e20a141301006101d149500e954680e10308280c540282800d000204042c0c540c8200b681c41c001c018000c3e002c010040741e5025030424442d42c50b01c4c40c008403c0c0c1c074001000003855001a40461210320100c61001024101c030314810403100081a6150480581a8165001004903a1100c00700f00071030301070486004014001040c0c5a03441d550b9401152403401100041c901c001c0c0d0004041080581103c03e4001408640c07500900d40c804003400302d880403182203400b820841c400310b202d50107544110407031103880901502038003c5040500e00003505a1880c0506140c0c00b4052855020109001800c14820384000b4a00340ca15198607078181c0c2c083c58880c0c0701d0340450040c0c1001041e2614100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 251647455 1250 251646205 251646211
    0x1a090d3b120319030b18010608040302071a0d0605060a20011506030b0909150703020d1e0c090905040201080a110d0c050405040c09120b0c070c0f0302010e1c0b061305 73
    0x1200103006a0386a0b18004c0844000e0915a807142c041c1464052500352482c003c141507075128140380c0d01c42d840b24201030381b820245078044442011541d0f0011b4160b20000c0c013410f5000c44c8102c00740219602c550820005010f60b000c8400081c460b01c4401c10003d19070900880404040000018010004100d044032002031381c002d040480e442e40002c04d140e05007130708850390154044010b802c003001da00507905030b4444040c06c01000c058004c142a0714654140d808088a084041c0a01c114a405802e50802a004808502c0302003020380c440000c0a1029005040c071072ba50594441800f070303813170701400402456416080d200ca69420b0100400301c160030f12900e8003c21142c0c540030740b281c2ca0304003000240c840e010312910420200c148100304002c000090b410303030030f0392000c2120b075035a4441c540c80703010340200840030700211840403000580c1079882c4c14401c2900e000ba0395107402400380c801401701c1403500300c5884060500d44400c00c3c0100d06080e091b00c9d00014010484540030070130841e110190b40c015 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 251648705 1250 251647455 251647477
    0x4080f07050d0e0405101502010b03010e060703050906091c0306090207060603020907020703050a060e12040b180402090f010e0102190803010f120206030a091a090d3b1203 75
    0xb10106688150070620003801c0340401c5806200301d2030004089802200c0703d01c2000c000c00310310303014100000c1c000c1d001280990401b400801c52007000d1280680d03210300a8401201003490301e804506105404903c1910482d955002440c0d58404c000ca0700e0041110120b201d0304040c0e80c1c1c680424070450304e00050030754900491000c1011070030360040280d02640a40844259402403034200300044d0040741901c64281c000f0302c000b9460790051032040c01c2c8803500a0b05040392a0004000c00d95400c004080c000c9600484841d200080c1d0640501c401c0f4403e410200c4c0d800580c0049112041d0b2207280f03440b082030710610540300742c8a2114003100d00645403403400c550201c00480180203049041c003401c40204849810110003010a40100f4907a10010780b2124520392240340c1c800c00d002d128801c51400d0303850342d54440800d00e01100c140c0d4892014203c02030025400c0c010021040d82c00c6062030742020001102c10b10496647c2c25440c1b2040c4241640c903401c2000c101e100c80601c8001c2c0003629a80ca00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 251649955 1250 251648705 251648713
    0x7120c020a0302151003030c02030c090f04060c090b0702220213050909060403050405060c010204030206131d06010915120603060507170108190201110d0f0f0c150504080f0705 77
    0x101c0e00d000b0f818024000c00158030440c01000300f149500c2c41c00d2804080342d806007044080d07e0054000329041410b010140c980043d0f401c0d003444901c2407804140d82c8500d0059004000c806185181101d030610035205034081801e00b030028001500d00680c41d904444200201c030074080034581c1c41d0006a8020003269030f080081c8542c1040705041c42c445061344804e03401b02616161600c0d603000340c00d40c09907016050181401054040e40d05c40c003581100d01a5400400854807000035a0744407082c1402d81c0945008152340e15081400c040300d01c1c0c4120301640d016154540d801e41030170300340105c0f03c003446c2d4444108400c003032208421030020b00c104405036010303850219003440c2880000e00b41c480d200d20700c00c44803902a4010401858046240030b0310400710f05400ea482c05080c00100c800c54265841e0442600030420f00d416019005100502c071400c0685076549199a04001990262510540076001e25854603008816074050350250f94031038415040c40b410203014121030411500420003c8036a030380 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 251651205 1250 251649955 251649973
    0x30515270f010e1207060b0a0e011e050105160b06030a02130f06050901080304060c020f040f0f05091906110c0a060203010e0615090d060608010e030306090a05071707120c02 76
    0x5080c0510f21181c0d02890007000d04d11684020a40130f4070802c40060000c0c0e544004000c09640c0e801800b4005001c40407100005503110098481c0e030451038507501d0715204410000041c1940650140e807940d0389175241000c00d03400315858195012000500566040c00b42c0f501c45070044e5602d1100c0c0000c05610f8a00260681032500da1204681040c1c100700d01c100007000040280303a100100700d0301501d20914040741184943d1010655590983c40d8a980c850304102d14268540695400344d420428030030400e100c551981c04e52a61a1080b0305d080716481c0030b00c010800c01203805600b04018101040c40c0e990300d03000306100c08500302200c40340200e03901a0000010054140c1d045241d680105d4111200d00101c40080c2907110144608007189008401a43c03812090100c564400b40041030740030f00030300004001c4840d540c4c0b641e0040354000c1c80b400300c400100325280041d2203098410000f5480e0b410440e07401014141d10f030b1900920b0001000740030f680b004e10b80108d03130140c2c243c1e101860b0028041c5030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 251652455 1250 251651205 251651233
    0x521010b010903051009030e0418020102011b12110417100501080c06030403110c121f02070c0501050d0906060905040506070206151002013e0403051527 67
    0x800c010310050400404000500c0420404106801c0c01198820001242c5072286016254500b07083c00302a07015180c10521003042803081110107140d4404da000b00f0440e482e505092504180084514000a40c619080700c580380c002c1e8032450207240c624401c1ca0409070746200f8003c0a03030704480d40e103056030408080110740802500070203000d0031030040a415201c3c21900410120b0100620289c01c01ca8032044c002c0c4071071020b011030950b0102c05045120000903044d03503680c1d1802d43c14a078a02c1c0040d003001198807402e2500c2550845540080c001e82e805182500445d85034100003156184c050703441c0d25400002e2514881c0d18003c054072580803656150a080850a05100a0031102590085010010740980d42d01c414a4020400c950a032080c40320a0b00490040c0383c100e001d1144c8640030000e5800701c228000c2004003080c21403080302e420518800301c01206019511000b0040da0214446450782001d9030300881e400014a02480c540d00b25041c00680102c0d200c00c0602c0e503640056509680e40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 251653705 1250 251652455 251652461
    0x20304091d0f0712020616020d05070611060903040b07051005040b040308010b070c030210050c0105090303010f05010906020307030f0c0210030b030c0117010b0304030c050d0f0320180307052101 85
    0x1405101d400780000310b14004d501070a01e0603410b0000e00c03410002980c0d080901480c0300004071030360064194020b14030a880e10a0b500c0d01d25014403030201c1da80001402c07600400042c2d103445840608051401c02d0f1038802c0e1036002da00040c104480c030f80128030525506143d070744180c0b031180b0700507008042582018100600040d4061b049110441000c01c0004042440400b50108482c0e058030b040500301150340c400c03901401780994004040d401c1c402030140124000001d141138424203a00c010701d0907a2000159641c1566100361405a0428418070700030034000c10554080107014241380400484a0340010400742e48040107102282d91a401c1c0e030100d050410140315815801e0070422001400403201702d804041c140302d08803c2400010020f8209840307031101da03c503254448111034509a8401020700511600d408080c0000d28180503644140d02c041c0100c2c10110010000603d03266001c0300300a43c118240e0880740d0035110750700c00000e5640364034075541241d0604803540c901e1048002030a40c25 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 251654955 1250 251653705 251653723
    0x1204050c0f0f0f1306050607151b0801030b0a0b0a0e040b010b1e180a0608180109150506040b0312040302010e090114090a0f05010b040e0901060b0307050a020304091d 73
    0x140762041c2209850b900c40a50290340741c40f0486074440c0c04000103600d01e01502c6903803c450b4024002081b41002c0041d17800c10900f600040142c1404040000c4050101050301e51140300002420f100c0104042010170103501d412525030340b404640b04040d0030101d8080c588a61024076001d8400e070401083c04103613540207024180960b611032803c0442c14109211480348280f120488030001540d00b583ca551407682001c03818040c000e51441d6135600f50240540300c0c101c1d1040c3c00e10107aa4502c01103a0018840c400100364401c0036101c1c40c050000b082001884000c8c001070f00303c1c3d50743c154180d85039010055902402c8003940706954450541c400101000640504180640c03100750060082d1801c05040c10125101616421442d94030307840c2d150007070060b46c40c1c4082060720341800403c207049080001c10582d40000d1040085c1e443e030320010340c200c840611900d40a04014008190450301c80d40013040031543d24811030781081d840e49609402c03500191503043d4040002c036200c808100f414400348030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 251656205 1250 251654955 251654959
    0x7020a0f030e151b06270c04061203020f0c01121a09010e060a0b0705030f130909030203030105010f0f02060f07030f29030a110d150c020f100c0e0409081204050c0f 72
    0x40d508104850011b00e4403640010b016400000707074029100241008540000d02009105000040e0341d1801c080e0040d00050b8280c0040c000c0180c9407521920008260b1003140040c0d45254690100900d014014084c03a1600a0402210b90400341d09503600f40d8111b000e8100b8440a000c141080c2c81006622204c070390040414030000d1201c030020030404001e8070101712400d200550344400603120354140e01e541d900800c0c00e2911748030b64002410390002c061410b0340c0c03081c6c1764001c40d442040d02c10740d60503000040080c01a8006000141b400c01c00345032003a00311440f0308001c94409080520301f000c0c3d6000c0c890581d02e03107182142c08035103c0ac0520402002c40000e07800350408840c2e80d00c5140c01d51043c04010760251102e42030341002c00807245518154609000810800d220759084d0094450300429828015442445075803040c641e41c034403442941503040e840f5185030500c80703814040600088001070740d41ca1010b004000c0c5106012051611451060002e40580c5d2030310000c211046000c6000d0b18 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 251657455 1250 251656205 251656213
    0x2060105040515060430030801060801060503010819050c0d03030902031212070302090f090712110c07061b0c0b0309100606080606070c03200301050f07020a0f030e151b 74
    0x400e81c0c94030380896050b180440b02000140c01b411080e0041081d8159011200510610b90a424590f1010185058a01c2952098039a0b6a50310f001c0300e030b03404280940301c429040641480013400c02030210b182240d20a1041e15244040b0100141075400c03103040a602007611842c042c2d0031444e00740902800303049884074a506101907002030505103030303008110001f41540002d00c2c07003d030742c0e803001d002252a8000304a903000380b0344402c004003c100c66110f02e9130864200f01c0702140802800303003511040000310340140300b402d1a00c8421140c070010410060110320700c00048101181143c410500608011514a5982d044c840c5010303180c294120003008043c3e10704042070081581c0600c260f60000c03000c445c0c6c541c03954202d0625000811103544024520001204024080e4003806a80800e002c0224001c1085580305403509001c0380045825400681120103d14005240e0b0108030042e540249010000030356000d010400b10101c103404c42030b0b200c001240741d44da039801d40340c1c0c5201c0844175040030b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 251658705 1250 251657455 251657491
    0x9090506010e090c15070b2e0e0a090609080301030c06080901140412170a0c0f0e0f0105070510020a120f09050a14030c01060f14060301120b0a021207020601050405 72
    0x1071500e4091344995144a80499a56000400c0b44001521040d03600030401c0703001402c013104904074411150208054006102c116080c9020071080c1660895000ea20307103180503a2154800c000411f40c00d203007200c105a031010186d01007151280610f0181d4810303114444400c1c00c1442c05040014001c011b602d03d0380c1804031511491006040d210b4005510900c0a0003410700110305440000042107000011803096040100810680d048070300c5e08072050301d564507105405901110780920380c0b14419080110390500a1040d4030840003051124020b106071a0b01840701e170160408c0e0f80c8044d01c6640005d4250f244404170a40a110701c03c00c1d0460002e0803c801907065a9503a2910001d80c800f6180d0845118a050091400d1086480c22a800e00c001c0240c55203400000c1c082008500a41d5010000c107660b00d81242400ba04590580748506640304a5083c240d48014900c1e00051500c071145400f0700c50803a18040b2001540c1c02100d058000c0c024a40c10710b03080c0012544000c1c08202c1c1c2c60408806 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 251659955 1250 251658705 251658721
    0x130f050c090c04140d022115070f02070506030601090510020303061912350d06290a05120403050c0f0601151d03070f1508070f0302090301110409090506010e 69
    0x130a04041400ba1400b401220980c00041c4580d4207039041c0c0c200380c031000080701c2c1030200085035811640a88a030348074140c0d1641c1d00221104480c034220507000da0300000b01808580b40c190083c503808401407429043c040c0c0c44030b0104a03a201c4502c41035000d40c0c804401e121041c505030004510803403548000600561a20300000410781000b60060050140c10142150407104c00004121064901c148041015030400b030101c099805140c114070850f10380400820191005019400c200040c0c041c01c04004020105001c0d06a10110451081c803c0c2000740d5016050740c00301451107103000f07071a100d449694000041c1e0034181a14032120036500140014804581001411076121881c2c0c94004d0f1f0010104c0408100003000a101e99814426490300040c010051a05842981c0ca5002c00766102c1030130703d400752000310003030f030302c10000c1030305c40d0703007510403a44664050240706000a00100d8181440704402c0883d50290f040341c2206612100d10b903050040403c010303401442c0410701c259032442e003541 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 251661205 1250 251659955 251659979
    0xb07090816051e060a050403050c090f06010f02012004090b01090308040b0c070807030b0702150106080a0504210f02190f1113020d02041508061305130f050c090c04 72
    0x1400e114460101c030701c008283c12061500001440a00760075501c520700344002c0c140e5002440100d80034421045d40c641c250420380c0e20a80500080341c0c885030940c0780c4400544116084c3d031441c80c00c665888900b04509002c0d0f2071901c1c42d0500c10140c41ea5180d06245030b203010b480d00481c1940c1402025071003040011900012141285c0c00c21044680719150322071f41030b0800c28103a018100602c543c000100600010300c1e80e4500910340c5408444603180012161803000a0901c500740100f2184000501e1a941c01c1d0080c0f680306209004813100340584092003000d220080400c080000c00070241419440d0701040710028600c000001c1c40c25003400ca5951900d03036400701c10000c2009a2040c0612030350780394207410303012400b0048001c2d5110120041d1300c6000790068490540c0c5561800c8551004500512a280c0104d401405404241010580c481c020f0311307001e040d003c0100c2d1500c0c50240400c4114681440c1d80e8400d602a06080c1051003c02016170809015030271000c001708410418184403278 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 251662455 1250 251661205 251661209
    0x10f03021c020a0201091a01060314040809040f0b031b0406090623040213031115270307081501030b2d06060d09140d030e0706031e0204030b07090816 66
    0x1e0809a0365a100e103900324007415510a000707007100e801d40060181281c05041c3d0302d050354460f03a4100840e032907029210700b0400081e60042e04102c41001000c0d01d5090981001085080c01400031440c00c0c001c402182c07400686900310754852940013031401041c581405010028100d21f0410b002560600b0f44d04403444600016800c0c80b402d00d4410310034135032110380559840050140700c102e41035940341480084070750401c580e140b04000071608400402c0e020401d0322481c0c0030344e06481070403410354000820305410701004a5818811a000003407111400c00c004442c1d154801e080ae00075525600c0c054401c40c0002c0c000416885015075542c1154500e4442c0d4004014207020403181c540300d640205030703144542c8500400580c01c2c40504c0081c04000039040d40b9078918032040b03d06901180070b080301260340c074540d641150f40000c1d0b02008900c0c4a80c025045032085060303008905c158540b01c51049038419030048859080400800059a80110340030005240390005000c0015059180048582541c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 251663705 1250 251662455 251662507
    0x3121d151f0612391b06091502040801020912010b090718231e01080c0702010e030d08072d030e16031506091e05041e11010f0302 57
    0x700503115103140240c102c40762801103806480c1004003415807503102800350200c83c0b4400034410800c1c1940328480c90500c44c0c03c82c98107001d0100045a0b50380c2e08050000c7c0c03002903071695041ea0750400b01c98072a02c024001025030900060f9622000018419540a00c0c0c500d07a10070b074581400c404054481c3c0700201d03889403ca1a101c002c1030610210110b48100e190000c07a10301e04051780510012402007107507845120101d0b07801c245024141640c80d080340c1c0007404140000d2180001c202d500c00e012000d00551481418031281d02060000840e1504d40c010b001580064420000d2018080d080203859410308280d82d000c603444002600c940415544c2c0d004600308240c2e03107040950400300c040c03090858258030840024043c07a07403801c2c450080c89064541c0282d1501e809400034404045210324850020b076101103a55141032081070500404004006a90421410844030f404221005081440612030b9075001d5108060900051507c0344c048800700074148100a9090074ac1e084c00400e030007020342 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 251664955 1250 251663705 251663717
    0x10617010f0e250f090e15040b03010f29030703080322081209010e01180b060f0904080406080f0403230f0705060615070b0403121d151f06 61
    0x56210304100811250380c5042c0340340c4405244844480d8403130007422640c2110341e50410340c1c9403500000828090190307160718095149501c03511090600c1c2e009601d0b040740040c00014003044507001481955880c80544000f000a11240301f45907c038481d425541c00c0d826801805070784d007580e0365220540f101400e40d403c03048500c151040f031402c040f004240080d038000130071a20340d404411a80560701c3c046d60340110950a010540c00002014480ca440c148a8040f400c06008820f813030b14170390410081d0009811071548114020241c8880e12141d000b00e00c101c1e01e081e03a440c5012030052000b000035100821400d50401407201003907200496a00810714003480c1407185001c071280000b1403181407071041e24580f0120b5294103000002c640c60b4406c4100303036500000c00100c1c40500783c2a11503110004c3c010782f44500442c011a1080d01c02142000398030000141100244013154141d0f10303101c1c080030859224074121031410f800304a54070380000d40907017a400f1603c01802007060214060040c2d1080000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 251666205 1250 251664955 251664961
    0x30c070b090c040f050a0608011b12060e0903040905060306010b041e0503010e0109060501081c05030907030807060e1605060f070501180c08060115080601200114010617010f0e 77
    0x2000b808071107510798004208110003002e089240b070180c94115901c080c40c52828000041c01c0d00103016512204100000412400c90100c2c030035580e803807000049020541d5500b03008606203070403d410a020341c2001c2d00a64072a441c1c40070b002d09075240180158000d0301310200401c2038050050550303098a401c00c003003590240040f140102402d01c90f03801141d1540c03c18103203a03032045042d8403404110703000c1d03001070295a072100f41132661913540d00303041c42540c041083e101c1c40d41441800034582000d81002654481a541d4803840703086e401c084410b4480b00e50f00e510014031800200f052000c1d00d03035424043c002040c503207000245280078040004003032072400078203481004000c0d4085035440441a00050a032020f6041007a0312802c54022062107204100c00070801d03004807220302c8019812640c410b40701d83d49100044031401d60700c441d50105e0f610f000015114025080c000c07400c81c00c1411112009540c50700f140104400c2c915040c17a105d0a0304c450051080d02ca21801603020740e21005c010901c992 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 251667455 1250 251666205 251666221
    0xf0c09010c3302090a1211060304020d05060f100e190c0c0b090102210c04050f0a050325050f18040f0c060c11010807022517160b030c070b 61
    0x20520b03a425840082d003000280c41101e060380c050b054500055510302503498403078001021301c842d1a0000740a5002d014001d035210310b000f4008550085c0301406401504085a4400f45403020035601c1300c509035805e0040041c10381007d59184002c107005901c0e02418202180c01c1051440d507442c10088658503032081e0000c0c68010040e020186a01c81198107243c5481a1101d0003074110854041da005a03240455030001c2d11824250300030300005204602d030602d0300c000c100c160607400b5001e540043d410480058036036020f0101c00c4020f50044110201c0d0380c44032084465a02182e040103100312810002403003551207002802c85410100c0c9058405078039941040b0101a000c08030041a00c5041c0038042007007a403145440c440503100c0c0381c80c9500f28882c0d0005407884d08044800d000182d11a05221114001d140d03003600c2c0c0d82584500a1081a4840340301c070f4855900c41140040941c0801d903190b01d07054200d9100001800c006101604500305001d02201a00c42e40c113028050220601c0441d50710 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 251668705 1250 251667455 251667503
    0x9020f100302270414100e09010b060a0806090601020609210c07030c080c0405010e040b150a09060609080109050d14090901031505060d050d1412070203030f0c09010c 73
    0x10740c83c0e143c0c550007424031246038420b500406044140c0240d080c00b880c2e01510480f00320382030180800049402c3c1076030a04d0000952058000d001c0310319503490b0024420940c64440040ca506401580c51404618240040c440300010151a2904560180041080d0350f000030808405010f807012552000d074203110022519400f45c40d80c10340c0c00e4019480c0000c1041841900007040710b01300400e58000503052410401107480034420541c3c003460071b000182c0013074404080c965100b400018202c0211401c5008118170f040c0340e13088441d45a0340c40030248226504440320400a00f200c4000b840300440a43c4c403581c4402c0e04205003828071009400307a64903502a4406e42d40e0810b4003a00b80c100541e900c0c10000c00c950301c036540306c00c0003901e01804502c09080030007080700c2a5030040000d10038051254800c175980c0000c00e103860300d000750a21100c00c48013035440740107000b549917500954690400d402c0700c10b400c40c8003401e0f41411800401070f41c2540d076000001d41c00c6090b0020705610010303006251007010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 251669955 1250 251668705 251668717
    0xd05070e0906100b0307050a0c1b030804050f04050907150c0524070513030b060a0503030c030a02010e0a050703030f0c0503030a0c02010c03020a0203041707030b04110102010f09020f100302 83
    0xc21600401000003551000903064401c0c1d07801000215225076542c910030851009681c4071001074002c000700420075006240508003075102c0e54500d4103020780381403001451902500120352140001404105501c0c00300448105020226810803a50818180031a5598110305ca20380c440410b152075911300380c0c0108413034204641c11000340c40d60b2074250060092050a80a081c00c0801e5515012504081c0700b481600c0c51150001c001c00c0c9010f003562908a10104000e1280d03510024811011501c0d840600107801600e007140d0056840300f0403900c0107825640071008001082e071090500c8400302d1000103001d41101c2d054185103040100e02c9400719043c01c1c406c1d40c05000c80c8400401d004c800d03001e076030200685c403150f075000700300b41043c41e001141179100b404a44001a441440184a0710709441d040c03007014a00305d070450326002d94940e5801441132085505948070424082440f0507546c080c00741543c201c0d4002c82c20003608401e81c0c0001c01c801200d242043c02207941d0000691007038001d074100e0b25 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 251671205 1250 251669955 251669969
    0x3060b090f0429090c07030f030b030129030c0d080414040b040606020c090105062b0905010603080d050a0603120c050114091f020c0304051c120c051902010206060d0507 74
    0x48a0b1a020b544501c00712140044940138151039400070300102d6207002035640b0a6851356408003000c0711404102d02034440151074617450f550b104a1a80040c0c242c550061102d00903858880401c060340041600700329001c1101c6d07000c3c0b010694401e00040b207260844042d903101f03032a01c10540c116800458020403c6201050304907251041c0450400d070000380202c5c9030a41154481c174542c2e2180103100c07450080c022200310f800d5120b90741180007007030006810000d03041c060b0005229000303a1101400c0d200694402d8642c2c01d800968140c40d0341c141d0240590083c401140ad102d40c0f4a13560ba004024a4840040810058014030034401c0010030340010444014003150540702d41004c9900c503841e000c11840c540070314201040c5441d940e4006000303480b420706800c4051400c0034034203000c0c00141c1c2e01c28100d42c0501184001000005440410700d10704215440c1e071240d44140c1585005450188024041404400700c0144100140c0c1d00140c1a03030700200c1544e1150780c2ca01f082c0b4100d407070001d07203030003046c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 251672455 1250 251671205 251671241
    0x30f0501150905191401050d02220c080106090b070807031101050a02180d0210050c030d150f050301020306091f0819051509060406020a090509091b0103060b090f04 72
    0xd10318003983c0225016003020b4000003602c0c15210b2860084854040c8500002142100100500c1c03610820071000d860018040c14002e41006c408200108100b101007202240c2d502e0200c3c0c40360707621803501800340905052550f80c41b420f20303c3c903020600540320010101800010b000041611907201103545c5144000280101d040100ca0140603401000072103020003191406030a85d46009000383c4c0c0741540150191f0245848401c00b12129444210800c0b0b40b0301c0304010045c00c030f0540c2d10031160481040b103a103829843c03e03c551400c10082c15130000d0b03c02d0f030041c82406550341c1c49003d103582042614218001031017140c40c901c01401c0320b03070303014000500608400c41d21003000501101415880382e0291200a1700044401318940b10595400c4007960008001400040c1c407a07009040c074140505009106d00d0391000085e00000084504040a0b0031180d06240d00a0420b039a050b5140c04c01d08040c050f50b03081071b40c1080c480c0a0541101c0c41140001d500360001c1c2c841394411108810f40070020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 251673705 1250 251672455 251672459
    0x604090f0516051810030209100206040b060603090d0e040e070b030f0c130b070602040f0605070c0602010c0e0f0a05042f04030f060203040615080a050c0613030f050115 74
    0x401040c040399448030010782c0d5000306001030f00c29000ca5210007940b9014541303803c1d52209101182c0741a00c000c07070a040d801c00a1582c0d560741d400d07014510000d10780c0181454a0f2071318180b007442c0c002030010b0380540c0003030040c0300c02d03100d01040c1720544041d2454030030000095080020007070b200406002c2814010789202280d8000d4000082d44146d40b0444110710319200e1241003031a81c8110140f0b129140c2c41564140301074031134032000f0505580514000341c2003d8462046e00c040441651010000c0ba01c00036040c0d0070002c0b861002001440980002c001140820401400b200e00284450384610211058040c0e966030341d03c0d10740e0141c0070180041081150001c1312010b5091480c1d8042d201081c1e0b20b203000c61a0304001d08985c2640d90141a0f88050f8000b6503c0074040e40003c2c0c000c540003521a02e6408030400c90103c21002002a9801080c403481c090505600b40840c0c4075240c5d00544081080c40050350401000c0401c5990080002e0020041030404500400491841c030084401503840 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 251674955 1250 251673705 251673731
    0x30b01021c090e13020d15061a04140102070f060f020102120907170a02010e01030509031e0d0f090515100f06030b010306142b06022205060703080114060409 69
    0x102c00b91514a03d201600f40c8803080c00c11001a080c2c0c5000390300141d02c1e0050b000103071300c03002020401c0041e20004640203855100442e00e0441c80701d03281d04060400705040184c60316000341e04104070000e002901020303040c075032441c4103044c5a01420043c01980e5084440d4103200354100c44590002c50304015050805448076500c60307034148130b40701310561200ca090020040c04542c07040c07000ea050319240b081c42482001940074042c01450304107140001c0c0491403803028010304685100119001081d07076880302d003040200711640c8030204140a031031300c400b6100060300002e0503a800041c400d4481901d41c0c0707a610b85018440c00b07070044200720300d10510004080b40c140c1c000701f40078902600c00340580381d00d40100041c9101030010095004c82d050108003101030100c0c0442811210034600d941d00c044140d12158244ea000089000002c81d0303a18034140e1149000f8000360241a0864a032442d00900e41c500910054060040603024410040c1403100c0355038070b8080f100208ac2c4d090050000c0500303800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 251676205 1250 251674955 251674967
    0xc050a060603120504060219170307080402130903020c1e0a060503040b0c0f07060c0e03120c0714090c032208120c09150708070611130605120601030b01021c 69
    0x1100301c41c4001100740d40c3e0507480c0030380103450540740c0b241c0c010404406102c001c507004000090341a103050034104141c0103001610002584101165191144542072a1040c443d40c56200c072801407000c3d143c583e00c1c0c03000960201e40c0344c00b21802110071202c4000440682034881c01c0c0307140d040b903201e10200c01c00a204c5420401a612642c00768043c01031030380d603a0420382c82030b2240440c200d100c51010085240084d559a00440d49001076107840790084500001103442c081402c02e01511051001c540b244600c401000603c0190190710404686040c0d2a000304004040c0908510711540d800310001d205201404000011601010143c0c20700000324285010305a119000c102d144805c40e03000244c1d003072007800450703000d00406881c010000360000c1000342d0350b41100204582821081145501003805c0340a0200c0034410394900c0399035003107070030040da03901072a0b50701150922070240070300012441c1d0f4400c00c03540241e0030b00780401c0510480c00100c0c02e0422002e00e01e041880038100c1b4848559120b6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 251677455 1250 251676205 251676209
    0xa02060a0c05122e1205190c0e0a022710030c27050d05010605011803020904060b011707020f07140a03061e0e01020a08011202030703060c0c050a0606 66
    0x81081040d003046680498541c4900843d440711840a040482c0400390301c1c03464080d0080b08000d529094003400c006081100d2042e40c418210310b80b01850501c2404010310040e5000301c01844080b8803014199241001c440c2c241c4582c00e22554108002180300341e0ba50111607140c1003000c000e8407140248050003004081c41500c030341c092902c0d00d1240450f68024405c0801f0700c910b6440b412522000c45140d00411100a00c080200e10010713040003c1e07544406100501d400e114000100b06503082600041c6410045011501d181480b4030f01013001d1386510110f550003d8101802003600d00f006030050760900d5a81c1c045e901c1500b65a0100320140e907001c5402d081e400c0d026400d8442c1c5940da5440e030314414015441daa40d000c0031a2108100203802507104c040340c07405410400040800c80c8015408603410415000110394001800320401580000b90501401d41200d038200c0e0700d1442d80120b0354442245c00020112580c44c0e980b05001409500ca042025902ca01140c00f111454540080500014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 251678705 1250 251677455 251677471
    0x903100e0d0e10020a020405090a0c1517310f0605040209090304380d050702060a061805061909090506070305040302060f070905060304030314010f050f06130b0a0206 73
    0x610541d526450f01c0903c41e46a4000f541c01488004025020030005040103803400c1d9040c891504a6400580c60b120400020405040e0754602954203001c0030b0202801e445110300003c8460f000c1040790a1035143c241484005c03042c0d00d10b80310f2409040b420440e41d003103602030006100382c003030f40d420405581c120740e108a209540c0d01002e5260003900c240d90340203d000c1c00d5400c4001c240c5595042c40030011041e02581c0c0c5030340042003010f83d40901171459000300302022045840b02c0421108603010450947c0100c07181108001e400e1074000e4501c441c90014000f0b8960640b5080811035503901c500040f44100c4103101003650b59640d0304034140c000c001852045496000e520300003541d080c080d1044511541d0550041c01c116500c40680c10101c40f0010301000600940d603201141a132108000fa520861080d00c0024141c0388103148000300f60b50580c00789880741e514000a1205444020203070440b21400c2c0c170025103500c10200d4020818000d85c020104000780032520f6441b450340000d40500514035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 251679955 1250 251678705 251678717
    0x30803090d02100204051c081911010b03060c0a0c03210606020106080a0b160309080316021605030d050d0b12150c070b0103030509011b0c080f010203010e0604020903100e0d 76
    0xe040503e040e4055031180365480350150131030f841002d9010b000a6451440b650f2450700c0c04d40c2c5685551016461414548009412085902843d0341c01f4400c11440403000c400614061a06910209092145000a00411a20350010400c050103410880000e50003048070207514545d0303030341c80c00c01001da0307101e8400158208000002c101c84007064000800d40c1105038001c19581c0c10b041d40c028480c5031a0340d0350030503691701c41440104400b0b001460080902081c9c000310101f00c0d0100a1904d000c0c43e18084841411b032004101c0c3e40c0d400202c4944140282c1407058858000030000f100a101200c1195040031280c0e8010745900c4022400c402680b4802c00424003580350344503001c0c6607001c2d100c0014102c0410000501c0420b0096001e001400c505140640c501e206120710b01203501c0191f6400c9070301000d9094240b0170350a040c4914603c206050300218110340c03521001c0c054951014000c140500d500003440c07100b41d20f041c004003145851044062080019650005961f81009a825000284 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 251681205 1250 251679955 251679973
    0x60f0c0d111b06031513020406081014010c0204150b030a0608010c0906090603050a02040b070506151215070903050a05030909011202011d04060503070e19091a060a030803090d02 78
    0x240715980c000e085405407007503065030303543c5d4038010225525400035a0321a6441800c0382c940310107800104060802e0f5501d41d4031a091042400f05030440d0b40c1c002c2c501407580229550304036607114400c0182d40b501241e02040c02070000c1c0080c100440c0304d40004000c0301000003000943d282542005045841d0349000700542d200d6488221110b1000b0b0043e40e0014155020400900e0b110f900520f402c01451800185416900d031940d0501da4464034048174941c02580400a0185131040e01c0c3d03400c2130080d035640c01409980c6500c540c880800d480c0d180c440c244440b010400d000e100c0c90040000c0c580c04030403903250070002c0c00e220355650401821070740f1030070b9014000b08a186010b440c04082d241d040e1075003181001c030038844d804482032600006402580d6094002038954003041101c000f07260a5120403010f050480d0640107101e031021039510b2890814420340009054641c40c402c060740b070414030007116203e80b40042c440d140c40790f001411881000c402c5c00142500410b414658020b0790b022564616 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 251682455 1250 251681205 251681233
    0x120f09110901080a2619230310090e0a1a25170a0f020406030e0111040b070210020f0a03080f06040608100f020702030102030906040b0c0414060f0c0d11 67
    0x7000e80c4001003071072280102000300d4050703404107070019221700b01c1800d090105680d000159a40d100089000082c6080e00d0a90034403105d4504000c5001c541e4041031451a1406c0e0110305c00c03441d84070f041704c04c50b0f4039039001e800080c2c140402e02c1200d070300c031100c050400a032007040b0303204440035186064900550111031061a00548441c1d207014456281d03607850b6180e03e0400c0c5040c1100031300d115041600c074000503405612a00c004c00203440c158400141c040f01b20480103003107410142e18000242d00400c418000e0010740c0c000da540350307030341150030000140104000304c1c141103600c0490346240c0b20360080d000401d900648201e106821030900542180e582c0d40030042914214821000150040b50a5000032501e940081c0036002c0550390140c03a0140c15800b203403c90307004690f1328005411810601082100c00f000c09600441c00406031402d040c10900469941413000000a02c40d190006030b160a004840301510101441d040540e5280128404040d224001f4031420048a003d20180d26441c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 251683705 1250 251682455 251682463
    0x609060e01061b061a0312030a0c0311390706030f1e0507051315020c01020d0e06090d0506130b091b15040e0108030409060e070c03120f0911090108 65
    0x610680c0c25601081c0d0a0f80b5130000a0901e00790041d59030407068058003085e00d04100c0b0304c103003100b0380f007046507246080300c043c800703c620036901801014101140310b4914410032003030702d020042c1505802c500f40c02041c003469001401d2000805201c50400d40105c0903000813071020200c41480c0c0f028041843d03040098011503c00340030101620620710300051182803140e00c0f40394400701c50706242c2e14041d07018024020041d801e41c091540f800c43d10f22403506040d030521025801c480203000501d40078056400c090400d0b003070408618056040469207101325929051600030454011054400c0c030b040246625000c4000c50340d040c0c50b182440c10110741c6011000418640347c000303080b85510600345084c100001c0803100007038926108014400840d090541039502802044404011650341d450501c00728140c4905611819105054008000c54543c000ca1b4516900394140f030300c10308401038207014100512401c074040340550b140842c0e010421001070724005094400f214801e41980ea124a050b0350303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 251684955 1250 251683705 251683727
    0x7060c0e010c060e0c040f0e1506010801060e0102011d0f0c06040f1a071b150305010f050d050114010f05010e04061518080a0c0914100b0c010f0609060e0106 69
    0x24008100342c0000c60540e82c0554a0110441c0c04e035202040340000083c10303125030500101180703036a010590800d00d000c003d40c400000c100d600071500c40c0b90180010f0001d040501c511000d1000c07040c4140c1051f8801e501c130a00851002001240181d0100d411b555030f03d1000c000ca03c454801ca850614140c82c001c0180c0742160410030b81a0200c0d420103252962502913a0700c05401d00406000c0d0078005800104651003100188000c3ea01070f0f03190507022405144021541d0052501d02401030210040c503c4982081e210140c598050354192460154014146501d0100c9020425400031801d0358244902c5021100300340e07249131130b1b40188410001240c002c1d00c9400d00d00d0748120610100075000d10446501c00c0b003c00b00c2c00038901c1d540c8081d542010f1808104030b980058004090200c19158450148000f8504c6102c254900c1d1020300300706840c08030f02544644003800f14404103400800d4100d0b00f131000c4aa0000e00a680d40c480d0b0341d130701800b043e00075024145c1141001103055449050b0a02d6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 251686205 1250 251684955 251684957
    0x1a060307050f060714030702011e0806040504020303130e15120303011a0714030910020c21070f140f060a05030402060306060c0a0302280206072909010207060c0e01 72
    0x4016403800c0100015111400b521580040041c01070f0b07408207203500140c00385421600701030355076401903200050000781138900301400501e014118014455000601a034131a1050b100024151106e000007491405044e00c0c4419500780d00402040903603202c1c00060040010400303c80080080804022010314880749940480d4000c1c00100481001e40300c02000a24208141a07e400142d0b201d039400208028100155580700094940050a0244d0000443e440904c0034101c900310400005036002074400c80800c10900b00d07440d1b2380d80c05a050180400800c1d005070319001443d0b452030112182d15004d040300e4420140014040d0060401ca4200c0b50300070b500e0f56441d4a155600d03820030015410142410b1f8200d0414010302001c1d00e0104200c0e98542d000c1d070014080c022120300045020000d5842140d003e01407400c0100040c1c4804040e076591030f911600400c0c4070070000c01408890b84200d00070140020742042440180c41046d0300811403a4000c200500040f001d0721001d844001d0303183d500354 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 251687455 1250 251686205 251686213
    0x22107110a060c111c021b09270a06090b131a190c021e030a0906120e240703051006032307170a090503220f0303030204031a0603 57
    0xa4001402c95000403903400c0e0604103003840300c1a522180b40b410550442ca840501c07414402003070415010003c0984c14a01101c50074142d068030400310340e01a0b0050300070072211000c0001c58044006107003940503405c440d070044401c524094104440688100c9106540f00700459012450300030003042a00c5040d0740241300a040042015140d80d80030320001d050b00f400b144803800480c05c0001c80d0040b4100640a41e0003810207000c449152620700130f14100100165204000b08510340b50040e4105045940d44d0812511491500c00803202600501c100920a40203a407510391668101100380320719410217000800c4d00d90ba03030040035005c0320010b54450286500c0e8840c2003001d24401d4100440e400d409100c04203d9024485d507516409806071684000305500c10001e0b4031441072612600d80c0140000400e0181d480b0780e03152252a449001420142c0030340d1040079103100400d90040364000c10300c8804208000703030f580c10020000e4205000c2141c050030b6024025200340e1015100da0300404006000e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 251688705 1250 251687455 251687473
    0x2070c15020712050a05010c0914010c030206011e03020d060c020f0a052e0501143c0a0b0403050a02010e0d02030c120705062d0f090906060403050102210711 69
    0x100030000c03c1a941160701c1d00c00ca440203c0010b000b0f000340b101e610b40c142c94407611141410001c445101c0b218401383c0c100014902000046540090040e04407494a11060007040c0c1504001180843c290000f030340001c1a090254204201640b10604000055080d038010020512480781ca0760500340c1c003d031241c1d0241482c00d00700e002c8c0b4840800d5600c0b10380e8142d10424074288a1000b07440f02640030302d0440700c9200b00c90503641841511a102e03c4040085400c1c8801c101c03100c030014044509030342e8880d10001c1c0880c813282d01c40060f42e10180407555612511150742c1c0c50001d03614a03401c48224009669031002070481e041c52640c0c00758444e402400b0340201903ea1781841032840c01a000790300759203c0c081c400070711601c07230000a28150700e0302d5041505003114906034400d00c0d0f40912401c0c80303140040000b03040a000e004191294520300715a6150b003274a07400c00180841c080c5400141030380d4800142c20000c0d0320400d8445205040505c82c880450351940e0058440039010040c0007a203400c80020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 251689955 1250 251688705 251688719
    0x8070f08030f18040906050103022106010e130b0a020418050c071203022505060705030f010303030b03030d05010b0d0b1203090118170f010b10090510170a02070c150207 74
    0x5069081c501c1c40c000c04250f6490360000c3c0c107850314800150742c3c00d9500c0b40144290f040899404e04a1030104041042500a41580725901d04051280d505a4507050011506044020540fa0446500047c20055504200d20458020345c0140319070710b18007144800040c14aa40350145521800c2e425501908048241d02c034409080c2e86c1c440c03881c2c10981e081051044c04043c0b946200e8104600001d11101c04409250440c0341040140205092000c00c0c0300f084000d1882942c51030540303516180c00f00d020318500002c02d1450107a2400034176007074140800130841c03072a810040c1048020303024041c03050310105d0f0300340300819442448280f03198101b0880321445500502c1c681030604c68500442807000c1d910610140d40c2c800000b5aa103c070307080059640c0c00c1c031030240682d08a180301141c84c801e8080e802c5401a0480d030076440380c0390062800354a400301c014041c4554806c041c240181441c8a4549030760780400940c444c0c04200d44411b1940c0d00418900c0100b0741881e1618110340090400909140c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 251691205 1250 251689955 251689957
    0x1060e06040c030e0106080a060e03040e04152019080c0307031a030604050c2d150c0f102004030b040c080a1b05010512010b03060312040f08070f08030f 67
    0x40b48002d040d102c1c100441c1d51902403003031000520045001c0c03c03010909140100a607113059424030ac0e90350003880188003640605d101c040c1c00079444030b4000302e16074500030fa00e80070302158850302c51590441900f0000c8104440000c00c0512036042600c0c0016800000c01d8035006025200c10b06500002d000003406580a940205200001c00b10013100103005040000c1ca028000c6808848030342107d407403c02941000c801c0d40c0948480c0031404407002d0307241050032030401072041c1100c0c80b90001240700d06104001c041221190041007081d0b402a0384003962180e41c40402c41d8898907454545a01240f086082e2100d507030b00f4803900010646000d00c1c54540c4103425802800944110000350400100d41000b01704c90403000c4d00c42c09211107804d82d4034031001034031250b41e0302803418807004010303101184c81d403070415034151104904084c0e00e0341c480c040403a1401c40d00074400310b000c040002d4003080e1490703800510f2044540b804120703103450382c40c0d1198642c1c00106125011217a80123000240c0c5000d8550 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 251692455 1250 251691205 251691221
    0x10e040903140a0309080706150509010303080708040804211205040b030c0c030f0d050604270f050c060a02011506020a0201090b030619140a1401050a0c0f210806010201060e0604 78
    0x124002c00d080d6400c0d220340c6c6a0b41c0c03000b0400c84510b03070743d0040c05565203800c0300c800f401010708807554421585181c03406802014018004010441c1c51f41c00101040070407001d032405000380407101001440200d00b0840041480013045d54003680c01e8421a81c078a03c00d50840f0b0030f8501c0c14141c0c504580341c074541d008541d00704501b4544c15000030304c0a0b40b0b808480c01c000d0030b640c100c2c80202184505140060204488010354000500c9a00960405c5528030000c0c1d540a8107074003101102c082206824100d042c141445c640c0c0358800400145a0319483d8150480010726003100b140080c401da03a01030607a40d51062003030080c045200703200c04000000030f4001a513030091002e07000d200a0300d5004040e002c000180e030803c140f882c0f03140000300c2c202d0a00031501e4000d4505c900048408507107130b80020313045014044030302d0100190301c2d010400304492182024000c1b5440054801c01001e540f4400a14040c500e82c0880000e0514000544542c4140a4181102c40c11018540a5103d841c20300000d0a00c00e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 251693705 1250 251692455 251692457
    0x6040b0906091203100305030a080a0e071a0d0f020301080c0f180f0403110321060307140d0602040305030f0c0d05040b030c2803020d11090a0506071b0608010302010e040903140a 78
    0xc00c0001001c60000c2c03005127201100c0382e4580841d40340c0a03c02d081180e12680200300f0f6070740500c60510042c1c00d034102ca00da0300f0004024094490801c2c03610940170707114055080312180d0010000284407200000d00001443d4200c03400d80042d1840018401c40e494510524000010540081130701d443d40301e010103820501900d8401003054031000d04500e154042803000344d406010b00240c585031141c03103034070710b401c00c0c421000f86c23665902e44240c0703031021141c8102d00383c0b00d1810005281d0800140e9030459000795440b00550391101c510000342c41980e0042003400845000d40007102c084244510115400e48032803040190640e180d402c050307034260308109c4407070602b209468645074009141c08500003c0d1000b60b83d000d41e8801d83d40c4002426030303000ba403051f69210310911100c125036441138038200541e00b003035488544480240c1010401c4070710401e940f403040f00c40c2c070b80045400c5038401d0b10355040e81e000b03888502411039100188022a10010750240000b046c010168504c805c0b01c2d0005c02d840065 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 251694955 1250 251693705 251693731
    0x30304110105130e0c0901140306210c0a030602040f0605032202180f150312190201020405060705060108011d030306010e010e120c03060108010e0a080a05040b0c06040b0906091203 79
    0x26204c6492003a01e0981e40e01c4255000402c2190956a10800703e12a1038500c0424a08500f4020042080c1c4da03101c1e03500720704e0744201041a22a815003044142d0a01da8000c0c1242003595603800c00070025032103400307150000081a04041007440c014401c0700e002d40e01000600c02403070b200c0b00c00100a6403042078102d0f401541d5070100c0041030030710948280101c1d049e88082c404d60500f0154400b4004c25404031500907080041240b106001e40420343e003441c0f483c640c65030710031802080128020304c503d4000301c2d071108000c40c3d04000e0100000b0400c2c1612001402005078606082da4614085801140f130195540100001610365200b04110020b00006040c10704462210600240800c91405403a201650281d400c41e801c51404020007401091181c000300700d03a05006181d42d8641c0d02a2401a080c0480000c00055082c8100111001851509805500e50024400701030715003c0940c2c044c0c69070b90060000c56810100070503110300a000b050001c00c49101c50704007208564100900300c00340484 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 251696205 1250 251694955 251694959
    0x5030c0403080a0f08010501180306021309020a1d030c0d02041508061302210604030513030c06090501030c110309010c05010b041b02120a02031602040902040905030a09050303030411010513 83
    0xb0941c0c0a020400c003240c580b00ea8550b84004001c0140704140c1c07090b410071000c000c080261098210303401d42500e40100015950350804200d01c04540002c0c1e00541445200045a81500d540492455500c1d90700e019095807a0700282c04060f91490b0400c0102d610050762140d4038010714055018030b00043c01c0c8040c00c0e50741a581c000490034540c0440d00300a070245695009030841c030340840b03d240340341044201d0180080c00740d00316039a5030800401c010140b240004024941c0c1d00200c44141c0110b9002c0c10244003151a818010701c010200e2140601180c1020080c421103402641c098a20180480085062040c40ca004503880d0800f01001c0e2059540e030442c6c40b095460354061407002881d0603001c0d42d01140580d0300203150001080d40045103101c103009104000b94040102d070004070f070354015681d16100d1400000c00405900500a40c020b2420200d04100080800a8040c481a54503443e0340030740c0d02e01c01e02d600c901c400c880091030904d1511610410358014005454200341200c407010f0016 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 251697455 1250 251696205 251696213
    0x606040b090d121d061204080a11100903030c050a120c050f03090303180d2c03010504050601180207080304080f220302090a020403111002030d0c050903010f0b09040305030c0403 78
    0x3c40104000c0001043e00e80c2c410302d115200000d81100c2c00080e6100e501c0c08160102c0c40c046c410300a040180010400124424158825042c202c1030850316011744000320f81c641c001c00024100d1003422070200c0e06003004038141e60302580a071198000320b501e0710845455074080c07401c020b04100e2003041c14410244424030300c3d0048030002d14402c1d2030f88801541d490800c0002c51010400000b584c01c0241e01c501050000580e112201006681c40c1510703120420841c180e41400c0da01300101e80c01c2c1c0561070401000240107000600c24100d5203260340c00c104540d50250310f80240c0c41020700140050300c2c100013140c006450200144240c80c4000d510038181008064402c0001c0b001c50043c0349505054a001e00c158a0664030740383c0c021264100031481c07d8556942e00c401040300c7c0d01000e105d10415415900258002c0c030803614480e401c0b9104128540c41e008024040360003d03203c0b00d0003580b92201c50708010300103126452546200402042690b0741356602110300d60f0009107660042c401c1071100000117 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 251698705 1250 251697455 251697473
    0x608032221020a0f0506190e090f100b030c07030503090313030c0906060c110103020a0e100309031b0503160c0510030b0f0a0e1617010f18050606040b090d 68
    0x1070036860050000001a0780108580390540d80c00030500886246020449540c0f02400c13541001e0ba041e00700c510412050b14140e030146140c030540da420002160400038104404001181700703844900044160f9a00d58900ba000350004030f81e0002c1612041050300d001c04e00900195a01c12001801c40f480c00310349007002070043d45954803c8404c00c06007107040c403081c0c480d40144000381c105464019140803007502c4101680001c84980d40c185035000a2580040348583c22085901d9000751504005031003411000340200010307a03068000615500b45000d00c03d00700903401d1002030b0414000d504101101202803541c058001c07080b109042c030040300250316285c010502c1c8050307a240d00c0004007400d800f000e11078030b098140c0c1c00e03e110f260400e0040c050361042021160704a060002c40d2411380350340c11000c0d0768402500003010010100d5000018407100e0b4540c0c0c8400b5a020980a02582d0003560011029120152411075001d44117110074485000008050124901e00401301804080300d51508410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 251699955 1250 251698705 251698739
    0xe0705070c1701060303020609010219030f021e090310090203030a140c07090501180b130b0d05060c0301050f0a0f1e15030b0a0f0501050306061605030301080f0d0306080322 76
    0x101d035140e200170030a2503014411980d0110f5601c0c000e514041c0120000c680241143c1e50480070305039980c00c444440318550741a2074201203c50009540c04080f420795050640103492500c0c42807151441d1150041c085001e080d00403940074000f14117003104100190f40f40c0c0022403020700045424004107005500c2001140000c0989586c0042e1650410701030a052400004840840b41c0c180f04180ca901c2e101d29070a00c1c03a0800d0404000f81c201050400240c01c044a0314000d042031003079005000c3c1900000b0700540c12100110750244112000109111201d2a130b44102c00d00a007412004101c40d1542500300900388580b8200c40e41803e032a0482e071070184440c0c080382e4000941c0d03000303480403030304056100401600700d680e01c9201c16440c1030002440d510006107900e008080c0400c11000180030134640604503580101a65160341e1101142c80da1951270003036200041c0300740500000e01600030311500c4251615180611b20b444800d9100c0c01e40c00308540345124040e400c25400040a05214401043e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 251701205 1250 251699955 251699999
    0xf03050409050105060a0c031d030703061509050f0a1e022d03090712080c01112203020108010e090a061a090f070c020114271201060e0705070c 63
    0x5212030801c18840e04442e01600b1140c062482049040001a0031080e2039200e19850f1400c114060b40700d43c84e41440c0d500c030903510b94240c031071b80b4000710411415400050600c04007014001415503070b014104213445040d03451b4200b0b0804030340800e880c412640c002c2d2240403003a003c03a2045405d0646050200c0e48040840c001140041032039000c0100c4a052209101c0d007020241c1d800e5040c0494040d45403802d0744105030404010628100c00c000f1840c0550300c40d000d84200070002d201460500b81c11130341c41000300885580700654002440540a05d1010a480d0181d481c43e82e50b07820a6000001000d000d040761105104542ea040c0004640380142e46a590511181c0403281a0440902440c6d50024001c03514101e8502c04008903290b101c10b50404d000c1d02440c00f810341840200c428401c6100d2195a92019001c10500e03281c950090325400411880950f100000c00c00820b02c401d0032601240110600051140040755000d8411401b9091050185401a21040d55280044022080701200172 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 251702455 1250 251701205 251701207
    0x206040e041a01090b010e010e06192115230108070e0405010810140402091609090f02180613060e0301021b0616080108031c0e0105190e012c0a0f0305 66
    0x11440d6070100d0420201f01e402e0a05010256158000030624015030380091940e2000c0c6c001241d8144c414401c5840000544491003200b0000c0c5040c10302410000160081e0030258800c00248050503410701d800d0031708220000017000620000450f0b0340b04001e0085010400c10354000d44140d40c0e10b1080b24020410070000b0301a00c0513000c214425a480e0100700341002c0c0b500c00801026032200100d0a0303004074446a141402501e0f01c000391000341981c0c00c00410325107020890000381c00554024144282e28030030b4649402d90181c00c00c0b0440c8100c01050b0b0103501d088008100e40350241100e40f60900e0000c0003d41003881d01c007a0b140746528000903030403041c2e20250602040d034458055010492030146032107a140d40c18403080d99904d1084a4440c10b0400303010084006202196201030f006031100d0000b8403850074142484841032001107444030b41180b9001078110500740c14490300494402c940b2141d69010303043c04901c030002445451100c92802001000c80010700034044504216100e52245 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 251703705 1250 251702455 251702471
    0x6010f151d0414090d03020c06040602070201051c05010305100c051209010b130914010207080f03190c08071206061d030c04020310080d0e0d0b040f0c0807170a0206040e041a0109 78
    0x11358034200150340048289441080355402c030850114486900c240c0154000d61b90707910500c0100c800e48540c0623152030301503986150300316241590b0409412280180704560910005110780c0c4200c0381c41210705004680301f0006444140c242c0000c1070741c00304820700005610280000800c1c130b426980c805004442c0d60304e2134041c080042c8258440c3c00346000e84001c5041a0b030341da842a42030704c64003451446440011000500e0007490144200f1800c4031880c1c14855170101c403a005d841110240c6503500800e8000c40b810701842520300c900422144c03295584045903000d040f03c01c0e0058040303103080ba018003540440071142d44a41c0000d501a000e0100011903841c90800110300306451640307400304010362100c005041340c0d1404d122036017030360308160300c01c0480e103032454540124501054000e100e9407462400241481707004c554581203509107403040104000c0721540341e4132290f903548020360141c020300c02032000348058102aa4000d00c69902000b0303e00c072880440108070002d92020303144075103600b11 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 251704955 1250 251703705 251703721
    0x1203120e2113030206071103011a0301050f0f070e04020c030a09150206040305030402130b150d0b01110d2102030a02130518150f0d0c030506010f151d0414 68
    0x5100a446003075034003036040c20100b50380422266000d200c040d210f040c020a41d90240803039006404241c0c08010000c002d0007a0a000910b881d00c041a6030354480e528040000341002100841075114009107150f0b08903030381d40e108003904d003941004c002d0354216a09210803010120104000c0003099041e48580d00c18501e012a4245482d90041c0c00c481150082c009100010b034201c002d81e50020350454000001851b61007101d4014031a501c0d070305a100c0e418807003da004100c1903008001c1440d000d8400d00854040c4401035034103504c030318600542c950004184d070589920400348501e124008a410300c0c03580348201202d601343c1e001035035410700a0750700240d2100390406280491004000649484054513201254004d03103c07001051500c815400c91001e203059681c05500c001c02644c02082c0b002d80385000d0810300361000040c081215035101c0c003000442d034000e500806104031400019000003854031030b00111507120812101c5c141c0340f030300e41f1a0b0703110348d80d00c074003032850301e01c0c5456441041071900b401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 251706205 1250 251704955 251704993
    0x605030601170c011b0b130b0907030519020402090d1101020d090b03060d030306080115050f01050f07061a0a120611030601051b0a170406080105010203131203120e 72
    0x8041072400181000b20807181c00c1c045038407450003a0034242050341801d8184800240c0c080c500000740204511800c000900e425007003250ba049006034031288803503403440049603640030b06000150160b40a00b8071900c03110740848040c2e020f00c1c40588090b08101c1850080b070600c1e100124103d135407000c00d60351180e007564100504400b0410600e80b51248034541409421144009130240e40039050903488041031601030340040d002003040c2c00003005203140500c866400b40405004a030310560304050005440c0d0308c101c06941252010302e0407507107024095510303440100699540e8102c801740110184119a07100795000c03004190240114245290918048040707920410500f55840f8040c018406640d070b004054030000726049880d10001050404281c2ca00400e1840041156000342009101c3c3d00c1103402030300485820307894640c0c860b6210001640c0f40e003e13210010292943c04041009903842c0484840b1126000b17007090300500095110b4002564818121700034254030405018000d000c0c101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 251707455 1250 251706205 251706209
    0x110a11060a0204060c0f0309030510020d110c2a0901090518070e01171f0b1e0609090c160c080d08010518060111010c020c1e030601061b08030a0605030601 68
    0x154214a0f16080c11401303020310030048005000000d100510714105405040e0000140d50000c0450b40c084000e0300130784000e9409903050310411428400d842e8021503840090b40c501403629809003009a0160345644100d40c4103c1e50b00040311038840300b0300010b423102842c2501803c00c5450205080ca0f00310322015103008106000102d90340421800c20451510f0b40300b141c103450914501840040e100000e0a18050348080e0010103281c0300031b141941405641e1102c00c4039001503c4030504412282031841044c00c41004507904018100140710840c41c1007141300e070b84032841040075420044141110348142411800072101c440c0031000c02c1c01010010030004100302214504903480303604040214008035071a1178030710200403818002c20074682c000e01c042031000311000e000300b0825814030802592610a00c17500e5020703d5210303c0300301141102d802c6100760700340007a00a240a900e004411196119801c2201842040c0310812000080d18100210300413403000c0004116503040c80105820101c042e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 251708705 1250 251707455 251707471
    0x614010e0c090906010e06040e160908060108190c08010c0e0406080d020a0602181903030905011b1218030f05060f0907150207180f0b06090f0f04110a1106 68
    0x14440c06000b0750350410541c4d80040c2c2860802c810100060210f40d0900440c1c10205039000303203500300114040700010170203030001160307260614070b40d40701d08940d200d078003e025110403600045c0d070401c811010303405003516503482075580301800e0f561107240310300b102e0456034007a0006160202e80c221a15090050750050300d0620042c0a004d4041c0300082e51b071b82d080a00080c4025008120521040022000c031449a00046e000c0d0b07040b01c08030703003690900d00c03414081100171400a04000c540340d4464000f40e4420302d4151a014031011103a1540042d900131543c803242003120301c484030f4030032020304281d1100840c0300f420600286c4134140b034030500301100140340b80c00c0d04808204001e10120000349110442c0c4c10b500d00e101014004000c101d0505030142c100b0a00202c9252001e00381600036030003001c1141540700f0070400340508504101c2523104100b00103606c142c014000c2025490510010311070444006c000103650041e4004c194031a03040043f201d404030b1340c038141c12510980103010b01903100402c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 251709955 1250 251708705 251708707
    0x90c3f02180114040905012a02011b0c0b0421020f06060402090d0b07111605010f02060610120603060c020a0c1403031602030109140c0f09010b04090b0d0614010e0c 72
    0x40c4010f403140945450741d41441142c8401070503060003020340c0151035184106041c001c1d00c01468110086141030500b200700150b1030300b1080004410504400c4940070305558410130244000c1d02c50075881c0c60040c01c10b0780d0042130740a040180300720350300b000341480d19035402a10b08003001007252400c2c4100200054080c9004008100702039488000d0a030b089907002401d102246c41352041112410080b203500c5c0303264032171200300350043d1a0b46440003048070000da03a4004a4002e121041707803101000e892550b0010707503554a441009008214601c04040401d10004000743e49032038980076075400e806154090307003006800078107201100111101a04180c6c144044449030703040480e40d84d101d048101c840d44040c03200c00b0300440d80d00303411004aa035041500c414045a001019a460384500c01e403040c1f042d84001038900e501c0c1040c001c020f040700c400b40756480c1818500180300380507144400c4640d81c000c0b0350380f80e2180081c2ea10300c40c204042074046203602d250b41c1040b9400e4202c040c007904030120110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 251711205 1250 251709955 251709959
    0x20a11250807081216050706053601031a031006030b070206102c0a0c0e100801031e0c030302010b10030204034101050910090c3f021801 60
    0x80012040b2500090310612995480c13010545c041d8861804802405400f48100c000303009540000505034010822a803203c50700c1c298200e00b401c0101d01c3c0e505120040700c001c00529958002d500c140354888034039016442c1c2c0405a80003d0512a0311580001e0091b42d41c0390a2060110f51088945d000755240021701c294144000040710107030300343c0301e2911710b100000107240e120061000250307940c8025000201c014106440d841b03000c0c21441c41d170000010049161070a2618104200560440741c0d5100c856107030342142c0360001c1640c07c0c03031201c4615240c502040000941d905610380001c6000b0ba00006e070481b00d88040103689103c0c000b101080500602050010505648000c0450443c200e4501c1c610400c90071244401d900c0e00d10307030f000620710540d4a0721801e10103400040c806c214200c10303620f07521441040842191a00d010162401494007401d12103c89240842c51810054441750071000071032509400c101c40301940c0140c0c03012003130103d0908500741085011803074181c1e0304290307400398 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 251712455 1250 251711205 251711219
    0x13230906090c0c030d0c11010b010801050f1207032406060e060d02030601020c030f010f06050402040e0106051806040f060f0c03020d030c050405090a02040302011d0109030204020a11250807 83
    0x203140a06050b86481c400126608103480030001c550071454000402e12150742a0340010304903240600390452554241840c0306059886445c0103816074600a2030304045850311014080b140081c2910001140304e40e50f00031002c10802d00503940584034015110304004080450703007041e108642d0000084c09884003c1c84615034030001500c0c0e0000c00c4120058890b0b540d00c0c0100d05d415000d43c0f081c0c0e018040c80181c401d800206403c150707848540d040051021550710010701c0128452846211400180c000052100d207108600501e42e80b0509440c031410f803888000090030740d6000c2d6018500a81c5100d134208401034002038040c82414090038056032500150300c0107900c514100340715030101a0341d001181e000358043c0082d900a03100240c5001c2c5145410190310009501038003003a40400e8810160782e4030001c0b981c007209200201a0344480003a8559400c1c03001035007200044c001400800d80b02d81134460307000c100d47d0080c6180c0c0700c084d000c51401c0c08203204003d1100c0d005860301d84c0126600b03000603 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 251713705 1250 251712455 251712469
    0x204260d02010515010806010c0b0702011a0d080706020307051b0c1206070c110d0c031a01120c0306110408030309010605040c0e031c020a050303070903050d051903050c13230906 78
    0x400800c0c281b5401b944d0703d08004841c0c29030098001081100d1040c103020381554150b006254074014007400e270307603132029400420034401c18000c0001c044400c1005100c002070807940141d030b084540c40c10014148122200d10f80b4024800020003591503005a82036069403030054040e14000300707864050032075030600c00001030209000ca040900b000441e1000c004107030b142e14924031903554002d60716459460301c034601228100c41d6460180079002c060130000c2200512002c01d101e800b40c0c052204c2c504140745540388ad003d0800900d00d030040c4042800b00103038010040c4011032291a10800000320b540c1010100030444030540049420040c095540c101c103618002010151441018001c10b9a10114042203140c640c09020040c03071400084107014580703400c40c0f40c50060740c0c4220151039a01d001036804441500850948000c0040f115010089890003603004540050041900d1458142400c200c148000d8060b4404040854120041050b00e0728000d0307110b003200ca007103986840c1410180e00003511 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 251714955 1250 251713705 251713741
    0x603060302010c110a090e060105101b03030b03010b1f0216050604061409040204080a031e080c030709051203070311070317030c040537180b040204260d020105 70
    0x4e41d58070203400740c41d9450803441c00040510750414002c3da1010311503141c442400303208450240300d00c883d00d854820300400c6c20800503180c205201a0364210b50314114042d06d42014542c1d015541c826552030340c2d84a1920b4080c2c4a000300d1810b11800c59540303c0240381000010340d6060601428500740a182c2d9144122400c41d201803800d00b011103c2c58109400c41e10071898640da02610004000400c1600855110390250203601e548042c0701b040c074410041d080302486080300044215001540044001d17003e180c0203401482d100071019104c5d00401c0394124040c41b0a1000da00100e1502c003010f51000c0101d804001c0d18014010607441c50392a813192560519000e444648080700080007034140e08150b0b0024003000b88100210580c000c1701440016007891051079403001910700c200d1a01140304407104850042d45964911488003603410000c005a012441d4400c2e001c00000504035008c00440401e00360710980300e1000c01007a0395092801c918200c1d0f40080d0b90603d0200040700c4c102102080c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 251716205 1250 251714955 251714963
    0xa03030e0907111c1134091a180f040f030c0209010602031312080901030c050f0336150c1b1c2303040f05060901090b0912270307120c0603060302010c 66
    0x390401d00341e8203c0760b0325681000041514008038001c48c40d83c501d000c50701c120025a8402040389080e400d0910f083c000300c83c81c101d6494000040742c0080c49690a2040640c040e2030801211860351b400501100c00c00c0c0c0c80040140e00101f800e9038642068000c1800801030008000e6001d64565951000c030301500300e0060501d40e8617401f1880d102d020b13004503441458460b001e83d5991800c1002c50001d00c414128401508030314500101c3c000501250f030365400c00801000b40380514110903200650b510060030303400c08031000d106000640d5500b002903455060840050410405e2a00c0d90268010305028024100400e81485004401c20104100d21800040322525500c1d80c0d135081800300c642c1c1c0300714018654842c0500b000100361041d80110400c0d03108950202e2141c9850390b407240c0d102d2a005900c0d064010400071700c001502000c42c046451501140704c9e201084410300020708107011039119140201071480484100880c10f0445000341215082c108038403811030b00000e14100c800d2600074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 251717455 1250 251716205 251716273
    0x15070b040b061504031a0711030a080403170c030402040b0114120405061003080d02030702030714160f060f0c060e0a080a0f030621140313140a03030e0907111c11 71
    0x100c4462288c0002c0050341c1d03120048170341d50200d1000090031070f03000b21030550004030520304407800003004000c4503008420220700349040d0b449a030200402006039001860501400494400d5000340c00c001918449080e54960401031030b0a0a1803402c24600a103c102c4640c5070040900000343c0b4881a00c2d418038503400010303103036603071030005a142d4030440401818180d00742e40c4a000305400040d001070395080e2003512420440c0d032000c81014162b118000c440c042120145410300d00c40c4244001c0800502030400441da00717a01c1402c09007044800b8800f911079003c0000d20101d2160080c48482018656113000c00045242844425402c00f01000010082c0c9040703800c01c0500030f640c00003000707040404060780d944010104560450611078411304c3d10340c07403001c0100d2203280303080304a10742242d815445508650510300304201565100070030410500440e00c0e0320454002c1c04005900b03682441d500c00d42403460310b0f01e4014010014403894070319503600810b00c00d14401843c486004804044d2880340d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 251718705 1250 251717455 251717461
    0x70201022107060911010f02010b030304121a010e04140a110d0501021c050613050103020a0905090703080d0c111c140405040f140708011415070b040b061504031a 71
    0x10314214802c40902520382401c1095076020300003440e11899400360700340c807031300d040040e2110164240ca0140c680f0b01da1580003448100140603a051282000c2841000c24a80d000700105102c1c225800a822000603800d4a000308400c00198100419100540d08010308810040b60b8401c7c0624440d4000c00340281420940d00041200940694103c90071012003040004ca4580003140204000c8a18500c19800b0b11007540030910140b00340c03416280c001d480703540b00905040000c4003074a03003d0701d004014803508200002295003400602140c00c001000807640408440c802420706400641100311034000c11540001d20005a05e140403c500b28204803004030301c42d012490540c066031348055001410055400d4400ca00f641c00b100b849065142206105e0315080002c45200500740240000c0b4265551407109902d804003d9641244190180c4d41c0340c4062036943d0007581d00140c4088407188040401d000c03151904d16212988525030000f0b180c205442c40d110812618100114101c84105000c04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 251719955 1250 251718705 251718763
    0x20c071706011203120e0d080105060403050606041a03030705010b090c090f042406021507050a020304030609110d0605060405150312071a0108030a08010519210b0a09031407020102 79
    0x15141416184030800c01c051039071b2400a5490f000a201b055002442000020686181600076541600c0d0880c004203540c0d6542014000101380780e20700410620024074070500303e56000c000500d10301e807059002242507004030080c050f0200b00509151400d1100f0302140c0d150b1341340c2d5450545040400c071008200103080e14807101031411402444960b2051103080458420340000f40d07203594402c140614240c81c0c0e2a480110703400d010395082080140c00c01c101c00c10100d010707a0040ea05407401440380c204150300c0f50f400118100004003080f580c2907154010003503076107464840d15074820103404182c40c4050800c80020b0711480e03410f1000001c8240400c0510030300c00781c2c16018842c002d49281c090004d58540b10303a641c0e0b80d00f10305440c86c0005c14440011419040101514147e0403104018003039460511190403611940051300029400444050902049170011128016903400710001102c910740e0600524001e031180780340741000c504224600050b6800200240c1c040c0c40520310340c15813154149 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 251721205 1250 251719955 251719967
    0x50d0b130c03020406020606181b040b0415110105060105041205010b090901140703060b040312021903090815010b0301050910080d05120f100e07110a06020c071706011203 75
    0x1031200349a6240585600c8182d03010340c02481911016021a10955180c01c100607042c0d03030030490046a040d001d4082610344c110112501c5074581d00e0100d540c1000d494440c00ea6003a00554424440c0300c1e03240554119040e04481d42e203034a020340d5402880b0030f140841c0060702500c610720500c80740e08000c61801007800800c1d44070f076110400042034030390036040241300302d80a480300702100c14050051402041009000e0310a10f4100c407107400d04030341440e14640b0b40b28102840d40e2188415406985101c0002c0c5a40185207105148a0b84031500381c0c1e814101107c5c80c0101d100e80e6003104a00741801440b080414005580c11a8412103440c0c5455841004d03110743d0300280d034040701701c510507920585d00d25074004000d804e585003288903504042d91a2a40c1d1800440141c1c6e0f034000c1100ca8a0091103545000074195a024810341004120300188180c000c0ca41480340340305817410365001c40e419080344c4041c045800207041481200c401140034420243d20761606208007254002030b02511020940508 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 251722455 1250 251721205 251721229
    0x1508070e1503090a0b0603030a08010302010f0507050a1b1e0302040f020427050f130f05120a0309061103160e040906020408101b0c0308151011100606050d0b 69
    0x40500754603070500700d0720240d8a0054070021144040d0050002d0603c1c01c000041c0c591540a994a981c81646950015103000c0ba100740505c0c1002420401a0b0101e04108a0459514403680301300c203032480c002c501502160050740100c2c40000c101000107407800c040303c04c6141560740496000621142c81811400248507075841a420302c2c02580c801c503481150b086011600002e03068091020360f50b0081c2d4008061400c44180d00d01c054050340a001280f0a00540e14601c2d10880403101e1000b44c401d11441e06401c41d42064002907100c03030780001000302d58050380180c000c090101c1400c2d8140201074045a6401c500f81c0c600b00103071041084010313a5a41c0140044e039030007000840d074440c0c403010407640311964143c01e0401c89082200300c40c084003c032140b09032070800c2e9640c7d0303000005d246e41d4100c80350400500300d0654500500d440303410f00d944940340110280d104c1d4441454154034005201e0070f0842c10349906200d03a10f0818100001078000c0308031031810303c00c0c1b48001081000c0b9400a00512001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 251723705 1250 251722455 251722489
    0x50a0b01090b1b0d0908010609050f0f100939080601050a14040b041707051302090303070b130c06090f03060506060c0a0305130905090d0305042301090209011508070e 73
    0x400c944c400d500740c002e92440245da034a2402441116250a8950306607401910300c040c04501c2d68001540c0030481000258101c102c1014011070a03680316080001c0d0350f1000c03e00e06e00c5a8014800100850301040400da80001c0d51000c5941110848000b070301054000740b800e0305101c1d002554040300c80c46501c100c14035030002c10b07690f500d41340c540e0408a11500300740503000d5080d0010030803001010000505034103c99004190f0000006800000b2000e9009601c0a98041c44144025000968654400f910800a04070048080c0c184d41c18001401c1358540d00c13580c00e001c802403041c046004404c1e8284252504284082200e0b29010301241482c480d001c81481c1c1030151103108001c0640c00380c01880c802c82d4044503c08035644441d042811580141d0341008142d1050b503068500d03d01940286502c94041d408141901d07031901085100c40d04001044c1d8401d035500e1024a086141040c202c60241100c41c0480100c00c891010140a905c0041c00010a000030040415150358401d0040100f0b403401d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 251724955 1250 251723705 251723713
    0xd03090e070f0f1803080903010b040518120a080f07091214070f0f12030c140c04050109090f060e0c0402040905090106120206030f07091215050a0b01090b1b 69
    0xc6901c0c01058488126406000500ca81802043c0701d4441d00c09481e43e5030401c4041a61a803441d5039405042c0d00c4440040c1c1c140d5200c0d043d00c0d000f42d845c0d00c102c0380b14a6a205580400c1c1103115401c0c0d0510010203024545100c0c1032040264243c0d1056400758412205502e000240d02c5a15080c0c68911403940f18420102c2d00b415a1020072200c41c14404c0190003a03030803507040b140c4601c0c0300c0240043d54040d808603200c04d90400c000d03c0c4111342e0030001d924041d04204102d43c5035034858142500741c050000c0d400c1e9001c100c80c00c55605040c440c480c01000d0f101da013003125006542d030f0400040d568040107084070f1b89071024001036080500480d44018401481155aa40c0d01c03d49034000d001e0442e5001ca06518200d00028039003048402016080e6000b003082c1d01c1c40d901e10312461900d91018210004105002c0c03404900b034403100c5c3c004103080307003d0070b008407448050403010420703201d0051030f118801d403e050300d007031141c8d0300a001403080e500d160b080144c446030300303212401044c416140b04645600c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 251726205 1250 251724955 251724961
    0x30a03020d110d020c06010608280e06090f0606180604050411060a030606030b0d03051c2408190c06030b010302071505041a040b2404090302030307030612080304020d03090e 76
    0x180d07600826010017101c06441032603070b0f188025554a08200e80c410500d0b40340100c5403941c001c54180c0141e20481c1c02800141ca5030032801014502081190a150294042548084000010400103502c00d0084603079000300c54282112240703292000d40002e009986640c080340421400048a009014000d0040358039040706001c0100601443c2c840c60022910300040d601113428503001e0054496090740b0b441d46840c5000e000c400a449494500c07425869a4004081a8204088003441007003e04001d444c0120700f0404180c0c01d000c00d0f0800c41c5030400566000d000055855032a2804031030f041c0c100001c1c02c2d0018001039010b445141c0005000001141c00c03a45000080e80c8014082c6000d2580b50380300d9804d148800709282416213000d40b50306909000211240784481c018144d00c1d03c0d1068152032001080c0100d400d6550741142200583c0000c0200424240c0c9823040740c009008101d161500000d05031600c2134180b00182c0080d00130001088050b043c036001f0300c2e10400810120b90300542600d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 251727455 1250 251726205 251726227
    0x71205070e2b1110020102122d01090213050105071127011806060215160509040e1506010e0a1211121506010306080d0804061d07050a080708030a03020d11 68
    0x2001c8126070a1082d00708044c00b4104502c1442500c0c4041100e0743c4564241c1c82d400c01d100c03803414041c001110b100019184940390302910b90a614002d000d403190260300c82c10308854403640c1c005150042030411100303028003404120660315404508a00b40c4860518400046403407104407241c6c4c42966890201400005041c07504140c03200703040e13405110800440c1d8940302c0481c2c6400d040c0c82c29014000b007540114000c81c0411031558002001030501c1c40c40d0003105000f0a0a03150400b0018159811100500703010036110300780554041c40919201066014403000960740b980203001d50b0f01c10640d9581c5d618208020007100c40f4000c0b4005000c04248284143c0c50f1b551140c00c0440045003140300c1c0c000ca445540240116000d45800d10084e26012340719500440d2280d80040050f1000d544030090441e12140a44140d840110083c0141c040c040c100814404911a250310251051b44402d10070000030130f01000341c4440032428a00581d4810005a110000d0050781c0140d04001e100061400321107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 251728705 1250 251727455 251727473
    0x80a0804081002120f090724030522080d020d02040803030a0f0605151e130e062e02030c0d0c11040506010e210105040506071205070e2b 60
    0x1d039003030001c0754000710700d6035464010f0707000d220055021034080b900854107142d00740120541c840a410115912030340d0341d0130350042d03040b4031401180071841020780400e04aa031500410750301100d010040c05a03500d60b400006551214598040d00356400803507003d0b0000c1e03507601140c5159554420564649858041c0c0c11346907032055564210b080e2a20754011002407590080c01c0468000402c1405010380190595409601100c0a203031801c0103103401200c000111005010200a04100d4199050415401c01c40144d0094506d612600040ca240ca50003c4a04404520407030481e078807146980402c1c00580c07850240710500fa9190056030280c910003580601c00c4189a03003c0d00f80e410001402c80309120858205641a90006600c00750000c00f41c141705030504000c8441a5144407140c0e02d81444500b1a103060714110b61503000802031142855000c6014507a0100c0100100131034280480d000d00ba540fa0181a13501410a00802c0d00f0b02031a01400380b248501c03400c01e0107d10807a1403800e001c00c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 251729955 1250 251728705 251728709
    0x1103130317090319080402061819090b0a0603141308040e0424020903100b061c2301080a030806040221010906060f0e060714100203251205040606080a0804 68
    0x3c03150401480c40d030313101d00c034542c25806960013421041c0f620040c2c003000e850811404031041e0f0004284800c1198401c03040d01268010880c2c0748000a05580080c100050714480b60300035820141481582e0202450345030500340c001d00c40c113048650713084c664600030815001c0e0703600400100441000704010f20004070b40344040c0081c0700e00811203914204d00d0200480c0925840f180d0142d10904417281c880c60582e20020850400621440c2440d41c5021603e01008401d00c400400544070500949442c10020220111941c0440b209100b90704100740190788441214001d006c000c5207502083e20fa444941c1202c1070300401300020900b00340401c6c024240354400b03201e028010f40c6001e0340000d403540704280e44a00140140c0d01d10504101043c00c020150300081c6007a1559401904c0a820180c402c01c604c06214402c0400540c491811441d12282402400001e018118410301c1e600002d60b4000c44a016140707131080c00199540312810540c00410b401d40100c0241c0c41400c210100380200300340603200f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 251731205 1250 251729955 251729977
    0x6051e0111103215031c050903010605090f04080a0c12020f160807050603090304090519060b0301180903021015090f0606021c1103030112060506030111031303170903 73
    0x500c0010019440843e01c1001001e00d803010442012400c020162110010801c1c0c0c014100c560a5034040b80c0040796150740100c440c080780c0c00144180050a013805214014801102d00c0b02051508451103008560300400c02080c0000000c0e00d80c8009008403031030001e031500220b403417100c164040c60295941c0003c4207030702114441c002001e843d0409642458041c0c84040001d4802c091408080c030010b45c0001d084000c42e40001d00021540c10f6051140b240700300481c90500b003085d42408800320446110741c001d1040d2540400041c8195543c0f8040e2103104890a03c00280200480c10200d0412554884520100b401c101c2e680b80080d101030451020794070501d00800810f8a400120b00031190580300d8500980c0100e01030702851002c10700342205c95032517401c00d0102683d8020f082400c5510981101c003000c6002034043c0d042c09000e01c10654030090560003040007142d0381d070400030f0a000003404120203005c0e07107494108051080b216101681c0070040680030700c0c14030000d030586035008007107200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 251732455 1250 251731205 251731241
    0x2a030204200405040b030f0a08040510020a03230705070b1806040806040816060501090234060f0204120602070506071803060207060212070201140a06051e011110 71
    0x45010407440300101c01c840c1d107814100d032070b107450801400054082c005072540d01d405014040216804140038450215204210440c2d9075401c0c4800c010040380c14007001c104640c8801c504c0e50000e41c11115050b56409000410304100c1401030703101070644034607003000f0410700500c1000548260050060071074081c181d5606c00401d0820014442980036901c1191a01c0d4000c1c008034003c20314110040c603150a0200145502031860b44448041e1802030b0722280b41e003640092005198a5140755403203024952143c1800810701440801d80040c0402c0006010a0b82e241540709242c0d038164115001020b101b0754141c850651414414001d41002000741c4050103101b002548a07440b4403203170894216054942c5407600e0854642200070b400a08080300c4c10340d0308114880140600c254024821016580040f070303000404c40c9005074020b03000d40000600c03820220140f01503980c40350099118030510380e000307000c444d550004179282c0107840c030040918001d400060070703031803c030350002c01d2280303030404003d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 251733705 1250 251732455 251732471
    0x9080607121a10120612081801020a08030f06030705040e0d110106090c030b0909010b090406020c07050a0e090d0f020a031d04090b18030405010c030c02040605060a030c0201051005030c09042a030204 87
    0x40002201046c80c020b101c002d081090741c58405d1024564144007070103204840e040301042d078814a00e5031090324158503401ca6401003001c28a401c000002c043d25080d0303400d008280e514030a00740d40e848481080410701c0001d07800c1d2240031200b54045401015213800a01582d285120b02900402e07800421a0007080c07a400012919001406030106080c2c0143c094441c650f100c2e01c410b8025040751900c02c5040c055400005400c0c1d50700301c1400007510207404580d6040c01c1045a003440d21400c1c020700c605008025000659150300401e191031900d4150804810f8816405032201c0c0c00c1c0a246140d6034014a4140c10400b030020440741c00b4402c2904060400d41078011805643c0c3d24051407066500140c0141480400203200d0984141c829202078000f168050305c450000c0c0300354002290b4840029520170401111640c24010f07103170455451071071084080d08080c0406e88640400e44800d008801d0751010408112900f0056031483e00c08603041040d1101000c503a060000c42480160303ca503003480c0380 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 251734955 1250 251733705 251733719
    0x50a0b19061a07020d06090807031110051b210c0c070801050f01030f02040e06010b0a12090c0e040302030c030a17151e0102070302130c09080607121a101206 69
    0x10005401007603080c243c2007030b226500b0000c1501e400030040310030a0712103c2540002d04060701500c002e521a864540d0716251044100346081c50400c240312015003403605100d4400e40d0b400c652003c08048103444d0360f841d8440c2080c4c441c10540e41811b080c07500180c41c100300d401900b49010789129460704054412941d50b4035060340c07e0b13940a98081d10340d4100310b0010800242d88a01f509060b52010308080b400b0780704a007009051440c00d0740031a0340d8050009070060f071540c1c4003030040361005a14504000c000101d480c2c80f8044003442c0541d91807100b1720004101818001c2059481c880491000c032030344d44881210090051980e040384c11070400800000c511b10306034070748215400c60300c058010740e040d90640b200003940b400c1b040e84a9041d400703080710110158940340b213030071030b402c00f00d100c0819200f0324100018440308980d0300c040c11303a410080501101d1035000d01540302400700344d400411911010b22040408801c00d03d00320341e2112020001103000783d0031803801900c00b016110200700030707070307850360 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 251736205 1250 251734955 251734979
    0x304081c051305060d0e01051905010803040b190504080d0507230c0424030b0105030606040506010206040f061824020f0403061e360803070804050a0b1906 68
    0x154140e85030090a20074041402c015000c0c0441e450b150030040343d644d201e031000c0f1382150429520340400c3e030400271030140f03540040d001d8640185040b0004500c0c0601c0d160401300217004501000c5020308080014041d0180f10b40142da005e0300d03406090320f02c079070f82c0702c40050019400808100c80807503042440b0318000b803001212a1000150201600c9640701d10403c01009050300d01c0900d40440e000c0300200b04103002d07a46004090341c07080c5040d0840354104400c041c603140c002080f080c0311318102400c2108a0340c3c049035140e04590302a6120f1030060325846e10380c02401845046000e0100d80c01c060b038080c8920000c8101c144128030500c185506050b83c901000d07482140c8900b0f8040b4410003003040029060b90102990750380022a03507681090300d0960005031901030788005502007a07038044000080f00d40c442e226402030790301d00d1150409003c1d40c030700d880303400010001d10510502100141c28840f003444204010355000000e030803d0f24106d800060180c1d101105450703d1482c1000204024100203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 251737455 1250 251736205 251736217
    0xa0506060a0c110102070b0a2106210503040e0c270f10050405090a060f060302040620150907080106050f0306011728201f110304081c05 60
    0x1565108142c480b0361204a81011416207030b41c118880c581002610f609100c01034509600640d48401141c0c0b41076680301f4030050b111700c1d0803040f94070340007007005034151a86291490380b007a0705100da04d80c00541072840c00c40c092640810f152041c66010056409104c0004114405220b213806110000394030b602442707140601c0c00d8940114032004031329030324540043c805032406094030b0030914094079240400e0401c3c4003910001000c54440310144014540102204080c00355840c0271824076160540c024510740007141030031044400d800103015a000140452101ca083c0300880500703a00b800000e00359103d00038400c5035419403030000042420b140410300b0b4481000e000f001094180d007810301c4214503110703210340e00c025407040f03805040b408005210000200a5810141c1070740b24001d0034a0003807076031002d1184503958044480d400d820703600c400c0700f03204030078182544c6070182c41d20704016103003020702ca1310903246444045070010f60405d0001d1070705200c0304404901c0e100c1e41c0401005640300d0280e2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 251738705 1250 251737455 251737457
    0x201090909030e04180c0b0c060c0c0c0d020103090501020a081602032b0605030f01020d060902030603100f0b0a0b0910030506030d080705070b150103060f12170705030c060a0506060a 80
    0xd159181c0f4a0320f07003500304c00300c005000080b80c0702003000c664911940488a0b4040003501070040b554900030700c424415030f54480c2d9000d10076880c0c0719115030219104c007054460385200b56650411b00c02564882e9200030300341035024008642d111420309010704206800c494002c0b8004035500a44e0000788044155007e42c05d0000300c3c5611440c245507018180303c020780c81503544695032040014143c2d420041c07040d03460540b0000598900348800c4000645200d0742089504a0041040c00002e440008210890000c0c01d00c0c00109419102d400801800c1c0040d4400d03804079039500081241e44850780180924181240c6064110280b134000781c3c01c0c0d9034110b48460b80b5401085610b040c02c0c2c0100403041d40030b030702864024500003040c2d8890a4543c2d0658908564a480005142140d609446017102820401c03840341c4105240c87c940740c540900c13074800108540c4c03603081d03841201100d401c1075501142d130100951b0380b00c40281030802d549000840c1c14020660030034010440c1414501c0481d0116401c0f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 251739955 1250 251738705 251738717
    0x40209030d051804060608040b10051528020304140d11150903011103090d02060103120f0207030c080f100e100e100504112e21020c03030103020109090903 68
    0x4050140e980d500150b03103c1500b1207200002140c41d03a90341c40754902030403458640c404035003814288151548002400ba400940b03450b0402e10917541c0d522902c40100c2080c0b4022035031140f00c45841c160746000b082100c80f200c007070b07903103111880da8000c00600155080300c48400009072541007048014101700f03201030244800321041600605140504142c0000c800b0b01551134118181d02003800c42d00103080c0c0f00040a00401401240c1c2024040380040140c00d100170031542d4110f4541d428100310500c0d94006101848001440c003500a010340c10096402c180c0d4524003903900c600705621420b0041500b081030080d1507c5045800c0700348a1040340c1900103008101440e9400c003c00d0003400c91004030200c8d40320380a0504d0081d60345014062266118406158449141030180005141410100145001126540c124141c808007030050340200601e405d80038002940c0080c0300f860040340701401050300001c0e240795141800401103042300d02c00e07a96940040d6640c01c501040303d0f5002d00003000207603 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 251741205 1250 251739955 251739973
    0x1060b0906070f08130f08030a120b150f0d110a02030d0b0f0409050d02010609020c03191701060504051e031c110f06060907051201030b070921060b04020903 69
    0x10920054041d2503c2007a0386502102c05131034010680d001441059080000c4801c2441107420082d0f110008014120003541403182d00030001c3d1000c1c03441c01815080c20b5441c1100380d41990b4041311451110780c002030050359546c0300408030b20700d81d1120042e95450382c10a020403070315660070800c0f100d20144a9001c0d40c10072039200c1100c8050f10340e6120007507103e070b68880f100e00544c0da01c2c4220080244110014036410705580d00c041d007500c10aa001000151060010656900340442110f1609005441c0d2100b05011380300180d80c456004400a552400c03000004198a60050700910989008a903c0606851003001e0b185030128003e00d0190507030000c2e50f4104034090b00d03c0740000c0f01d44041c01e00b6400a0880c0d0305071171916190101d480581d0b48601d05000960901c40740c0180c1100e03007464050720307240d0786000d0300e1700c5800184070080c44ca15449000440c4c0c4c81c89182010050701c403000340c3d03c1c0b65216050480001000098095525500c4c100004c0410310b051b00c04c403044000081c0140828503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 251742455 1250 251741205 251741209
    0x207060f02120c0a0201080703061d0912161106090d0b060f1909050f01030503030402061c1811090702070b07080d020304030201022101031109071701030c05040e01060b09 75
    0x1214056003805520076010b00c054607040c80d0020b860a0301000006000c42c0015000040c20302002070300c0f01003407514100040c03082d12410a91845c1228640b0301c0e5614030740b0b681900303d1600c0050151052951380200d59540c5803100017014404007409142c0340384001d841442000b100d803040c1c0010651055040c0503000c00115a10070f1158884070083c800c00301c110715003000c60b090750210b00740b182942c142d4034000e01c41a500d600c1620342180e40c041c1034584941c1180d4403540c0d284800783c0007900c28000403903180b041010680104100e07100200080c48549014000781d00300865000b02110b001c2c0c541c000d02e00d294201a01c92038454292540140b5480789000d00342c0e01c60364408001aa08044104400314005070640000c6001c7c40c03083c0d00040c0d40c2c90005124203c40d03441040342200843c10480100301055006403003071381c44001145e40e180240c1300c00342c06a40011510035000c0703080d0241c40000003802a124000d0040302e906603002e000b030660b200c0c240741c00c881d103a000b100500a004e100c501828 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 251743705 1250 251742455 251742467
    0x14060601020c21060c0d0e0105160e1306081c0509030703021c0203030738010603020306042306030d05040303090e2d16030203010806060411040902071a1006020706 72
    0x74024240e5906a450348115040e04213a01110043d5180c480011200314402d1240f043e070044880c02c0700200b0590602a0040302c030315403014420f6041111040c0c02c41c000340d0310340305800176800700c0760340800904e590f0311034858503072245000c040300c0b85c100741a10400c1507006070110790506d00d000300944003a90030359007080280103440c0c01c103811011084280c500182c500b00001c02c03407107020310502102860441e44100c2d600300d200c265040350102280d4042c221143c3d030f5188505440842c14003685a42d00c54020500610359050146401c0d050159420a2062481f211394022070055054a10249c83c40001390748901c110300c001000100388050400481c00c60380c1031550012200d4090303e112500b0300762030701d00461450420b5851300e000541813109840c8014030f620b0251260341810743c2103616043c0000c0d22004014a058050f40c4c0303844c000182c40c59100e0072100038000b0311008640f1405a4101404200781d0040c101c3c04c0070b4081c0020850640301a060b230f03000c071203840d40100b005d1404c085040f07582d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 251744955 1250 251743705 251743729
    0xd0804081207260405070506040e0c09040f1404030f08010803040302060705120c060f0f0f0609150303180901090b0901030807050c100f020d09050603070c02031609060314060601020c 80
    0xc0100c200c0b0001c941e881084642c1050400d004505803e50400d820308604160035540400c0c410760080000f002403d905112441d80310010b0400f281d298076064001c40d000d0034807a10070720603007450642d26401c4480094031290050b03000b503840c90100301c0c0318501512204401e0103400042e038810300040005103080c00050034807600c03404c01d5400f030040300c0040314210f41142d00080d099402c1601005051000303074454580c0200034400c400c00900305070b0100c7c09403800c0900142d003d030544d4400118101b5404a550f50002d6025013220f950301481518020311003c071420b05032080079400e00000b801c0d100350196041d0070800606100d9280d103941e03070310b0300c2c5a03101d040c08542c036005090b440301c043d1b510040e00300301002464450114041c2c01080c02420a4400c3c102030381444040301081c0716680303901050b680c3c00132040c180360055010500000385800014443c034000b000c501c90300411082c05580000c3c2c1124800d0119070b13403a40c100311501d9100c060881e005c50040c2d01404407401c0c0c13407070302c5400490 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 251746205 1250 251744955 251744957
    0xe01030c0e1309020a080d12020f030a0c020a17030106020706030b060d0903170703020d0f0c1d131505150a0c030e12010e0a14070e190b0a06020106080d0804081207 72
    0x103103c070420390118000c3c1a5a50203150b150300620301001000d44c2101d004580280b101108524001c1858581074032804003600510001e40d0b98546441c41c230303008000d01e6000640160b80030002240348212041c2c10f03402400381d40014007800100240c214007034019100e84600080103070741045041c05058004103640350040c0c0801c00800b0b80c00c0700700040255114015007840d5400750fa80c115088585003a910b1096a01c0c03941480d14510381d841e00d038800c00b29007501c40c52501c0300b40d010f610680040e28031500012880b0f0241d180241a203560300f0041d1246084070001d60309e50416025542490a9074001c520b040d0020038060801c1c0030010b40b250201940014005010540c5030310007540050840d401005820490f83c04480c840c5c0912000101e10801034010200500b805030401000021241c1e000d030424002c43c1030084ca801120406805c90101e050300a4601c8641e2980ca610003401303007200b4880c0c01c125000c0c02d000049180e200f00784091103540c001c400380f0314106000000380034411004007400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 251747455 1250 251746205 251746211
    0x61620061207050f0403032c0f040507020115090b090c070302070e22060b040510050109050402030a02070b040308040c08010c0c08070c0f090b0306010902120402010807020f0d0801060e01030c0e13 86
    0x844d50000100c06000598001d50b40c4071840e80440d0000b0080c400d050340c07400940305803004c1b41502c0342d440c24910001d8640a88002c00c01d9140c0140c1640540b1805001d0f0308000781400d00490f481001d40d000743d041e40030440d0b030703004c040d250401c00114920540401030f00507002103900340304191020081607000314001c3c0300719010b5580c6140c0c204101c01d0352082101c940d5140d8049048030303c6c060003400d070010003c03000740348103078a0000064407070711a17403152501842c1c0100c0003440820040d410340f80b44c5a00034455100a191034070b0000e00c1c50b00c0c200e404480d0082c46c140040340c1240140320b00150075800c0d0302c40b5076000b60a41c61303201d16500150300c1200c0304e001d1a172010450b034240d00c401314010b003410440803e460180c5003c00d410160705800c029174552050242500281d18402c00b43d030000c3d021308220041d501c0301e010072070400c500c41200000c00d2281112803290346500c1000a8101c1d45a90f0703900c169111042c00440549100c145443c0009401d40352040780c42c03908404001c00d4120b000000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 251748705 1250 251747455 251747467
    0x60c031219020315040b040c08070c060e1905190b0402090925060e0102010b0a03020423010e18060603150c0d0509100b090f0c07060b06162006120705 66
    0x10000d0360302c1103980301d41c4c25002c5403101e01c090816000f20032902404403818003030008040d030001c0c03191100a1100c000c000c404044002401515032216146021074815520030501c80c4000c03144405100ca4100c030b881c46822415100c500702c41c0181c1d50707c5a800034a01441c0e41342e680821480600c0900b445040e402201c2549c01c0c01e50b031f410540411901d078403600300c03c2c50b403402001031300078642d10880d1815641070080142d0070350b841d400f448007901e6041b0360018106010340a16165900b900802c220a895400c0005c070701c030007403e503045210f01c407660641e5110700c0385510326544444064803041d07010745c003140c0c00901e61450909441d41c800849030b4654103004a12107000c090312070669050722030b40c0003005800384103820b0703009144146209649a81f0309080c0040984400c0e00010001060248045140020451a900444281030300281242c0c0c8070140400b0480908088001c1101c16a07130014036800800114a0810900f0360014212410250145401445039000500010030001c0400403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 251749955 1250 251748705 251748751
    0x4030c0501080c09010c0819030b0f01090602060a090c050d0302010603060b1206070f0201022205120105130318050904060e0d090b070204020c1903020d08151f030f0501081b060c0312 80
    0x310754901c162796400b01c1c0c1c03a4204001e00404805081d03800d41080801d62040c0540303a00010200e40141d00c01d05e0010300035601e800d00c03201a42254100c0356200c02002d03100c105155054100c00180c9016410400c4821140e000304180301e8441c180c0d5a2198010500090b2050b0080c5a0700c0c5c0038140341e000162404045440821100b6241510f458176558068024000360801e05042002a0200c400802c11420501c01c016a05c901c5094024200505d258082602d4040308010700000c20010300501640c3c102450079501400440007040e419114840d81e151180e840381c2c0c1250115016030341c141e45060072540a100283d884014604014810701c0d0180500c1c0d05461042c090550103903014203200e03000007900406294014066017000996007130350316090380c2e903031400001c5041c86075070882c0c8104981c00b059024001356041d6101d85403030b00c800042e260901080400360b0441158140608040f1481045481c3c007031200300c019542d0041c041c0030414602e889030181c000c0c0422006280f01010307a42 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 251751205 1250 251749955 251749987
    0x130b0a05130e1b0102071502010213180c0804080a0e030703020315180d0504181803030b03010e07260a0512040306141e0703021b010204030c0501080c09010c08 70
    0x980714520658520080442402c14009508440c072265601490341c404400001e43e03900c0d02c0d000740314000c0c519581e040502c0d4000d5048860f160f60540c400d4440d250348900030041c01d80c13a0342425503d1404d211601e64024400d024503880b540c0e100d6503840c140f0910707080c11200c1814043e2599050f01c62041c0110241c0c0d8100986485c452844580101074a0555806441245900341e0100703240d01c0007540d035040e079400c041079501781e0f4140005540103643d8061a20041c0420910119265910240301014558160400d0040f490300364001d01890311311301640c59580386248035a003202c000a816802c04002d05483c2000e00104141c104c510324906501c0340303420040008081404000000760401c20090a80100d00c0c5080b500c0c00c5011103803802100d0803540002000c0c40b079110b0045400050740c0301d8000c0d41500d6803000504081805002c0201a0f03078001c0d401800241e03145819440c001850b0741c8140c0300360b031003040e1118840b0b0401000400540700c02c4401d0000300c6d608142408403450825a0314 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 251752455 1250 251751205 251751229
    0x5030703090b04050d030612030909020904092a17070510020312010e01050906010c030c060e071701060e0606280302040b031e06040b0a2c190c020705130b0a05 70
    0x203070000b41790740c41000c0c00f2661035070b100c150700250541800e4046500007201c0400c4985030309000d81d44020340300002c0c1c002d011401c030003840502e03d544500c010311a03264020b043d40d0003010044400580741c010b07041420303c42815130f400541c4107060520240c00d04041000b0292410f00459080c510f040041d031400d00802d80050b03506006601c0100628513000701c101d6003025007800c2c0045000e19a03103000300070041803034002c0c000f00c1d16291076003140c002c00c1052800074000c100c00240b40d50b05403011a07000c4c003014400c8841012903040410194545103044039040c00c030120610703a0494440d00903c0b0504c00c1c0c11004c00078107034244400207080c910880158030900c210004940c245030000c0e0042d003840005018280194a0f11060111a03294542c410b002da4503c201044240e0760000441618884a400c001d20780703521100921503981941004454000c032203603800d1050307440710042241e448010317200b0154441000c4155021034115a40540c04010020344140252034580010500c82000c45d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 251753705 1250 251752455 251752463
    0x1302040e09010f0203040c0608060307030b09010e06152211070f20090c0d0e030c0604201003020a180303020f0c0612060105091210050601080f0403090605030703090b04 74
    0xc0010001070100c20300ca50840031043c0034086003035003410b455031040c1c0c10380d40c01104140464000440d4640d41c0401c40706000b0741d40322001c548645009441a4003030551100100454890392002c14103c0003500b1404000040c064150705000d481e405c80900b0210170700348045074050380c1d04030024200b08a1002040d2003070181c0f4001c1030030742e054a0304404500c2e0b170043d8050095903090040da619691281c02513000440444d401d51982c0c2000710368402031840e2007440341c03640700000c1c041025003c08103a1a200d14019403880b84001400d04c0e414802d101c034800040c3d0b0103403030307004500707030b440e0107075018200390504d070318040880c0c40301d00e60111110001c0d500305401580c001c80f030340c1100a0041021507034442054400c14204800c040600910503c040c0a440c180b01004c182103a050316002441580d0801c603000319460340d589400703520001c0100781d8401e4009244000020000c5100d4001a070181c0d034140d80e441301103442c00c001200d094102410081c04c141c0c4818403607021800001e107650003a801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 251754955 1250 251753705 251753729
    0xb060f0d060e061603021204061a04020d0b1008070503270f0a0c1401020709090317040c0504050703090f0609170418060f050a09090f0605070203031906050d030c02130204 75
    0x2840408004030384c0144150405004100d2010099944d00750650841e0740408003080e1940d44d2001c0c02d020490440b0141c0c2c11920104040c400140780c0c0c5c11038440380c03206031600d14200340c000c001107446540843d8000c02040003080841c141020b1307240100c0b0703004200b0210b80c07015449002d405082848451605540d40e003c08000303010310a050040c0d10003004030241e24210500c8100001c0d458a04a10070000090341d510000400d00d8028030358800070480c0340348801d141d440c0900c2c114a10716900d0280c036000b00d10302400265058080c1c03107280c9403550030070080b840341605651014040e0890f10811142440c5c54482d02c000c0d2524403010340068407610310002d005541c880c504000700c0d03859070b0064200c184044020400d0343c071090703515415146200c0003c80e2402d074504000ca09081c0b603203401403605181004210016501002950003592249040450200f001080340207036019801400d80c4000c4507296076000174000c0f0019608a0310180000c2c801c581c5188005003240c02c1a4003055006603 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 251756205 1250 251754955 251754961
    0x1020901080a0b030703030c05070e040f030e06070b0109020a11100f0b03030306010801060f1112030601080f0402130914030c010b01110f0303150301020903160612090b060f0d060e06 80
    0xa0400452a40101421000c10503c045080000c0c0e55844502c0050188040e11941ca41030020503c0400007801c24440798020030300b401d1500003150282c03403800786d00140c111a41c1c070900c3e00c2c024003103501842d0441c520060b26400c00d08204004c2d4030203042e02043c0301420300140d520300804e04c000403040c40b81e00030008599520640c0d00341a1215404d041d4441e400400c2040210f0b80c019507035905540c0c2610b02800c07845d000da03100740c030620710702d60600045218518401c518400c149005520800007a40e901c4942e45820303240f1240c10b40c040d58000e502c149032200340511024541c0c03008000c0390103200080c41d10344507121541d0455000710030081549c4d440d00700009031560096480000c40000400528401c48400e1400d522400013400c81c400030200b1216500007607400750141c80d264a0010190703004000b24000081c0d4005042c403420700800c000780c00c014039960f0280300c3e6401d9940c02a60181c000d55500040100040101c84086d5002c0316071450a00412300b43c1c846d6a60403c20701d001840710307003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 251757455 1250 251756205 251756207
    0x1b05060a0f06080703080d2c0601090c0816030e0304090e0303090606010f171308130f1d191d070503100c1e0201020d020a0518040e12030c0d0207030201020901 70
    0x8010307030044201980004010000507070000215440c0e0030340707c2000203442844040c4240820701545032024600e20b44031102e24200030208442c1c0c1200d0072800100180303064008183d5403420300b114454800c176030b05000c1140c880e01035080103841e01c2d1901c0c241ca14141d20741070600101c80c08031000c40711691000c0200810340008100c010341081c001d0030421506039150000410700d040c02400c50410146030000f1442500c0482c10480445510104882d203c1203c00d8041c41c000c11203214200d201c8c03d503060006500007228040303008074209040c06000d96610020a000302402d000103686501d40d030340e03143c0c2589071242241c158400c1800c0c0081c282a80c60103003003525058100411060040c81d200b032038405150455000c40c0e596844c142103e030b81c1c0000e01ca05034024007031050280d100070f000017050801c0310b600c007008088600d90702d040c3c0c078003061404080c442111404001102c0c903a2140000c03a800c0007046002c2c6502003940184585095040449030042c0d800c2401d084016070340104441c0040c2d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 251758705 1250 251757455 251757461
    0x7050a12020405030f281e02040f02031608060609060714030c01060303020a030e0a0e0a0518030d091707171b03040f05010815011e0207050a060504031a0708071b05060a0f 75
    0x8594018280e001e88295103c500c548010345094800c04c4401101f100210740761608664640070303022104540b00d10300f90340e41080061030441d100c800a01c18500180d124a020b20588203824000b4009a08001d042e585245c20516911155807540c4000d004d1003581c002c003401680302a61095000c1e204841c01c5150150269108210350f40c031500c240442844000c8030740b44044c1c1d22070074a44001c1203540f61440d940103000140206050306000c002203a040c081c82580041c60314134850401d20080202c0c2d2504034455024410f4020003206004400529007900003018000e80060300c00103501c18200d8030221840d644c05640014604100e000040081d507800c0715030507900111001070b41c0130ba418000d00085c5450304002120483c4c0304541d851641e000c0c82004088054a03019141d03c5005807142030160280c5c000d480f00322200410891042481c910012466008a21030748030704200341c440d40c906803400340301d0164280e40101c5038051708001c03460401c00b00d130241203082e8000400040c031280400503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 251759955 1250 251758705 251758753
    0x150609180429010b0d02030402012717030304110f010210020304120f021b100c05070f090e030406020c090a020f18150403030e130e06250807050a12020405030f 70
    0x50841102c01000a120703014201d410099648a006a40380e17118070060b1000251400c0d2048030303030409184010154600b1b2041d20584d0b01303d144152401c40321a80181d0b5030703c0304072001450b140c00b5124000203400c0c801d24a02a0600500690320034406002e100e100300e070070480301a03901c80c128403003580d900f81c1c22614440303050415101402c4210510100b000030403280701c144034001d850791910440c1d8541b05182d5400701c1a03103e03058610f85642ca0b420020203201c40d028010b0103d01d0240e44280b10b2400100322012035801d40c014001e205c141e0f10400c01e603a81c00601040c540d44d020040101e074140d0341ca00034051030010780305162070100c9034014070103160f02e4a140d04499800030001403001c0707900303c0c0d1007440711403040b19031030302d03980d0213900c150068800742044202900c5110b051259454600603080308035a0403814802e1040640501291340c0f80781554484080303101042915000c030320070b00c0d07040350100714850054506139a60001c03d00c1d195800180040c1504101140b424040128040b401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 251761205 1250 251759955 251760023
    0xf01020702010905101119060b0d2103150602060f0f130b0406020f12040507050406140d0221061504090213092102070f091a06220902041d1506091804 66
    0xac2260710365654407600849180c440355059404240e0031029120750002420b0b482c100020410b11642d518002e50340340d80c00e0f1000d480300501c404c00908080000e010962149402a07000b0b08110519203e00242180140c01500e0f401e400b042a94000c1c0fa4500c0102201506103908450a142500f005410035801d42c03c41c034032843c1001400c100a0480d0885c0320119541120440c1c4850402d00c005210f6003815990b025040d00b00c0c850700030407034002040e003503c2485000103840811414004010132102120300c000d6201902142c80c24241104e90700c04c1322841d11604e420031460305082c01d400d84d80c0c1c00031103c03500103a111600c00d008462074030301400024180070724103000007018802503800c1c3c00051035499001351400310b000d081c00b8010421104220003044054058030f9114030586000c1e50003402418010f540060008010800c2c0c010141d20030405c3c07040402c90000700104020043e4041040142c0c0405803022002c072007800c1030401c1e8011440741c28000b41d0b040d48043c90094078448091180 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 251762455 1250 251761205 251761219
    0x30c0a080601030504030806011b151e060b070303090816061b03050609060123040626131103150108060a05010501080f070c151a030f01020702010905101119060b 71
    0x2904103480d6500702e0803d0803c000a1b4840a400b8030500620040107015001743c8070003030500b10702603800b12003603010ce4a81d403066420825004000e40f41e141c800c1140d8104104a80030200340700390301c5220814070650646292214600044684a1907441c00390781943d038600308411540900e581000105d07181d400d0901c018030307101c0002034910320300410b01414402c0b5a0080040e24800402071310307840034039030b900d2500c1d00e03140e44000b0074903080701c00791200920085420045801000e0b1015110390018500c040b01c581d0541c0c0c444580141c031420382c1e0b401d4490300c4011101001c1c01007226000c2c20384100104030502c0c1c4011581d0590341d06034000f6060114200901400349560003076554810103509000a03151554502008134503841401c1e44202803501c50b440401e60060700a0740c800081c205c01b02c401d040c0c0451b0b945801c03440f60354002404514503480800142c244800702d02441074641c148100c40300103c1010f40d041c6520b840002030a40504424071041103094458070400d400107907264 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 251763705 1250 251762455 251762461
    0x6020615060304060b06160b0603060703021228090305250c030b0603100e030a030e340302040c081e060105270a06090e01210b040507030206030c0a0806010305 70
    0x21603510b11010340041c0c103050319203081c01480e4880c401214013490110704582c84041c003a003400103085000765881c82c403d004e00004200d45a100f4000d8038000d141e510300c070004503120b4900080b400c4414403c00c0d640300140001210342c20b225846510007590107a1500b030342d903e440d611482e0040143ca81c0c0d03003030301e02c40c0700303070030740045880364840d8001d4a034000a070000070740b18071000902c2c000070410306e6000281402d000309100d000c04400740802c001c65840c1030001e010240e00a81d1200020368503204090300c10020041407814447c0701001c8007409045083c1c5407502c035000b0600742c1d1290543d0001041c0c3d5902440050034049481c0080c0d40d22040f8840c00c0703801c0000008201d4464000c0c00d0b80b40700013410802410f0001010050b032000d074001d080e800c0c0c1d0b1b82d940f82c01070700e110030503c40c0c0c056602c411800001c8503010040601822081818180140c2d1055580c1d1401c0000203082500e0521541c0b40200041e1500300080d4040c000c0e05441c0c41d03d556540d000203110780030080c18941054141024 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 251764955 1250 251763705 251763709
    0x62a0703020a02010c0305220303030b240a140c0d1b0803010509090f010c080709050d1703071803030201060e06010c02010c020906060f0f030601020f0a150506012706020615 76
    0x590100760382440d09000354080f03810202d1f014000c216141004010005921014120900c51581101c2c070a4400740244091a0208100100312100c100124030003031000504641d610f0000f130500c6880c80c2400011681c0030040d203107035600a2200c00d40580d0200700403019694000700b8074103940180c17920143d1900c4d0155140c411a00061242a01903903041b40480c407030000511400340030100070b40003001510403014004080c0e01d0143c4001c0c0110740c1002c0c010589090241c0a41400c0e50010749034000100220f44907580c0b6031000380700c8410040f42004085080c855607002d000207500036030000c1115402d001040c488062b001d0311b80c0c3d041c06507482082c80141d070400c45480b41d980d0111350145950f6220b901040c554800d8428400220400040054260100e038001d98000d44013a400c55940504072009075070b4883e008080a440300e09c00c00d0160000d131100ea049035034030800c185414002c8140050f618404203070708403000c21595074481c1e400d00880364100411907004003c00d6040e0050080307500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 251766205 1250 251764955 251764963
    0xb1512030f03040f1b1701180f060204081501030302010c0f0e010e030304051512010609081e0a080f0d111318060b07050d080604020a0807031508062a070302 69
    0x1010189103100071002400f480036460111090981085c9200c122071205401182004118000c4800700c5000b5400b841e1030380b9051060190240c205940e42ca842c2300d0503102c1040c583c1d0281402c44005408000104000b402800440a0389101d0301ca000c03001d50441c5030181c03c1d205840c80c900c0070007411011159600d54030540d142c0c0d5482c0f082c200006c1200c80d6002007411881130b500034a800c0056868100203c2c14994006c24160f040e410803481d0a90725444226940300c07052085e818070b903115441030307007000c0c11440240703050050550480e019a02190703240ac01c07580101e40c2c0400051404a424604460180922200c9600007069035143c000b541a100c400040340303005480e1460050715643c04580004c0d44904050039040301510744608841c81e2041e0307104075442040d030010748d1074800f1503603c1c2854026500c500240d0b8444242c583d68131031089004002c40c85201d45080c402400006660505000e003500030120010440716044400c041c600c071400011014541d820030801c441c0e40070030380c049 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 251767455 1250 251766205 251766217
    0xe030910120e061503101103040227010308070b07030e071703090904060b031204030804050d02040b0d032304050904170408030d020d0c030b0f1513030b151203 70
    0x1c20030068807040308654100a0400084468440c8100780074001c0844001c2e9110703680c44000c50454900882c0148244103aa40348400c0ca2046441403000c0350051600781d050002451194501e108140c0040400c0703500b1920a0f07000740d035030700b90000300881441500c070707403ca41c02403a50078103000704003034a00c0043d5070700d00910408001c03442e202190300c0c203003038244103c1d480c003203004000704070303508003401d218000b0078880019910038402c00100f1a24100d40101303580407030350000f500e20300b0a0303d0401032000e01003030644101c0c0e00541e9134049592503034503074070740349881802903403124901c06d1207046841446a10390542001003000384006c01080c0d481480840e440355110416800301d84808000c1c0c602406260070005647c000410750000105090f400b0f00152043c418050041c00c06510040c0c1c00c55400e0890160808412145050a800e05c0742019207103042d40e840039860900107404040e605946a00100c0b10790803040d090040c802030940c02c2900c0d11404403003000034078400c1401250f59200d10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 251768705 1250 251767455 251767457
    0x9090604020f0109032301050709060e040c03020c010207030c02121906020d090f03020d020c0402090f011404051905030609010c020601060e0f040c022a060a0507060219050a030e030910 81
    0x207840c00c81000c2c1d03c941482c6004580c44440040b445c656810880100c140c41c100c6c01d5000e602e0403000800c0d40740700e88805411a00141c6416810054010a01016004560081042c1902000b0583c0706503400d10007050114041e64512141d108c0030b204200001c036a01180390b40e940c0c02141c400990034103982440141727960001c00141e45040091150020309800d040107008000f2894100d1300340768020072a8954100e069003501c0c140105941000120301641c00d05503004552550b6000031940284075840e091184514054201590307400055005004044000502030a907501004213003000c01a070758005004000a0020300741c501030007592504140300358001c1094210042e00552907200b103080180d640604140300100c0401c20180d590350610082c41004400390071903e100c003a1036420111040e00003481546802401002103c003030308414029108541d0802070b00310046000d51444290711700949070706468a110b420702608882c1c407200424040d420410258000740c0e2100e1504081001c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 251769955 1250 251768705 251768719
    0x71208061207140d14030a0c0c050a03031403070e130b04060f03030c0807080c01021611030c030d0e03030d020d0b01080a1b0809011506031d12040605071a04030801050a050909060402 80
    0x4d6030602501c8070620284000417400f0005401a0680d400728514201e180207041201181c2e907a0010300008078103602c4090002032100450f1031458840d4002150011180e00c0e0441c90384910b02c00080c0d4100c030f103840400c4103c3e51051000c81609081c0107860041401c0d001903101d207072440c2c5000e0440c401c0310b040203080090000b054410844850281c42005190394021511440d8400580000c03401a41c402c0c0c40a408007804098503140018045810b410050060700d584d41804805031407030b2410043d081c2c0c1c58002840101c2d2159a1072001c0c00d40041e0500d0040342c041150340015290940c00b801c000c0b4503d090900b44503000d54001c0c40802818100e00c1d0002650b6500b0784000c1c0104128202d0a4070b16010322400503085a00d500700c603982044a0005d440c1d828041c00c9041c0c3d517070505800d504040c1209100420100340100080e1407694004ca520b000000c0740d00f8203040040004440442c0407802e164010301c903a0900d000303108050481601c0741e501a06054482d0b5550b080002c00027481041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 251771205 1250 251769955 251769979
    0x501141207090906090b061e01050a03140a150f1d040602070f11030c0d030903020405060303040302060408030c060c0403052d2a0f090c0f07120806120714 68
    0x200311801c01801030000800407042c3d5032800c0d00142290780c001359501c0003a500403134201d20300358100b89016121010031050005290005446a0300580d0348041850b0303586d000b80a15903103008585e403152400380c400240507241c90390707100030000c5140c00014080102032030034404c60760307051a55414051008501c00d21a40c0d0752409070040e21551200400400c08059040104240a03046030f181c994220706403030505d200ca10602c11140c0d100d41e0042c002400350f900800250400350f02184c0c0000d4060103803072405440340c01044060703015501505c629480003a9010b0001800d000e05604080c0d280c0c407052a00340f4644032141e503000d03814030070700100b5078110703402003040c1d880c0301003000c0844100d0075110f410b0250100c7c440070811030050312500205102e80325045107003040f1070340d0b01c01d9401130204038291a2507414100d00d40040c00d0715003080d80c0400c00740d400304070b10b8444202d04005607070b20355106182c04001d020030510036440340c48043c0d207c102c3c00e200382c0c03a42c007854040006007500d050320a81c1c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 251772455 1250 251771205 251771239
    0x308030405120a12050a0507050f090301020c010c0512060108011203080709051306050102061510081810091a1012020303091f1b172a1c0201050114 65
    0x110364402050b5410303200081c4280e006412000c1188007468003001081140c0c0c480d46410b0941c0d4049030341c080000d00400000b10404e400c0c10281c040420050001420080040c042c5030031241040005404210040740e025282103500ea10b0319400202881e041d407044d494070501200b01795407080000c09004042000628091054888200038800281001144a41401c0344c0f001000e442c000d01c1e0041c06131200003001500403561900f2440000303440c4003c08000c8100444504001a2603c1d0790041468ac506c0e80f1030008004007400b04038034420006614145241101441c2e1954001c40c4446803800304000801043c00c150004440c0f600800028030b803410b10020303041d0322038450141d074424508000154100034260201d40f07103429a031107480018000c0c11011150540640f402089100b40c3d032001d010a141358000303400079040c201e00d134009240e65040003201801080015803000e41c00b6000d50002c2903840052080c8403407050000b00290b5040c01c580001154081c0001401041d030310b45c1601c104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 251773705 1250 251772455 251772463
    0x106061209031b030801080c0301090507060c0309090e07090605031b09070c0c030606060f020a0803040602161e0512040f140d140c040c0302090607140705040c0c0c0e07090308030405 80
    0x480320b03d060300781c0e00383c4628020b04802c6080c042d0034000d01c90041c400312581014440c0514084c0c20500070100d003072816004031107142c08001c044007080180c14001490416a0044490080e800d00141040320304000751942141c1c4680d02091085c1d000d882c900e02e400401c90085a10b2140544030504965901030003900c2030346c49810010302c0c50040c44000002c0c400300d40e01600030f590150380e031225000f0b14003000326503078803401302c0146c8000304c00c0001c500066180e81c001c00100784241d8994030303444401e803110142c2402511254003012410728240e02001010701c280d061841881c650ba41c2841e0802da81c4040003da58000d00c0301044c1d0140308102d40ba9160700180580c1a440103880500b1440c9252494403400318600b01c501540c10800354101090090099a40c1004040d0519081140540b03a48030500d00c1d100c0d020016008400c00440c1e980c440d030140070746054281e281c80785c0111452404101c104410b80c842260000c0000c20311008560041c5824200d079003140485443e0303110342c00c220f420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 251774955 1250 251773705 251773727
    0x3181a040507170312070c08030c13050a06020303160504081f021201031202070e01030b1303030b030706032703351009051510050c01140a0209030708010606120903 72
    0x4030a428449500ca0f1000000180b100c6828920303001e0142d11180c80070b82e07202d1540321004240020600014001d16900b001501c8440160301803110020380e100b021401200e000d401010060300008200520403c280301d150020407c146080d9162031b181451180e142e05d00c48a00241c07440000810340303000f00700c540550380c4905040c406c0c2c003d1940d580c5004918461002120ba015000d0082d0004000710a003212504070380c4c1104031040c0c1a9500c40350440458910b01f811001d155a52007460076039101005810041c05107a140041d801035007500402421080c4001da805510081402500181d1700000304204a03103861100c090444248400c040108118105c0d00340e60075801e800c201007100700207144021625100c2d0300704000e480e21060420305641400c006034016074001108804c0f02c2c810070040000c0c0b01b400d000024810900260038004038400d5500301600764002c01e0b0724803103103030520040c0c00030080e000081020303d03d404005040300301043c404981069807003000380c060501640a42e0700d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 251776205 1250 251774955 251774969
    0x1905041701150602030c10090311060115021018030f090e040b07110a02151e0c06040c0611060f191e180305090607030e0d0c03020103181a040507 64
    0x50040c0203503240a00030409081448440705a004002418900210458007851801d1002c0d00d0040188110310300540f11849044041148038504071100c52403c1c005140600a160224810b50100c5d1000a25055202c010b07501d0052508007000b072951304002c1c0c40c00949038181041c004808102c3c40c1580e2010f5182e00030217060f407901003084204618a81014450092178417000d03004169054860f81d100407110000b90017a0009030f0fa07191403403214001d04041d5042d8146140f440103264030a04040d0030142d0740d0082d41c0e00040c2844100032680980c00058001c5107061001070b1547e07402d036513495802924000c42145c0c100080741c144101c3c2d4254011104820009200804448140004201c10f801c101581d06291500e040c0443c1c40a01201480b240c040c0d0300d1904141c03030f2104004003540500000c40900900350f204200c162510310413800340034003405a9a02c00c0b032440c00094103458002244a80050215035078030001409450001025991101800c074240d460380f44c25481d10b40707107401000e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 251777455 1250 251776205 251776229
    0x203100b03070b07241806092a060f050d0504080d05060604140f030307060509030712030c0503180a051f0b0d0803040b1b070f050f070803190504 64
    0x500200000e40010040c840103404403001103640e69020841809640001840d401e10110b14201d120350345040010040e00c0d8a02c002040242505002c05802e24103074203c680701c2e2500340d00c90909c45440c41a03088184c41644a00410480300100d00b010101b0380924404e028048900e280c43c984070b513040e40c0002003008020012400c007410115010f4002e0020700740c182d41018000b43e01c1d03040000989003150451000e1010484864040000c1007411240d5150584402e1002401003085c2d4020745004c0c0000318069a0780d40c4040c1051415501031000302000e1500349295145190703803200441c0c1d80001c1c41803030f080401c5140b12245042050104028200344034030408081450244082c1102d5070b0305440d420080302c0402c80510181180a18003d040f84206000140208030070807070940d40002c2d820100041420301030f00070b0806400881050f5a5099459100020040c040156512251115000782076462502c40380c03c0c2d892092002d400703c0c2d2407000103103401c1039019009481c00f4140b060102 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 251778705 1250 251777455 251777473
    0x1802061b07030f03081501030c08060120010504080403031101020702030c09130c09020a030e1603031103121e130c0b0c0709020d1b0c032a0b04050106090608030f180d0203 75
    0x21710210090b909040d8070200d02c107501010b9130081c0b060000e0214140c40d03481c2a81e0b110401550754003848400c02c0041101c000409160940030b2080604c290301c6203141135111030560400401740303150100a89402c1c1c0c41005a180907943c002410307420042c003110690116507034a1501540c000d981203008141012100010490038402c2e0040c0403500b0896504102184411079601c4e99801c48045000000810718424408203100d58070200400c0c80a03800c8900c0e2002c0c060180c43c20755812500d0780202040c0004c025200c43c45030409a03000502c819125140303d140e51a000d040016a20031104080c4c40004c5600c0c80640071f0010f080140300b900c00442d244d40b0f009004201030080104444003402168180410080c01200f60400705034141e92602988400c515111400d00309400c05640750100c0e001c2d81d00c002907600842c551280740300e0400440c015241c150b00c4019244180c0040d8905d810501c034801d103203d4404182c8895043c034080e246c0c044480980410240204501c0294040c0241070007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 251779955 1250 251778705 251778707
    0x11010c0f0b0714070c0909020102211e0306060a0f030b031b0a1e03120905060f0715020301080c010804060b1810081b0103020711040f09061802061b07030f03 69
    0x240a10514103a02c902d8030380122072000c0f180ba0321070110020a076407819141440104101c0d80041c00161040c01150030034034000d05085640c03200054500c40c103060000b0314644080d091890003444040a910440c110700740a0f002070203074007030305507194100031541e603103180120311a4221a4084801506548075a1083d4460449803c80c17201d005002c0c20130580d001842c00c6a02038104078100e0300003404c1110600750741d02c800c0e040303048007881420002c40d1500420103590b26401405010ba160410b20b03500c02d998a4000340101c58a0100140c00b8810704c0100440c03180070500d480c40403000d10307041005a43d1464103a00621088044d00e41003010044001c450b00500c07203c0d0340c09141c00801c2d103954140d07100e1038160f981c201416580d290962621000704554000d8001e06020f603c10b200400900319090301240403908902c2400c60f0440e00c4031108005d00415101d44030001205411042c1e148986801145080c8220160940704801c041c42c8840700401c02c0c17044401940c4d20a45080203002c0c0741c20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 251781205 1250 251779955 251779973
    0x5040f14010623031006050c070803040608091509121e0d02070c0e1005040c030b030129010302121303170405150f0907090216020315090618060411010c0f 68
    0x6801400d200c44614605034201070302e080e13900c20009200030301d0b200c1d03003040c20440e65a0404c900b55103c5210386140441e81c48010306c040c0c005080d1556031034006240040049207840c150711113280c4d03400460003d2020f1680046401e500c0311648000507a9030b4913014604264448000103541000c0da07010641c80441a0150001d00e5114014042d118499444010401000704181c525132404c403100c410401003820160010940e51003582000200307200460046408c1d5030010b0324459000c100000c0010b09007166a110000b250b03002e103400c5003000d180d60092285620054440410020203168850402d0b1003455101c03103207052403052444d1804c2500c0d046503610030f04851840603803400030004044444c0b1101040c423034240c3d680142801440c003a182002907001a0b4212030160f03209481002585041040e881c0d90b00b5140c2d5004528a024400241800f8020703003680c098050035040c1c24803840000a000f038009030480c0203000180c800100688215241040041c0203012400f8041c051058a034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 251782455 1250 251781205 251781227
    0x1203121109040207060c030e0303151509120a0606080d2007030c030305030114010309120c020f061b010e120a111005150f030f0304060c02060c010905033105040f140106 74
    0x80c41c223006c030b041407204058890000315010740580603043c1800005203000c4060084003201d9040d200e20703107201c6c0c0002c0384040c180c1f8804031107c1c0d400100c28104010740c500c0340d0304c01840c0e07400140c040c080f0002801072100c0c0c426441c020b00e849031490030b40180f000a100c600011075214090030a160365914025029400902c516007441001150042c40c9500034026103d070298401d01c41c0c110b09100090666074500d1290b0300b07981000d131244c090001510b9040040044905030241d404c0b011600451481c256a0100206003458004020401d01850030f0020307210340d00c0d10303410009001e844d680e103000e280c5581166808400342c180340510500c01104461800b0055041e114510480b4042c0705155a801c0380000302c00710350b0f104020401040d882100e02d0101d5510051100c0e241241c00904c550079200206801e6421b030b040024807050b01341d40d0b10007000705a03500d003103400c41c040703804201d041400d4800d1051900698841c1e091045034200340c1e009800715900e80c0b04040c81561074403c010041d104079 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 251783705 1250 251782455 251782457
    0x1b0d030b030307030818150a0212090a0803010b18030303010b040302010201051608010b130b070b01080d020c012a2f040902150c030c01050103050d091203121109040207060c 76
    0x314000480c100441100c0c0d440e500740e100c42c0c0703198803540120201c608580a051410b8024203000d401d8006c00c184403180070386540b05c0c0160301c1c0e040c10a0014101c80c4050b298045580c40a64080b0000d1241e400b03417811122403418032500d0740c0a1884094000d800c441c3c6056150000100200b400719181c009002984d000780e00070031499444c000b4004140f4041c61300140800c811000411003040c1180007050000102c40e80544056611119185140c00614085500004603401405002810003103000402c4140c0b0090141103100707030002e0b094001420307045a012041407458aa40201031100c010000e50084542d8030b0042d9500e078a42042c83d001d5602703680080d4001c0f000d003080c901070064519064000323124041440c500b03400d50702d03264080e92500103035000074460a9030388030080c81800d001b50300900c040c001c0e191020400070241760a907005104803120290504020075071001d0050840ca0b03091800140740380d900c2e90248100d00401d03030015889400040c44d0001c10200350401075014041d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 251784955 1250 251783705 251783711
    0x41a070605071b1403070213020d2a1805090703050714180609041413030e090702032a0703031d030316030309020f0901121109060a06050f1b0d03 64
    0x1c42604480046240400c11500f00c0c9400c041004503000e0148145075410401c2101c1c50191030f9404221810720150050003444c6c1c1c00320b84082407011900608845010946807418000d1218188240c1e403411388418104000e803581842510005843c10305010b0480100b0400c0790340341c5400020040d00f81210072000048051410300f0284c40c101d0162280700c9006480e013040030320794000748a071a0300000b401e07503849512410000c480520210003203010303060040f4030090040d01414050300041a0050060041c9503a0b401c100100b94048107846221081c8114400b101d00c0042c9040c4003410880602035180c083c211001003055003118034010002c44122144440716004003c00d0744038000d18109142c401d607024940d4002910a84c00b154280e440146000400c01d465400b064a0072400d800034090410400b540c10180b05403105c03005d008100031929020f0616004021400b181418030440c81804800300d882400c42c840c01040e01c1107000030850490305500c54401c4241da0394108412100400d103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 251786205 1250 251784955 251784961
    0x306050307060207030b0a110301060207171f021e0d0b040b09041a130f03030501050f0409050714030319090e07020a080910050c160512010912030908041a070605 71
    0x3004035004049440b80e4026240061541c4c941112482008100d010003035596a04a0015a003501c0030b14046c26643e80101120b604040005480e80c1340e0030304400ea00d9101480d100d10700d924444131111160304140001d600ea048420b014108042070800d0141940c0010a50100c0e41344243e00030480f1041c110390600c0b0303d00160301880408a030503030b03000c0c04074014810603a280c600390031051504000c0814080d881e071402c580b1101c03c1c00d0380600084000035180c60040080380303880a1064110001141d0421652046944d0306580301d105104a401c401d14507000842103613070520540b04414800c952500c0d041030386a0000b003a80915004a07a4801c2403540881c250314400074044424541c002d400511b0304501c1c2d030811158840c0259081d04001e0200961001800180848081c402110807c4440342d42002c0c00c000940c0c2d2002c0c0c03d0981c43e0f142c0000140031900080750f001c03200347c0e507050000d8822020308000001f4412038104005120100040f403004228940080c0301440c014074003000551 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 251787455 1250 251786205 251786209
    0x12030b04140a0f11090d02010917210a09060e0a030b0406050103050618030a03110c0f1f02090604030b0a0b10090302031b010e090612010f0f0b0f011706060906041203030605 76
    0x151000c20113544040188000c140ca030a1444d81d030881c1d50300504006840a9440c500342c4030080d4041c5800b4130326003000d106d1840800502c0300106081c10390650060520750315403c018010603003482500304000241c0001030107900c4650745803010315000003020741c461800303050410140c1400c3c4011a102d1282200107503410080f81c260280641c0c2d40b001461901b2070311241107014000995152162010400005140200c10011070302d9501105024000c0003c04c1e10132184200415100340d428a801084244d6440e03450b24111000d40754044005c188030389a80c8550f81c01004400205508030f80070300d081d141c110f600884030307004691088085819080d1305401031440400a02040c1e4046010342c11089641d250800116601c403002030010002d0503241d00c0c0082c00d540546070131100d403d54a2610022503000342c010404501000d544060030b0502e1140000c0c09100994054421910303401e000c035006a8070141241c80d803803802409940c48940343c80305221072020703800d002c0300071a1600358000703614 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 251788705 1250 251787455 251787461
    0x1202040b0403230601060c110f090a09051b01020d2f060f100b0910121b0206060d030915090503010204090c170403080c07050f010603110102060114030a12030b04140a0f 74
    0x30306e0590750340341300e69515a5100110b103032914070000d40c804003500442c0c1864542c0b00c00389108110808001c41c82407814140541000003102c86040301c0e9400d01c4171480143d80000d56400e10304034501c0c2c414a10044c080000502a0101b12602c282c45108410441900300018605010750f08070b0349158101c0e15002c45040c40301d4024031581c05030103001c1c040000d1500e00601c0b030840d64011307400c001d01da000704410604111014004082c000e9852400041e01407070b81046150b074000c4003035400c102c00c50341a84003d051405284509103601c40c64103196105144507070b40c4040106000b4000b075484944404082001d00406a8001c000039600c00800c0c205800069100d4041c0380c054541c04041c1d2500b1561040035800b010f0141c03a1803051006501c0c0d1010300348650340c0203500625600501c0075414000a0902e241a44100c000d641c142d000d040c0d250350b01003041e80095a200080d404048510310058000d030880849241d4030500c0c009050308410310301801c080c4140900041009052005c40c031103021 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 251789955 1250 251788705 251788709
    0x20d080c19021c0221060a0b010c0b0a0504020d080a0801061202071208060f0604090b1008040c0510120f09050d02010c020606150f04170705120303071202040b0403230601 75
    0x40030b0f140c5020702c540340e10000b080781d0829001414514406070146100194405245480074441e03100d18100294081c0328447c140b4810403d1078542c82926458940348a03c210207089020706d240d44001040031135641c1d42da0390003515807003045580c4640411501800c241c00034419040818060b030845007400900344200c3e454154000003190f940c80240300304503405400106a242c110003510803801ca07681d2800098802400013000200c2c1048240c01840955102c1840315400d00452200740000146c041c052401511b10981e40c480740c2d00d684139403c03904460308a1b640040d05181201d41042c40140386c200c8450b01e40613004403614070a4400b4224200e5900d61010401600311b0790118403a0300d04810b2100c1d0444100403981e044c16500f02102d0321aa010382e202845096036901c00e502c65080034406803009007411901c4e424014214480700d6200d01c0020184000c100708a2543e194054807035042d00d0240c00350440641e2615200d00d040d400c84190b041c120405c50f07403a201030b08018400050a80c1c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 251791205 1250 251789955 251789959
    0x20a05040e150405070806180c090303040b190c120507060f2306090c09041107080f1803070e06040203040c0306060b0406020f06091903020f060403030614010201050402060a1b020d080c1902 83
    0x323010000c0904041e40c5140103490107107004000c01080f541560100094006803c2c0f0640c516640c0d0a548884424405100f00781c0703041c0903405103050046032100400c00d01c01f42c00f5080ca82c0e5100070a10f041d80040040320161110145403005040c030203176030421480c02e1b07207515000e02042922048200302240c04200d812550a841c01c00050b039160406800500a51404045182c10300c001355035500070f0fa07040700d9090038800c100414401d501103410b0140d408424401c0e0701078001607041c0804240c440e02d008007031300c2c01150000003107002c120100c44d00000454203d5820804561207182c4001c1c1ea502034440c102c01407244480c203141e11900801c2031760050b004807004101000300850140361001c2100802c1e405d5006030ba1204c9030981c014401070707129511035600054010b003400c43d03540c0940c40e2150000c0c11a032504040000680700e9004903403044150381048100c41e00041e80c0018002c059602c000d400c00b2031601414100500600540b00501c040401d43d0040990a0071640c02c4882c0031001035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 251792455 1250 251791205 251791219
    0x42003030405040c110318011209030206010b16060603050c131b08040c03150219050306310f1d0f03070f0606090e0d0f0c0213020a05040e150405070806 67
    0x49070b840c3c164001201070459051011a411955014500f5500020500b840800c82011002d0103580e002c8091881500040c000300656003194070003c0d607810050059650515000500c070500031002908003a140d0380c4039000344199510b034503240380c5075204a450b580c060352040c81c1ca1038014569004100700800c2c6a030b0003000d41c00c20040115065900544150303841048c5510100211703c0c40c115040030300e115008003598419000c0e0002e0300400051008004000c0d083c42130041039a5800202680203402024070110355010b4002d004500d881c1c540c8401190303180050200280c1c0d119040030301404105407603a03012140303140b141d6480c0c0c1210744078640540c10800500001408110381c05100500038600043c4035a1520b010030105d4400413240c0c00c0d00d82c03080c3c0e11640840c0d40800203408200320b510f81180260402c3c0c0c0419000340100034040c55540d00411012000f612400644000300015103403a5200e0a040d58030124010a1806050159042c100012656405070010902480c0050101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 251793705 1250 251792455 251792459
    0x20d02060112020310090f0f0609110907050a0e010912050105010e060d15050c0909070804170406120e0c15070b0609070e0405041109010f140a06020703080c0106120602030420030304 80
    0x1000081c600c1b000b044440c603910346d14580201da05030700840b0001d0f01c10440082c0b40885d6003010030711040d00243e1300788a071400400300094503034060107686a92405040a021103003003880140c9040c80301d0740086103070b5410041d00d6028006d054108034101c03404c2c900130440d55140e0b80c0c28010010148200a801d9000d400500c03104400b07182e11813588007815040f49410700513060005101e811050300c144000403034603070a10052044450362210510000058546080d10b80f0f00d010b44080c290700a01559181e0b030300f81c140d071250400e1050709884980142109059040128203a001e40c11003002500d50540480c0010f0090a00703040486c0100c1840e2110081c50034500f041002602000f00119442e40960b01024070030b881d010a914081e280024060122604003100b880c400c00d9804241449103400c2d000811255401140780c82c180c035001800d00ba0344400c80d24a06002d4003103030b40226900300c2c10314101001e025090380618010703449040c8445422005034a41e01e4001d00c070740c00041e41a0005c101c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 251794955 1250 251793705 251793733
    0x30a0507030c1e11030c01081801060306051015030501060c08070819020d0e0a0b0a08090f0307120e060702151b1c020706051e03060619020d020601120203 68
    0x6410058030a00e0200c0b00542203030350b00350f03104040d115000000001e0074640401c0004071003c4160110b4150004c1607042c0e20390340020000f070800b8240300c800348100b00036809402c200b0f40212000d150010010b1005060040044200ca03260744903071038020300c04030340280401e482401014100d0321250340f4400f000075540c41e07144569010070b104030350814040096000c00f800340c14210074111007540203090782002c02080a420140c2c0c642e0380d43c0c440c030398980c0c1c20311032085e080080e90403020320b6182c20886650741c2c141e000d1402c0c2002e05d130940300e4400420010308000012240040c000e65695451680c01e00e41014450940241c00300203510008008080142c03400b000080c01103034840301c0a06541d50320748404107040c0048000c200c804284010000c030392180d0104038010003420a072401515005c80e00562103500d44500b02c0c1003480000c00408102c0a0351440107584040341d800810142c0200b0908010f940c9403000e51520016000c0c0000000d032150b0300e0b001c14500c00341c0140c0a0801321110b012 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 251796205 1250 251794955 251794957
    0x4020306070206190f0906150501031a0a2d0e0103120e010203070318090609020d060f06020d180e270d0c0f0218090303091903120b150c030913060503030a05 69
    0x46031703812a6200c6410000c101e0500070066451003150320982d084e4100000107003070b9a5009047d03c80300036840d20a1843c0e80300d11904100701d801c545003a5a41d04c51010720041c0d003550204050100e000079100118004600c0102e490407240705002e452a0003181c2c0e103090f00d01020b0000c101d40980c00c14054100464020400c0c1603141241100c8201a06d880b04956403c44446402c1030b880d195020520202e000070900c0392001070404008152212881c00b60000c0da00c072000140c000420040c2e0205260003007000c41400003a0071040d030721926910340506514800c0403110540940c41d440c1108a1250b40303400b0418406102c0e9541d42c012054009844200c0300000c60b0030201c0e004041c43d81083c0104255800150285414201940d5641016104907140c4001d41c40b0304000c41240344449400a500010f07075820303070030703d03d10042099008031001440d85107980300c604581c40800a070300e8402c2e00020004101400c001c403a28059052540c20381800c440380d902805406910400c503c0c032221317002d50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 251797455 1250 251796205 251796221
    0xd230403050d09081b010b0d08091201060509040308150d05070b0c0c03031603020d020601140d0302190605010911090612060307080d020a030e06120105060c0f01050f0402030607020619 81
    0x40d001041807a1150380c0c03078034590310482c84400807003c4101c01605d12907080c0030b0718141030b200300e90700103d00c44640c85403c0181300c0c2000c0300d07100e550f14541404c9540000e42003900102401010100a843e050401800c5280b089034128440204215184224a894500c0c070844035041001407030300300d0420140f4001035111440c2c9031900d114104819110b41da080004011385076000c14030203c40d1001f443c02910300900586000c083d504082c0040c032101c21403001e4a84075000889107811180e5050505a042c0700070748803030b0f903c40140c158001c000d109403034005074100c40d001041080070b08407441b101e643c9030040001d4654001020020180721220b03522646410074002010354014551300e103201c40c6050309148050015800032801c0070181a0000c140360b07a80322042d03070b00d58074103500304001d01c80313001050040500c142c1020a120f00300980c2004020a4001468020030040c1000d4001414114040310304a01c28880c07540002e806034030101c1c1c41c03030140305c208141d00c1a2045420304003028200708 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 251798561 1106 251797455 251797477
    0x90b03090303060d0609020303072402040308030a0506010201140a051015020a02010c060b1c0606080a080406030504030212031e0a181502040b03010b0d23040305 71
    0x4001c03282c0c0102c0442d0610703040130b05454940010403001030003075050711010135454100070441f440c15540442000030081035103a0b0141001c144d20643c00024105007041c008170b404100c0940002c3d0f082181400081901c004c0c0f6040c03180308078001c4404607503054031a030034132200c90203200c0c0c4100a410101c40b890b10f0f065005a005e580e07141415070084c10044443c0780241849465440402100710040841c8119801c02c0310184640144d0a400d8030280c1c500600050889000141d040040e036200245078201850b240066006043c010020313401c2d400340301800095080542e00035071140c500080d010303100c01c181c038124005110005218508c0c0e01d1901c042d850100e940384031003e000b194010148600350507040c40c883c000c0d010b142c1c00005000e00120001c204a0b4005000d03003a60500d14004100305010411500e0041b2918828000900d0070385000c240420710a0005044e14090 = true := by decide +kernel

theorem cover : BRFrame.Cov 251618705 251798561 := by
  have h0 := BRFrame.cov_init 251618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 251618705 ≤ n) (h2 : n < 251798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
