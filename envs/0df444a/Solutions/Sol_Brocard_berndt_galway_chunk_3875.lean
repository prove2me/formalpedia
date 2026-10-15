-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3875
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:56:12.813776+00:00
-- url     : https://prove2.me/submissions/e052f4e6-ad0d-46f8-b600-be1ef7f0f8eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 696762589 ≤ n < 696942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 696763839 1250 696762589 696762601
    0xf070806060d020d060b0d021e091806040902031c0e040203012103180803040501021905191703190509150613020c030c0114100312050c0f1002030702010b06040311041d0114 76
    0x2040342c44049c130110520350b240c089120009038040b40981c0c10241f81d0701090000407601e50741c90b40310f505129000b50076210171940c1720003940301d85c6010f04e06c540301064030b01c3c10000590909100380e034140c800ba49054025080034100103a4910b4415200b02d0401105030190b06200f010700d429580200b0f40c05008548403802d14001900f00714a002e9603180d840b11201030f01010850009440c02d200c4001148003940c080181440c03116562496003a402c041e8002060180001c0042c0454110b030309010b5040101d0b07282c00941c41d0716006800c42c15808811742c040480e926141c07041001c110800400401460440c040d54090b0658006d0110f00110381d64031400031205201e40e0503103030341c41340c1b410031801c0b000fa0441c1c1c0c0702d0000c8074000034110100072010a00c5080024100054450301c08072380d04540b8080701e070706442d0029500480d41c5400550900e10305018030305040c41500c0c180d0768042c1c3c00d440001c5244050100030300040503180004e00c0d603107016080b0f00c1001e102c0d001c100300b00c62100414502e0a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 696765089 1250 696763839 696763867
    0xc040f0219050924030a050403110d090e01080d230c071d070908030403030e13051005010207050a080318061201082404030c03030c030209030d0203030f070806060d020d060b0d02 78
    0x81c150034140700c2d4200d154000004c10b240c04803a0b00c607002500014081d211401e086680403002480c2c3c822520401030740340034441d04803002404480e103660904c1c20503030721074010700e403188980d8100b40042003003582d50040304003900103481081d1034500f0340d5900f46001c00b4030103403070180c660340007181f00344001c070400c034a8886807108070381d021005d4108261101c0c6003070000c96480c0304500c4058100500c0c695150600d5030303100030829415049040501140c00d0981117031140d22120300c0b989016201d00800001c05045c58500d0740211a020070280d81000840301da104482140b510b45982d11002c02c00201c5060035400e202c06010785551001041900c1070501c00c56813001d84406074400b15110715081000080d44410520446139151501150010841c1e200f60064018a46015490701410406900e02940040614880c8184161002e2a0f4a6a00b0300b96280c845c15036030306401620821801a0700b42454009140414514600050343d507510414094240c1109102049490b0001100e400c80c0e114 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 696766339 1250 696765089 696765109
    0x40902040317040602070315110304060509061b0403030305090309090415200319060506041d0f10030f0c09020f030103110102060105010906030b0f0409030203070b180c040f02190509 80
    0xb0b00750300c02c1c5000e08004d0042d40c0c590081c80000c05425000c0b90b900104115a00140100611001354680320b080138a01207010f0102140c2c9041c045c0b00c1c00000404032200d46c1c2c0340456001c44600a24503140c02c6842c11009040010b00800461004008100740740e100c41070080d201c1d44c00f03034021b82c0a11f00d03035031108020344038081d401c0341019a000c85084001e0300039004503030700181e5100c00b0541c07645500543c08090306195001950100c070100300015070f44000883d84c080309000c881000f50310794403440c55080d601400d946107080880c080c0001c0c00000c4003d5072440100b0300482e901c3d050650398070782c50340c16640a003040c0b444404001c4010402c20190a1000307140700c2d002d00141c0807540c10200000c102140b180704200c101900c6000410480d103031403a5264030302c24041c2081c4210300f042c2c1000780d0744e0703404900c04441704902000003c0c0c044100341c401e07038008102e48001d0f2400c0da0f2498100800790201515000ba00c2e9420000302c4414809440300a9403e03400380c680756120b0700124100560702d21 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 696767589 1250 696766339 696766373
    0x11403152d0c04091a0307092f2a190c060f020c0f040b0303030f0103020a0b0c120307030228020714030a060216020a0e15010306060e01031a060409020403 68
    0xc0100784207004203100c0c00e076419203e100e0303400a060259520b82108511840805c950140195040415141682d4014203a0b1440f990035500c540e41d0710a100321020401c420103190700d103106024202100d85a1410641c2c0b12021a40000d41c0c3d410203a461814010480300c0e41401e1000400e0000c100702031406000c00030300c02800c0c11280309540c0c00003e900d8140504105100b005189179224240ea075590102e007405101800301c0c0d480b0b00c0d10003400c140007202804103a1160038081000035040c0011012a06410065405845c41d8421800701c0380b600e81000d4032a405041d001e100c01c5030010b00c2004900560541683c050715000d4072000040d06215190304010b83c132203c020b0803645141c070f001488000aa5000e41d006a03600d090103418034400000c50002948820381038000101c20328001601400743c1ca0f0034860b20036404011006400b11032440c0b140c0700100d1001c20004807e907019074444a1802e030000041c280c182c000000040c0300354003e40140c55110b5022606005000540c040711101d0300c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 696768839 1250 696767589 696767671
    0xb0a030501050906010e0103050403050f0a11060109181b03060f0b041d0a0f080c06101d10060c02040605120f1b0102062716061b02060301140315 64
    0x8186040000c105c00031202c6d145050503159404501018812821a83c41174007075589161204800c0b03100070300f480f8980b00b860105110b40d40c00454900064032807010700c40c00d032006500000c1a43d65030f0181103103035000a02581c0124280001c0814458003910b8480042c9010000d2102800003c1100700c402d411480b66580010082c001030040d0002256901550062a490701e010382601d13003144103214400c08000b40340200814030003100d441e4240300040c0c0d20010f058030200030b103440781d228143c02c00711344001c0803820100341000003501801c40080c110340044c1003c50000d0300c0d103001c00c4644401e40141600d60340b12449242c00424280304d81c1d91200304000c070b41001046c2500000707544e4100544044000202e00d010048028000803520500500d00e0040c1d0300c602c26030200d068010035843c4592004100b0455140040c100040030f10241154001c14850035039007482c072080a5200d41e104110340500c1040d4141140003490340034548641114120349001034815002031120316507060a00c0343c80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 696770089 1250 696768839 696768841
    0x50a060312110307050118050d030911010305040203150f0106090807050607080c0a060504050a03090b0310060f020a0f11100c05060f0402181e070203090105120c040f0b0a0305010509 80
    0x248010028090001d062034103103900c0885488560652040c11401803096181c95000e00d200d0200c03204c1810024025826031b1262030b440ea4003135003075602c001401000420b0340c450b10b140542c02540030940050018013261706461428480b01e22285c410b94070300c2c0220074140c004000d001d511180560281a010000d0a1058603141c08202d90740202c0b80d00804119000c240d0022044d001c1141000641d0004004d00250401e8140701c5d03200c090104040e00003403001c0742c010919026400880c1d0048100c1011180c0180c43c101c0e0485081d00e000c50f1500841c041e64103180c01144405161644d15800b808003a02c6104800c0f04102e003200d05510580144040501c011000c2170700440c966034881d150081000c2c16030341e5880000c0c1c00321040340a44000081a40900941c185085540038a001c1c04c20001907441d141c034007060f07aa90295602950008000700711502c445405a01c400350881e400d440402d05041d10340d91041c00110058000030000785005c03c1440d40c5a40c580503076401041c01b51082552 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 696771339 1250 696770089 696770093
    0x150a0303080a020304060b0901060518060703021903140406051c1104170109080c030c0106050f03070911040e13060606030c0e06031b0f0403110909060f13060618050a0603 75
    0x1c0040024401c000090780480050306108168115652100c4000e101d5105507840340c601404540000c1d49207950072506d035030a00c08904042d411140019010303001800a4800440001e41c00041d0320070450402100c8000300c070b182030141020b00040c1416450b0f01d501c0308001645055031583d0b0100b9090b045080209600521141e003080300c06030342840701c42140381c50500030445c1c003412110200134000f0350700140f07440156070080301404e01d5100c0308c002440419955002c102185100da02c8050741070b00505c0081002e030300f05511290411410f80c11060400340e4441000139044001c845402a221031800d40b0401c00c2260f10803140900524107040081c04180d000003440d41c1100e200380c5000f40c0c0c1c000081444a0519541d0070300035100d48603116614101c0302184004c542081c4030031a604d07854860705114500c1c02c0b24a00e131181400c000242980c1d5904220260007034405040e0300340d2841c02200800120700c1c2e5001e58005001c1c0780e042c0e502c0a0111001c84400c50300024060881c0510340401840 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 696772589 1250 696771339 696771347
    0xa061a04061b0c180501170a0b18010e0a0c06090e0c090112090203011113091404030503181218011110050a1d060a0c0c0308010e0726150a0303 63
    0xe040e207581c80310351000100b900d4a075846405a0300142c019494010320b40e102003072140c10079410399640c00400f58014032480d48196461001810003440908144002144900400b440024034400400003042000160388664204502c904040e9603031450b2007801e001e8581c004100c1001066000c4a40141d4a080403c481c1e0900648222904002d202008031104500581040740d855800500821240d44200c03d0040c03640c1c4645c074000c800030714407000095a03103101c0c0300e0301074072084054004202e0380c1d0701d41c2d007101c89500017001c0448224807120125207111080210f840d1550540701a140e640210b03406808455030180f00042c100600314001040c0c0c0d840128a184407070b000c4100100d50354664003d190701506941400d0814030100100122540e00c000803c18003444106008100711800c03100d04503000119154041d000c90b18038401040071200c80c80b0416803208051071b10b2100d0481220004184e6864441c1d8403240500840134071000c1288d60485c682c0d8500101c485190716459550060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 696773839 1250 696772589 696772607
    0x906070807110a02090402060d0203090a030306080f1e1e010e15250e030d02550f05031305010f120203090a0c06080a050601051606020913050a061a0406 67
    0x17806400c500c0c020a0854940d007040e00c1e207420b0300b441e041d0b481e4684210050384d1001d86150640000c1d091143c0061030305404902c0800444030740014004600041d88407003102115824100500d04c2518047c5000003094001780714541503500001c11344228841c0000c0c03406a403081005510042c0e641441007540d1111520316100c014548070000000515000b620b070060040c0c51b464040c007841d11000348899011032140b6500f0002e0803121001410b208400f24042d003070300c3c8000840400180744035017040e1401180110114031440d00d64041a00b60b54818240210035400c641c168000b14a401c01c051041d811040508020710b880500d41d40460300041030700340c4403080304c10020343c000045120103000380017001110741c01100f2200443c1c1c2d43c28004207241d03800c640d092011450580843c03510740c03180040f1880405160480254240e06845640003940a109001d5200449014240d0f44401500a080c03090301c5100000071454641a01d420000c200f11000c2e01c91050b081200340200b030f800100305 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 696775089 1250 696773839 696773843
    0x606090a090506130501060504061106010501020307020114071b29090d0203070f0621060b0a0e030a02040e030306010e270601140301030c0f0504090c0b210906070807110a 75
    0x1c02c40c0e4030b40d0700110b800703040000d224003289400c080001c00c10b00d1304140200700f200c2c00d0b580e403195925030700b0010b15228a003c2c0166401a04100400b0001d903205810700e21440412294140c50002c065441032000c05201507890102280b07002e08000b031555200b01c940c5822101e0301d036508020a50101c40c20b044c0700d04118a407150f6081c0c0800410342d18100019400741220400030a0303140d880da000a401203401070f641d214072150110440c0c903c50706034050741044807035036243c060410300101000c1c0c3d505000c0900306a0140b1441140001603543c900981c6140503103e0055a030700d04005000600541c0818403d5010f0300090341e0141801c00c100b42c99010a1215078004d810300c4c0c40f07100c0103c5070040d42009420b5803041c08800481400701d0b400f41075040303454042c100b10006584006000642e044043c0c050140401c1d8030003001780302c200d00000c018041d0406211100384048014100c610031058524810650100c410000c21581000b10103421000a083c906c0c0107000c0340e11000e03a600445000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 696776339 1250 696775089 696775091
    0x1a0f0c1e06040201201f0e0d0f020a02040f0e1603050d020a0209010302040509010b06190339050d090f0b0c0708030103120e04050109090219060f0302070f290606090a09 74
    0x40300c0345e0000784200c143d0000c0fa0100d44081036648155103000c0c00c0d19555010b000d01030306004007003140c0100001c060440a5070040d1540b440641c00700002010a01d000c07944c0e998450040089c3c889062100201903030b0040c11400c0c044d03040d410500d1400c01000c40e100d043d940010207044c00b5a80d0724103401d044950441e0003150a69a00c084a4054110025200d0300207130041051100702e80404060481489580e40800c140d112002202ca081028203903e40b20b0f20070740e602d4480d0f404031f613003421010325401c50504d40e00c0d121a03e8107420840f000010142c5c1c1d0303a181140140100081d84205680100703140100c2d44c1440c0341c9844200c0248010310004050551080f45030b40b80c50b029400300e0380f90020041081040c2d680d14606038014010780d141c102e1148140e22060340903200f281e580351054507165960180c4182441e0403d030004e40c4600b0040c2c4001c90a540b1041c00600d80c0e00d035449206001c0e4100e42201d007170000c50b48255501c090440c500c1402d0602c241a4951100001c40c03085610000d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 696777589 1250 696776339 696776387
    0xc05040501020c040e0f12031602070b09040504060b031009150e03220306060f080d0f09230303070501020a080c071203020d1401032004050603071a0f0c1e06040201 72
    0x280052900360761490206c901d00501040051a101c4403016610a1090704966508802c01510407619a03003a17008101082d00280329406440c240750b4400c96000c1d200344000991960f01381c000a107071101800c4c05240305900c40007000100030100b80c0c003420041d1270000500020341c0c1d903481e0315180d004c0c210708e4102555401810400c0c20708546401001950040006c0203416160b44d0200e2a0301c0301030003001124865595002100b03480381452025511355952108a4982850741141c04854101103403119040007940820700c030741d81400200b1070607108000041e9201400d141c044c1032510010904510268107000f00804103000d0015812400c1881c500103a650650f18282d9009243d4505c000c85a040e503400040200300592290201042d10131080c954414040c0d4100700982e003048480c2034141d049610200441c00700306541c542458070210b5018103040c036030f940d001c859801c0341c0b04c1d2810a0344540c0c0427080300310030f5020104000e001e032000303803c491030141c001800e00d01449020540e0288081 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 696778839 1250 696777589 696777611
    0x1a01180302092206020711010c0b041202010e010e01090b06010215070f03061503061a0726070803040c0f232803050a061a01080c030a0f0c080a0c05040501020c04 71
    0x501d8504210759490f601d1282c3c54140d0078198000e400520341150050008555a8007540c002d8020300540360f84801014110b51b111390b00c00030604e01d190503510940d0340310620b82c4030148080c0500180000321000000e020300f8a81090b8915101c090559415500001030a80d0009892080542d0100b41402c01150303089801400b1802812076038012100c2542c01116055042d034583c0006040341c3d01c54180e00d10f541d11840c800c100600c900b200040c51000e40e0010b02c6d01d0032214032810403840c00b03042100b42c1009520f8403056000c0d4001ca40494112031001d60502c5020340d110215000382c440001c145108401c0c110701000c003007241c201c2c0c0b01e21030303600350044d01d00300700d443c0b0b007000c07060b10340c1c55031485481e0740d41d103441552401040e070100d80e603c2c2402c940700c8188148510078401d440f0169038034801a100e1459003000740c2c0c40036201420042e00c0b07056207a0391441c2d9001e1081e82d5140d580d940709852078425890801c4036443d4403020b040286c100020032040e03a000840b009250000c0b0360000e0407118507 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 696780089 1250 696778839 696778861
    0x70308070c08030106020604030908010c09030213020421140c0616021f02010e0c030c010903021c050a030f170609061507061b12020a0206010e0c120a1a0118030209 72
    0x380000c2c00e04000000204201e940810a14019442031300e13411001c035103950146081c0c0c0ea00084507000214040b82c100058075110411003040310703290b00c0051400c0d8540300241000d800004001c0a9081d80212030b004201c0d409154840445140014000030a1201c0000d0200d00c01d14000760610749002003c0c0d000e6566880e81443c81880c805808901d44801d0003000e4060007050410344ca15006040c1441420708001c1030255a1075016502c2d6185941194200100b02d1411303081d00c000b8243c000040c4000540c100460504513010f0b8843c5114100c2c686001001c0000ba014081703041082103007445000d4581050868024508580a4442841c1001151180d001d00746001d0040390030324002030300240803010100110b03551503540304110f05403c1112000ea01c522004180140e10030401007010314054070081c1d03040a887c8c4201e603e0308051118000310042c0569070315103825030b280c1c12581542c000c648845a001d500303007020501000c261170b5a980860492002034002c00400000890490750 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 696781339 1250 696780089 696780107
    0x9061d09070e0904050f071403071a0409060303020309090106211d240903031b0904112101090b0603040b04051c0903031805060d0902060c030d0b1e0607030807 70
    0x5000c5418626090525603980da86d02000120785010760080403030591955240c10301092806401403c00c00d103401110400301c0c68030204c2c07442004c02804045100a9540980c0e8015400381d4001c58856240b0000c210202106a00400a0025402c40480e003040c04807142d05001a50030000034100450118022885004041c0f800d028068240d042648515080c4400e0303600800a9000910b960740741c0009540e440141c2d9403100c050900e46000869110110041041e114007a001141c51412030012032003640050a14a403010308403007828545400001c20b55005010808040c00440c00800c0459131b40d11002e0030141440031540c00140a1003000c100b040f1a480074144010140032700b442001741106554001100000c507943c2c462890b0a00c0142040e0030303110300925461500904103030050042c00714581c2241c01020a108075081d5034414806081324800705000410700e42c0c81c43c0704000040e041c420341440320340c48840c901941619298243c0e088591305080505064880d01400e82d01100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 696782589 1250 696781339 696781367
    0x3030f0708040f0f230a050c09060108040b0408040f09020c060702030a0f080c04030b07090311010309020f120a081b010f1109120c040c110d09050319060f061509061d0907 75
    0x915030148418001002a901011902410980d1062400300723040048600060300c10500082014003c50080340c011800e0580003403140d0b180f2460b00d9507684032402006600c0c1c0c041540300d40c0c0483d000a4020050051690000c118405149080704400014040c21040c82898003005903240010b00203080c0001100c001c2d58102c1c01d01249850518001400e66140e400104c030a489420f0000c14594040c0c000e01e1161a4000d00da90540000c00082c070680141c0e5101603403240c41414401404501ca900091000710880805607801503000c01e80903003074400030010712480510380345210381001c0c03000068400040080340c44c000103030004d40c6101c1c549403480100c1544180b170602088a040d4000c607440e003110b45e43d1000d030ba4500881107000c2d200701c040c507c81c05806070425000b05030070110800170202d40601c90940007030b2030712903654084111101c1c2e80103c071011000b030b000701c1d0300c258111949070000e01c210f252110110b200c010b400c4094800140000c1e01810000e0041046603026a0707107034403004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 696783839 1250 696782589 696782633
    0x8100e1501240318080910050f030a020307030b1f022406041d010c0801030c080f07090e1e0c030f0715030f0b040f1a0604031a0703150803030f0708040f0f 68
    0x84014204503040707910201b4058410786200d1501c00b0894040c1055580d841c864400c16420f40d43c407014014042d60008103c9420180c0d1510410301c0d59030307481d0310440740e2252200d50040042c03c041c0040d180100c0c60501d0420440c0d00003210b00000d55560410758414402d07036002c038400c07004005003441502d48610100c0340b0b508094490740c81c5031744400b00380d040740d00660a0300216907540300c0c0180c0781c0c2e0000c019400c641d0001d100900c126481038004040d00c414500841d4141c84068000c80c00d0450000041d2400c0e400048050026103010481032011013141000362520500e40402c65911908110aa000741519298400000282c0341d0100d4000d080213482030200403d0706003400020f0000d807034a4108411110301240c13941c1829000d5905603684050380303180d0503a0380f003141c0c410000000c5c0203004164031810301245aa1306021170500403d60040116107a040c410800d86142d40e0091010702082018030807c0302080c0ba40f24034070b01e01d942040b12440e80c80840e04000c4100382d0200903e40c982 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 696785089 1250 696783839 696783881
    0x6190b030c030907060512040b1005030102040906180c02190602130e09100606050a08100b0c15011508010603021305120a0501050108011103160908100e15012403 71
    0x14204003004502c100f0b000300a0381d4400c2d4640130107071081d01841525903403c02c050300003e8005078000c1821a00414000c2110b40400e075150300003400e980c4280c004404050b2075100c10000036045880788000440401c0050000c1000008002d40e00c0004d64903580486105500c10800c2c0301740382c5c1c121421003410350458400c05458001c9205100001d65840e6a00d10030010101050701c400d21420742510604d0b0b645510f05403108208542d01c400180c03000d904400303000c2c400510308001c000184400300301000036003852809011100201c4005a0150010102c44900c0c00035055104032850b0545109050041c0c075002c4d0421b0050180500350001a0440160343c40152160400594a0074052242000b80001d0b81c8814649099801003c1d4196242d81c0600118031140701018208140108a02e0714841050756032582030700d48009201d280030b4480d070302d40401d410010144281c4254500c02441c0311202e5162186180303180580080d000e4800e00000b8120620074400e801186c5100550040f00c200c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 696786339 1250 696785089 696785101
    0x1d040906091a0103120507020a051c0b13020a0e0915090f0d03060b0f090310050f2211060c010e03040801020301140a1a071502130e0a02070203030306190b03 69
    0x1401c508a0a5803503490003070107000d00c0c903260180e040c1a2640064071442000103c001550183c000440481c0d100321181400300704c03511032000700200d40c10700d0403030a112500d0900313180320804805004401c1081d00c143c007610150710b070844203008030b92400e200001281e43c0c01000504100030400c00c01c07056192901401f562803800501d414009190303000b52480c922010000b5811104240b00b030343c0c540c0d00f0a004890340343d01703190080c00b4605d4000d015035260b0003048212908031181103a0031417560281c5414040e00d8a075411000328841201c10220301d009140c0e03210568060340c7c4240061140c00002445520064290420000260940b00700d035100c54581c01e92601030342003405030358940441d5040d13a03901403500e00300e000115540c0c0381c0000c03610810321880025640c00b400c400e072400000c0c0303000c1c2d00300c1000900c01010a10290080704081c2030070158050400d401c0613205a0201e401809158056a0080100c0703400c1617003124080c03c41d40107140c03c0e119121084e442610b1004001c800c00030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 696787589 1250 696786339 696786341
    0x618120b040318050906060901050c10091709010c060504050f031612030b090a0c230702040c0207060509040f14092103010e07030b0301091502181f1d040906 69
    0x2005038401e44640c00694600381403c603028440340701d45580103400c0d0f40400e00604207103004018801040c5061880c0805892034940f505600349a2060180e03900c00040041c810b01d2048140d0207101074440354039041410000910099240d0000382210750382d400400d003005070810000075481d14002c20313a0303204c3c2000301d20b030184030380d400c1429612200090000750780c461091041518440e03000300240e01c1c5490b181c420f1401410340310a11820301c1689212807004001c5041007032036030b20005000c0c55645810744107200c152441c804407202035502140c0306101940e007000a803039090409032000a180c3e503400310010064904885000044403100090040d9202c2c00709162000c100e040101211080b4544005403040c842441030510340c804000100d83c00a10940040c101c890004001042c418003d80f140714148480d004901c1d032213039002907155034100c10b580b03060810304800c4036241c02800280d60b02c800315411400c0301904100003c2d1100c841484401521590680040d0082105060600d0010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 696788839 1250 696787589 696787591
    0x1032a0e2214010f11130e0a09020301060b312c0a0b1509090a09050c09180c0906030a020405100306050f04031b210905190e07050c03040618120b 64
    0x66800d5050400015505c04210101c88440c40502c8800041600d0a016a0f1003060041e0214a040ba12440c0c15030143c1e50034056200604402c000c40c594510705000300000c4684001e001c09510f03032381050000d91203001d4486500031261080c001421803c5100e0344041d104402a40c1900c0012180090108109050f402040d413a10b0985828a00d074a048003031301e9843c024103281d0b030f91002104c000110464026000301d460306e80f20300d0444800320003442c005800000308680b501000300d440065440300b013000b044001181e02d01640d000720541010008070f9103820495001900550310341002ca140c001c1060a11340045030131174001c0195051207550410b58020589003580020301110088a0400010100c0c510b40381c0c0c801c074886c801c280c0c900552110008107410080910251400019040e2100800040003000d5003440414150400e074100c5201074000c1e103008200201404a484402d20000458050b02d000381809d000c10000160419010416908012402d050300b140d608108441c0883c0a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 696790089 1250 696788839 696788861
    0x3040812070807080d0209060c010f05100b0f0a1b060603121706040f060b0c01020d0e030a0228060e010b1008130311030f0301032a0e221401 62
    0x240320000a0042048603600030321501074030115007000f1050000b84024018013111300e000e41c0250500d42c0540001d9040e801580c0b414400765101c01d400034a01c40d1a02c1840c2e800100f41559000d504d0800101854074090b04001c68444170001540c0040d49008104040400341000c003a0b0704560900d29214024103094401281c2c480707143c1c803511440d58001c401001d0005400380f00c040c0141c0d240e40030007000d8101c80840c00c2c1802d6454201003070008906000745500700d056800540d41e00c5005259100b01d42c09421000d0090300188403d8038000e50224800140c9034144040b5125131056402420802091003402000f1900c0d0008484100ad4103400881c2618001c030740c500c4811401540c2504d04180840d1002003a1600b404403000090240c400c1c141203011360000c403410801c4c9009101c000303074400e0b0405c0d1680090001103440c110140050000d182241502c4141840d1611032892881c1801030300c0315110504903281700140e4030144d64400c0341c4035000b04008541010107211107000746089454 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 696791339 1250 696790089 696790093
    0x6031704150e0603042006030a09050705030a0503070b1b04180e210d02090a03050a0b0121030e061306030b010f1d01030507051209010b090906090c060a1709030408 72
    0x4001d0540500507620b49100b02821541c910b42c1d40e5500c4800c00424046031102124241c100c43d010b03a292440994030a01c80480002010001e5003071642c42e05155a200e28030a611000c14003001070030110680d482260f00440c14040d689800c035a100003000307410030000210101040015090f044025004144c00845008020402280000548030040d421200049240844c04000d00704400c5004041400a140c4014202086040000d0031940a940140d40b25489000c50000b8014010139240c010815241e40852400002e1104802c15144281c05024056140b811a22948800003200c111007a4100c030f040369192600005030080c0101020b060001b2004c010f0050b031a0b01814150355420401210710030b9004914004402504d0000c1203002040002d0090b180c0c078040c41301429004840f03a43c00401c840d0406030601610400050285503268042c1050100c50600400ca52145040c10f94141d65504d03000042a00c1000c40540000c1000f1080e004000107118080080c006881030301c01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 696792589 1250 696791339 696791369
    0x180e151e0708070906050a0212030405030901090e0103170a030b180a1803092306160210090b0d1a18090c011403130507050d0f0209010902031b0c0106031704 69
    0x801201d4100c41200c044001c04c810644c00c0c0b1285000d2001340030180c580c3d10468500300c0070b81c2049119500155000c55980c1e0000ca13103a07d0560b0444a041d014029900141200d985143c075280100000058036641c2c4100000d851068140710ba00a10100702c000340402d40400e00030000c03a82144801c941c410141c6240c12603c1039600180900c6100140c1c040d42c540c0c510a05101c1c150300c4a0007500b11641c44400c910800d44c0c0e0340d4a800d00a8034041b18030000f0900000081d0062091721111200b0110410045d003406000c024060416110000e4011000041c0144079040c00ca10b400b14000810317a001c01c150880194111100103024030504512040d1600c080c0544015100c103502d40f00d2466801d003003400000e5161084024004005002e9803c0324041c40d91440400d03e00d0b0301207c0c0075540d4090f01c145607001d5042106845005201d607000851840c5080c0f035031441d81c001c041c1c1131481541c00000311105192000d40100c800380d60040d00580e1100c95181820300380c4d6110384911100b81a6841c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 696793839 1250 696792589 696792601
    0x9140901050f01050d0b0a140f040c0f0303090e1f0b091f051603021f0f1d030d091502280f0e0f0d0507060e1801180e151e 54
    0x40110b9049910160041131120034580d03c410043c90001d18000501c1d82d6000d00d13082001e010405903000306002c192400d400c2c00c041c2814205443d054000c01c101e04407810f030400000e9404010a411152040e24852030b5445106620f40070383e05503024030b10416a84c41012078540e83c0c1070001c0c94505000c58000d00c20382d0403545681e0b4002c1e0307043c03052004500103000020700341a030a045844441d21a10544103c001c402014248100400c1c0700c3c200d40d684e48081721007000b400351003440011b041601c41d50700c2130045403c2140c2e0340d205000134801c0d82d54407041e01804000c1202d03035095a6241d410015519180803648580306c02d501681895030b40101c014071000480d0084091110340400342d580c04900403810b4080c0700344040d03108881034004c10f0302c5440d100812402e01035100503000c195103c044d602d42c40410004003400340d0311880d4507814403000403c411180303500708520084640901003203814401044908100500011a0526440c1401c0210b061a40307900d4103100c079064000c00e10580ca501e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 696795089 1250 696793839 696793861
    0x60b0a090b0607020d020303071b0306061d010915030f050d090509010b0d0504032c090603070605030f0c070f12031407050a08040507050d0f02040e0c100e03070914090105 75
    0x81d00c1190044000c022040140c2046415211200d0025044a20b0100c0035070361402c4020030b04c002902229407010040c001c02496010303680c0200021540d0640080c1440d5203002c229206100340000c1c160b80301a038001c9248820240d0300210741102d04000f00042a040c559140c0c041c180e001c9002075840c0300081454a0002c038400d060f140d100c0c20890505100c030010000501c40a44281c00384504014010645484010252222a20f0b1411071046d034108500344105080e01400262091b04001c3c801c0c8585030313004007940e9021280d62050080c5844990361094075220f00540540040d004282e140d00740028645090316a020391741d030400c071800d0051030011a2900648400300040c904002001226101e28210394005004c2c0089e03c115603a9140043d204880982080300c1400f410009881980b82600c220802a141040030313120480c1140001808080c03554482c200f4014400d45c06411a00c040003820003400640d030302080780810360522800040400c0302c124440b5820480005c40041d45 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 696796339 1250 696795089 696795101
    0x30908060c2106120f06010f151d0a09020d0e060606090616020a0305030a0206010806070e1008060415080c0102010b0a1d04030302130b030901180c05061602090c03090d031406090405011404060b0a09 87
    0x1060703030380c580c3c06c90074507400c16035a190007180542d004c1e520070342c04038520cd21840141644000400005075529200c4070450826400034412803090794284504103580d00c07040d045034898190481102207505d598030024080c0196600050902c1c400454081905900000d405059070120822500b10f952039603403c503001000707021055040700c420b410340d19426014048040d0052001480800c580000316600f000317200850340b1030700c0d03958030200040d034142d42c081c8240c072441030b000d6458560700d50030003c003031114007124802c20154101070400201454401d034180c50301c0702001401d4081250341d45580400781e40064030200120352800a0500030308141c010441541980080c0000c2c1c642d207030108001050b004070090405216041d401a0300503501c4a02103803280c1d103481d448a40b607040405040385008005d40b264001e162501030814042e03a45103c030f0035030151b01281e1600c441c0c2e50318031b807003030250905460040e07d514504082c841004026000158008c034140c031041c0c8019a50380511055400b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 696797589 1250 696796339 696796379
    0x6020f210907030f0b250206100b0405090606070f050105040b0f13030e01030f0612080304030813050c0918011505030d0201140114030a0b04030908060c2106120f06010f 74
    0x31001c4114800285d255108651006010009840c02c48003002003842070541c0842c01401a0030020402c0904d2880703041610142c08410708150419040c000800c08004014206074031500000c280401044501d91441c051664010000d104a080c28580180075110540e110208004013400007001c644000444c2c0c2446034142e651038100c1c161820042d80140303d820340914405844e0540854150740388a051004d151040c44403640d6460700b81001064000050041c01d548119000c120300828000140f00c02c6014088a08001c03603140c084440c2800c0c180300b00119191b50030002c03410041d014425010302100c00c1503064402420061500308e003202d0a001402f51008405001807001c0e01d54a6418040c00764043c0c00c41d9210b4480d030702c5600100c001106c0c21000988c004c01c1c20700240c0800e10100c0e070050302010b1424240401c1240b00d85115104020f440c2c84a880200014890780c1c640c074060b10201c0e40c50003a90746006120350520f440c0c0d00300b40078440c0640301d80c90002554100e40c00023040050307 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 696798839 1250 696797589 696797603
    0x1051005090d031812111003020c0307060c0905040606110606030613110409080f210f04020d0507030b0108101a03030f030a060f06030603030e040903050d020706020f21090703 77
    0x668580d0b0907200c18840114106000d4140d00d03010810000d108255405c3c00d0142c40c8890044044804001c42030319010400c5040500511124090080c000141d5a03401c3e40300c0030100d03c040c4807020071624030103654081c41d809420305900045041d0048169007010108100360388070340d030307658003419640c12054620b216440c107200702c40c1d400b18404040482032a10010b0004c01c480d500c070344581e100307500100ca84c5d0554480004410407c1020101c020300c072070809008160340c41c5030244000d00d600800a00190069001070440b0301001000c5c05520041d45d88400442d2072540c417041c0b01d035540c64554050490840c60007001c070064003422040740406910040046181c40c01c4c40e030708002990005840008013985699011408080d0302119a002e004180d0300043e80c1c501e54280107040c0c0c80c441002c07074091854056202b001c0303603010f411115103080344032001d66104100d00e0900000c3c802c141c4c406001c0c0001150300c0d0304840600201481c01c00c0304412001458641340400c546507041807000500310 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 696800089 1250 696798839 696798859
    0x1180f0b0a0902090c0a1407030e0901060305040506070f0203070515100b040b03070f090e010e0703060902162d110f090c030a27230c06040e0a11120105100509 70
    0x28005e44c4002c2162000900d0076540300c202a034120161078015801c100c3c003044140e00c0400b05800c10b030012074011300d4140380611141c145626400c3d12010050006000c110807100304a600c98000c10445034410b0303000089901d054111907013240752035015201a000c0304815000005e02c0b8150ba4191003c0d1113091519600d0350300c2e107402c16149500784840400a0025007800000c1c11304260030314a00800e03440c143c0c100b1500c1d1260b07004003150081c0d0002d0350383c14414131508446d980014102c0b88910343c800c2c0c95038410704007280d04040304c980c18800c608030051504000010030460340c10400658406a80300100c94a40c3c81c20040b0035081110b5400c1c45020a10001e200b13801c083d0000391280d0345040c1580030404280000c603442d110402e0007900c910031208551007084510740d040200bca81040040c0081d420101e0000e1994411740c071644800114000100304c07150075580c84403c0340400d03280155690f80701c40f94091000b01c0248541846613110010410f10280a10125888400014111208 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 696801339 1250 696800089 696800101
    0x60109061401080a02160b0403090305011d0d0c0302010e01060623040302011407150e0c010822060203040503190f09080303040c091a09070201092108071101180f0b0a090209 76
    0x9412074100c004a404c1b8a100030340c0420103120020740614000d50300da0b0311031800c40c2842c0c7c2c291071444042c00303030180e179030503010810307490203d29050340d50324500d402420744005042c1203016045922211702a94a06a0300280440c3c01128480c20710400d01603000140521910b140c00501842c40080d011034100c0140d5130743c1213803110082900c0c40c0710f20200b840101000c4504021107074001d0507201140e00c280320158040d071304040220f501c1005041c0d071404074405100c698442c0d500001000741115000f002040400c41c007401038802c1040751590382000c000e55000700412000da40090140810080200803031090b0003c01101d202c4c2d41c001d84810328161401034504020a421000c010040403050a05d103625990100d0050186c5465400490b1125031402d0050380c000c10540a219955100030407000300c01d4000303140650050031410b0107406101014a0103026009184040026511080248041007603c11410385028040c248014040d903034140803000322900700c000a9449440400080e10b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 696802589 1250 696801339 696801341
    0x18030b011e0305011e05090706020309060901171f06020319050f0904060905150105070f020f120307150b0607390b04080607050a0c030e01140309060109061401080a 72
    0x6201101e1240780000c490380da4403201e00b1101400c1c40940005469005080082094050150030411001c0034120700c0e49010b0010f540c138030440000502682c0c01107005004c0f42c0c0a04640d00c481c07022031038444408e250030081a000700680da66408603034003119002249262000007519076090600020508031000301e503003a04d4036000000c206c550040e04000454203a00ea40c010701e4000e00001c2d40100e1107041190b0449041c08180d00c20f641008400d2100d00c0200e5000000102196010364540030180450070204022484465201d00300d0301c4001065030030440d441340e80b1800888900c100700850050700f020043c81d803140d404043d180c40074525881c80c0072119000000d2204111100c207071400c540009072010303821001c0c4d01510703001002042c02c000d4514207100150380008640740c60351601c080400003805802070400d000e02003040d050003801190f40130300c03288200c46011303001c0c1c0d035100d10b0003100d5141e5400b000d000b89690321781440c10000d00c0340000020b220408005071030740c0c81d680c0d03928013540e0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 696803839 1250 696802589 696802619
    0xa05010510022e020d1e06090207020321040f0605120a0b0d0303050a0b0307030515060d0201050d050c0d022a0706020a141608100c09050d060906090b0709050118030b01 74
    0x1d402d95007004605502c2050b40301c0d50380100341e10320000034021071800c06071041f218250301c000c0c102401045600010380d0003140d4074000c00b81002002c1154040c40a4011240c01260880043c42c004c00c040410301c2078101c4042c01041103a03401295243d507404e820002503c5400c0441c03500050300298040019020340c00280c1d00c16004e01b0002200f030000070000340742c06099030080e40c079030300580720b00c061000300e01d0140c2e0360081c010381d81e814200f0b071103500007040c920998804d100b5455980000c5150340b10504201c1c0c1d0030114402c025074584d524540202d00c0071040d00e9004000c410361886c5007030420b030042910011070301160040c043c8910700d03885540c8a154494800600c6001e25070000c0900586414044007801809e0020040e100c03210400340d04a88100e2219400d100d00304404019540d01d00c00c580e04050360007d80400c1c00c103c680703002e0307000e40740c60200140b40007503080c02c1050342c0358089484070071140709a80b004598030722200c6561940321507020240410203403400521400c500c101c0a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 696805089 1250 696803839 696803923
    0xb0403051c020a1b1a15040609020a0203160c05060406110613050d050c07050312030919020a06111906020a390206220f091e0b01090e0a0501051002 65
    0xb0112501e50b1542e48112908100c8114a142ca03542d80e6022147c10140300e100c0180113220021441c066071110065646c0c003860458000d110003900c10b180800c8a151061401003201400c601e4a50703440c0c00c00905102103184629050340b040e0310001d4024070401c11003080d50f40d00b1401403d240c040581d81100c06901041900b2028802c000b0001455202001340000c0c0c2d40325461a0340c0c60342000da40141c1400c000c2000742046084c015200400b595440c0110001c5800c03e04024103544941c41200d810030401c440000c044a200c2203694040c00301c290010000800c040d591132101030809a20382c40003840c60b1460bc48400c50000030600d030204070103045440035000a0800b030901040718000d9031841070801e00040201400b88040010941030300c00b41c40600488007003481a40003033004045884010191022560307111048030790564059000d001c003401c1c20883c2407605251000714500901420b20440e4010788001d1018038031148081041345c0c0c00300d80c1a000d0a60102040310314110902d01c03140f9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 696806339 1250 696805089 696805103
    0xf0b0d1506050d050a05160608070513170709050108120d021303050307050a110f060a030c140d0e06070905060406031e0216021203030c0a030207050a0b0403051c020a1b 74
    0x482d903551030702070951515105000600010040d8030b4400e00300402c1060782003252280100901000d07400002e61a8007034410310303020b42c0394004215001d850b4200760340071102c60030310f101000400341d10201d812400d40b00050020b100a90369103020036a00d00440c41c2c3c5000440060040fa5885c07401b58008190814019001c1c1e55007036265100d039800c40d03000c02c50403110307907100703104a00070044071001802c00c0c904101c0b900241c401052011510501c10306042c1e0042503502d8440703109031401018001140710410640a0719162320301060001400c0d200008a400c0c070a0800241503144514140d006075540901094281072070031760160040c0881030042c0c20310201c01c940d188030b40c074041e1003d040c0c000d0b2030b10402c0040c0e19241c01481890b10000e003415106420400030446a8284c5004031000201203140044e510202800c100d4108001c079400104105c540d4400c1c40141940f01001d011840c09040603060070a0f80080c00408922411440101140644e4801e8541801e110010450540503444d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 696807589 1250 696806339 696806351
    0xf0605070914061c14041e080304080c01140c04030506010801090c05011103041a0a170403050405010f200303010f14131a0a0906080d0503061507150e01050402040f0b0d15 75
    0x209204c2a1044504080207a02400341040305001c1d1848601070029528844007403180c1e80c0b9255a5480e2000800140000100182d00388200509500004090079900890840c505003100300380c4080d449072100f540c0503c00c01001080d511010310400560300d41c0030500c00f24903480c1c080150b803a0a0b08404010176400103100020796500400d20071406c4101c007006c400d83d660480e28001c0e214030016503d044440c2080410400080c0e045800c0341c0c00c3d00c60134202004002e030301d040116a00c3c40e0140d480e0700100c010110010702c440001000d141a21070001d035103148152228044558050302c0c1c096164400741c120031786456a0600d51003090203584410501c0390f004140d90100e0030481c0319a00401400d581c441080002500511541c401c000842c501a499814210000f601d054080c0c0c0340c090150400051060400c82c2c05091018141020302c2c092016500b9002c60600808080310b050740564140849003c41030700302d1040070102000140034815001a5850f0010b24000c210900955039513242 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 696808839 1250 696807589 696807637
    0x1d060f1b040305070501080a0b09010e0a020f07060c1b03170c0c0a120e1e1036060f022a031603020a080606150f160f060507091406 58
    0xd005101542c05040100821031401000500904009003e0110310340340003480301e030703580d54554001c1c1100c050140104107500c806101030002e20801c41c00307401305200090308070200151a00031111310041a220000303085001c46442c0d480d4110f08200400042c04d007044001240c13100c260701500203d01561150174100c51aa14034034001c1b400c681a954510313641240d00780191312100030030a03202c091b2051140c082c526100c1c84650300c0c5020010740304842040300b0b202c40b64894044039482203004100c0000c00040035060354400c807408503101403c021440340205070726000e21210140c2020320350013041c850001307008030105000c2c0810b01d0300b265801c1c51891401641c0800040d440c60807401048031580e440c61040040640c0030f640b2085441d000349042061030340ea4441002e6030340c6440c0e0f0b0308030740e44d255404841015200d4181c4540c500744024020500307020842c20109502d80c45000e041085858100c0c0c150b5880c4c095200c5d104a103200344072810500c0c03c094010f402c00310b918181900f140305403070b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 696810089 1250 696808839 696808891
    0xf010e062a04030b04060606050f09040b1305160e0f010806040e0a05010c020d0305010f0b0313030c02090c03070e0108010e0105012303181204050603060d050f1507031d060f 76
    0x2e40c0c0705540f411400380c03e11061080c43e03c10180180254200b08d40342c844c5c00c81c06450f007400f034444800d101d03e9850300c03254541c7c2c031201003a001c04014144104820300d401c2440b00445040701c0408000250344e541545010b0401c940401144041611201c1d00740e6250803c0102420381c00122001178014103078900000780f001d0080340065811034001e0100ca21401100904aa80590080c1c01c0000d02c2041003145075aa5011242c0011030400c001d1923241c854101070783c2c080c42c91035001b50071034503103404c0183c105070b41000746019400b650b4a003006c000d204001101d60712428069134000c2d6480400400103036010341c04100300b4511085100d01c0340554992000081e4004a0b0508280c0c007620544524000090007003001c2d0070625050141020b0800c2c001c00c0700e9010040c221030243c3d40140c42002804801c0086850380d90101c0d085885c0700c107502e40c5115200400380c40e0380d030110b03080c54080d036040d021503521000ea07031100c4002050642d540107881c031168400900403a845c41e4140007414480130316 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 696811339 1250 696810089 696810097
    0x14090c09180114062110150e010e01110c1311071208061906080a1404030309020901050411031302060705061518150112150f080f010e062a 61
    0x401c50301c041d0714046207040d040c100c08958510441041080a44c82851a10040c548281103840c4480b0340c2e6500d440b0311320030201c0f5000300b90740590740d05800301e4596100b445007030b40c00c5c0282e8a5400c5442c0d69001980d0a02c108070020815410956520b034071401c01101506016586a2010a89200d06410070b1140e0740718550588003071a1041c8001d50300e540044081d90803550036141d55580f08aa4181e00820380303000d0164608202801d40801c251660940003540750a03507039000360301e05050528002e0002c0880400882c0140030910000030180350620030041081c0780d005d401d80c1345658100818895800c0d409040341d11607420700c0848041034080054034400c0c21800e0741b01000c44202010060b404450f1200d0910500380d43d0f040000c1d48440100c50400c524003802c108c01c0c0d1600054034140a04240c24a461400380304a40025041244646803c2101d01c9c46060311580208894400c0c00c0e260201c9031b80301031b41c1c4140e012440c03034410803034421400940c441d8081a0080744205401c150343c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 696812589 1250 696811339 696811369
    0x130c210905010b0f06030703050c09131d0c030d14040b0301030c17160b1e0f0721020a030c06020408010f090b1501140a050903010c0201141014090c09 66
    0x180ea08142400c1040c244641444260b00311031204000d4880c030005403103440010490303800c060725200801c99450b44282600c0e01c00c500100345805241c5410040c4d8000c2c14414074140c0c009005450308143c80340301080b42d1603040000b9000d040080c032009815100b110f08000c15810a03181040b0001c0c2800c1303d040554040e52042d00620130541c5000c0f0b101110203c41c1c4e10782c3c01d0540104040502c1070500200380812100407142240c0c4408154159441d0040300c80e00d402200600000c8031541d00040310f00920f60507100d44520594020448031504e000a8500001009648840300c400e0110380540700010030f0701d12501000d498030f42c681e542e07079096403803000f000d00700981c45884907000c00c400f22440ca0382c03003140b04501d0a120080700d00020300b200d048582d05109440c00280746560680300e4030440d1400b44016000f801400d81340c0900034000e145900b2441c60700084070001c554240d4039000314400711808400c0d0301e128640d8610810a24000243c2a4080e14404010001c0607403500c0f10f086840603 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 696813839 1250 696812589 696812591
    0x30c0a03031e020301080a0f03020109061d0f030f09040209060d061503060b03060901060f020109051917040e060f1219020418050a08070c03020619140405130c21 71
    0x20914840c4031501da40310b503080c03401070050005008028000403218030407500042d4000075241d1900b0b05030300402c03028102030314841c204440e40300b50b0030020711007080d4490301c00201c50b40e003000c10180d00e480b800f07401d010758501401002003010514060700030303001c0d407200100b0152034914007c281340200c0d11603030f1024440d440340031035a04109070503105000082802d4840d280c6180703801d400081b044e0303e050040c6414030014018041d9018404d42c0318800c5103501104031900011400e5031805505402ca034102d801e42c09501c5142c24640801c2c05031005c4498100009040da100d01c01000f543c1d074205001c1c1c940255010420031042c20f010800710000b2010307114414003188070782c014801510000002c09910025607081000000e000003201c070001c5400002e955110318943c0382c03c4101c0780c000c0d0b001a500c41e802180e00384c20081002228001d8800a403902211710b5544490300b405800740e8071405900ca0185040c600180a00e50440360444481c1d20303002000a9003900840c0264041d80f60f0f4500c11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 696815089 1250 696813839 696813851
    0x6010e03211606061a0a08060409061107030302070b090a0317341d100e031002040b130501030b0f09192309060c091e060d0e0c090907090e030c0a0303 66
    0x1080c80d008190700741201e6150307011b1404042c5000a458484054140d80c00740d0382e10044407003030042ca1341c0200c0c1407000c07240030380707680c0da015080080194024107030a40b40480240003180c29203400049104d8450303810f40314410369600c43c52668040c031000078000b45804903916450001d03101404884c400ba0a11219000c1c03031b801c60078100408170b03618000801811005184012840c1d912020303160031040031850301c6c6d40011030800101e814004480101e50085002040114650000c00054024803440004140005e503880d4011403d50752055041500701c01503840d00c00b66420002c449961081d0a0200415070401842c518000c54115a04c403002d400c0c1c9041035411030688258280e0b0708805d50900074030090900284001052042d02d01c03007845540d02c40d042c612001d80a098000e403a940c01810f1949403420400002c0c0542200c480743c408030b005440002030545442a89180141350f20703001002810305121019000b8008007512498620051101d0340c1070a000f00540c546440c802d42d0080b0b00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 696816339 1250 696815089 696815099
    0x30d0f0e06060a06090515090301020708071712040204021b0615041103190e07210213020a140a0905030703060e011b050703120b0607050c0906010e0321160606 70
    0x80075400351400b489800141000c0046560121604080d80ca04a0364103500e10a0105601d020b88210074203150107500106841c000e11004a01401ca20b90140304100803207034603480040c90901c40c039510419180010400314026090603800303051900c010344a0008070f040528811440d0500c101d800f08240074041c1002e00c0329042a016a910ba1040305e07040508500b010b0312042d0842c00d0345d031000c422142d510055043c90003410440c080082a05e0320080101c03a100820310500e1500c1100160b004840308104144005114800c8030003042207541c0e40a00030390b080c0480c1540d54001072440081041d20b01001c00c20303540900031840154444c1c000042c04c8503040007a03600703440b10301010b0202812009400c0b503c158100c42220a030760361514050790011020482c080041c008a403910790050004100c0904000c8002030070240e9107004c43d00202c41e541e440c40110741c025030901d601c94140e0090a0344807122820341e040c14142410060015040c54200c4400d64941000100140d0300e66860301d004201e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 696817589 1250 696816339 696816343
    0xb04031211032d090102190f1506060221030f281506090605031612020c03090f06040506040918050a0b07080f0628050310060f09020723030d0f0e 64
    0x40c858403092206130600d10b003a40007039201c4034031461f1246220b100480c10f0f010040d01d80216a0301303a90114110040c49489603c100003031066000780c2c40036106412860905403150714010b0001d1504281c01407641d601c0d62800a03040d1000780c40403c00c0f4035103c00c0038030b2001d80c0c4001110b40c0948034000040f072a00c080003040303404065034005414018038403008d10015900c0001c6a600403c0031a9144001500711001c070b681821f200b040300d5095101182c035115a90000c40144007002c422901814100d80c1c000c2003100502c1075103e800c4c0e00030001c1104007e007040c941c010100620941c189a0052960390300c42505240940e90704440318101da000300407206400c10429034010122103400d0740545822b9011603244540721500f406401c1140c4690500700c41603012000281038040c0c00e90701c0890740c1841c044080c090318018103c01d20382c2c43c84081403484440c401e441c0302a42001c44010080c0702e45ca41212111070544101010340410861580f100e161b501684905142d008400240c843e04190b0b941c2c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 696818839 1250 696817589 696817657
    0x50f030c0c040b1c1e0b1549050106060908060106021902012a030801090b060309070621090813061b02040b0d0b090606030607090b0403121103 63
    0x907100741e02134103080c00c094105400f80e0050980c48004614240c2820109100741441d0100060015040b031080041e54001a00034012203502035030445400c0c01c51040c0c442c0100c0c002c01c00c3c520800748003502c4440c1038402210f03c031560900c2d91581d203810320407a1181420f6406030340000000c0f928680c010801c0e40f00411070b060060035076202504158400041c4103040d250000400f80c1000b01c0065441d15030101000c42000d04488400c080d07581c030b202e40c0380c06004000244503480b0742e07a1801e801c1c01494284201140d109a1551024200d00350400f6000da60b0129017440000b0032044c80f480ea5180000e5500c00c2c1d0700d2a03406141440e848040e07401c454120180c1a402210401040e80d40c039507504084e144078013851540c101d80c040b40d5000440003007152803d00c1d030405003100c080c54041c00034108000c1909409110706605442007030b65030313200c00d40c3c07480714504c01e40300c0c0007108010800c00f00341d60b03c44004071441c292078180c0140e81c80c0000c6504d140c00101007900003c00c1150750b201004500b54a40c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 696820089 1250 696818839 696818861
    0x5011e1d121b012a02060708121306050901060b03010320060d0e07050a0b090d0201020f0a03030b030c01020d050f0307020c0a090e0c040528020d05010609060206010e1909050f030c0c04 81
    0x40c203c45604c041016400003400e4400034041c0300081a00006c0140c81020344040b450389000040c9585440c1d080703040c0c448140c40301658141e15107800b00d07413040810301414003032350b81c801451861a4610b96560084000c0d0b10a00e48040c2c5d0207a030034fc0700b180c2e60000140088507041c100800e030180e40c195003030304000d0160712951240200402c00c001403151881030766141030003110b00c0c201c00d13070103400180e051500c00000d040003030248000369020940c041c1d00550340c00d241541100d2020001700016aa910003c0c0b40031408241c0500c86031021001c03441c011039000606105a40001c8815004540e0110044d00010600380d110904181078480070445980481011a4140100e05181c055089c2540c0d000608101d08446103c2200420820350100e0700c84211090040120350f0355200000c2c42c64040b4011301005020384000020f024501031080c1c0d000b00d0380180c0c1c1007864900c007400034004040e0503c0460741402150418040c000301270000d4a00300b0003000107868040b051904000c122a0041c3c02 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 696821339 1250 696820089 696820127
    0x30f0a030906121e0c0908010c09030501050a020c0606120f030301060807081308090f0d020a0b1902010b180613050705220e070c080c0d020705011e1d121b01 69
    0x300103005204ca500c192404155044000341c1103036082c604640708621340d0420007056007080880b4005c1944401442c003140e000b40001c1005403215000d00090740b00301c0703020300d485174402404100c0e0391801010f081940c4001030304030742201e1520f86865017550026448007000c503e41c05c0801204a80002d051980f01055096035241c412050b43c607c05180101c500c02c40c061010030b039050304c4640360f4100c0f44510540040582540b030b84c0ea040103020580c0501c03121050034401c160718000081c014051110010002059000c0041680c40a2440540300070a21540141d003040901c101500764816280038034001d50329659a00780003c10388880a2546c03016400120307900c43d0030081c0710360002d134164024440385040d8000048604012006025050007540580244c05140f00682d0b00043d00342d08640d000e80310050400b43c0300c541d000c0c020703901303503038010104000c8003032248030924240ca01140510010050000724084081043c03401c102910b5466004103020313140552903810480c4006042d00da511 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 696822589 1250 696821339 696821351
    0x411120a090b28020318010519060f030b060f0f040903030507020636031309090b06040603321501050f0a0b04060804240203150a06140306030f0a03090612 68
    0x107021100c0e00ca501c540c0f664942d84c0400865040002c1003082545035007444002d00c844d01780080191034009483c2051030400c3e180c00350016559125070303209000c0300e40242d003c105d190b41b0303e000e02a0b00840c120101d0b46c401920000c120096480f8413840880034000c0e81c0006182c0b60201d4040e28007540030f4525120b24140100103000194204600003c1c0400a400d13411004142e203415403546c003592200d504020030301100070400001075407100e00e220b070040d944842c2e1a12807030144011111107010103015140640c84050905246165401145200608180c0103288281e022414a9041f000101104d4075100040025160504d01554041000c03508103035007500c5c2c036040c0ca080e131249119a405200026000400b8000203040921200e920140907202d12007030f40300301c02d0007507000311004a10700520703020129482c00c5c40007000c002e8680c552038400001d02c40b50003e84094000800456051290704d03d0022407420500428928a2190329907041c2c241c1000c0d0060805480c0040448916283c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 696823839 1250 696822589 696822631
    0x2060307230c190501060b0705100b040b010e060c280c09020f07020d030908060c030f07020106140d02040207050f0304031208070c14011508101404050c0411120a090b 73
    0x1081c1440a5400f080b541c0c2504445841d03d00e015003a95841881d11701c00120382407007484004251490010f241c56020411007100310200002c894607a0021400149440d802082604100d4001c041d000040b208580c803d003961076140d9400e00d40d540d080144400a66002c004102c0c01217081d4003e406140c0702076007440350f40b0041c101d56000b80030000c0d100d405482484028140a0034191000d0700d10a01620681d207040e440c0d8080992003a90b0681c000491070000035021807040c4180d00943e620324000d00701c000519010031800211140c1c05982c4951b081100c2d00000d039003080040c0041c04c2407c06103803a9840c600349081100e0754840f0308010700a07400104080154864291007401e54050000d26034003514000c041d005000d0f07a12040c03e603071145640401d42c3c4d40001000705010b500c2c018280460980040b50405010094500030901c1d8010b4a101909207460b4000130710a0f0a48012a820002040e2209241480507502c00c2c3c1c1043c2d490300820b081c0654400c041d5404485060380c01e081c09142 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 696825089 1250 696823839 696823843
    0x2031c020f0d020306150708040f05090403020714030304270612150c03020909250507230a0209010303080f060402091c03110a03080603070602120f1602060307230c 72
    0x4652031100b9580e001000800741d9565012101800781c18040581c0c50305114904240726900030b01560550040d461030025082c03030940d1103588140d6042e8042d2589c0d07403402c0b121a000103040c80540380d01d030100784400700700440342c507200410714400c8040030019441d1951407803044130002d40002050344c100c522132001041da0204054503011300c41c0d0b0002540e045940301180240101ca10301c60b8403a40d01414092803480415080700107004000e4158210421600140c1d028850000b00030301d504990fa10400e101d80c180340002c400d0072000c10a036403c00000c0d03400500311380c809800c1203000c6000801401007148181c0c1d00c0c00da000800307131001c61400e980312000400c04004407460001244040c0803800815228a0448d04040c0c040021159005041c0c5000341807070307074221103a5000744510200021100c1c0300142151807020805001450a1070300e81415815a00c4601070002d208001d014905c0140c071550f004600c606061b0352450802100c05088282080c3c142010b0b00c83d131501804503030341804c40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 696826339 1250 696825089 696825097
    0x60608120a110c0a0308130608070e0d0503040911040915061409040f1503110603011d04060e030a091403060f060d0f0507060c030248090702031c020f 66
    0x200d042c10240070300c0900303101d46440307810740c0c035142c00ca10003038000410400518054568a603c55078541c2405454100c03c5500020440ea020001504001c19000504181040c802443d01070029649002d03102e400c10344c155100701181210005000408114025040c03040340c1140ca290460003480f00d150100042484081075502d80c00e6210002c5c2d211015030300d07540701c1216030000d000107121b99400021998500b20943c8030550b10406482c4040d0786034540b20085a040e641d400c51181b28441ca504808418650000c104580c410790300d4180c0c11342c020080019100c001102d58400031294280080403c0c40074800e89814080d60248040c0a5034048a40b9095803003501544c0c60944515a41400c0c0c0e000c0091110141c01d900a200000c140c0c50b41c05807c07840070501903000c46540784005101c00f603115160b90840032400c2032080c10030726041104075442a400044019030f4110071407520014129100503142400981e10001e46007070b51902c6240b1710300e0b450b01c0c410f108506280b00b4101d0780b1010b00c9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 696827589 1250 696826339 696826357
    0x12020a0201081602012309160302061204140307050601170a12030f240e130c060311070203011802090a0e0601090e01022515183c06060812 61
    0x40d10941003e500d40b00754841219240d031010242c248801c1800d02c8184020144c956000502900032614900c0030002c2c80c19003100d501a20061a0200e01400c41881c44d5000d03204035014011082000c8800070100080c117103c07070003000507052781d5240180d6140020f41446503801660803403004480810310042d0300005210f003038200802c1503c0803101c003000034101985070848281c1d84c43c0380b50610b0400148100140d40c08414150100e03200c2c40c0321258050124140188800340b0020705228403803194000350550711115240b18188110740d80040d081d10002107c450a110a4040c25025894181da0b05a00901b03a40c00402800c0040d0310400d442d82014080c0220440e02d4104c8405410340c25412603440384022005044200b00440300101545c10302c4d01c054422000042c49501c80440074468180046d40300d51162010b102c0d035a0b50014103070752145207503200c40780300300f000e1791001c01c00d41d040c0c0c6402c5003111400714054458a800d00817200c1d103400458065104404009a0004440841b80414 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 696828839 1250 696827589 696827611
    0x5071106061e060406030506040e1c050d1506030515040501261005090609010f020f040603150f0b0a02011a0f0618100f02060a090201080a02090f030604050a12020a020108 75
    0x302d56029100412522114658100300b0003d400584654198000c41c02200c0072502480100106105035595401c801e00a41c1040044002071105502a2006083c0b0140c28000450a02c030440340e0f01032440c056034441400309403258200200468040c0f00e151204000b100d0030010355042c130008080703400304024481e5142642c00e40211382841c0c10421003881d140d001d032040c0901c0c03402e1069207844800035950304100e9801c0c02038501c12070324240240c40c0781c90b40e030083c0941071a1826904034050f0003810b6030084841c45070039021920080d132845e54405014400701700c50741c030407413040d00074211424034a8401c1d20b1102d801c42d0a4040e920440c41d60a0600b08841d16515402d4006071000190b41540000f540240c08902e00010240c0100806110101d40d800b034418980d5460000000c1c2c80c03200e44001d002410003c0080e0965071a40d020386103002010f0b14044c80780c4d034100c0c04240b030030200f5103043d50390b81c1c0300e20008810444501c880d02c0d00103515102801d02032141e40d0000e403170210049d09101e03c0c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 696830089 1250 696828839 696828859
    0x60a05091b042c0f01020f0a0f03021210050f060403020d0f140d2c030703080f0c01020403080c0c031c0509041806050a050a061a090607170d0507110606 67
    0x1076541d5400680c402005000000010420503d1550245440e1201c0c0005406401c0c150306504c041071082c0c0e060080d5040c0a00d01d0082c92040c1100c552703d400d40400c05040e0700303103d54078200341500710f541d200784014040c1a90b90707400c1c02d0801943c1100d0300784c0300780304010800c02400140c4955004100056000b10f03640106080340c41e10b604c20040c13501c2604d9030741c4510b180a2400ca50b004030301044c40640144202e22001c00318440c5415101860040c54241c1d201e2001000000c104500422003180112603e50a002d0042c40160a980c0540d005481441d4041049030110b80700748441440700504034020702c052076400c200700c46040c0400403a0020300001283d1a0603645464115031030341c0011921294142440b4a007000040405581204c00246800009113185001e40300303039400c0d00c0e003600d0142071101c03143c40c14100d20f41c84150b401303030820010300c184c00001d00040740da509900800419262104500314041049403802001c01007001310305c124054010002151040d04000d0548400c1c070300f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 696831339 1250 696830089 696830143
    0x120c091e0b0c010204060e06121b360301020a0c0b090109060504050a0c05010806010212180307080d0e01090f122a050a1a0a122c060a0509 61
    0x306004591100c680544009480c040540d4190300600075a074154503090070741010202403002e5030064404107446848048085000704640d4403060250040b9008800e180c00b2980c1006026140000030101840c08101742c0000300541180d0900030a010540c006c60504080542c0140b00226050002c2d0a1a0307a400102d5403a6030203421203000150400320501c2181040d26181e943c03140c04c0d0f10107a41052042a010444d0f40c86a072100d402000140e0060528202040003103940e0b03072007081c060040507540c1c1410100d6403001d01103035000307107042000703809203070305101003e820003680750001c81c1000a561014010071280b84c20344d0f030036a6004651011031000390300d810704050004000b44030340010b01c0301c03010140c09014180c8105550060700c451074025a00c100034241c2c1480b40c0401b0b0b000c0c0c5014041113648130301c1090603410304540c41e000403a90050900360100e025440c00f180404007100305101c0307528040c04001079604243c01d54000c01c60f038a03080c00e214bd1200040300308540c83c070600c00601e0711 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 696832589 1250 696831339 696831389
    0xa091814070c030c20010e0f03030f091903050c120c010f140c01050109150e0906070c0f0c0e0f0c07030c0201030203090c0909030a11030a0e0910030501050405010507120c09 76
    0x3101503102e035032400d070440c5d59110720710419081212140001c45003205900c00b130506048840b14503d000d030082d8100703000461b00000340d80140101540dc000e80725401110b207020301c07000c0c00c001c500880c050441241d481d018822180d07034001e0031100750350103c0e1000c0c280340d80c450490384442c000c502d400c021380c4101d440100c10a100d4081100750a6003403000110721160744c0d5010059004040c2015050b8650b940008115000b084468110a400480c00107038424022001d07203401a11130341c0b100112120541da503403642c096039084200078038072200800a5245803850344030f070441160b19440d805c041c07103603070700074401541c2c01002410140c0200200d0b0300c201c0200041d011840b4000c0100c11145440c04c0646e40d65004030300000001400415180c01c0170328080100c0c2c1d0706080c950307a0300c14000401d41c01d0000d04440038115813241c0d8404240040450021322415018505c10000401c1d18100448010540c03000000011800d0b40b600c480c061086400c08942401c403044907540c101c040300044a012 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 696833839 1250 696832589 696832607
    0xa0b0f0f012301050c060702011a0a0f090b030c030613050c12031b0304080d030207060b10050d0510050913022803151d2a13050402030c03030a091814070c03 69
    0x10f101c1b440303214180044150190041c0d0400e0800100014140e40580100140451640304d4840c1017110784901384104002ea030404041c00c8809421031b020456000013080c03402c04102e0310420420410960340e0b08000d0184040040c01c2011100c0f0400d800312240b000351030348900c004030407861140381000e18510707030309005980007000d61105450b0308540640300600a0350050030100c6205103080181046860a81b2200e0400019542d82c2400c20171000743e010000e01003d00030007040260301000037207541d256401d583c480d80b41d4035503450000e8203610500098200302c0c285510300052500d0074200300c2001000310012641c0110b0f4580140c0480440100100509002e0b450203807003420481e0f1328000006000004502245450b6118a01071041041458003c40000e54032110f0301c41c2d28445001d09030010398010b40000e040d143c1041910700000d1856201c0f540800110700e4a039010414100c0b510003e150b000c1407000140803410064641500c2c0c61401003249083c0001d03100700b00d0501d880340d5802c03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 696835089 1250 696833839 696833857
    0x9090f01061d09010501080601181e020d0f060b091e0315040b090a0210120222140d02030d0f0c060e1f0c1e110a0b0f0f01230105 57
    0x8119503911016200b0600000d800780301886060140400c0d07420805101c1c1034120b51492010f00403903400e2189800384000320b80e2212102a8454a80c800c0441e00c004170014110740940c80141d44543c0150702d103041d04c8402020b00015442d010040018a0318107085404241013207030911130039441c3d2081c4c4800c085c0380079840758162080706242c0002c51090101a8080c0340290103409080d9034408030140e40d0608004000d4010114124051016014000c042c0c17085c029150058108850034200c001d9009a99840380b540d001b0900042042c0181d410f1603103242c3c02d055413400000803668011950302d0210390301c100b042001c4000c0a00455202d04840e4155650012040c0105840c01c3c00059581c43c030003d604041407101a44d6408211461082d446586442c0d280c0e0b2214400503580c40c18021070084001060200070048040400d0f02070054030441032144c4c80403900b03420b09800502051030024030f5181114128001445210700b18003004681c0001400701d10700400290004948500940ca10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 696836339 1250 696835089 696835091
    0x160501060e06031501030c030f030e041802090c070c0e13080d02040905070c03121509060306090b130515040515090a1101030c1709151608090a03090509090f01 70
    0x11403000320650080e4041c002c118200c5500003500d5034103100e580801c0c40010300000b040001000010100300c02032903c1e074024140040078a2004000c1400e5808000e4508042441d01c0c681c00c0461902c5041c654214040c800f41504100b21f540d00d0b810340513418080c10712001e41d07042c00210410790111030a020160300080440d00d688000e40b05038040c0d085401411082c9041100041302c40784100003240c00320380c0569440c001e01c0ca0300c008140081100d11072a051030300880e1700100e450f0f103103409250001c500c104000621089030b400d0a030426030021b4068180b10048844200100700b0002e940500206030303204c03640e0a600e82d07113000c2d4648108ad412070320080012104004150501103450f40c80e0364000c1c003084941171013440045044841030200040030501904c0800c4403002d0251b60380350311160b03c1046462808241c21594000c06080ba4076000c41c0e4400c5d80c40c2c5060503800240e240d00301c0001c0c0018031007003000d41c0e0007412106450207254000c030304030000640d0b04030082140306c3ccc4007a11080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 696837589 1250 696836339 696836351
    0x18060e0402041a030f061f2319120203060102030a0503070207180c022b0e01090e040c05011112040b22090507020c01110d0e060f040f030623070302160501 68
    0x3c0c801c0320a400c11120901c410302041c000580c94100b9081c0d115101c20320b5104980c0c044401203060341e040058402c00e011040001e0015128a0841c000a001d1140282c44a03109290780c0e100040c89400180308d0180c2a134010720030300400b642c000064811103442400c240da103139581c4040492800302581c0c480007940c1140c5060201c80c160551007202c0040c00390b4290748402c04c458070402404118051510134240c620542e0001c00c40c403a00000c028018140340a01c0030390b64900c0320311090303d825034003511001c450b40380030421580c0241601c1ca403845400007501c1c00d201d18150311003d6005030311801d100c681c00054002d01e2101e5082c4802a440100200740070341d01d803120a100c0c003c2004031091070240c4a032102c1c21290390301884d4084400280d003001003400c241a08421a41000325121464101d10240b10541c00c010083c00a0405030031401c0c0c90071a01482c505288040d00c27140c40d0481c00c9141c1000c41d0200484849101c9540455141001750361140403505404041001501c0036000d540303005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 696838839 1250 696837589 696837629
    0xe03070e072c040c0201090f1b03051b030114010b030a020901111605031b060d0c05120906040c0506181020010506120610090c020114090a1218060e040204 68
    0xb80101d185881030394100414002004141d00320744104501a240c60070481030f007000522200c1480280c2e100203030344046002c2c0d413540c0d05482e040340e8174000d07101030307108031810806810244920400c0d5024076102c00300b903524202100e2400d00c005800c81c3c082e80d40002d4a101035901403003290b400000d41c078080b5044185601809120196a07000300ea00ca40107500c7d0702e00d00802003405020392140024941450b200320f080c441001040e09415400a000d23040c401c0300f0051480310320651207070704541c02904142c0340901e410303200744040e86c201c2489400140202407030100030003004107550b08151aa100c0851a41005441c00c1c2066085040c01910b1540010089681901f01d18012003040e01c6010801c50a0302c00c5540712141190814040140340340104105034540d000000d03100514000060300780b60000420b06086421075015200358041d40c415010407124003030304604c00d100f525118640248865024012004900c984002c1000210000145035520340c1110b0040060322194505070b0310700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 696840089 1250 696838839 696838907
    0x60b030c1f230a0e091618030c03080301060f0302031005010806030a05100b190b03060603130c06030504020f1f0f02030c030301090507020f061320030106081c0e03070e07 75
    0x20f80040c006480c03c002400035040c010802d07400782200e130300c180d1450320902600711800e0460042d086416029520004081400c2210b00b1020794001ca12003136607907050a2010b4005603041030814105031041003081401c00c600149103042d10340910340714020b038a880c0d00284c80e11012a4010300310380111001204040700c03d602120704650f0650714a10721184104d14034180c08150701c80d8280300d400400c0002e840c0d1918100030765101d81c05c0759240c005503034070341c403060540380143c0c10050101c0e50300c00a000c298a01610006030400040301c01c030805150100713000c1c121060108040090009020b03991800034000d00a503460800c0690031242c50b580d6404079000039144c00da4000c400340c05110a01840c0540c04190705204802032090042000b040f941e0700d00c914203508880b2200d42c1407601c41910240d900303004000c000d120000040c940d0440f00c106505820030303855804030501511102c81c1c0742948003c03580c0e0046034000e814100d4103a0b00e02c0c50544120601ca1005c00680780031808010f01e0441c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 696841339 1250 696840089 696840097
    0x291507050309031c232b02070b04030305010e0610050f07050a1a0c0307081f080a060c20060a0c0203090a030804030b1b162103020403060b030c1f23 65
    0x11950340e111040e40b0003956110500c50044244503210b070100701d41004181c03961144051517013828011104440c02000240423070b0070403441290f00700c4e00401072005240c0d0600071980074002e40e000942c44c508111000418110340c3d040b603941408004211517070388480030400d4030142500242550b000415910340f51800702c0d25141040981000304012030300001080041d28802d68881c0c49480003031300c900440306a003004902d1001ca06d030742d900d40045144c0005204404c5054441c40010844024042000d020703011441e080d0407140100c05882180350b640010136079000540060300084040b43e0007400c80c107501c58810100c0d0441c20100002040025001c024421240602c48100580e00c0c2c55a80e80c000004d2030500c03840542c8140300400401c07403030880e141d00052054200750001100308190701c0d0032240704a2074902107a400704082050245501500411640803006401f60306840f000041c08540492590460040408001580c00e0300450040013410300018404052503001c11842045900c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 696842589 1250 696841339 696841393
    0x11b0c0512070323030a1b140309031c0c080d060902030403120f0204060905060a03091502070c05040902030d1b061a030c0108010e0a02070501020f04080129150705030903 75
    0x4c481803035103401c56112070b0042e980381c2405003c1c500d04008103c04446070f4004901120300351414404000010b0b452034220010300d00958003440d203401e066400c15081c540c50412560070301d0076007140c10201660100c034140003a40d00160058880851a07040001030149822044040f8400001d00c02450f030020300d914141032100405201d451340c200a410168000d0b40308160100304442030900140c43c09501a0890010030301d4009141106600c40c0b0220000300600000140e07800125081440409040b94002d80030039201031120701c000e40e02003580c0e07040580c0980c08111541c10003100004121350400035850700500c2c20301032102c60302100c4140800c2519282e10078403070b840c080c0c0a294040c00380181201c40b100003c0c4140d41c0c5410801001c0c0d40081808c03030381550700b04510090f141d0a24060300150071401c00006035118a008002c0310303103a41e44146040203080c0d00000300599a49100a589008640841501c6810ba49000c2746140608600c2c1075040c00b501120442089440f0040442c0380 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 696843839 1250 696842589 696842603
    0x110d050d0f02190203131e150210090605190911151902011a090f0703180203010501080f0f070f0302040207170a11070b040815070c08040f06170105011b0c05120703 72
    0x70b907880c0300c5050200f07c10750002c0c10000da018020881140020724192032185140140c44a02c03a8460010f01217a54030a02109d075a90384005020361038006620b901c14000c4001020001010345865041580d0703929120700b48181d098051610518020700e0958091040f800740c90148560795a00190280204054848200b0b10104c0319441c80c1c9401d40c1d20501a0035201d03c20703009038a0300300048010f03091014100080c1040c0301d5800d001071301c09104030750081000001410f840200349803a1814494610328080c5581d1002e00144902c100c0801e0640c1101c0e8111401661a0001c0c503012002280039400d00701c04800100c3c80c02030b2103030042d412141044062082da2041c0da110030b041181402079000c0e44825a100c2c10000d01d10760341b10303a00250046a2410640ea1403200c0c0d41e100303032040d4000d80103803018021031041000311b42d8000405850702c188006140d0803540c10400020154010030381c2c6419420402c2c683c20041c0803101c42c00401414006e0314121400661031401c079502e400c1c5120803500d070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 696845089 1250 696843839 696843877
    0x21909050a0605100e01051e041d06093c1f120602090301060509010b0714060601050f0a270e0c070f0f0c0504020d0606110d050d0f02190203 62
    0x105000d0310032002034507001080404d1a1030704200440d4411305800c03082d81070140803c045030803040721210308031207018011400d6641b40c0c02c000c0a1001ca4102400e0382112020640c2405140c1c2c0e114200305602c4280f007019560b5422860308c002684811b000d61017401b102d02d055100321100070441e102403080d03180001304c040c0107003100b40b8291820364511586555203400945500003401343d0300140b0101c2c0000f40040744035901d40000583c43c81007a0320030310780c5507000200c1c5420071400c4854548280207a0000d03195518020001a10512401640220882002455640312801801102e9074807a100846190040803c003454400c60701502408100c1608480002c2e154440803044902241c0c2c42202414a800241d6403070b0701001c401c01b400c83c0d80d10055240412561142c3c80a8003843c20180c03804609149000c0c000b0b8040110052501c0081d00020b20704480a40c020701181c0841902c175900040110301030b83e200000b409010308890381c5003003883c1140040d075400405004145d00d504806020303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 696846339 1250 696845089 696845101
    0x5011706070806010509040605150306090a090308040f06020c060903030109140108071e0803030a140606070209150a0803040e01081608070915240f020c01050304020409020a0302190905 81
    0x628882180d5040000346000e0000b8510b500c14009001e100c90301030000328150b82c1303275000282e071002c80c66440c14041601101300320b00c07031070440c01e025044002d280c1b0802105110f500d008121070b00083c4040d00d001d00d685294801c0250550466024410401c1500d5241c1428850a62258400c4c414040070138100722980c000308180c18501c50489050000500c07009180c1b001c1e040c21b9048103103012080c2c002680c40010300c100141f00961040314851000075801d2120f03614800c0880010f481c60340036003014040d18005894142003a900300110b1545040790030b224100084481010307130400d20707141c000404c0c0015201e000d690307040e050b0342900003511220401480001c040344918403a10141c1c0e030001c0002c00980209501981e1a401c0d000345040300c4c152030300c0c80701b143c11000013100c41e0bc0300e4201c1c03c4807401e01e9001e0960b4030120078502c05407040201c101c0000701603000c00b402c017902c0703150395925a5046503100c0c01c80c00d000b9580075240f030000800c80c40c01800f0300c02c41031007508090390030100042c40b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 696847589 1250 696846339 696846343
    0x2d060405071d0d02040219020303090d1b2402040801051504090b181603110a2c19140a050705030c040611010b0a0b0c07050f060337050117 61
    0x50701000b0b800d0031500310003100080040208803164141d810560800512000c401c40d002200262070350f9070011a83c90410540462800c8820f070380034800c00020243d030a00c402074008080c0603c0d0b410500554802d011004c0300c1007141e50501d1859001ca200040c00030b408038041d046a4031401d000c0711290b08040c041c105220a0b9520454010146e004041c000354440b403e00100b42a50400b4000320351075040c0c0c1c0f61400107001c81d507030003d40b08617076084060b000306d00c0d0a80c0c910016080398001c8071600d507000100c0f012180d4509540550241e10400061040c000c1440000114090344030188240b00303080707098181200c41035900c01c150505085c00901040d005400b100d01036404600698941460981c040b901120b08003010600c9540302c00c41d10800341e41301d1040e68098202c203002d05641e41403090301c03240362000652255001c0c1001940b40c002c20768681e001d40c0e902501c0c05840c042003003c00107242500f903402a128507140400c40540201032074855024906a4101011286c00c0c04e900102c85a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 696848839 1250 696847589 696847607
    0x6080312040b0c1608041502161205030705070909230607030b0d0b16031a0303040b0a02070f080d120e211c0c031803172d06040507 58
    0x148024004100002c140a51a541c81034401584604143c130b40c14420358903100122098446000c049820b003c1e03a542c541000e51502054001003614041e20401610010101c3c0b00d0062007210024009080c08800e204a6072240c2e8032005507210a6141e01c1420000c021600007602c10001d002e000d1080f888a02d103d1000103a81c41000b006291b55980b4120301900203140d0701500040f0b0441c1c58000204a008210b0240002201d05990300711003020080441e280d24590300c1100347c1400e01041503071000f0007201c0c1a1a85451255628020480140d24001d81940255400c0c0320503a0001506c0f500851302e40342060b130300d42d142a400c001d00e203c45020790f4400182c01035140c00c41442085d1005009510381d1001e00c1281107181460f09040b00318581d2140c1e088104c040d15101e030030440d2074903814800c0c45c101c24003408280c2c8280c2d865031001840091031940113400032544001007200040c01454000e45c1a4503991411040150400c103a44049820745d42c4600980c100004100c1d2540124504 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 696850089 1250 696848839 696848857
    0x13180b1503010b09130513050c010c0f08030709080f0a0210050a050d0504031b0602040e1807061b1403180f030c270403020607020d0311040509180102180103060803 72
    0x40ca080d80d0818100d1841a405106101d40c841c1440d0f1250718902524080c0c2841040908002e2511040600308241002e030400525410000f88564420000741c00c42c400b1032450350418081c0b07483c0d66603c00c0581d003025441c0c1011140e4415104d0300d001e01e45000544003d000e100350707a410005e080100040d2814045c4000c407030f0124009009121117076400342d006c01d602500130310749066007141e10001c44000701d424900580c1c845030005428005008542c0710541c101018243c00704800d8a000c01194503000740d4042d000030080c1030941da10a54585101c1e8101190700020150708102580d115582d40e50302403000709150058010702c03a140762a10b40826000500c0c0a0040e00300c1c3c1c5000f070704106006503085070600c0d0450071450100c50520a03950b2807842a8400d80041c122800c01a10280c6040d014000000c00c06083c0320b00e02c10800c3c0e460341078504664050b40c2a480303035213487d180c0b0003529214403d107803450b610100e0903a501d40e11400448040140c2078034200044c9441d40b0900b5102e124101c10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 696851339 1250 696850089 696850129
    0xb06040303120b060d09021807050702061b1212070915030b0102030d1a01080a05190522050304050103060b07050a080306180c07060506010c0b06120313180b 69
    0x8201080c040c074410000803020060020306a140c0f10000380c4a50083d0320700b1040e542c0d45078480801c5090810048150740c1d5190101c3d130851034480c400400354400c192000b0700400c07001c211041006818407503081400302c1c02d403d40780000e0481019501e5a0003014480161071440700c04281490f016095440c01d8484001c02840410200315054000d0f20741540309c68114407003000340152031003440c030804180081c50211a4411440d14000400b030b00d0340030744040485031501d818006502806880380c04c04104109001c940f541e601c03015100300b0071104240c480d0610000003c00100b240100c01017042d50002d032010414140c035420885424003902c90010b00c15801000002c0c0400d02c000090340d0304c110010b086000300f628000004c0e4860806036048800390401140310b80401c1114010580d120800b80b07030020301c5801c50348031060707800c001500b91030013990b4548080482c00001e0086a84200100c0d120503066075446c07241031045400412001007440c6012900d144600d031880c1215098025210 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 696852589 1250 696851339 696851347
    0xa0905040b3303011d010e07080f07090302040905061b040302010c06021308120a09060806090411011b210302041a091c1209090213090504021c240b06 66
    0x551182c0c8956010211021040706010b0060341500709802540649207181000400200e900d140300c14441c1d043c0c01c0b079240c0b06100e1040010301c650003909658485030000620781540c40e16401500d28038199007003e508903091207900003c2c4000015401d015006a169801d40415075064000d0306000394000280010719030721220700414841d4000d41070611804441c0340d0480d645044440c90610780c40b800d040080400b0450740d40c1d0342c1e004514580149000c2c20441c0e002e14040c1d00280e001100203100500c1d005401980030000c1c0d01c60302c4500500d1b007000c100c2c03e11048980c100794090b1386048140414220101d01171521b0701d0701c24003d403021195160100e902d98250304c00781002e40d8110010303054000780341c003030340180d14420200c1c0000034600420088082c400c801c20b00034107052185d001032204034010400e0007500c000581003202211090640001d403500caa100042c010b444139030480c8000c51b9241d1498003408240c0540b034150749404640c0f1168100c0c1d100c641d00c151844003a0182d403008045c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 696853839 1250 696852589 696852619
    0x40b010e090a110412060c090f0501051e031806090a1e08120709081b030d0318120302031e0402090f06120708061b131e0f030303020a0905040b 63
    0x100d03160452030480c408610f80c80710303003000040c2e50000d6010051001da14658031062000da40700383c00c442c00041c82d0108505013040d080c000352480a1040038104040001c242e800100900044444001c032500215500d04104c2000005524a0307002c903030203802080d0208030f1036000081c0301c0b03445a6008040c1c0c2e02c07005d003002c0000c200501400341501c10340d40400c20100443e001000c80340c4109801e4035811002e03030070111a14500041140044d00c010840e180f151115a0009120303902a02140b6011900000c02404034141110303040d00241100741441d0b0740009107400d500507503c1001c055590844203d1001024410003c0a50b004ac1d044030000c0085651040b07181d24866001d20050026513080d40351002007841e09130241d015201c190009410b000c00b5005507541c050100f450340c03103614200f603080c18041d40341c007417140301d190404031002c0c94400030701c11300031a90f40041041c1144029115540e0401901a41c0004000320005d01c0700303200404e15103450b1042070002000079040d1a2040c10f4a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 696855089 1250 696853839 696853849
    0x6050d080705070e090106150c0309030b070509041404020424060815060a0201060e070203130b0a210c03050a1406010f0306050411090307170a11010c0c0b0304050c040b010e 76
    0x1407206580e14000d003040810301814040741d06000e550024000203001d03103461a281c0706800c41c05041810400c412103ea07000c42d81c00b403a82001e0304d81200343c100440d16010f1040c2c40c00e110341d605c1070350040d00304028008217400300f4010a100c0c9000380d03414440a040d0031068521280e00085c2624908149007050050903c00d80d13210340e02178806104401801641000030342590440c10b81c400061303455410902000b8543d103195078201c5018001141000441d000e55456400d15005194603c0030200350050900d1103000003902c0b6280304030400316080d80f180000009855581e024801217420400441c11039020352184100c2c646400f44044103d0b1504001183e0500258000c90101500c070440407510b40d640384a80f440c510171501409680301c2e110020f0500344980d50b17201504540e00709107000e10704080480c6440d01254007000c101c03813110189005031003084030b404028010020b05000802c0340707040070b0001c0d40518090000ca50602080d0420841a100e50580d00f500050420441c42c03540d00706 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 696856339 1250 696855089 696855097
    0xe012f0c15160c0906150e0405151215180f19030f090e09030403021504030c1509030c0905421c051f0902090105060c0f1006060f0306050d08 62
    0x1c43d8090f4210103035100d0500040c1e98841c1c0100d41d0f500c40d90b000d0303002c0b00c98104102052615064030140310524120701070302002c0c070b00d180d2028012580c40d0440c242114061110542070f40e01400031700f84c5030501501000f00480d100400796900c2c030a0318512611400e001440386100c840c84241840c0e80503007960103e42c030698546191080c8980420b021880d04948030786c942c40740940000460300c552443c0100304452404110340c00d2000802c02050000c81d0308000c80500f42c4220404802020080d004100c070955202d5001801c00613800d2004112401c0582046008920002501e04c072000900103c400390000100e00e4a80031401000c070840c00c6540b407103d201598002171040f440751519210140005003103130740464140c0c0113548140f05006545008003081c2e002004204400c0c1d140d9804580cc641c0107014984c445c0001180ca804080010000e0a4403c9440400d0310000d2119210440240060b8011040801e0250410700d4500d88a4072030407040300d1008060300303150240d40c2c03507802e21030748 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 696857589 1250 696856339 696856343
    0x60e010e030d020f1203161b1a250e1306090203040516170705040203041e0b0a060b09010c0f26090414090604030e012f0c1516 56
    0x9510030411040ea4082c0a41840e00c101038000d00304420001c0007940c00d02c020380d010b00d512140180184224a03c0d10200031031080d015040c40340e1100400d45a0503990750b808a002071100e942132440f01041040d9400f40b03030080030382d4491101002c000140c00440400141c0080000882071081044d19203881600b2840302103104a00081030354994840d43c05980c000c44080c0e0f5194040548030521524000d403c8006180005c150f03124078140c540c006440381d040f44640c6105a4021003c5014061224191100080340204840040a00b8030702541e4200088500d0b04400c0d203003140007c0e002e22001e08a1710300300c01c140d682c40b06588895407100300b0b50320f90380c6040c0c0c0d4a0300c100d043e0074038690107124510040403141c220541c84140e0781c07007000282c48815100e442200016001c0c0003a0301c0780024a682c1207541402c2400e0f109140c0c2c1c00407a10391a404503160500c00208540281c0719100f0210f0644042c0440255000510202c1c00d00c0100385c0c2200304c60184910410282d07031071034800f402d1a071b00301e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 696858839 1250 696857589 696857597
    0xb0c070507060c050d0c02130f1b0e1003090305090604090c020c04270501060e010b03040c050409150911040204060f0e030613241109030606150d0b2d180103080301060e01 75
    0x1904100346030844982d009d841901c0c0f69a0b114111088849201040c8020101c1c0307480540f24840c100403d90b58151220440145525000707002d0400d80a40309440104001400c982d840326540c0c102c0b5805400e801d841c140150190381c03081041410180501c81c00080d80260700c8102c00b440c502c801904c0d01201c08190340a541c0c41d00b001c103000c850b840250340200f00203640706e503c81c01c3c01d040c4468807a02c1a48003d200350f00d0b003040703500011220f04010070001c140240c00500b28580d4203280505a680c0c0e100313241d1061000401182650700b02e108011080065038803e071a4803440c42c180740c5c0e40c035800c0c0c03040e07030405521043d40000204031500d10560080769001200030910000c0c12042661400d0807460707000200401c0444031030032f080100541c400c000700d4208040c1c1403000c065000e684246600d21101548800164102da1240030a0840180c44d20f0f04000710031010081418030320700c580390805d1240b8028100340c1d01900348584054181c91300100044e103142d10313100c0151500e84825054034140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 696860089 1250 696858839 696858859
    0x706050c0f01050403080609071d100302071401020d1109060f0c030c060f16300204030f1b060c03120c0c14060f06010201060f05040b0402070b0c070507060c050d0c02 73
    0x78100c00e010b0940503078030a440341541804d15004120380100021b0240d0108007030003990103a141c1c000c030307200308004600783e41c4618072020144089010f441041030151000001c0b01c1580080c050540c0100030100c00960b003000b01c0002d60503900d5003446044000c940c4079100f8800c40001c00030910007400c080c180c5804a91500c06200c3c2420b0a040c070883d0003d8400d0b03200e100300b20790421b0303403200042511b02c01c0c64242e2841d45140100d208100250380100b00f00d0f03040c05030410302e0721359940c1120b01440d000780514000d032003d864102d80105405041071041201c240b0000342181c0680000e0900e1075041e1030318245d0302d40c2d5101050003032110032584020001c0340180e1201240a000d62400c2e01d081032000313030001d440d01c01003410580d4405803007a4110381c500724023001440703810907580050300c4040350082a800c0c0c5800c0020080e0064041c041c1c001403811043c00500e0300200014011644901d081e10f041d61350781c03d001c0c3c924400416014210740c00605040707007518807c60518042904c01000380c60300c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 696861339 1250 696860089 696860113
    0x60e18011e1d160516030f120e0109051506062b0203090d0e0a08031e040f1e050d020109090902040608030d0207020f0d0c0b0307020715030501180605030706050c 71
    0x4038155429030030040541c083c800200166103c4501040e55824007528003c00044000188026074001030b0410244000b10070442e4400c000c0060000c014034000e01c8400b440c4078000d4024030034000708640b00d1048450100d010030191003020306c5190001d000e182800509004005006140f11042d8074810401c401180a2481d070310180d4040c224a000a00c0c04003c15640a0712070602c4044140c031400c002c0400b0401400c00004807140c0a1b40030301804401190004540c4050045402c0462003102099001c1207504028005c148104003c502c1001c030613a8403001d000030306213522400b90000384605020f001000361504002105480580000b580c10354680600d404c54000b00c500e82070560300003808105524003800f00600d100412128080c114119a403030302803070400c0388201088084c01100007041e05000344140c070000c2014005042d140781d150342000f40144000d024200c40e4031800389020186584500c240402d44134064000d03c03141d4108003054450782c120300c1a01c8060310075801d041c14 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 696862589 1250 696861339 696861359
    0x70203041a04030b060a0807090218092805070c0f020303221514070308072313080102160602090402040f1206110a08010306051801020310060e18011e 66
    0x203001d1404600007500d03141580390080e4116009000303c6d200700801d100900c01d6010100b24501100c1902c5801641d40a2a19442941c00c401c0328000d6480305c0864100f200c0c801c00019250b2860340d1440d0170303810540700603940c0b00803a54203a44a4001400321140e0800081c068038040111f540010b0845e0b040c1554543c1e65448140c143c0990209428440d000f0000301003684070b00d814146090405100c65088050720544501866801030100b15414004c98100e6000341d460800c07440000500c1d2040da0110014104141e00100c91040c20007203203040040c1c6001c1c11310a9031444040c045112100210a4031048040d40120782c07220346c0b00b582000b001901070903080414004040340b01c0064503500e201e0a00d036003102c2c00701c603034400b03076560800070072400c04d60052071141503d5000074006030517100d0743d88004009440c20501c480c1e6600c00014800322914032074604040300c107207130780b80c103501f44104080c001c0d4440c229004100800004006008039503000310304840d081e90140da000d52690755404045 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 696863839 1250 696862589 696862619
    0x13080712030c0f020703031b111f0905040903051210080f010b0301140705030f040501062c100b0d0b030a050106030f0605060f1c1104020a1706090f06010807020304 72
    0x4004a961002c400089603049001c44243c9201400076001e07a40c511b4401400c0d0502e210003011416100003000c00421075500d000d094099809810b0f5a1b00b86080c0c4246031007072804075003000108620541c0010340f0314003030040da010790b94166505400c01c080c040d0007411095001e00303215160108030a000c11080c1d41044212240c1c0420000810168909000c0c1800c6a40790a1b14640111f006420004013541100890f50440d010704812182d40d501c90034000e0040034160810440c45840c1500c142d15080c0b0344100c410307034000003980065503840e007056101c511120f40c4a01150000107000c1c0305000e0301158440c090000700601a55029249561450b003107a08682003150100078110600301031101622034a81d00000070703580c48402c640390170300284551482c15452001c007901c0c46941000c0061404159864020162040d91038025004000d451183c0014901c8a07150140d8005520303440e00c684071038001c100c00040600e003911450011100444000d21010640c0f0041000180008001c84d21b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 696865089 1250 696863839 696863873
    0xe06030423030d150b0910030e1902181506090a1205150c040f030f051603080c0c0d02130c050f0406050406080a1e02090f060705010902100c0b130807 66
    0x1841c1d0b1181034019410032951554808184c4d891001014404010b0240480c0c0241900302c41045184071104000c9019090318181006039018103002034a1020340b9842c5016614030894030340c070706030360b26002d02240d00104880014540c1c6c0c16000c402c5490909000404200c540030b010b5201150310f0364244809041d541100f21610303404510074001d42c6002c41c030b001d90002020880f04d450145000480c4003c40da00c4e0202a1040440c5d410030020030104000c0040940a001d0510447e9903880c1000384003900680d2401c08030b400740303a0b000881e914020b024107008030f90041080c0c00c54400901000020031603070115a0500c42e00b04038205913000b481c00600000c0c0390695030b01d90740e1824218024010341020304034003695814241c09a0088070740044100e102c03202650010780b1440014000303207101080c010b5003900100001424020300806401c0031120074003d0740d040180310a0401c0c03c8410300e280710400b0340515000404141c150441c000c850201034010011a41041c9050300c0e051450004a008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 696866339 1250 696865089 696865093
    0x50f1309290f01120b06031e073b0405070e0f03190b0903040317090f011103070b0619090905062d130b01170706080c040b0904110a020d0e100e06030423 67
    0x419100c00100d2140b2030340c0030065107030001d810344810440b041c55030030383c00506810900350190980c001000080b2b5207102040144180001d052401016241c12089010503005d85000c0200d03009a06002403454681d0380030b5003c80a43e00c50f151151141c1c1c08000d44400c031240410000080440d0401c1033a40120070980c0704956224155010490444286000b00341440034000000c02100740200503184038640007e50b4515641da5100015001c507103070000c140102c00e02d0100403801c0307100c0c0c2d4041c00456100d4400c40b1455191030031840b020000103241146500b088240e41034544048100e03294020448020000d0200090350380c498408101340c010704070310045400100b00c881c2007040302c20020095424500464100101d40750a00d03c514044d00f18810400034100c1101e80b00d6600199800348003482d2142c540040c0213000703440d0042d002d031080000308903505540141c600007807001c210109548914288020507824800150002041502d0510110f08054a10240e0016004d400b18181d00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 696867589 1250 696866339 696866371
    0x1205010605180f0a091a04050c030f010f1104030c0b1309050f040b0a0509030412020f060706020c07061110051f0303050d1503020907050f1309290f01120b0603 70
    0xa440d0f10110307000f0800301c0500e00b0f0801c8030000c61303601410340c21140c1081d03100d0704040d43c60f030805038601030b982203699070103218003008440c240c041335100380e1080190300414001001c404150b00418080c0e03000103070095021600030807825850a0041c200a413038000c00c008400ea4a01c0002d00302c1b10129580340c11094400e04000c10045e240441960041c2070304010020b0303040c03071a181a5039008500410150030305020001c81950f40c1d61a10b1034001400030b21191341c859a629040000c3d400001d00148144aa09400700e001303801800c1e481080b69150009104070300000001802814020300290b00006442c501d800700701d16070781c200c10061402511a40c0d80c4941c80c00f4001c0860701c2803e0100f806084e0f0003001c0c801680c0740d605564000348640362141d00d45085915464142c0300e03800c03243c941120000d0b0006501c200c260842e00070100080320b000c001002030500c0905003051101a641e0210041c2182401c41d8011520004a05950b950004805540401090155200b42c2e00d040d402d0f80064 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 696868839 1250 696867589 696867601
    0x318030c150c0a090e0702122a0a0f03050d0207080a0e011b0b0f090c09151c3906021506060a0503011a0d05070c0203071a04120501060518 61
    0x1c0c40c80754010340402d030640c2c40c014000320010701c00d060a0007510418918000440c0c40140b00300051102c000f110800103903540300b00050030128017081d0b08404100c12000507141980c820206144801f00d4124503030021750b020302e50f03044480350f10500d9411038055080c0098808184134501402009542c0e4544081040c0c0500c005481180000542800b981c0b40b0f00010000500780031006401540d171071078500706511003107000c1c0d0508500c1209144c02c007014204010444181901d09800c4080981e2303080400250004030402c0544c0032080902403803010b11001c8078006d94181498903049500ac81980300900a0000d0341852070264080c400507071000245480c2c4007460015a1780020046901a2500c080c0100c05002c90005100c2c44510127544000005006038580440b014038002c00c1c0104850320b05400302400c17041c0c1d900b034140e000c2d12034800042001c60a000c0c4a4915011310b0905504280c50004018040c0d204d40700200c8855485000c00030303103511440c2c0061088850406040c09902d070ac2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 696870089 1250 696868839 696868873
    0x102030a0b030601080d050708040302061c0b010813031805090a060602100204030c0b0d2a031a01020613030201060e0721050c0a08181005060f010903080f0318030c 72
    0x1c030712803090b0082d50040004000005e4541c1d0329041c2410101e460b81c03680e040c070b07980e1401540e00c00703900800c2c000f030110805d01e4203d0f003081d15160040820882c041d401e900446044100300c2c0d0b0b60058003c1801140c01090240e1200f042040e03940184c0080291a9004110f14000694001e00c50584519081c03102075010300903003003003030a03104003107040030300e5500ca40030344501610400c202044d000540c156000c4058005034082d4544801e80d24070518007901d022404003620010500103498880f114000a00f0070b182800d5482050780180425200e5488074000e40c0040b5004a041d590b03550381c0068048040410b45106c1c0510391100741128184400d0204250203030040c8110b4185803c007001030040410090355943c1d040b51a01e070001d590f5601c00d07808032903107107401c11800d4030410750307481e10600f51070308407520500e030a80d0010840e12024005503451049408000c001c0030091011410004101300915800810030140404840a0201385403c40e44000c0340901c02d0b0b002a41480d10041038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 696871339 1250 696870089 696870101
    0x50f030a090e160305100906031a0a200913231b18040b0d060911040605032a0901060c02042a1202040504150e060405060d0303020a090b0c0102030a 65
    0x12100507054502d02440c2c107050001c00a8801d03004c1c56500c03000314964014079a4800040c010010f02042526100d0620410b040d00c0901681c510030207003c001401905280143c411034044502507654074991031003a82c10a0700700440d1542c12070280040a600b10302c03180214401c00011030074884906101440b4102c0d04d07200107042040208000d81c00711010a84941210210000c114100480042803000500a03060301003901e07502518104151007401480c0c2d010b8640d85100d0340d403104042e140181444250783c0307284202603058111072009200040202c040c6015046105410542c00700c030380000070210f20702a00910b001540c0c00441c0e10031403d180c03140041950060446015403802c030f8800f08440301804410004110108003584200095601034401900c0e008000303014450041c00702000b04c2100d03100b0401100301c400082903590920313204e1140210000307040c10380182d019480a4029522085e081400c00601c0da0300014000e8950005d031a42c92695800544c1e20705003951420140c801e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 696872589 1250 696871339 696871349
    0xc0606030307021f02030d09120305060f0a030609080d2c03030f16020f0d0e01090512030a051305040903050c0f0601050a1a040506030a060303120b01140313050f030a09 74
    0x7100304a5600540c0c2c5106034040d0701800c1c05a6500c2c0440c003480200e0640c000c00c4d40203030003203040069650030061132a901c00360b815029a010444ea91700c001c02c1201441750415059045005110140041131071500240b40650044040524003801d00c40c44608466890081940c50307e58070480c44aaa4204100300002e11903407001141035007840e900c04c4d920540e01410b002c40c0707200c2e4000b002903164000d100042c2140300000680d401110081e401426180107070079440c6c0081c405580200340d51030444145006400401d000b14144610301c501901d00713134000341203140924184040010203a60fa4090350b80e12501c40d40c0c41d582c46402081c07000d841c0416411900c081d40d00181d00501c03031502d40418000803a0801a515040704101c0812505548202e03040785400900010070010f0061054004204a0744203640740205ca99040000c0c0342200c00d0540c000303000440c20104c2070000082c180145802c038203c8030300d00318213034001e17501c1c50b14180c20441c0c81101d540001c074001c070130350350400d6a9a0040c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 696873839 1250 696872589 696872593
    0xf07110901120510020c16090519020309061f0b0c03071a0403081603020d140907170c06071a0a09060b010e1c14031b1905032d0409020c060603 63
    0x182e956290b0b030b200c403c1c40449003681a400301c0c8290030314400b00582c0c420400c030428000140ba84032003c52001e040308907005003901c4541c440c180d51001f11882281d100700245009401036403a0300d000108441ca408000f01da0b10700e5009404140c01041d800203001d0701c10042d000b581c4c2c0301182c0c41e01c0500070640400c00c0c801007814600300300103e500040640e61000c126000807601301c22080c02500280125420713420014a4400720f83d802e0044a05018011010001190314035543c45040026803085c0101e0102e140d004080c5c04101c2d404c0800180042500c00c1005400012007180c4100d00100100c1e1440070b610780f180c9050040c81401d00c1000c15020080c60400034403000c64012990100324078101485800c4070300008030130300c115a00144c15844111082d00d03aa140504040c10004406018103113690090a205080076841060005120342c0d01c5000b55003040200106510014110301c4541c000e503d01c2c034848446181443e00500261189010041e11140081a0f03140b81c80b100408a0303000b5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 696875089 1250 696873839 696873869
    0x30708041707050a061d040e0304090b03060f130308060117070201050412030507051c06030503031914040209042303031e01090612021507120504090b010f051903020f07110901 77
    0x1c40d131142c405500c0846c0500e0100031003100740d000c20020101d010141542e400081400b00c0d222400e50880780344d091084040301d0240d00c0d110401320040700252138500c0c41040c04680980001d02139144954084014109030b0700e10390080024800e025801c4034100b0040c0d543c1e008000c01c022280030702117a8000389140810031840e00d1800641b0350310036111102c4040099012006032100280c00030800703140d2200a49499046c00d016696030203803d0103200d1038403801c0400410a5190a02c8130502c03854000b030080115485585030805400000301c05d4100011220400042c640d20803c011401b566805c2c0000303a000d21040112100c5210680100495904108081080c032450051085415404842d4070070303094241811000305228551004009110203a02040b8050300301000c2e100311079504205112030380d4100c00456007485c4244086010400c00e01010b00e80c56441c003441d0a208070750381070040c070340500703900740b0040754008481c211100d000c444d28110f03180c1020b4100a00500760000000c0c19 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 696876339 1250 696875089 696875099
    0xc1e05030f130807030b071101051302010e130e0c0301060608090c1011060403030902150307140307090b070b2502030d0209130905060a051b1803030708041707050a 72
    0x4920880184100c100004181450749540c200218001030030908101d80c00c055403846d010302c0103481115010041080020881d003520702c18000c0340c2c0b0860385410110b4009909500548002840c0ca411940186c000b00000c0000c8011748504108100c01c4c41c000c111060b070600425007900c0c05600100304105200061100e803240000b040300320010304440c1d07a005115095402c03503c010740c4c07121407440e51040c4001e000c2810303055842100220f000340c440c0c000a1441c002580c00611041c1c850000145113420a044101141c01c0915000001d91402152044d03580712040c4071034000810507110b91541100340200e200542c0010506490f0309248441131003090071006e5201d0040c20319034004c5540010f040c0b1801e83c0e80c0c0e980c2d451165024501041824800d0404540e1b41703504940c2c030310209182c1400b05030082110082ca903110036000b801a4900580e424803000040f04101d58950503110912203400011b50500c05070001d40541341070b2204094644090b1450301c02d2a42c01240250000402806 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 696877589 1250 696876339 696876343
    0x203010b031506100203191d0a050904060e030d06091506030506060409020703031d03120a11180a080a0b0703230c090a0812130b2a16060c1e05 63
    0x10380b0401c1110b460b40f1388450520f00b6420751003007002038003101000c01d80c03182490350003400c02c20016212002c40108007066505008016046020f1640d020401000040c00a0102e8004801224545042d241011a4681da88003501c109400c2071100648031080300a4068540354400c0043c4018602030002d401d142d004071303215115038081c801c80d0320f8001131182c051500075080003c58880c908415619407503800c50350341c0c403508100c1c06100c09070720704404540c0c104818098854041e40210800740b409581401868140301c0317003140345400080846000505040901402c0b020301c1c011003c0300005d1804010060842d060100102280e891441940d00d92003100000e065201241c2001203685071040320000d5000e048603405005c452140700100b4207007540722005030002086d01c010b0300340d9440d150956100c10707001d0340036001c0300b0301412119a03250041080010800c04450f405a0711014481c41c2c0c400105276244d00040c0114803c14819420403000024041035100d03070021544000c2c10540d1515 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 696878839 1250 696877589 696877591
    0x6010801060c06090c030f03030c0f050409180c090b0910030510020306181f0f1d04020a030f0501051603050f0612190b06041d0a060203070e0d0f0203010b0315 70
    0x18200051000c0b03100030480140d100c0d200d0150840d61085e84943e0301e182000e4014041881240007074207254000d0031843c09038881440e0000b840d00c42d182460f0411441000428540820710420340f001d044050214001010300e03c06007503042c0f030109600c0449010b0050110020f850004003002c070620800119001041308100580a20009a600c0d00c82d036001078092201008404603c02d41c44003800014660103540b1510818031411100f1016541d119803122407040e03110f01840d10014171002d2290381c001041155201d8801404003403c80e449840e105aa200c040c03500b19141d039590400e03c450602d11202d07000c1c4090b10303480c00303010f14600307091440b94100340a0880340c01400c002c40c1c000c1d2079000600c00700c1a15010401d1100f402003103030415030400c0d40140c500030f026078a000100340081c445403913013040b4807000b44000c040b002e0640e40e5510095100500c03c0d410000683c5078440151b0b50b8003101040d580c011010320300d2130903150042500b11660f101489229034455503c94039105141e46d551 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 696880089 1250 696878839 696878849
    0x1403070906030906061805040618030c08030406021c0c091202180903160804051005131401030216050d0e09130f020301090c26070e1f15121406010801 66
    0x4203903000e079890140085d000e0380c0c10444240c0011810241e1844465100c14400c5003d260180400b00c0c804c205c417012020f0800000e0009042c5017103000214410300f00450300076210f1000146006034070054214100140311007490569103a80d50820140d0b44005110060411107580408044d0300f40d0005401006010303000d00d603c1d42003c0080c40091081c420f4444446101042c00c0e61101316141c0b4242036401401303000c2c49020901e010312401c6120300c09a840741003040410040c644e090803045400c0c40102c0104504040e000c210540351201c1c0100c00c40c1949102d13100600c2c80201006000c1c0107007035002c0a041c040d541803401c0002813052412021a0076070003221000c110b1aa90003c47e001d0620342e803000c1e054070750302c01c0e000424a1910300c101840c048442640d11f2440702d1036900c1515200b20780700e41100c4000110105540052903c008009146440303144000155191010650190070701210070101d03c0c80c050900b4190100d0060074000441841e82501d945481070018060f00d03c10f00036 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 696881339 1250 696880089 696880091
    0x90105040b011206090204050301140609061e1c03170601020c040c030609020301121401050907091a130614010306080a0605130b0c1c05040c031b24140307090603 71
    0x80c081c1640a00c48940d03001240c0302080c840941c070380031080c000c0e60280c440e5500039840c00a0300c60620900c40320050007660b000b4402d11558444104100e83c0340501922100c4904034104a0031050f6a5110b400044c07a02407110f8041c2d01c00c0b50305003d40340400001c010490aa0314104014690f1f0340403904014440707040b074002820700f100d00000c80080c89075401070b900e202d10000c00030820807a203085c4030301824415103010445030000e00f05c1500361082614070300104e6100e42d205124203d581e811010088940d800001910921000001c2148000c410b00e82c80881c0e44201c14030085a181d41c030803c1080c401c2c2400e101d06494210003030b40d511038555020b4a4960303100013043c0b180303103880e070460001038100700c10300e1040c00c01040d0100c095000046004c0840c00090106c0e40d0800c640c002c052186400c046020051441c5440364007121201032101d900b41c0c200e901c40410542031420303500400c400c03100e00109590121240162201d001201e01188496041c410085003030380c4102800c065407040c2c40c2c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 696882589 1250 696881339 696881351
    0xe04140906041205040e090102070519080f1c0f06080c0f0916140f03090601050901240509030706170105090115030b030a0c180f060602030703110f010e0f070b0909010504 75
    0x11039445c0125088000c1040d044400d02141c0171054001d86003980c0104260f030340b09290302060401748903c501d8021701c0c2d01018482081c4038070f05403003d800552041004403200c00100304481c022100c50901c81561259203030400c4c04041e404000c00552214181c441403c0c0a645e040003800d00c540060140d40d916030310210100240b0312400c0070301c00030503000038020f403a00d40c005840c00e00750f0811034901140e40301d4800006400d242c07607500d09048684121600d00701c9408011104c11002c01201e000081c09002c001c0c0340082d0300e0410481e402880d20b0b690b080100b07035201c2a031050110040e40032512400390300c3d0040c0580c1c2c1441c7d0014900b0b40c1141000034808450702d010070704000e9039800181c00c0f46a1140001624210185000c41300d0303000c1d83d010024035106908020441b5202e0269a0060384203000310000a4001e80600c2c0c0c08801c1001100c0c0000c209500c040c1c01c0d6140c407000c00c40141c0001082201c09501040407a010380120301c541424144100041900040b0500ca901c2c4240d403655 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 696883839 1250 696882589 696882623
    0xe0c0906040603140a0506091c0507020d1515151b0c05030d030203090d030603080922050114011e0807121b02070602070905012105030c07060e0414090604 68
    0x15215034011135100e00914a115a180006511008120b170b0503a110301481c0009102d000f40807580a15012160821070050031a04008a40780c2c3c101e042c040303030803c01502450021600501e4505c81506400a0124079442820365600303190b0f586074040c500d99200c01540b84140c582250b9405d410721060000c0070310802c3c00d401c1031401110036078020f60301400703899a803200d21541358000350305c6034200c034089031075401c40313140c08804403003061101402150003401000303072900d007a00e2a400c0c28980b051040c07414442c10203090702203c5007a80500e0603a060401502d0035540c0002e00498500e951409040e03004410480180c0f50707040080010080041800450030850601d034818044409141c0c400308010381c0c1404040d6440c1d0003801920058070401c500014004441d0280c24141c6c2e00441110314220a01e05900141210b050000c9a40740409d01000800d8002005030400a29555544010306a010300c280b0084400e00c000c0002c2c20080c4800b00a28101c0015501e60484e40c031100e0882510002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 696885089 1250 696883839 696883841
    0x70609050d1223030601030c050715020a0309211407080d09140f07051207031109040305090312030402210303180726060c0406021009080405040c120f0e0c090604 71
    0x7000c003403103142901c000005880f031200014611841081c0c904000c81c107030f0403605039154003458000800b0a144a075075402591480d40290080c2642130402190038002c0d50f59403041202002d0101e00081001d5058070b01c0554080141185031045051040c07034490341d510303035841911070f60000f411025220081c40341080030030130040407070402c0c007002d4034400841d00303001548800203481500d1040300c030251a6860000042504011a503011601410424044040c0198800020710a40511509000b60019a03c0030300880b078002c988014019030741c0c0340c513104001d142c9510105031090200796484070092443e0000031603801041d4125040007005042d10300300c1c42c00c1295006200c00103035100c140b6000400c3c12460300101c0c09140140c80340c6030b40342c2c61410f042d0f009601c2450010fa20413841c0740400c88035030b48030070315050040054610702500d40020800ba903031174000c2c0c40c2c002095030100a8540d50780340302c0c01c86d400201c200300788181b032180c4503042e503900441f6441e41d1145c2c0e45203010801725652 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 696886339 1250 696885089 696885107
    0xa1a040513020703200307030327230336041d06180a02010f090b0a09060f020708060a0b03030c10050f07230c010f091202070609050d12 60
    0x41241e55044180500c54000e5005030f40220301007840464820004113807103444010140403500210b05201305524100c000d4004845c0d2907a004055040b903080c0c004501110000341802420b0005090034011b404801031102a01c500c0f481e60410305c018405100c08403401190442100902c8080d1903000e158021440c12103642c03554802d01c3d00b04659002da41c40508280080c0e0281c081d52400c0e543c50000c0076140003420b100004503040035480100540c061a14100302d001e083c40c150802584a004802a95125042c10400b185d0fa15008101b4150301260390006212144040d00d041442c2c9900180da40a0280100f6190303520f0f400250400c0d2401c20039034515031401d0081350000e0404a120400030503041c0c0340b00c558608007400040c15640200002002c4110b891398a04250f0040204d3f190190000394013500b040d501d1380396001e104290790207000513440c01544140030760101607201034130740340c8503038070803428441192407c00065448150040c08039030404c000a241c0c0416000446449107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 696887589 1250 696886339 696886349
    0x221030904090b060f0607050c060c0f0d031b021f050703090f0606170d0e0103020d0b0405100f09060602070909061103010f0f060e0306061002120f071703060a1a04 72
    0x8581030050050184292a0f98041c03041a100c9002c05010711082c803a0600c54441c0140250748029041e40d66814508014400ca001e03100aa8103425065551181040e1000710607a001913102d250b640c4001c10201058150144030380014a01d010102c50600303070b0b1a0900c0b80f0030030640c0d99000010390aa029401521903035502c90b000119514042c54408000c12860046c1072102d0041e5030000850800000d0311201c00101c0e40340d0f1080c5440c100c0c0110042c1d80450b210101c0c4035115018800162124081c0f2801200000c1446000d1030a00040e400a501580c0c070015650b400c00804206064010800c0070644070b00400108801145082c04405044140c22503064410008000600710320101190030a0394241141c10b040240c1e200c808445002000d5110755042e0030007004500c071490900d0018455130460300607102801c2140d0b1604005401c505001c8014180008561007003290300c07051012105190400c850440c10f000000c10118800c600440c1c10700e403401c07419111f50305400301c02c0d200105 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 696888839 1250 696887589 696887591
    0xc020d020303040b0f0322020105072d0501021206040507090521070b03041406010b0d0e0a06050c0c0f0106060e010c060b0913022d1903080c010509190221030904 71
    0x10442d003d0716450303a40111f8154aa00c01c07034044445c440b100448400703140381d405a480508000d0a500c8040758074501c80040008400c1c0021044491900c6100c0743c240c640c09a000142c5894118445100f0301100030001403003a0301c2d080c10000b2281c0c12254a0041e1107080e01d60b9003104e001c40710818120502941c1400759031181800000d150748910300158403c900c05c10340744000b18003a41d030329980c50400317000d414108802482180300070101a408548030301d405008481110000791900011180c0a031b50300d4025003000119620807100c1046940250000c8078001c0040c41d18081d8001c00e41f6540d022860b0400a55031110014410680c115210000d801003840c022130400890b144403095800c5000c034040c85c0a10b0505d082c56011404800b00c0c0320034500d1240ba103041c4a410044e4031281c07010308446a00b0040c0000c00441c0485018144000c1040000941810032025451a10b40d407048030f00c0100d00040f80d00b80040e01c80c950400c210345007080504500d25652520075065000d003041443d006 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 696890089 1250 696888839 696888847
    0x2c2d0604090e120f04050607030c020d0b0105181e0619180509190201030f02120c030114060406021f091a0403090503120405100201140c040906050405070c020d020303040b 75
    0xd084a9480030301c420b50031104070303074142020300c210b002640074001e9102109003041c4010407403800c2100061120310300c07900d090300320368042e03038002034802944440c183c444544a50040c000c60805004816004800c03035034034000761502140c0358a00742c0c00c40750f41c55100000d01001c209036886585100014a03400703841d81c440c0907100c99210440b902c200c0800070315a410300001c510040d04c0822038082c9c00046451902c0d00800302d070015006002411440034213141d081100444c400c0c40860142c4c0a54992000e81d070ba40c0d45811107c81e0942d5541c0c01e42403003610100302c1017120301d4000410f40242514a90b00d04908041806100001e0100c11009080810743c502aa80305c0c240b01c0040d40e2185110b1303206c144071181c54105240d0b84c0d050190741804400c00130072081c04145000240a511542c480c07001051400c051b0b000400740340410b40c0c00e80b0507204049014440700c450340c02000003825065074100140e140000000344036905132200a401205032074103000954034140b045602400300340c98040d5403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 696891339 1250 696890089 696890099
    0x1303030207140607020c0f0913150e010203010302030c0301050f1315020313060c0e22020910092306030402040c1103210108160e0702011b2c2d0604 65
    0x440c401104c1501c01409105480c0c0769514207801c0103682d040000d0300300301c40e5a039400c581c0c40c5148081c9070240c1d026038442c0400320740301489000d8811a03006180003d07880c1c2d455071050510b0001c85c1e00e5284c5c0b10341d040000700300e158020913451540c00040700280405103a00b43c1040c0c0410140d40c8000b448242c000020072001c10444000131600a1089030108004404098210380000b40c00403810b1740302000a40041100c0402050030000c81d00c0317840d00501e04015040021300300c004000d151008196466400c0040450340b2040e072490b12a021031000a001440000070b86a00c001040244035554407013040c40752910035a80c40c0f072840032a4089a564403c40c03110a400c85132202d00542204088200104101c48085400d40741085107400b4030f0247c40c10728686420a0301c0080c02401159038824540a01c0d031024501c110401000303494030b000d14000d0708200041011141c00c1091584151600e004694445411507035440c80c5002e510404042c0c90b40b2200700004024107403980c03104001c00c1c0454 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 696892589 1250 696891339 696891343
    0x300d0c05090f09090613020a09060e010e1f2c01060e150705060a020919060302031501030203191107142409060a05060d2a0503070b03130303020714 65
    0x4070211040702d480801c4102032041002181044a10100345e4000ca00402c9401544400031401e10348010f041c201035070317169488841111082d9009440c21140c280040045201d0155499000401c0310504039560070a060800042c0d040c1d841000414011726121494411700010703010706e0601c22003400c2c0c0c0c003542c1d42c8500410501070380406900c90303050010040c41c94070080c8203c07036600b40e119000c3c02c401c1d61000c2c1c01c1002900411102c9800c014032075038155504a1042c0c2d09000751444e40c0380107841c0c0c100b039214684281c80c004480b41c1418410018460820107114010340e0b01c10b25028081405071302c4038031222481c010303044000d004c0d00312012a08415503001c0f039400c071524032903115601c2800c50811210044042910481590382018002c03461a40854014960010020b080f403808030a940d40c880c42803820582d0526080760400c4903500c0c3c140320380000040103100c101c000702842c90402300444003d12000e8015141c040801010000b0580290155018a5044201c04060003500c071385480d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 696893839 1250 696892589 696892597
    0x2040801022805070f08280215100513090302010e07030c090c020a03050421020904060506030c060307020318030c19080106050616022710080609300d0c05 68
    0xb000c041e100c458862009201e41d0507a502d5a80004051110301c0254030f4550055002e11005c040c1130a01e142d03015105641600c80d00f141841d603500800418220b1001e284a403d0050f03c42e008145460404001641e43d00759280400001c2c0b5000040c00380c030625060f8010921125038501c5401007203400418001d0544200003240c1c03181c0d0003404401d01e981412030300c4410420f00100400c801380014000391449080100e1140c582840c0c50420800680000c0c050507821078080760500c0e11002006518241488079803d80c1c1c00030b80c0c00b0f90039400c1048001c1c2d1680550a15141aa2052802412103a0742000580341038000036056609070001c044600307170781422038002d9202540c00c0003c0001c46050070b0003215181e644c10200c0040011042d420400b007030598400036010320380d04404012601d65085149402400890f0151a00601d84519117040170340040640e0303c150011300080d40d12071320304903150a41503403213881c07403000000da441780c0c4e80035000c0e81481c03030111440c217012104483e030098024 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 696895089 1250 696893839 696893887
    0x9020a05181207081f1b1b0203070f080c0a03051e010902060d0225050d03020307020a0b090705040e1903142709241003021204060204170706090302060d0204080102 72
    0x2080d5206040c90785d41c010f8504c07501d244a560120310388500c030010300c511a40f24640e24040b038001515038003900040d1801110b41c002095120300002d040060040402000b215004140ca00e81d080c20b1560b21103a8031640e550740089c910400340744000400000a610080b04503078020300140e150090399090030025040354080d241e401c1c1001540200002d0032402601c0d07000e50000051031032142528003140a90005040c840640c030406040c00c00207411012030610800101001b010f8282c94001007000b0b64071981506015604402002c03600f25210f40030314880b480e010300308001c500e200410801d00324455040165103000060707103009019450303182e50342640c4d038088654280365200c3e8145070f1000c0284400190a8000b00c8000c21580c1c2442d800d0110018668103006040c0340703101118034581501102c1c100d81003640040c0c28010301c400509034400d07480300758006001c00c500f007610141c2000201d0102900c10341c004640d002c0d0360b1342c2540441d0041d0003440000c2d0b442d00b8036504000300c851054490 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 696896339 1250 696895089 696895123
    0x20d0b0a0512061f0905280c0903290f010509010608092a0a030516060305010e0f04080d090f050d02030f0a03020705010b04060315050109020a0518120708 68
    0x2a0616110008800c400c074601c0180c90f8a455507105001a507006407090034100801003000038811202e48036003807141c1443d030310915a110141b03a0140c6030300c1481c0c0145170250703e8004d44900182e8002d00403002d80382e01c041403c6114011641c183c030b81d032070000a0040800d1148040120742408940c0d070034101c0e54162488156030340c0344c0e0b20603654400f04803054200342d400a5a41c00500110b06894103800305000451403600d0b40040115801c4241c6800a44403030b40701c404c02c03810740800000050002c00081c501002154181074840d440142d014040352066500000070a090101c50012a03001086060701001440480c0c901138400d4401c1c1d04d82919207000e10042003607600d0000c0200ca1440f90010036051400e030103203006034004d4100c5401581d8a640c1d13205000025107544c4104006180542c03c8a009040c00c4d81c403080c16203205820503440140188969400280c00c1400c0d6140303603601d261490070698420001c80e11a01d180840070802e8441c403200010503900100c0c585040c0082040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 696897589 1250 696896339 696896359
    0x9080d0801050d0b04030e100203041409090c0d051617010b1906031d010903020312010f08060601080c07061d0d09030507050f0324061002010c0806190306020d0b 71
    0x990380200244507094004504122035000201900304144d130281c401c0c20b01c2d4501c40c0d4503034003141119441c02c150f440940c1c400a028810b8014958098030240c44c00c5030440d08074680140800e840c1c114044095000b40d01c00c4520500f0094284068107044a003444001d140558802c494407400204240d4803d181d40303400c900c00014208194202d80031403000700142c2304680342031400c038000c04210b09444e1926082c0e40c01903082d00710a0040e540418043d90042d607c488a1a813000034404060303012050414441004014000c00400d03582e62081007400e000d80543e40e01000c07190f2030701c0b031800010181031504c03019481c1c800c032004180921006d61070407030742d80d1110b0321425900d00209010140072503000620400c142d00d401c040f0040d070380e00b001c1e0035100c4110369001b85940034440e82941c44c10b40b1000030b003000704504007070f40f50f010f140701c1910090001803803001001d81500c501401d842d00605040c18000100e01e80307c4800e03070095500c02001c650f902416101440200a201e030420305c20300c10b2070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 696898839 1250 696897589 696897613
    0xe0c07060606022a030f1b010801060c050d030c031e15050a0b03012610090506130b0a0c0302040b0c03040f050301060e0c0a0207051c02280302010e060c010207030908 73
    0x1284140510a4200c05808241c00c102d50f9404050742d48070203505114041244602c00801c0c4580c00640b208000c1c25298101d01f10000f50030107205030064010024244450f0340030810005202502d0000e508000551000754a8203c0141110300401b0a800c9407030f2041c1451030f505a80302040000320160910340e26a00c840402c06181507600c14041050020320040c031401d100088112102c05d41d40001450f400c2c1d03000c06590514510b0036807110516610403203c0f00f80711041c040e10390720030780159402540d42c2c4290f0b24002d115401902c00c5400d01e64130011441524041d074111800f5225814946440d03100d11000641e407607000b401042ea030a5191100058941014058a005e5070150038040c000c580d80c105460700550805001344085200d41040000c454030b032070710b0468260013104015401402d040c01800038481417143c06550317000c00d0f4100d2407108103000c210710080d2942441d10886420111002135042d010700030680c82c4551000405030101500609068100c030210000d444211500c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 696900089 1250 696898839 696898843
    0xa08090c190303140412050327013006090f1802030607050f16060f1a030d120f051515070f110d0c080f0c09090c09100e0c0706060602 59
    0x11804081900c07004036080c00000c0c004c0c080e12400c1c1c0000a1080d04003541c1c2d54242c00180440e0b0800e95180d00300045007080400700d04288290b83d0729103c0320048000d905400286030800c1d400e20014054684514243c0054103412850781400c0000000d2210741d858401c118018108500c00403083c0d450441402d2504a105104802c40303500100580748995842d00141d90070780c401c4070302004c2a9000c2014604040059084004041c0200400030b4407c207094030390b10449040c02420010002c3e219541070590382c0000d004802c250181c500121004d03240c1403400e000e41050b00102e000c1506001c200918881c00c5d401071212484200c4035501d41c045803e0814600d40310785500501075002d04140314010a80803600441c0e078060140051f010140580c980d0541c064094000c0510f64000080c5050060801c00005069850480310300c0f10b9410310010950384d07120349001c00307809008420b00044d407401c55a500e07103000b0b15890320413450742d00d0108024030171944a510100d0b851464444007044007440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 696901339 1250 696900089 696900109
    0x7140a23060609011401110115090c030510140f120f060106170703020a110604030c030801210212010204030c0f061404060f2109030c05010b150703030e0a080a08090c 73
    0x90f0940300c01d0390034008040c03003841c211403800e81030003128403002c0900c40007482095400051281c1010b549420300d40050151095481014205410b00c8244000c00d07404c00c1c01d0380110340a120710558a0840340011803100e00c4074550b4a07138400c0100c450380b0802200403a400c81070000b61801e0790321507a255001500c0d40400024041125a0700b0400281481c0c003d80c002c1160384150b080c04400207445552140c54100f04941c21000100540c0d09013040580101c1170a0250481003051402c2c004050800c034071040e8112400380c45500c401e000c101121600b90304440103103800c600c007801000c0e19550040001e040c60301c0b5103030018400500b185c1c0b0a081d407105480039520550b40f2210004642041150000f042c48051200a60345810050900129106401d000c510a84500a6400007800c1182c00c42e80d040b80500d0060044015140040e82e03004200c841301985030800140c40580c031002c851a18200e08001002c070803002460203006078101120500c1015682d0840308815601400d1000040c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 696902589 1250 696901339 696901351
    0x1d030c06010924030302100f0605060f030a020f031e06030105070f210510060207150507021903080307050909090a052e020301030606080f030a080a0207140a2306 71
    0x2100140804856a0010050a480b0b080f00c1e600d03200d16080065440501940110090b9112514200c000a52070107454624240000208947c0c6d14000220300d9512031840304201c450400400600c000d071a80d1305441600303c0841115480b0f01e403442002010510702e4940074810419100050214a01400366512600d256624008884105a01a00e031440440d4001451007240074000840f5101032142ca40310b51916941b082c0b919140010107410b211580e0083d0084000e12a450f5a1507500318048a4500b68140c0c4c600304125412207060031540700711341006188840000c01d2040c2d4580c888042c003a25481240c5122894464204e001e6a5a500c0d0300c00400710703048001d030455001001c00f030f06c1c8010380101c06502c85091100c41520100e0303009030011500c40e40d031090280003011080040c8050310a95200962a0072050000644508401440c41d40e03980d0b00018102c08111440f110007161000060403110711100318a0481e00000b40401c0d4000e5000085580c00341c0480c0c00528140209 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 696903839 1250 696902589 696902593
    0x180909060504052a040b131506110f0d110709060806010303110a020f040f02042105150121030c021e030f0d1b0f08030403110114010311311d030c 64
    0x13440d9414400070b0601c0c03940255004001c5c00c021890000c2c68014103c0e14000001244032050801c2000342c04008444021440d0798041003076640080000260992030441500340b00b04185440c070401882d0030714a401c554003080c200100002c00120008526068a10070b80f6078200a07020884078a543e10f141b0540650310151038003a07905a030401e50b00c0300084a0382120003618058a8026000d00368600000400e080c0310720b100d413003060000512050141c840080c24078550740d454501176a198605004020888228100c00c0e04c04043c021009013503516030203000418020420b05c056a0321800c07940801c3d02030300400d500130340c0f695004030f500c44540740b060300d0700b4541301a4000d80c092001a50423044480300700c00c0403180089040b15010b58491442551502030119400b11241d0a40f4a030303031402c0038103040c0a001070002545041c83e40446070410307201c6402804c1911180d8491421048560070600321644031a15040080c0d080921403051703207036a00c94010741c0040c400340e4030720a0a144440035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 696905089 1250 696903839 696903913
    0x5030d110a0308060a1706091b0306150409200a0e0702070e090309040e0f010c0216060c03030b06040f0501021c090b030415021908060a1518090906050405 68
    0x1038064411940c220760090419505c013a154407003134000990764141b10b09a80d1100c0c08000c07950700100000300480301c0b4001840d0340185a03d021984d00d43e4050036000c104034100100c1100340d2125404040c00031b801c0b070020040401c0601e04414401ea01c0e450441c0219410007001c0b5000e003064440030b000785201e90062080c5450f140c80d20850401c0900381000d42d0004101c0440b0650319802900340300301c204405001c00c900b02c00101421070b10319081c010b0640d0811203240040c40c0d560600c010403a202410f1005140203030b0300c1c1c124014109042c2540d4801000305000c80e849028640103c143c900070380071680189180100703c0e003a112041c2c4411300040039500140200c4110300059501301e403181e000d80c104c2908541d1240c0c10783e08501550400102c40e04d4446a0300c9070303c40c01c05904034505036650036089050421500d0f66010002e28403061000a8480e10540c0340c1c0ea41440c40208100b06080044480c2807409034040e2000355420740b01e5110f1550013629000401c400d12440284030841800700d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 696906339 1250 696905089 696905093
    0x8060f0a03050c040903050705011109120109031202220803090a0f080a0f021c0807021c030f2f061506040b09010806010c021305040303050c120402120f0703030905030d110a 76
    0xa015017817812020088280074250000b0424040c1481640761160026101c0c000e0307005002c0211780f04200d041c22031303060040d41e0000c00c3c0c00408500040303514440160380c45c034803441410340142000082c02c1c140301c800c2c41c0008101c003000c0046d10300100100e8461103d03664480c0e01c003190140d40c1c007640c2c0c199009040004001420701d030940407658030180034030a030b91150803a91080298404000e8404e01000906041181b82140090314520040365200e000c0c03100d6518014401e05080c120501400800443c0ba902a90100c1d000304201c10001001006004484103264031128240c0700d0790000c4c00d041078040c0301880c14000b81c130103840c1c504840c0d40c144903003600119404103000d018281884035512a010258880b20751811300c1c05d0f50316070082558201881c009044460081110302d0108081c8018403540214190494000743c040300e54440b05241c155000342050300d50b548800d5140705030b540000c1010b4020082404a400803003d68a0214101409403620005501040c001c2d400144103640 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 696907589 1250 696906339 696906341
    0x3020c060a02150c03060102010f020f03180102090409050309040e011817042c070f141b03160605010b030705030412020a02040e030405040f0605060912010b09040308060f0a03050c04 80
    0x4260203140c4103c0c1c040020140e109407550300c06480c1a0040b120000412209580900a1098810198904600d845680160711000d400040c0072099011007100c01400c4107042501911602140100200315002541c90210380e65404680740f280540d0a014030342d011000c06201e0070b170039410003680d40d9100c5039056880c0300321080401c0c40c4140d0103009010228921221010004121b94446120219590444064105054000d203403008124004001407e256400b041c111000300340c3c0b0100d10740b140301c44d080c0b02c981c1e054007170001040c921001c0345248200c0c81007030035201c000d80a07000030009640c0381c200c075078043d00c01103c40300c011802c1000401d00141d06001d1816183e0700e0307441035460124669000a0580300000b011b0005a4008141030025140c45d1054004816100c07008100c01440c000101d09240150351a052155503000c0103420030140a41010808050080091000d850189005030140070240e40c100e00a88010300181040e0034003540140039660060014000d41014200b088 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 696908839 1250 696907589 696907597
    0x9180403050c161d0613022503031401080303060904020f2e02010b040501030f0b0912030406050a061d06040c23030105011e080a18080a030903020d030903020c06 71
    0x9003008010009080400c006220414421469180c81000759140c0030811040c0501d6521541554600605021480d40c54403001d0380090051400581c4a1421234a2402044002038842e00e10524900d032200405034503030310005002428440e466010798030b401c0015900d0008640040d000f84854000c5400b500e881d54a880150900400e810b45a41c070740007103008810009003107401803d00d81c17101e44801940a01136561210804e8504105030341c51074980b001d000d648000050002141c040104101d200b0070300208a4031038004090980c4c038241440c10b00d000b858211000e40d901c1e450a2404207809080c3c00780f0401c1d000e0b1f1001d10b9a015280d400402005080004c034400910051541045c4028045840114003e030b480e56459185e41c90702c03002500c4043d91031049003400050003807000c00b6541000c4c110303400c0441118005500603211941c4110204c0c41e5101400101020803d07510032581500325070040c900c0385e400e0301d040040494058055a81140004025801c204a14006030400300050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 696910089 1250 696908839 696908843
    0x8060d0215070f02010909090b0118020919140904030e1e0409030905090603210c19120906110c010e0f060c1e0d090608270304030215091804 62
    0x304003408004000c1e90720507402000102c80f00d40407504043d05640c2c00815000c0200070301c010910010f40b103643c1d0000310200500420740d800c005020704003141e03052503040e101c9503400900300f0810000c400f50107000c0c2140d14030400040782c1702d0055030051401d0400c011070280341d068444081c55405441000803449820030391180e241c064900c00801c6548500a40c9030850003902c1d9840068101400c2c40b4248074014500350180e4400e603c2440030321028040c1084007540a8213254440c40d1006240c2e082a00303c0040c45120302d26a803580f014844540b904401e88842511001032544d40c03101c06a444400d8008000f0b0039070080c122015465000d01c885a40303d5000a203042c0540301d001001402c00d412100701c90903154010010780070080203075007009007401d01c4030f40107116103450000004d110001038007420301049543e0003c0345001c5900668800c25542241c01c1642e4402c45449180e525000b51100781d104000c40d03920403003080540c0044801092000c3c1002c41e0b18160b228000030404005042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 696911339 1250 696910089 696910099
    0x705061b0c300a080901110c03060106090608090a05030f0f070807140d0e0a141207061e0311030106030507050f03092103160807050f0309030c071508060d02 69
    0x200c2000c82c0e59015060b440003080001034000740c03801074070001c1140c031031140c0701005034002000f02000c02c0c0880c0030b0322800402483c1084204e4968207003103003490000840c1356058807524001044c0309400080c0034041c1e521a94030800c296480751410340d524081c050b4090305a8000304000d02c601c3c107000b8002c240d6040c0c0c00c0c1c02c0070700d45402540c9400641d030001c1c0050361000d94000800710084018060802c4400503458031006901031a0002070f64510544103818020048081c0442a5103030344060801007207101082e94503065517110051301c007209042e002500100614400030125000c0d10440501d00c040e400402e086070b00f07182c425401408054410300502000340960590011050b000703611030300f02c0c0006008000402e120290b00c01a03000007a07403048200b40b04000440103400136100c00e100d4289042c0c80661208403059a0302d1240b01c400301c0c40c44030008208110b0302c10002c001c04140c0440000c88a03a66516102902d4821071138003e0780024030b012000c500207150200418801c00e0000340 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 696912589 1250 696911339 696911353
    0x21010605060706060911120105040b0a15090812040605071209050307120201021902060d09030e13090b09010e03041503061d0f16020703080304060e0a08030405010e0705061b 76
    0x100052054000b004200e800750b40b554400d1121038105e00074010220840c515031400c0c42e408800c24080240140106c0b4080e50f070b01c0141c6000707a40c412a5844c02040d254091218800b8a160020301d0801a405103604602c6041c410940900002c000c8130200c0e0f0050340e0b03075802d28107666a16281c0c881d03c10140001c0044050f000b080ca03580922103400103154164619242d0505031001a00304240e00040c680401c61000da00c10250315580210f5005096201e0005804103580c42c050300c09102c1810050303003282c03c2090300075190b1860317403007405d000f800342844481036540c42c002c040c241d802c00340581140c1d4000340301c00c1040c1c5d29143d46941c1300300f40320f00380851840d440c0c140400b040c2e405c1144400701140b00d1000d00c11003a0012100c15001641c0c480681e00705264008060740c0c44006100c0203200302400000141840101e60280d40e2802e103900c01d4481d011014105911190800d880940f031039482c1c0b00760700c0d810050010307400c1e0494a000e408507060415400c0c039201c0342d03516503c4404041c00f9803a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 696913839 1250 696912589 696912599
    0x4060e1c0b010b0d06060206011a1c180b1605091005090d03120e0a0b0106050f0405030706110d0503130f03020f010f06140906030705150f03091f0506210106 69
    0x4541c40d40038004090f11152130b40f00d107a800000783c642c0b55000c2d80541d0484c0300107005a202c00001d1840217400102c016030b64031440c0000d0300d4181d42e40741844074060300e024413480311310482056048c4010700070035940c041c42c3c5501090860b000059001500440c20410000100d0b09144406000004650810500304440200860310500d003529040740060300514065440d8552817081045030203007a4010005660259101062600c043c052002031241c0401c410040c05010011035010301400380075100c259949032400350000128088005207800b03400b6200580c1031040040d2441903071385140c14043c0014945840c0d81403d11014294210b028a000c00400d1010901aa0510030120000020b0042c50301041c204804052024144a00028014800c080c0e400088285c00d66030119881d03242c0003183c030783c0540e0300d100c1d41460700c0b011180402003000003e030128a6007000d01440c50441e00d003444244514003100e0040380d4140d8403108801c95035110301c80e40c0088602c0b02c00c8070000054580c2d214 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 696915089 1250 696913839 696913853
    0x2402030d0207030504030b22140c030313090506010804050c04090206070501090302060411031203060402031e131104110703030e010e1b10020718270602031b04060e1c 73
    0x4140c0907004284c002904204002c050f0720082d900401d0380345440c2c00209200c0703e07000303e0703001c0180c082d1000444112400300c40d0403d000024411b403004044030350f20200c2040101c1741c455070744a14003840d450480002d101c0d50013508820312846d40000905012440c03402000010100300300d060b600910140803001c0000c4092082e103085501035002480d0601c1c061400c07182c1d526003c040365000307400440d80140f0700290303803003500c0d00144122005601e80d500d850600141a00c0e441c03e09010502240c14000c00b07160a00100e40814015640b6a5074004e20f0014442070b10b41124100c2c40400e001c00038940444d100398000680000ca401c0045804c40c2d180801910308034000c4050592040c142d0141030180c03500468001441c1100e0001e00b80042ca01500240d0041c21030510107280c945808045099541c07503100c11040c00841020002c2d089458245000290000c850300804408801c01e404444165036041d03400316a0550b0303030170048401800c1407000d40860740a0090025103051110000a000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 696916339 1250 696915089 696915097
    0x602070b070609062904152304021c0b0d0209010909170a0207090e010b03120a031103010906051003050c03011205010902041a10030603080a080c0d062d2402030d02 72
    0xc984009100042118594004920300c005d64602c00d074030786501c102054429040444c2110b129555502c101e40641c0e41248200344200300780b65010384006020340c400e0b0342c4440d560088042001d01003101201c018203000b002015240040c2d802005c05004000b520401c1d000310318104c1c8113003d0b440103540e080450320300356041940c1103805604200d8040c44000c800d840703159803984403c0000c0c0f004054020102c3c1d2035207500522248000d41c0000c08917a0301d8000d4120b920900711230310354181c0da9a96803d150004045034001c43c1e1240360480c00001c02d0070301c64019039004501e40c51101d03103584d00e0803c41c407841c5080306908507125502d41e4024805a90b441c440c599440d100035492001c0c24448000700320313184000044007020705207490303018400f082c0300303c1c10340c0c68900d03203030420810a8031510790090341c6019030040e115480d82030017004164596a111003540303203030003114184445e0320406500140d9070502d000d902010306143c00d83da41105aa60300100c080c962500659140c84c41315042031084c5e0f80 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 696917589 1250 696916339 696916361
    0x3070e0105031204050a030b13050303040308010f1d010605031f080a020a0f08060c0306040902120a02010201062709080c0a1a060609010e09040303060b130f050402040602070b07060906 81
    0x56000100014103040c0702d2034011100500c911440c0ca0304183c0052100074450001600d0102c0a00001c0c1d80360490243c49801079411101b12510b92500c0d14000308040000d008e2803007040b000e00000a008034441f002c0e0080610b10f040c1d2688580c0c01c2c8907007169203400c000c1045c0500d2401e03e0042c2840a21044248064490000644400b034410b0040c40100900c59000c4500c0e140e40040c10007030090701040550700480d402010a5070707511880d00007000b404c1680e10195110028a507402030814000840004152007038000f0300c0750981d610540058102c088080f81d10b03a07800c02400386c2070a40039070700140926103e4a5003608207882219075503c1d01e012090b04807030070705440e083e100440340c1051503030380e00c1803003124130300c4c50100c0341000200003118090040b401141031002090400d4029003201e07020700a840202502e8010b81c180180c000300131841070001d50781d240480455541024001c841c250f640980051101c146070001d11103195102d20403d98003140e94024100001d0094010444814 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 696918839 1250 696917589 696917609
    0x1e020c031e0a0206070305060123091216050108100b0c07360504050c04051608150105070821010306060305010c181413020a020105100f240c020307 65
    0x742803103110664441e00400030306a1120103000154405500054003548502e881c40e012540c0c0e124840103861181c041e03884124412250070002101ca404400034010422048a404c210805900c0003a621103842a80060607494182014401940a140025080340382d410010b0541c82d0385e032440c101e064101d000c800b002c5800510b8100310101101c8a501004089070b050683c0f402c000703071407030524031b4284000f4481c0b69031030b100010305100c01072104a1500c14060001d1106180c90380007800b4000c99500354001060f01d440c00b04001c4a01012415050101038440d9850103999407071307010280e00580c0c01107240309850f264801d0504580003165009500c26440803550034118a001401e440320750702580b00700401d858030807d41070340b440100812107030410f0904c20751018500104441c0c1309140350041200b800001c0520745143d0562010f4461019014910012601c0301803d00c50300d0018414220341c00002c0b0214544c40340c080c180d2400d50401400e101c02d0560b121390109050021552182d4604 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 696920089 1250 696918839 696918847
    0xc0203030d0903180602061504140921090a05010818011a0103050c0c0a020f0a0f0f140303120c030a06080f0a11100504030f030912060c090501050711041e020c03 71
    0x103400c452000742c04a000040074401c01d08001740290340b0300008166180c00c44d1401d002000903102e0341d11605548550034100340140c41c0c10305815680b000e289084081d40100306002840203491103082d60180607000300010b0a80d450100115074030407001d0441e044114110001d0010030b0300c01d11a080b0204101c011482408030310500140031030b6002804c905801c101085064614503001c50b44046880c3d046800c0030003124844c001ca01046159005041c19511510010030140b440c0d0525004940c0c440b00035000c4212504103040e200e010b20350714412201800400f00d0420440c040c040c55005a20910005815076a042c41c503150032199102c00802e500916810010f10642ca0f00e1944040b4060324251108000401e008065201e90711000c0c0c20603854094100403d4485e0450b00300400780a06801e20544080c03c1c00340c02440740c0c007403150124040e03040c0080c465016a040d10030181d045410020400800800c0c00054108106003080400c0b0200c5000011030052001d4004101c40030f00440d06d07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 696921339 1250 696920089 696920093
    0x12010e07020d090303080619170a060f02040510081b070305270d020d1a0405100c021207020402090d1226100b0f0c030f030601031401051e010c0203030d09 68
    0x421411040c2d0b9410402403000078004030750815104c580206040c0c0b141160607060910030401104203030810b40c801410501c11071603200000880410f400e014000c1000380c44001c00c0500101d2085104813a040005010104002c0307000750301d00d65000b5900700c020380680c080f45c1600403565009503411808144081943e0340c4031000d070701c02c1100315004202100103800c41640061070890802c01c009108480d040c913141d04102205da51402022400810400c1034105803600c0d075281c40c0c5600008090900d000036145a480c80055643c250100b0f41d100189440942d4003880003a601c143d0b051030700003034018954800900b50158450110b995681d030501c6440b15024840c8070400c1000300034840c5000c44052158650103e00c0910490307500340c44a40c2d84019001800c1028000c4012090305400045420819044108000e5102e0384099908012502ca90380b5003044042007030140a8001c00307080020080e001102140d400040300c14145a82c0001d030540c002807035903000070718400d030b0340b1780743c00041007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 696922589 1250 696921339 696921343
    0x6060e06040903050d020d0e0d0f021626011b030509071a0306011803142103090a140304030b0103080d0e060411040519150608070309080d0203060612010e0702 70
    0x50031120803a8103001050140d20010100c0c010b0b0741000080f5640081d40120300d8680b0382c0891004105030041c0c1d020310240b000f0142003a0341d4440500c0242c001d2140306481000e400d002441515403000a084441c4900c1401e0808001c20700d0001d1100d41da10941c840c45280c03489103001d58980301b59030100d501d281081c4042e00b09001d640c0194032100801140c000d00b4224101178a0b40003200f868508400713a4803d610b407a203014941d2000d06480503403590100f5104000c039944007444c881c01c400702501602640091030a2004a44000541d0851103411000501c19461b800c03641c0c01410480342801d0700d9888441806400784d0084408107000a07100701c42070868001c118158200d50054295440d141c0c9810340e00700111288a0320841d610400149007420100c0500501201400704110005400300d150801400341c2c02618042105c440c0010b044c1e034400e0183d0300900f90301c00b07603c3e8201511084520065080640000c0d4048014000600c3c00e102c003040042c02440192591b8040d410f142201034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 696923839 1250 696922589 696922591
    0xc0d030f02070f08130b0c01020a080117030304060f0b04021b0c0409080d0c020a120804020f0f0a0603020d0219050703081b0a08040f20180f0f040f0506010306060e 72
    0x803003250040c407022001c00c042d5410140c0342900300f06030b84d60740e10620104000c02c00300c40c0c20190584d080030408010303440d41580a8402008942c070346400ea0303600d038580028100f89101c0007801aa004200040000398a031300244807003404034001140c12040710000500b0f07600000c0001003504140001c050500004104e2407030b6002e816074041040700010f0300c69112521982c94095549525201840016032080040100141d004800d0b200c40201c0350f5002032000e84169400c0c3d21465070104501c82d24036003540e0b44444020005c00b10050b07503103040e805901a4000c0400e07072031810307402e2003040111450403454041180c0e559039919620341c0107140c0a0900300d00501011f61185e202002820004900c50842e00e40c0722203418180d02d25a81c03403038128583c070304a040040a13184485001880034215185c10040c420084451560f04c42e11041002c0c2030300002c80d03078072903052125000706207032413001e050301e82d0040c2c095424140380701c20f240c90f024a03148082e0b1089610a50b243c4e001c00c40310750400481d03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 696925089 1250 696923839 696923861
    0x312060e071215050303041e0801020708210f070e0102160e1b041215020d060e0108070803180111070b120609010b091f050c060a020405030c120726030c0d03 69
    0x4000c0040c280ba02181c0e03a40241e002d00700c07100001c08102340800b030348420743d00700410030080295914200c03450b118003207420910ba40404001e0410203288841c901c0070b4817034881c1a44014407925641d0b0700714222942c0d50040e144034158014820044c42c6800e01c0700b09100a130000b07014000701410640b0004000807045241d0f1200d00030244000d0101c086401202c40c0ba09400c201c84410903103031908420024071030700c0000003665241460001c1c2800c2c0309900e1318100c5c0d0560701a902c0007944d42034050303124406c0c0c81b0400600040000a0703015517010307403d611035000744601100c0c02c075a02c909a1200030b51051180d451009238480401965103800f2100501400c403109910f410a8545008940070800c90810801440720b07194150b070342c5922850039201c0c4107d040048800c1410103500d03103c000c1d4054000c444c0a401500c00c00000d40c144205030710840306d0004010450b1900d001c0b02e00c01c51007041c441304400d0b5045203140c44040401000600b0000910030060f1110404c00c3c1009005c0341c100c0140703 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 696926339 1250 696925089 696925121
    0xb0a05031b04020a0e0303130501030b150d090602091012050c0a23090303130f09020325030207020d1a07091409090304030501090c210b040312060e0712 67
    0x700a0305071105a800301c0c5018190b0b40541c440ca801c0c0400e454007000050f00f00c0d007510010032640004541c3e04c000e441160340a88082000302c0c2c91005100c1100104584101007031410491145401c039540c0c44002001d0003040e005007090070b41b50000e031320f04c4101254500000c100d004140f0000c01c0620032aa007180300304030300701d24140310944007030602c04000e12a009191031240202c4001d0f080941241e84406005003969030710701c114881076200940a028620030191400d4011a0f1004d40784222400342c00300b081c010100038002d027500050980006200c004058090103040300580301c40e802e80c06c20701d07c0b40820030021031342e040c0400c0324044d005040004120540000b007003141083c100e51b00446505a0f108032031591040106440c5105a07031004200d0762910000c030b014002c04040b8a403e47d07180d01d080102904044040c1401152250005400442d141010400290054020070b20400d0200c0000c10040c0c1d548200c01c2c0000b0701255902c01140d2040c2007041910000c0c45918590000200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 696927589 1250 696926339 696926353
    0x1209011a101215080d1e0e09100504050a0209040506010206071b02220501061211120612120406030c050c070e070512010b0702180601120216020607060b0a0503 70
    0x504000c0c25052900a210000e0b1440403500b1280d00100c0310141400100b141c015915030440b40e07141c04071012800000c41c54507041d0140703019040070150000065a521040702d0030b4004000c481c070009040c081d81000c0186001941e07072294051640310340540c13a801030729601494244410342c0c1006041d82e04641111007003000454000d0034a486880b020002142100c046102089480c1d0180e44101c000c00d03c4400c58683c1e84400750041c1741600d140e039071040403446914040344141d81d181d01881c4641c0e50140100340200d00c20050300c0d83c0c0400c0050540300d101d8a04407281e41441c0342d0a07003105d08010002000d10500380c15004402d210a89482c0c040d03c1c0003540700c102c0f5110b4465018030202d4418030300110f0031162045054a20727400c00c1904140095954141c40c801c0c5034801c41c4104e00a061800d4009050072020404a1143e20180c50300e1140c00351071611500207522506211411000303080014001d41c0766440584071091042800140720814807040020341c802c0c0b940818403d0303000e12 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 696928839 1250 696927589 696927641
    0xd0507051c02210405211c0b0d0f050105010501021905070b09011403071e1e0f09080706030f0e0303040503070f050c0907080f070201021e0d0908120901 67
    0x928a44003541c0107040050b01c607614150840b902d20100710f520a100e003003100900085c401e003ca02201d00605d40008164401c0c0f00c05420f841c240a06421083c1500d940403400c405062a40c010103403042d001065102d2201c0c2583d05d0a80740f40d001e420580303a070384d5100d0060000b96010001c2e05c0540880c0803003031100031010741e282d1b40d448105008000310280c1c0890300d0b2855034010945049140303032659860b41c0744d20b0300150042c00084802c515a43c2221843c07680300141d4014001031100f40320480d21001e51040000d001e5420030129040d0500b003011180340002c01e4801800040302800071030741c01003a01000d45c0381e0b0205039010f40030f083c6969003040050000181000040722451070340214607407158000da003407160800110451042e0060080401c01c428035611907151441040110700304a101d464144c2c00b02d00300d020b02d6450307900c5003140e203078419591400c520103020041c103e40400f04451540c0c1d614000741d50840540b94000f034200006220341d103482030103888014905c0f0142001c0500500b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 696930089 1250 696928839 696928867
    0x2010b031b0307030c030f0302010b040212070e01021501180501080304051018050402030a0905013c020d0e010203010303170408040b0d0b0a03030e010e04060e0a02130905070201020d050705 83
    0x411140d03000c45851050751215601e0074000040290381005100e1621980d9041c0172283c01c1e1101411001035103000a103000524261003998010005005500d5049c0d0360070704242c4102940d080c2003415441980b252861241007500441c1c00380400710074248040711076000d00d405803041a00810030540081c0000e110a440d0441c40d01040308051421501070307a4030b004040c640803141d400140d0460300000070415080c282e45c010340b40c44e40c440e10081100061907a0020b40304609003550f01d0304a100c031215800100500210703042000100c5400501e02902004820212240d8080c510116500880100145a0002620501c1704d041d0403e00303c2924055455400341e104502039142601ba000c07401804030b0364103034058010840d0140ca0520200d40700e00300030344000301003007003180000c0649209220a0606000c1c640c100c61005000105079122005c080e0087d401a00b029130034070345006070000306070015028442c0505070036000160355040d440e80c0c8400340c4000074800c0d01070180405c0001110544 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 696931339 1250 696930089 696930103
    0x3150305031921020a090b0306090c0a0210050f100b0c1f060308030a09060e03040501020c100302130b040f1a030412050903031b07060c15020331110102010b03 70
    0x10602421026110b01442692081c0300d180c0354440103d4401c0c4200a12141d80e4024202004903885440d580380d40c42c00300c0209440100d52240d008900c0d000814810520346018000d03e64860050740e419000c4540601c0c01c0f02c0c404c441410100c0289810b01c000304031140c0d1520041c1150000541c0791020640320681d661440c105490031a4004014203000031305035070301c4400610740c0032040035a09d0038241e03185005411201c00646a446ca012100d04495000204503400c594040c2c0141c402c0c20764105c10000203400079122036081c10b40800c6030341061342c403c18255002d4803c20540d1a02d450a11108102c421000d400c0207108607605034483d2000b210300c00a03203a02a0348a014805103148070741e801c80b92402602c50442d0148800300b400c9485d110007942603004801140c1c101c43c495a502c0ba01241c2402251002500040300440d6005200e00030340c0096502c8242c40f4080540c01540e01ca00080d120307254004500410724041041c002c100b11f0444100e400d1109200a00852400381e00080d102d0f95 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 696932589 1250 696931339 696931357
    0x7020d060612050606090c030c040e060f3001060503070b1806070b010e0a0b0109170a0503030c0c0f0106050a05010c1e0b06042a030c09081c0f0c0c05091305060c0a0315030503 77
    0x40c00c5400111035076030315080440c0ca050090200c800c1c82111a202c840c000d580421007180b0b82114a4804481c03b00512409085035401001491020300d00204180780360f1254100c0c09407007960800c4010b031519500024800303c0d2041441c540107600d04880034a0701000500b50780310043c00c0040c03241960380d018015801b40c5182d01e140c0c20307203000320205807440c04416250081c00ca002c04410090b010004c1d60180c43e42001c0803058a620700c0034414030500301c1d401401456441b03507154900f44415486a0202c240303c1e84035808511041c03403800b00d510700c0540004400c64055200340e042045e20700745030281c3c0345202042901d0002c1098565802182070721018220000c0640c0c0b031348071101c3d440c8145042c0c8020100c030016502c0302c62000f082401d503070403056031490214040210b02644c02c1c0c8140c40c803280642c4c0024800d91300d2820310003041488440034040d100769220340d10105001c520705000d218000c200f511810b030350361012000040d058440c640c680d4a11443c449804102248020044403036141d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 696933839 1250 696932589 696932609
    0x110403030f02030c0601081c11030a0311070507030f03120b010207150c0b0c07030206090601080a080a090b03101a0903060a090501090b0403030c090f0b07020d060612050606090c030c04 81
    0x1903200c1d4040b407a600550302600c48505c140000043d052101149a40380580080c3c0c0545101981da2800d03200905c4104050106510402c0402d000e02d1099001c0c0c60760300004003680707240031099100e40307162420381d4000380d41144012400300201600000200012110001c080c0a8040b141002070b4403040d56106158104a848480c02807440c840d06030100d031680c1c001e5000206040000e0b203003889030000903007100588a07920100c2d006040c0080c040341241c0c410b0009000707200c100c1ea01c5a116811075076040e801c0c0640031002081c000190000b55202c0c84d40300303840b080940e207407001a540504a0303084014800d42c08005c01d0310280c402048255205a0000740403a11044500d00a40180110100900350b528000184002c040e41900018415812039903040300003038071080b40714101c01140c464550f0021041106a005040040130303551814054140017503c81c3e5540d018040d100456103003111143c012804201240c0341030302d842030300301c0000024079044d481d00380e00ba0300841c0320324000c2030500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 696935089 1250 696933839 696933857
    0x1406090d0819261801090503030405160528030b0106050a14130e0405101e05241002010b0316052719020c1014090a020303031b090621010911040303 65
    0x565039132400126503404e1402045400341505000c0e40b290400d0740e0845042c000c0e075080794078200107109800b0170348100509040c403000090740079040100075020f01a0f000d403903080000000c1009801014000c04071a01c485d540c481c070014008100c01c81446100440d46001d000d000d84032214041c2a1040e5000b03011234008039250f504196151014105400d00ca0905003010b0100c030114207007070701d0240300301c0007003d021a1321090720180310300b101d5080c3d204152a030b0485004107071401c2d401200b1103d005000006698200001081c101005d02550412a40c0c40c44000c0086003000340000720302d050000b0001045010302d4180a40440b006001e0401120200032400584041a030495981401c250b04440f8141c81c2291444090411604007111030800392000614207a4081981c0c81c0341c0d076001b005107113199916441a100d500a501c600560341f0804d200180c0140c46800c01040e08c070710b408403400d041848580b044120020705801c40036040b420807003058081140001640e0680354141041004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 696936339 1250 696935089 696935101
    0x12030b030f01020703030204170d0212090f03070305030405031b03060705070c1814070e0102250812031f0303050403030c02280305061806011406090d081926 69
    0x140c95580c15070121994800600c881c10950554000d000301e0301558500c1d00440f2050700030a84540c03031b480400700541c1098a2030700d91110f648009014a400003070040000c55011400702c0e1070700d41d09800c1165207600014040c0003d250800098640741e094940030381e4483c045a01082d00c841d8041c00102c140314000c10000100015840c042c4c01900000071650071070000c158509014000c07400709060481208804211141d10650f050308084406070000e2481d1700300c40381e0444601c0460701300103125503004a00469a0700041c05100e00343d00940c072401d6101e042047c1e218000001c0c201082d03520b0290380d982080000d40040981d41201c1e0142041900d4080d2400843c00c042d07114502511030340c0c0b07500070b003200d602038044102d016240103404680d03496841c0e10608000026504401020b0f42c04040104005e00705e04116030b900d8140584124184400000414501008000100c3c4c4841011500380d0016800c940c203c2010203903464108a44800c1b0020110710040c01c0303115001000c0d031000000c031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 696937589 1250 696936339 696936343
    0x31106091e0a031b090f09020f0d080c01090818011b060c030b0907111506131509020a0c03081605041e150c030e09100521010627050412030b03 63
    0x4001d5800c0120100300840140c01049441a540207454170945088050760480c2818130800801681c098440d46010000e1410048103030f0307034010304581c40d640802403001d0424080c0180301c08c49100e61144d0741c558175448420208005060000e80c10410f071042c2005d1280300c901031a683d4250841d000184401801a044000e44000c11403250441e064400788800103074810259000c0b80302d018140d400b00b03404548200b515900a83e0303c2039000c0403d01907d50100701e207501440e4400b960001e0101e189036509001c4090b07810202890000c102c0e4440c0007400d150f04444050384c000003058400e2030121400102a0050140e4003d203100403800040c5001917480041c0b4210250003400c444054102003001e008103000704a420480005054513505022810082e910501a10042e20841c610906203414008803421b12071840c00b010707814502501c1c000c0401e1080501400e002c0320040703110000c60809126401c02c0603049246e0514043c104000305495810a103050905864081242003954002038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 696938839 1250 696937589 696937609
    0x30406060801050114100809030912010b0a0e04021201142707150e03010902030c0909070b133303050613020408013306050d0f020d0501031106091e 65
    0x2181d6600e0100003181551070448140e404040031aa641094140075408507901d40f010754441042d40c0c0300740110511480c0540403032040c181001c00009400c035407200001d00608071903120440d0060303100288400d60405052602c5000350440003884850302020441180d004020300101d4004030b80030004901c4100f40d4440600d04425008485015448a52422842c02284020000701d00211450715990906000c0e049990744c00a002d80001c1074400240301246400a015440340c2c01403180104920706440064090411074006000740c260903d007030701c8120745103003c00800c080450410a0204011441c200d40d02c91814940405c594403400c001c02d18002c1d0341d180039480c2d5800400d0110f03501e10154000c000d4441a402c0c101034104082441d0003c41084010358110940b4044090003818059002460360b05c02070000005c000c1d8415810b541280c206501e000012a25800104140000051400d8840314212015031030a440803000030700c01400c00150148201a20040c4d948a90340d00c4211 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 696940089 1250 696938839 696938849
    0xa0507030b220506060f1c02060a11070b04091808031b09030a0305030402090c0a0f05160606090b03100b0f09192c01050103082d0a09050906060a0c030503040606 71
    0x800103041843e1035901c5a408950650007642c00d00400f08440c54071103280840307891107811003005400c00384c0a00009030700185040040c401d020112007070303070b0f076041016000526400034a15100e6040c00320210035181c114010f40004d025024a500100d0f840004680d0800a5100003015070118451079000c50301444036016414000c81d0075a40500d038101e0010340c0304620844001d501607a856501c5406030149103d51000140d0014074240050f001c0d10080c004401e640034501001c50056a500064603165040380c54100e46429543c1018141048000c0a4281504080c0000c82224020841c0f446912607444c3c45109010040760421800481e031200f6000020320512440c4407441a40d602504c0400c1544009030540f43c8040c1c00700410701c2000e040c2d980c0070340721624103502248001c07850464800a65007052034945040302800c540f070018140c44006850b40d00002d40b610040003000c0100406050042108200c00a4032130792105800c2100341e41030525548a803101d0601ca03004003116000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 696941339 1250 696940089 696940141
    0x901031b18080703050c2106070f1d0609010f0e040e03040503100b0102060403030504052a030d0315031b030812010918030c02010f1119050706020a0507030b 69
    0x92000c01a40008001c4000c0c140000078a125a69802038665940c000c0c8030240c6a504007140f41c0e070003460a400000c4842c1c041120b2541c042c801440c035281031580c181d900c1404208942c070440e8200b504070b4103600b5008402032110401085910200d546845103172403890401c100c05a203a1748041c01005082240c07100038200f0401d1400142105a40b80d2250041c0d0b4428410503c81e0380001c405805a445980fa041c0c0c041c140c83d80701d0355003d4001e400003520444080c02400741c1e0140b2500e40004c110051712811308000100e5410310141414421203002c02c3d020581028402ca50440c00030f8900e40480341d100001c20600442901d103404094440d4100500711a0002450100510412105410381e15400420008030b21400600e96091501d40d10050100f001304980401540c05400d82100403c10781c280720440d100207540503800c180c4424054410074842c01c0703002c0d00b131003c100000700240c50140020b180d10001625540c2c1e03900407502c0024031100208001601c2d180c2e042014510001400350707 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 696942446 1107 696941339 696941381
    0x40302060706140a06060807050403050303270d0c0506130f060c0e060a03060819030203040b0d06170312102303010e06090d0f030506090705090103 65
    0x7401510180d981d01c11244603001040702e6035100300c205200024149003058000b5010000c00360140302008000d00060002440c000304076030b0040c5c0000c8080c00b01c403143d038250801049503103440510038050800e0610750382d900407800f211154810400e84040c0d94170240b040c004c0310307860321000c0c2840c25010f4005000c03070300701d81c400c0450028610b8038804070442d04020851545c0720000000010703a40d03071010092044244151000c0030040d070198083d403126510001d40e81d000b1809600c071820000941c14500001541c03220004000d0411400e0580d0f00700f03107001d51260400c1040421507580080000c0c42103100c68505425201c03083c2c02210b0522552225280799030420a01a401d5036039203039041608003003000943d00c5020800d00428069070b4080c030052480d05220444014107041009018850303465100d00caa00410916119884a04010048003d0005030145800c6125101 = true := by decide +kernel

theorem cover : BRFrame.Cov 696762589 696942446 := by
  have h0 := BRFrame.cov_init 696762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 696762589 ≤ n) (h2 : n < 696942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
