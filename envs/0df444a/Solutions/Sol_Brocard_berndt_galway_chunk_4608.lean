-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4608
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:09:45.296792+00:00
-- url     : https://prove2.me/submissions/ff5a8847-5ab0-4c96-82d2-8b8014ee9371

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 828597122 ≤ n < 828776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 828598372 1250 828597122 828597131
    0x150106031b02070311042301030c050d03120c0e06070c090e03030601050d020d200d1407090e13050a05060a050903090f13090c08010209040524060c01020d0501060f0f170a 75
    0x309035030b458108447c3c0e42003100c024098a9401d00412095081c2070108482e02034055002044505200d6408a9801e0f0946d50728890440311400003c000c2824805103010401c00c00d00c601c007141c54000051190621072050f4050b02c901d8000030b182200c0c8400c8101d02c0b10303001002030003a56070780f06043e01d03005400d551006a0792507466060710b0043c90382050400da0641440441c00003103103400040c0ca14400301c03c03021302100090304c03a000d6068904951300008100045002d000000d01400e030b15a00510036107189008180340d407103051400403100c1d005c84056101e601040600704560040b9030300040300304011170030320004500050084180c1500c4600070030882c030b900c41e440c00c81d90f00f081030302d942c00c071074814000703901c50702d000d80030350f2000320101c1c041c2d801c180c007080c401e000300000c0c00b02d43c662000d01e10b01b940d8014001c01241790f000103185040396409110501420042e40b160900815a40c0c841124a07010241e02030001c00ba0320100c40c050009105c907031580c0034642c240456000000700e00015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 828599622 1250 828598372 828598403
    0x30702120304090f0606030e0a08040b090a030213150b07030207170307060c05180609060f03040510020307030603172704060308130e0108060727030203150106031b020703 75
    0x41c50340c0100d5000108035400d04440c01d01d5100c03a0361085080d0f8015940610501180003129642c40161000090800c078041000304254103003240582040500103001c00307541503894001404400348410b0380310b200c55440e41840c2c0b07001101c03055070004054000c03406007000c55540b03000c0d40b19940c070301c2880c0500b000440703900c001c1c0c0000d0045540351980408104094141070100070403540024a042e5401c4030000b074400780a180c901c040d03a07400074004040a241000c466000b0015800c00307042120180f2a40540040003e203a001552040703030f0030b56000a103240b860410b0000140c089065444101003003004543d01c880c0040300c0744175a419401159000010000842d004299980c000350524002003206204001800c51580c12119459100b08540e602d45030911303100d0100303561001c00f041a0306000c13442080190a004100141c19034104101369981d001b080c00c088031540709141002800d40140441c03901440395010300001500c807000b52458011019540704000d001c0540030600b1811140d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 828600872 1250 828599622 828599659
    0x80d15052d220603150e0c10030b0d051f33080706030615020106121212020c0c040e0105061e0a09020c06100503030703050f0c01091205130f08030702 66
    0x40c81080c0710b421000c10080c40211400c0051407240021205140c0f04140303039044900c41d00413440c0c100c1c02c801c0a0300b49545c4034420040369007541108030060544600c006601903480345019488680944003810324400c0180b881540c00002c1004101200d1a0a2802c1000c0418480c9102d070111340c0c40c202e850f65003070785182003080d4074544c0c803800e581e2142c0c2101081582d4586c001004540c011403403071106010b0914281d0990340c4601440c501700c034849401101151040f4010a40e541080c20040c40000f00f00390f114083e0ba2101e09060080d50081104490341d00b0588105503400e1425002007125051003400a03140b0f01c1c0601114143c0e0b8401c5038a1085a6a0042000010b100610086580f11081da10781a00c829040b50303a0040603000d10400501401c01104403084d4a9242e5662898079000380c800031443d401c2280f890000c0c0d942c484200000404001540d24000801d4884036100d5143e213408441c1501f0300e401500ca030f07884000c400c003d1010000181c40381103504491480c250001e00810 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 828602122 1250 828600872 828600889
    0x902010905031b0a0803040302010507031d10050408061e2e090501170703080a0807180e010f0815070503040f201002010c080a0e0a080d15052d 63
    0x209915003d82000c0551403103001040d500f14080643d15420026900c1590035101d01480c0b10190100d2410090b00000a108090a00690010282c401075403810301000c00d4641c00e20781c18500c049940000e003400000b00800103c0d900c801090b4004a095030a00030300394141c200039003010303d007005034030b242100416024103100591500c00c1903820303400d580741d05a00c00fa1a0070310a151009400310980c07204e00b0404181c080c242d0342c019100c54a44003554000300e4a4100084c040b5003046500c0e6600c28860b001c1d199903100400100184400c59418500101c040800d00c0d07005001c0c84c1c2c031903120500007880498200d80d002c6140c0c18002c5d141c1d500c43c02c03c2200d060340880d009007220400d10030f0f007940c1081ca03583e0360080c3e1026124805480e16140c0d0507801c95000d102240007042c0c80c02c000502c4030006c4e401070f62012074440d041d80e0102c0d91542e40c0c0401d0350032044d50185855141c03200d03640d60301801e0868000034441100c1c40e0454860344d82051030405001c6c100e03000c40380764a000c2030020b50bd0f440030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 828603372 1250 828602122 828602129
    0x200c0d0f020a0b040b0417120609040c050d150e070e0103150b100809060708252007080d0e0604031416090b030c0f150d2c0d0201140a09020109 63
    0x10f49415518142c982000010f00450341203501d101120441c3e039580c1403032800d0360400e80c403036110b0880700d403100750030005503540c0100226000820903102040c02d88583d400102d1980c27044480001c09500c200f000f005440c0e682d4511030b080d03401204c0800044a05800304c50460b500030500c10101c408030a03020000d803150006a1790044c424100c8038a00a500c01d122078400c92a8a0607034000b43c544010842d4550701c141c81841e145403080402203854820300c80085040126803e010090300340b0b44039150b0441007a200311103003039040b40d513040140788028450a6200511450160680551200002c0107406107010180c410210412420f919076010400d2400240e1850b807030961190f03644018002034600000c005011b40150302440142c0d0420b1000c040340c3e80d00c0108140c2d5841850901c288150700452070302d4078000c0c0c407011402ca00404c01c07031140304007000b00d0803101c407080e00d401d03911403900d0341203103c400840e850260160b0b0502c110840da1508107103540000f2404441c10b0004841900b810380 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 828604622 1250 828603372 828603383
    0x603090d03110702040c090306050c13092a0c1406160f0207030c0f03110904030e060c1009030504080f060705030112020d05100213080a171e030a200c0d0f020a 70
    0x301b12202035600410080c04403482820705006c16601e90340035201c81e000301801a00c9181d0010024070900100703401c00d003072003c1c0d140c98113844028402150710210582c5212000030442d0f4060110a02810711400980000c0840045c10a42090b40ca010401e6880d404000204244032091150051090004400540c0c0040038040990748030180e04d04403081034402160782e40442a24240315007402039007144610b406441d1102112149c100344051176005608003551401561652102c4005511900aa5500942e121500d490505020b54070b82080361003604080e512000c20403281581c00412241910101d603d1500d00308403d2010880241903000024002d0240c0012115040b005901070040320083c80c90006080ea1703240c807002d4a542c5942c42c043d001c011030400c0525901846030040c40c5c40c0340500c0b6404448909405460340030341041d0741a0700c1d05a10780702001d80000b00700e04031424503280c401805d8035003210a841c050380c1e40728036a03402c010702001500200c2c0c224000e1003503400a68110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 828605872 1250 828604622 828604631
    0x1a16080415120c021b01030f09080417010507020613030507020103020c1b040b0a06021221010303080f1e0412020309041112010602060c04091119021b0603090d0311070204 75
    0x3508090042c0d5040355074600740390300c0d0070b089071441440054680f06175442c010f01d000441182d40d00444c040d00c0007054448400383c076014034800180c1400010700003401501e5000340e44440903d13025094a40c0030346050115408030050102c00d04245000294941c0c0c98245681c1c1e9104e14401640a801255440c031400e000e0317020307541c408609168a00382547c0040382d08000d035440240801c0088080c602034100181c2c0200c2c0804194100000144102d421500c6544256074011042440042c802d1b0000c40018064009000c11115000c1200783c0081c8442000d080005c8920100401200b00400141141c0344608202021034024421a9010f02c0013900503c080340d0503c200802d95442903003400c410844c0325000140380c1e071010503c0e80c0501d1100440d186420301e070400e00e00107401c440e540740a150b0b4042110100c11704400380440c500c541d2a4014184e000600809800600c3e00c11003014041d003001c004001961401194814a03c211410300060800e031000c43e40b0828081c0a00c0290001d192 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 828607122 1250 828605872 828605909
    0x1090b011e0f0e1e1c0524010b03010509150d2109090509030415121409010c0c1211011112090d05070c06110a0b1009061a160804 57
    0x81110601e030b0b445141c07210100e00400b0b40c2808600103104c001d54160030902021011107180540b00341860403203100315442154000c0d02d4041c02c000da560b0358910b00c0f425480c40300f410001d0420206004200500e4801e0031580b500c404504010700042101104442d0154201c000b982d401c091128090381102c900400013054030400000340814a03411000704031400c3c00050700040e107010b20752280c04c40c5000386051a1500d20b60850f1900d46007002d1040c000c1300740741480d0050142c840d0049000c00231b5201c3c0c620303003000078055084030740f0301c810b000810082c2c24200001c40d495034680d4410303d00754030380416045998460360b03006001880e15030040d00070004081b006250300c0034100c1d00034402503080d152440c2044400351003e1142c400b00a0414030000e80801c4124010b002201c1064220300030782d045a02d56584000322580c08896000180242500c1400000070900c601d0018000c1040842a1101d140491480301c0c0a0809061428480310b9080d44c04c003c0c00a0503580144240301e00072014101 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 828608372 1250 828607122 828607127
    0x80a050c1315140408071a04210309080109110910030812041a090d1805030a05010e07051e040c0e03060f010801050c03070804150b030d0309110f030601090b011e 71
    0x7144081c0b00d00161441208805280100341202c0440d00100b008000310b030303d0001c5d0b0094000001c000240407800502001850728075003408100111201001496054518a4082c0c10b1010310341254401d87c0c9003d182c4800944d4100850049003802c0700c1c541c80300c1d0307183c0003030f80304461030741d04010704908000c91044640e8105800d618003403442101600503141d00e4240415400c0000c0740d00b4406640131032045c1d28403e00800010400c52030140442603000e8960010919102d481442100c150795103138002d483c1c085050109030b000d400101d03000c0b0b1828a04401c0e0181da4912126442c2c0b0481d980c40c004110140107124071070010b174010702556070901d44001072801140091154540179400e20303000840d0502c594040301d08c681d54a8559001c40e440310b45682c04000d00c4081c00724200d0b41e44079140c04866808002c400710901041d507011559184a00c0d10b9140001d501c60100e000e10380003042e84030965030101c0c00702c0c1034039144940040d41118120040b00c411008600e5540c2d2000312401900c01241d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 828609622 1250 828608372 828608399
    0x23041a030f15090d02100902010e21011b020309010302180405010303050c07091e0e070e010b07051c210f060b070618020901090e0f01060602010b100201020703080a050c13 75
    0x544030419800b59643d0403030b01c07611400300d21210300042c0c00900050a0507840c0781c2c45000d043c2e0040c9000000d01c0d1010010034070a61540c481a681c80d014101c917070362000000d0195050000202c601034000a405410180d038034061908558103054022030080301c541c080d0303140c500070b07840b0081040c041940c0d01e081c082c2940d400031441c1b41081c050031b403001c50400c406008000750310a04803d800c1d60700c0e280740b10800003800a035040d40d9007405488400a07800c282c9003440c502070a10405095907980d000d19241c3c0c68101d01143d0032100c0c09085180511702604060050120b0a034100c011460741491400d0100900e0b0303030040200640c2c80d008001c02d03004440310250030514402c120400c010000340040d4284114403800c0227502010150040c0a50b5242d504840c2010400400f00c0e0b0b44006030b0b0000600b0f5030f403103030044d000503176562030006050300c0c080d504002c83d101d980c00214030708459070710002c10b4203e00500110000340c50f00086064900c24400303c6541041040e099000d443e100c40c0c450341e068 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 828610872 1250 828609622 828609643
    0x111030601260c09120109230106030510050907080a050c09360708061504060e01080a0303021b01020d0c0909061809050c03100b030723041a030f 64
    0x41c02c0c4541d050b900c200c0300c516000100500d40a40680380d91206800341840d4800d0016a410803126140c0d0102c140c000d015203840d041c401c410004a14001c00d5142082d0b186030303d03050110368141441000030540c0032500140b0344100e4107022803d1364500600314501101540004401d00c11400800248100412081080c07202141c100d9010744400c1462015068405600c2c0001d10617441c00c0050710081100d2016071500800c15522440e540d1101c4505148045601180c00310310380314009001d190034400e110251482ca103000803e541004521340d0344403540b0a008044c1a800501c1030001d28000c442455a440240001d650303c181035142c1d10084d0000b268034a01140000c0d00118050b19140100000e507001500c0c4100072521181016002e805030721400d860034020b0000c000a1030324144022000306444850100d45c001110301070503c2c0444952104070941d82040340f5a443ca014001c4402a290040394081200c008007800c071004546d180f920254988203c07181c45c1700104001c600700442 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 828612122 1250 828610872 828610877
    0x30c091021060b090d0203160e090c0103020f070b1329100612051b07051b1c03111203090708011a01020a0813031b15020c03060112050f0111030601 65
    0x104516549854182c841030300070201e04007400d00c00b11106092408040b080280024226069031011304150520510141c00030510041d00d41c0030490004030030443c10104560a00e811032805003100d412443c94040c0c0000245841c540c10302090500c40c0c1c01000498041c1c009820001c5041c11610400001d0000503001d0003401807280080c20800c4043c03480c20403240a0344403081034542801e00b2030000c090080000c031101c5100c200038114030182070f024002e0320348140010048030f07900b140c1d00d0600d58481401107100382545041013000c5032106141d40741207030385420841c00d102c3c50340030307038904203000f01e50618003188002c010010340c0031000482104449010008105214001c1349070500383c0b00d8001100c0c00759100e241c0d854002000800101511441000e14024030342d182e80d80c0c150000480030800c4104440a0303028030106a485940d115600258002080e1200884c00400c2e1a01d005104800b92111001c0d102e609100c0c050200c2c48840d401e1100030000c945500061084030f4105403100c2c2e00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 828613372 1250 828612122 828612167
    0x9040e01060513020705150705070b0c0f07170c060405010b0111030708121003050a060c0e09040f030f03020c010213150804050c130209100906110c15030c0910 70
    0x1040041885884142e480140510501c0003a043d54500030750300100301103450b485083e01e10000080702c0001d690081c0b80e03c2d9505551940749003401c041c0100c028120640f032000800888107006440c50403900c107180e00141010510300b2110761500b540c060a0ba00c0c17803050060508000401506600c5000301c1c04090700c50000041591001580d00c2c000c0d0300004102c80c104000000c0541d00101030a640b02e40c203e00300c1c1d52503545035541e960034540c0c010411140c4a486100007a94203400c048404419101039805c0c0440e0b160613212080354070031030f41000e014424006602136105101e501154190300700803000b0343d0381d18042c85440d02c40e0107092107885004e4107003c01c008403461059000c2402240c00c54020450014040100b000000e4880c0107038440c59400c0000a0700da441e10f01c040e40f0303901400c1d01c501010600d09400a852103c0a00072840030b0782110207a4403040d903400d40801096001803c4a0742c50740c1e10340b00d48018500c0791111aa521910203042030044c00e070721807000c10800001100148 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 828614622 1250 828613372 828613391
    0x1150e0108030a080c0702030c1807030c1d040c03020904060e06120d0f1b0609050c0111030423120f2b09060f140a020a1406010305032205090a020904 66
    0x64403401640003441c001380700000841c02c1c00400ca000b91070b4070382c0010280c036190b0041c2c90001c0d0b5400e4810340a00d003000d00b544204100107801d4480e4614128203800d042000c0800d00c5c40290141468003451803050350b80c1c102c0321f003116110b941502c100141c0030b00100302445d26510310b02e44d51441281c540c1d2180c40b400001003190034000c640d10b40b5800858950503044000a0300c02e40384000341ca040d000070150703000c90038408035080d4040c00101034022805454100901c0000600d0000d00003103c2110350f100b04400c102540216a9459034094020040349412403030800040c030703030780800070100d800b807040701c5021546600204103819013100400c92104220b2140561074070341d000b0280e075040401d190040800200d03010b144c03082c40c101d2080c64640700100c00c402c0f2204e559044015007074011f038855200841004a01e0035245000700c40700004240c1d42d0700d9641c0365a640d00c20044445010f800091481c008136010301c09074030250000070701c0180c0516004602400a41080442c03034030850070040100f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 828615872 1250 828614622 828614639
    0x200324061206100509030a030c1223090604030204062c01030b281407020f030403050715020307050304060e0f040b010e0f03100e06060405011706041b0801150e01 71
    0x4840315220000003641c1a42e403202006000040e290b504000d009041100d1607859a00344140141c641c400d84807101d6a0b451400d02080841e106090901444840d05d0702c41440c2e8060b00c2260034640361030003407a0380c45009601291b02d44c01950700013900b050829602150240000c602001d4070725000c00040e5600e04050501a011038080c8000348c4411000c00105402510382152080800164034040c203006100042010465801c001c591140d003004000f071089096060080900a45044c03008500b000d00359140c2030b4a80c9854880d1060300c166980d9030040300c0d4024802c2e2038016401400fa41c1c0c880d07907518006881e03000c19544540c070404e600302100304189000d00c1022010740043c2c2d919111070020a080c05801a210540d07a98944541c914694400115000308100000108054100c6041c400184001d40e00103801404001d4040307047d942c00414000766903644276800046024800d00c000d19005001900c0d500000225420308507072a458071046105c62003143c500e800135840036030741c0da03110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 828617122 1250 828615872 828615877
    0x14160209190b010216090b0a031406040b07050c0312060a030206040305010c0e01050c1009060b03161d0603060f0a060e010905060a050402180103090809030304170105090d08060420032406 82
    0xc035038803540219086c41404130301e07841105200c40240c1a6488a5143c1d01c510301c040094010f241d40da50b100380100030030081d99042d0302e5042425402c045040505803040540c9a019000654400350010740000b54590b4510320309000450b0080c000e2599140c490030224081c2000017900c02c0820004410200c42c1e5120320100d84940c0784000140c80d549005441d0380000d071403c1d01c415644a5200c010034447c0380d138103200c3c1c1c3c0c90740d5220f85485d8809070300e400c00c20310f8203c9000981c40d0415400404100d030a480c04210310340d102040c070340d6038800d40d5070342078000c0e00070144e540042484032044070020aa0342c249500a6018000454491a40c80d5460040005a00c1201c090841c51f1f452001d80c60307210f500a030800ca12640c4201045800d0071680390100c1d2450308294481561031003104100070308081c0070301c60160840103010182c0780c003110b8464081d0500070050240c40c0110368444140110910510081901694110101d03070f503130030991003000050300030302805a1028002903100c240c0340b034540c08 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 828618372 1250 828617122 828617143
    0x60b040603121e05281107060e0112090209040b04031b0f0510110405300303062706060d090c03050c0114040503120a0c050303130c1514160209190b0102 67
    0x6404824180d0700171810950512002084240044032420f0007071441c0a0210070094940e940d105a8409a16000142009013204522410382c0c90301c4503101c00340e264001d50507070044d082407042c04e580c0c0f540c2c6400c4410704042c0050962100141c8848000c000c00800400001d6000e4800c640c0c81c2c02003849440d08803403074a9140c40c1c01c0c6e01c040100300000d01b4289902c5e06440051308003500c4034002d040c0301d0303105869080482074142c0c00000c200015441e14180a09600340d01c01c5d20041c0c81c0e2420392502040340400381c4147d11407940490003034a01c1005400c00b10320326511082980389035580c2d00c1c08a9a901954803034a004c125501d01015036071050700e050b40d084400050051011a8541842c03000c1680100e294600700804004508013040302000114040c29110302c02e0031b807080450802007441500e41e0008610030542841000800d5882004824502e00b04c4c401d040e6164a1081c8822002090300740c02500701043d1070400403000b00c0f022007005241c40b50395040c021000c001e0012607c0d46244038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 828619622 1250 828618372 828618397
    0x504061407080910110f0c01061e03030f0e0f060d0905010b0d05060c0a110f030301080c0103020a0c0b2505090301050a09020d0305030c0f0415110d0507060b040603121e05 75
    0x603541c0302e8085035401210340f00360741421881c1b46c00c0c3d040510803a55406400400300580d11004100040c40d520540f001d101c0d41155600216542503030b600070108481e80e8403003010400442c50341c1d0203650700c544402d0800c02005003a966614031600c1d040000d810762844c10390340e40d4a00101c1c610302c3d003020211814401e0303000003d015140c0e99030b50307107030344980003000351200304000c8413407030b002410080088800d08090a00295200c0d03141000d0249401004a981030426005003d24003103540c0003010400c0c80360b441062040c0960320b40181c120302c01c4040706242295401a946104042d41090041811160503070090100d5610a82d43c2400c0d075011183c020340281e105002400864450300c00307940c00c1044d0f00c02061402c4000c0c2d0540f003040d001904518940c6000c90001c2e500b07550000340794503280303510101414568021081c085d0260288285c0134140a80794240900ea907a180d500c04000766a1107002000000d0b5441802003a03001c21003010010501154001da5155005405681d5030b609601c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 828620872 1250 828619622 828619633
    0x609050d02150f0307020a050d020a1e1406100302090f0105030303010303051b120901170c0d0905070b0a0c020907110d1b020d120201060b0f040605090a0905040614070809 75
    0x5a0030702405920303012000c90b40000078020a185624003400960081040380d0050600154506105080c1101001c0303c4007594094444c03000000d0040100009405190300c2c514482d500380d080843c00680003450f4801c01d030086100704003210b09400c1580040c0c81c000d4810300b400c2d5580c0081d88180800a000e0603501d58001d100400000e8030034801000f44030f0008004490180310107104524184e00c03115100c0c0030031000718482c0c0880d42e2003500c4480c2d0107031400c28403019060140c0c20380740c00c1c460358481a8060340c40c1e15403042405000c206101c010050001504d0ba40c8644a100828021143c0000c0384070300d044801141c0780c18422140b01021441a0020784540d000900c0180c030704100b1000f15400cbd07891020561800359451100000c0c00f28003910040c0c501d004003000003801c444203078000703444500081c0280c0e400c0319900300030384086eaa5542889581d075046130b00002c40030b80c055440039080c0f9080c8400c0000700000f41d0000e00000301c0f0103983c40f095864402042d41d0441c0b04444140159014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 828622122 1250 828620872 828620899
    0x120e01020f1b13020a080a1406011e111509150f070804060e0102160501060f1206150b040803040801061a27100c020a0b07020d06020a0e1c0c060905 65
    0xa0b0002118404002030501520450b24264401640c0022040d000441c61040420504d02e0080c010188148044005010249008400a490301c01c0c10b0566102021002550a41c1c0900981c51044034890100854258031001244000001011100001240242ca410754135030004004018010036022040606070f81d44c01d0300031035944400400644009850740d401c0c1c001038600b0302c020004004840c1c8000c016059604106082d128107a100300080c0c9140322080002804440000542030350000002c507510030340e02640310a0080c00e4010507005200001c0004030214004010001c485d039402c028461240e5404042403001580904800e565504004085d44c0c010446c841a9102100c802c11200c02207805002c0f500030815030740f2800c04100d00c1c0e10041c0540c9003012104009106900b2010710b0405e19501040f09010003070300c005d01e0590003003444680c15019100c441c68151000d0044000c020f86c034070300c05442c41c40d501802e0312021740503003002c10803501c030b02261420340c0c41c041c21401c02e2242 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 828623372 1250 828622122 828622153
    0x1201050103120f180303120e1f090510060e01080f07050d03030b0d080d090203100c0e01180305060c03010e1021020a0b0705030910050909060f120109120e01020f 71
    0x18050183d0341040115420446540f001e0000341010714007940d10004008040940b01c03044400840401c0281e510222a2a1a54010101314011a03801c00800700381c025081c03911074a004071031106c0080a90a0074004107080c860b100401d070407540d400c4110b4101c600c1e1030002c251107c156009044d00604d13024040340120b402600058803540000d04020034540c102d4803041429000f00d0b0f031064260703891b50544401d5180c01c0008000d0340820034020481c40313541d21030140c8003204070b00c50941030003001e134a01c420200600a40a000755001350980d0402c0c5004002003003554401d000b409002c107250f4002c05c1d08035000542207419240100350301c440ea10080c0c0005a45541da03000102d920400081d400310310319803410081e008141c071440045468070002000c00003012070b402010b0040140c24803007446c1503901c418440c0e4029409840240c000d007000c40204a0031800c80d1040002c545c20300031054200421010003c500d41c43c9a070792040031213030348001241c0381c2545200d80c2200e54840c00c8039244c24036 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 828624622 1250 828623372 828623387
    0x209011a0d231044060105120303060a05010c050a0507060305040303061205071a04090e01090b0121020405190903021501061715060702030a050109051207120806060c030d0506120105010312 83
    0xd0951040840c500380a6078980030440c03419010041c680017000100b140d82400c548441c40201904061400c502d40840441c40c00000e0703215042c100080041c410080c0941880a6010603400c0401c6c0c80b0002e0703c03454040c014000c241c4048001900e807400c0016203145407000c040017650f1160113000780c146414050821440f8403400041601005c0000054105c0203205072a0b80050604c00407441c03a620342850807261030142c1c05030381c9441c98480c5010390841030070b240b0001203504580c005a02d0302ca0601c0450140c2100908000c1e10380b034030714084141a000548440080714291030294140c6c2ca503007007201c62680c01c05229482c1c18086021030301102d140d098640f0a00c601030907090030040c0e40c0c0c000900d011801c03074081d14035035950f0390f540c0b052040c18001c100c568550b10718650320700002035582c1420a0744822501c410007442801041880e0b9803003089803040c0c40035074101d03510f8490192482005113002d07260035224049a007042d2003104010300a041c12640c0002103110f0a4448010070341e4600c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 828625872 1250 828624622 828624689
    0x6040b0316030506010302090a0c14070809041802031605010e04022d0418020f0a080a06260613020109030f0c0b0f250209011a0d2310 59
    0x40c02211503800050307100c28680c1e001540180b005100c15403460043c81070040c4080c01240d04913040402c01a0281e0300002a24117012154450645c0c501c0e007828180300340d020b21454254010300300707110400b2010523207803100510b40c000c40c15160345031000c01c2d203541103448900c11a03000c602400951416450168058550414003000148045098440880802d8180e000340d0045240c0400c060040c451070107146603005100386421481d20031400c3c00744007203014550310030081205540010b00003201c1900303d84001e00c5440303031a02c0054400da02c1d044007203116501c801d881d4840c44000540101041c074a00300c1894041c0c40300000e25086488562110345031032019105801c50300d00001d2030440c440001c0c8103040082c0c4c0b200d0740b20410785012502c0506448503642c46030714940144809607030348011040c1107410000583e4100010320385548600c0c003d400819440c2440d081644d100040160a040c09411709403580c0301e0300c0d0b83c8410885920100c03a0050316146002d428200d00038820f9415800c0b0b94 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 828627122 1250 828625872 828625879
    0xd202a010c0b15030c030703141e030405130e01051005010e0612010302040c0c1b03140a03090902091513050102160305060424230901020403030212131802072906040b 73
    0x6001708880401c1c0f50890581c021640001200100e2004ca030b81405058000174140051004081e071503a181540da01450140510404050303072591030300c8032075500071111180304000034021498400510901c0c45061701c641400320302c8807010f440d403e1a015088a0445e040304c8040d803516401e60302407100410000b0542d50030311408403950408601d0440c4204468003142c010514003509615102078071b500440d01c290782c5a8803286542c2c000941055030b5009480c4203210041e1141d40000c0024188003044920400405000a41802d0036401c0d01050781580c200317800320361030a151102e142100070795034030010344542c202c1c1c0c0210b400102809454101a400e40e0701040200c0c100b00580800c0350030b440c034502c1e00341000450b1542840320a04034603a0050f6860003c504040c59034501a440341c0001030f00848850001030380304d12010854108601400c08500c0b00e490014011a07100029402800c003501c000d5040815541040d0000700300d00c0880340f81c40d002006a40314501404007400b0800040da60 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 828628372 1250 828627122 828627133
    0x120c0c0f061b0f0c0314010f05040206030a05040c05060d0f180f0809030313240201020a020706110a060c09231503070e100c0b0907080d202a010c0b1503 67
    0x2c5840c04c5a91006103001d030032910b50030403200d08801e0854404130040201e10381402c0401c40940d030742d5016207074002840040810103039264035010701030743c400c3d4000790303400300022810403841000340c2d00071070081d81030180401903e620107030700c4240300c101c001009003d014048103450000ea00c50020386070410015040303e04011007641d02c2c091020082c0c20816035904489506500c011485002c248800e075a800210701c2c06811000c02526120b203800fa800c00e1011a91312022400010003030b40080326081300080280300d41c0151b005240462921800c44080020003004204510b024000352403d44000c1c500e00b28420081e01d041c1c07442e000204200c042c000c4980426010f0b80700c02115904186080d650914008483d2030a40e0541c08050030204c0d143d0301500003440041800500503045442d5810250044144540a030003a8008010b801c0910b0062403582030f600c00c40c18401003503540200058480303401c02c0b0001140c941002200c003511a41120700415000d03038a0440030305118601805844 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 828629622 1250 828628372 828628403
    0x5031e13030609120c020a14121504050d02160e06010c050d0203030a0f020f0f16060204091b020307050c090907090207231603060b010c120c0c0f061b 66
    0x100c4a000d40c8240c0d145510743c00d02da070801034a183c1c02c50755054141000d240d100c69a03004221408800d00601104840c2240f5282890741e505082c480a61400011607182c694009840c045184058804481c030f44154040801094008582100301c0000510b030f00740040d04d06440d0010201019040d1814840c488101d240803480901c110580011b0766002155641000d4111104450341a2021090030744140201c0c1419141c0c0b00c115095203000000b07941d10341c40c105a5564801120142c0100701d28030018001562004903041a800100c4041004c01048050401a41c80703206140d0010030741e0300b040701400250300c0c00c101301315004200750044a00c0103450300c3c4100c080368801c49040d078006c1c03068041220004620362003800d8513000c40c005468865001f60f450006140076020040449032608060368940c0d02c540c541c1ea0703900e40c115014128207644114040c00301c0400c010700751401100e07688003058090300e00301b0b4441169865910301000c480510f451a4106810100c04c80b6a40f94080000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 828630872 1250 828629622 828629647
    0xb0c0a0f0611070309150f0c060e03040b071202010f0c0c021002030c070603060504050c04050102060c0a0c020901030f051219050705030d1506030b0409031202090f03060a020a02010b0d05031e 84
    0xb000350a1085e200c2030f0745141400307249004081080d071000b042080000a8007002c2d5070100d03540d00007075403140001c90b042040d459002d08600407600280340700c5034042060340600ca2a004500c1511841ba00200840c0c091001500c0c151907a018003c0003103008541f6280c014105603a01e413204051034410789040c09001a01c250400207281d0000002a0302c0f1402030240e890184110741c0c001081c01c0c0360901d0185440000303902c0351401011884e0303514000c82c40c0040d480c000e00001103100c0d8000c00d8601c256859213003030034040c0780c2c8e201d05580900c142c65400d5a224541000c03640d4407003a181c12140c8541c45450704407010307440a1000c90b000e00013401070b82d8080d902c5008330204940b400310980c4001d81411401011241c940118501c1a401d203252240483c2d0040702e007080c00c21148501513955404170020030104540c505500c0d81621034002007040f080e45030b502034510510342d82d000b40701850000302040004040242c2c050110f03041080964200224864256088011a80c982e810301c880d10201 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 828632122 1250 828630872 828630877
    0x616060c03020a020f07050306071103190c060b09042312041413151a0712021b06180906010903050a0b0a052203140904020d0906060b0c0a0f0611 64
    0x21840425000f041500c030160701480300e4203410701d11200a00c00b880c40d10000994400029005209001c03004410452588043c403c50308054a80c11100c020a0040780c8024840c2c0ca040c013040d1250307450442160210700d0710452050080781c0099400344070746420840710100405115009049101d04401e4810031443d0750045c01c014420f00e0785c100042d01c004824000e42c10895940781c0300b042c0c42c09074400003d40240060106403a8003043c031880741e800f440c00164003840b03045405440e504801c44e004900300c0d030000e90001d00d81404007140e01c42050f03032024001d10780200d0000081029200409070000c0c00d0410001d41c0c484014900a0344c00c603583d0b00c5a504240c0b885000742d8105007000c0401c6080c400034020700340c11070b01a0310388001c401030000f01c403280c840c1c00303280003400c00c002c0c1e114a401203003480040e5800880c00500c11540c0e800c401e08032400500022200310746403418840002400030646080c2d0310076140750030140070b03003035110399540301d541d11058011200e01d556400c0602e802c0300c84c00003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 828633372 1250 828632122 828632141
    0x121805091017150618070c11121b010302120103060f1d070608070c020d14071703090a0b0c030a030b13020a0521070507141903020a060b0405060d02061606 68
    0x20300843d2100d03040c0640f00030b4000705030a02400c4452503103032040c0084200154008410b10300b4410b411860b00d05004000040300f482c40c0e01c0310071400c1010380d031781e4041601160444424440d0035602d42000040d0140e0056001c01e00c0711403280001080815403a800c0000341d00f100443c0020350880c0560b0041900c001000c0ea20544e80c071541d030134440c0c1908078009542140f5541004c40c040d0001d640041e108042d071040041010f1a00000c0d02c5820800300511005001c0c16060b1401e0030500b0402c1a949130040241e0502c41c8280140c0010380c001c2d41000c03030744134003240d9018500d0401c0200059001c0c00703d000c503442d01709507602540d507401442440a000c0e0101e1942d5510f03955a8001003040300c0c0010a0b0005900107050750600c00080d8002040310301c001c1d402a44500c03a00e0f40b00c10300c1400c011310f2548010107190011340c61820168081080404244102010014000701c241803104071801140c00c40e4200d100c0d80d41504c09440c01070003130201c1d41c0034800110028039142c4d950a003602c110f0030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 828634622 1250 828633372 828633419
    0x30f0d020a11010e0a09020c0109080a02010b13140c0f040f0b030415112703010e07031a010501080103022b152313030908191218050910 60
    0x14440c1c04100c462820030321107070701c2441c0c400000c00c2143d0004880b6400c5105981e002ca42c000f44070100f011083d0400c1050300d400c441c0f40f13030711042e411070040e0180060384036040c8125140740b0982e003401e80912568150f54560014052503a5803001c05441c140d10821284d07442e00030522000403070084804002e4041e144104020743c803818140b4110154030411140c603202541000000501342081e0010f030340d120141c4041d02c05150346441d200b900014400d103e495019400c24004000b8840c0005800049070b210386c040c000320502445919a0486003805203e000503000401000549803000041019406600742020900c01e00302440001c0609100111a0801d00f11942184881c40d841802c00c2c003000121490b01526400c0318085070004014000d40c1e0000b0012800401d00d4400c48410307001d001c01da03041303888901680503c8001e0340d2401d1411510f0500c0710600003400c0f827080c205054020800d0103004191814902000011103004241c03028088038034500281c10701d0f81c203801e00d401c0d900c1078 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 828635872 1250 828634622 828634633
    0x417030a1a010516110d020d0602040312110c100909020310050f0a030b0c030c0f030405031215090402042a09081c0915020114070206070206060f060a050306030f0d02 73
    0x10040410200c0c2116009814004240070b868002031310032080959003a403200f14070454143d101c001510101c200c04010350425048084d09003001543c0d401042981e000b02c9900a9094000008a4107240128581d4a0541001c01d9501141c1054240b40150b8450742c10120105034450030030104a81080301e42407008018031800f0002070829180002c040c850503a0700c41c0000381151251144d0350806450030050050010014002403043c0060301d007401d5088114640c5da0505042c0542c1d250440d0050315600002c46c40414014460000c1148015001520341c40066481d0b070200001800b5070000800c0481080c1c200340030000110100c0c402c10402d45c6c4602444608100c802407600010244c1c02e499010060710090002360001007042c100e4408002d4000c0005910740200d0150201e80c8140c80950f1405003406140ba4002c1a65403040c0e00d40e5085400940e0340108001401200c0201c894200f04208000e0070309038440e000a43c0d101c80068211001440100501403615215030000b03001a0060b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 828637122 1250 828635872 828635891
    0x1208190c150b090c0a27080d09060e04060e190f18140d09180f0f0b09060a061e0c0b0106020105100b090303041520030a020709090f0201080417030a 65
    0x200a100e42c2140307084c401039080c40840b42c00a066000c0344c482084000c044150b1703104a841e03d0a240001500d40c00301a03030303401860240c0141c14040c040c041d000200d030407500c00180e00d0034244541070845080003d8480c40d030b1980051003152032903801e04000603035160303024181c81a00d41c4c0205078685100c541c0b00c1305000103e00340650314040d8804106030b9608461919040c082d403050484080d80c10482c0d100481c40401c110840003400c2a0080790760890424845e150200902d0340b042c8101e50701551903c940d40d80302d100304000c0302114040d43d004142480780c90f11001016614a0910038182d0505813001062078641035038020b000d078130180050391164204030301c0c0c030480008840144103c00701603040864080009869000e6401a43c00c3c0a8202e580f9154480c402c01d880810444003080680140340712003240c903240d031310841d10040544074104000031900c00c503114620707040e41c21268811001e507680e801110441e00103801540c51711341020400032103041d004011030048440c044005582e505 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 828638372 1250 828637122 828637129
    0x150e031b011209051b01020f19030f0203030f010608100305070e0a20070201140d021305031b130f0209060d0204050102070b03060d060e0102161103071208190c150b 72
    0x700c10021101d05090311100001d00004032601d585c0076406068030a800b4540040b4505041004410b00c82e01c00d601340030745000d14116000e054140a66146a40401c241c1400d036904e110076240340d03228001e00b000410031103200d45240703900201006a83e4609030350f2901c0d034518120180d001303505107051250510500d00c3d058400d400036084a00048110b0003224414848a4080e4843c0a4180030f0740c0c1140e4175a0030401d5084820551079074804540303981040a0460213040c9074000c0e41c1c000c3c40392075111403003000411110000c0280090100080c02d22300c0d05404082c0c1440e69410003529000d011034610ba640e550043c000540e20400016100d83c43c00380020f242020b40c1c2d00072610030404006010090311209003120520703070400780106d03002400080b500d0091003800b0a8802e070719410070b00102040701c8200d021901001c00c804403402da6071201c07422000000c11600c01000600c040188040d020307206c5c1c0300c2021031140c03800d01c19030f030f0003140d01d90900c00c821107400c3d040b0265955420380258034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 828639622 1250 828638372 828638387
    0xe0105010f350a0b071e021f02070f08030403080a0630030e120a14010c170a090b040809011d0105090d020a090c080906090a030207150e031b01 63
    0x2a00010842458001000b02000846680c10318a09603003050b1084501e00801c00b04480c1944010f400105162150004003503058045540000c1c0760055510040d141c80050700e0055015100c440c0403094030708200c400000d40c0040c1080f41d2203500201110085241c45020b140710728040e4a40611170f1401c14501021155160002e5541c0604500c4a40010580032042c84c03440300c0240407080200c2490406495585000c3c2c05158410030040c0381d01c041071000304000e4069440340350269099081c00d4841401e0b28030b00403604002400d2018801d242401c21210150080c0b0241c0c00060f01c0707080c5440321000040119000e403002600001c0c42805541d000011a03a019a042c04000c1d40c1004600020090711071004035510429a01c100d5106564901240307100801c1c2034003007001641c11105001e0070741e160407541c3d141e0300c0c041c401c0049c089100c08200c42001e80c0d80b40d405800c1c014100928100150302200c0c54004005404411942d03580781040185c2c519050b028524082045d0000011f2001c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 828640872 1250 828639622 828639629
    0x201091e06030e1e0c0a0905010e06092505040e07030902090c2a0a03020d30020f0a0305010503060703140c0a0c020d110f0d0818030c040e0105010f 65
    0x4981044a10500003031988120040d100307246008100f604030a5426480d14410088200000c0c51031201c00050745030010300300b6980c20302501c030100081c1e039071800c20b42103410902c070340d00038180801c0010f045884c01000c51980081c410781202042e41895240c8107001c100404c509002c5880000d00703000181c86001d07181c1c2d2243c6145000c0c03158612640c04281c2008015010200b40705010a200302c200c0543d0083c44060180e124204089800f05004c20340d4030450301c0d5003500035014014003000400e20500c0c0d20015070924034002c5d4a01100e07070201200c0c41c0002061102032550a000c08420210010000c0001074400c0d600403c65504240406081c000080d110000380341c80d01c0400e4104165015120340d009a01000080d218090742809842500c1000002035100720410321403c200003140d42041c81c14141036a013240030b82410070501025980000c00038000c840280701c0c410b80c20903c2966000c0410000d0107076140d441511001c40c2c20384000618090180e511a0018400c03803000c1c24910008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 828642122 1250 828640872 828640889
    0x14010b040602010632030705030a080d1128180320010203130b030c0f0301260a0c140a08161e0614180d0b070201051621140108030304020109 62
    0x12080003030502041c0c082c1800078605c81c80c2e80c6060a4150354042c880c4100620001e030580e0081c1d007a51410700019481254000c50262410842000c3e02208100740c400c031600c1d12045208100240101c040d4404000011104111001f44111007580288000000442c0315488503004403035844040d0100d24007800c015411940309109007440142d0070341d0843e00329074000c40ca103582c2e51108040c0c000f140c400c9500c1e41c0d8000f0400400090500b4401c103014859929900314222000240d081366078444030b003a0006408401900010300c13981350f140c051a640c0302c80c010142103600f5500c02c0701905040802510045180f45102e04010448070f0307080c1105840074001605903183c7c00c100001c3c19001149194040c00c0c000424840c01303054450035100011040200380701c4251030a071806a0150404980d000c3c010f500780008590221445160700425110315101c000e207030071030f442c9002614101d4a00ca0004207489000413810702c44500800c43c0038103104800756683c2d2406000142801d4031a038000600c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 828643372 1250 828642122 828642149
    0x160f1e020a050607110409050f0f0a0c0e0a1806240515030622020910030b0306071b06060e07020c01050406050906090402040314010f1107022214010b0406020106 71
    0x5a5460381d4400603600e080380d00c1a00c403962424100d030310101c1000ea254000703141c240c04006100d800200c50070491540f004890f280400c080c00d980d11442c070b8500041c120500140c0034091503036550700495112507403103000101c07204101409007803100102020760380d0030f07942c4102d00b40040043c0c11044641c101c0c500e02404007458000480c4220000c0f458000703410794007002260681c0d641c500403480b540c034503085900381400044100c230300a6000c0080c00e031007003041034a107041e803074041e020310f020004006000d89001d03501c804041d0341100b418440d9128000c007007024000024480d210f1180076020085508019240001010b8680b08040300002d06000040c88100070355a882000c48244000c151040340e182c050304404540640500e8000401c8a03000038074100715510b05520143c0d400282080a201451580045650a114141019401c05d00c500060110b03031030500070b840755040314100e00180d408420f50040441007004e810404d80502c00050820031594240500000f07480d14090210 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 828644622 1250 828643372 828643433
    0x40c0e090a1e140a0302101503080a030510120503121308040603110d050a14071d0d02190b0301140402121503120c030c1509030f0f160f 60
    0x4103000100c46041000100001c00041001100f00c072104558110070b0807582c0884d214580a51210b803404040c80040e45001002c890190200c8000001c0302e4100c0e4485140400300803045001c0c0900034a07101d581d0710400380008440d04020241111903000301c0195858124289010303818000182c681d80c040c4c5c100300342400115080e01d00b02e401f116040e042c000b98bc0d401c0c00014112600481800340c003072518100800c4402c1c002134000030704019894840340700e03541d00c481051b6441e402c00217420500c080c940c031004400c0d007401d041d0310303000f1800140840b00c804001040340503032044580202d034401e00d02100400280208591121010504417415410605580903841c41800c000700004000030904001c0582a10b05001d80e104080c44030360a2507a400300c01408542c1c951050603584094030842d8810004908500d4125000389001c00266242070f00800000403160004115084480310812580c0e010502c05000301c018140715110b0300e41d640c8000e05200303241c611001c80a078400d00c40100c504 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 828645872 1250 828644622 828644633
    0x50a0f09060504091e0302150a0f0b090c0301150e1207060909020c0c060f22260607081e27010203040f020418050105010f17030a090b070218040c0e090a 67
    0x30301c2205c2c00817603615162480c5007001c80c41d01c060001400380748030541007400581601c6030490702210415090a200000000d01813080c0d1140488083c4801d01003440140b00305c540482c10f8242c0c0c07809624102480e0707002d80c80004d41c02004000c0e142d03410703404688100149074001581c0700081c1039030401141070809403428980c580074400003482c4184000a01811000d000b01c0a032031105089000e01034814250001101184d102401003a80032564a40074000008080c1080500380c09102d0103070040761981182510b440348081c2240741001030700358040384880250241c41d03120329442c03507800455042d40410710b080c280c0101704280139640108108004502040d0320030440aa045d50005800046d01e0034151a00f091100b00a0071542450000180c0c040c01040100c141c66042c0000c0840022542c902c90f40c07840390001440102e01c1800302005000b51550151500031b00140040075001a4094000c0d50b0540880341100c10318840901404106003100701e880d840304800001304503226041d00c45 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 828647122 1250 828645872 828645893
    0x3110306010f0303030903050f0d0603110f0f040903170a020a090b040b072a0e0423061603060f06080907081f0e071a1b070302010c060c0207050a0f0906050409 70
    0x6005e050710741d01c3e42802c05105200311840700c160302100390b84035001111480b000d0b02940c40242e8446100c8004441d60b4600803a1500c0380100061101041d00000c00620002d8404054140c050002c084549451003052442e8544211480c820050707039a696244082c0c0b03412030315008480b4501040c4804e1141080038400ca514040d0001c440b45001003010204010701e01100d01d070340402401d44000091780142641c1524000ca102d0000a640c0440c03124031641d11b44000550500c072a0302040205401c2d44103851021685002c620380403d0036600c540000c800081c4580c02000065140000c015aa91040c09800050441d020250070238280801740c001161684c0782d51f0701905c1e40d03240070000650b81d00b042000f0081c400d10711051160001140d400d4500e410102c0e14800c880020000f40414020124860040c6c070f60584801f070900f1400c0c3c035040f008156030940501503100c0c0c20750205003560742c905084c00a001000b2000400c5042c4000c000544401c0d51007a40100d06100010001600c008031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 828648372 1250 828647122 828647129
    0x71b0e16030f0605060415081e0f3102011e08061302090d0302071707080307080306010e0d0b0a0e0105060a032414160e09040308060102071e03110306010f 68
    0x60110b0766442101e40a8002c2c20541c2c0101e038011000100020b001c10072040c1c805810200e038030751071080d40d111002c081401030b181c40c0c08072841c100d14002505450307411450a40100e41c8103244503000b0460f01d10010000140e0082c0740c500c2030002c58400c11036a11091240c8948020000803440c81170012000d0070004d80035003503900c6000346111105092100740d065810f140300083c04502e4000d03131407c01030349800250080002e080c001c850752035807041000448004603003400b0002c500c0c000050300c5400e4250809070400b8100001116180c500e1396610342070403e11405020a1040b508204078a9421a0380030308110103942d0418007040566501d4240c00c0301182d0b00034248040329141d040946200100005141c1c0d88107192240300356a00d1500d4600610800300b0182c00100c8446039002620788404940140c2d5004034a0000540040c0c4609100c60304410103004441d02181c031480048a1000d40503800000b07451801000c03c180600c44d8444034003120240d0141406504140c8959450700b407a01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 828649622 1250 828648372 828648377
    0x90b0102011a0f060c1204090c17060f0a0b030f0901050604090c170f1e071a1b0106080f3403030c05030f1804050603010b061c090602071b0e16 63
    0x26a0744240c807100221795101800e4401c2c2d5034249100d242c9000990030600a82240c6031405000e007884501418a180c60382c4001c0c015140e02d640c5100800c00c02a0ba00b1080c1500043d6091000643c0d01203040994012113808000980c035207005c001c010708540340103280034452400c1101d11004110810301d0707042610b0750b01d083d5404e0302e1032102c175492a280d403e001100441c0b244000e02c2c282600c980c590380d000e175802c1034183c032442c543e503c48500d1a800d80c0050506001c06c100412280801e13000b80c00080c0e81c61100011503441c0ea14488182415501c100204103604643c180002444001c10381e50404400c51840407252000b100e980c01201c01c00d404020140658010803030b041c00420002d80c0e84150340d145203555181e2010b000d030020309403003a65003800385040401080300c0c0e18040c040e9010703106001d0452810030400b000140800e040d1003a86121503991510140040b804900040100070b004007c101041120402d800c9514010b59000714501c90760300c2c042c00340405c64101008202d16551 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 828650872 1250 828649622 828649639
    0xc03110723060f09100510060c020406031b0e060406061704030309060903090905070914060a0318080913090317180f10060f03050c0409051510090b0102011a 69
    0x280ca400d00e040c0341c15100084540304a004010340401e18400c2d45104110000c00e8034141301c49610484151030040e03552045000c804401402882e101d0010300390718500041001c56038a60300d844248084601d2084400303407500700d98090040610820540350001c0040d28100012407a110b0010480c40d2180310300d00100c0340307400104081c54820381100442c11f40050b000c020720095840e000d01038148074820201460300303141c0019040d40c021074885033160011514450005041c20400150f5070261031418141503541021040e201d680c01c0f080000c082c840e058182d5250107400c100103c0030840c4600014290400d200c3c4000a80c3c00840c6102c241148015400e060f01c0e00a440a409248000004134920454008400c0b5540c0000e02e0b1440b6030010b00200081d503180c0100290117200c901000e0b1080e40100b0420700745050950014007124090403d40b82e00c1224a04100d01d10f010035640c200c90004510024800158280f1507002c403c0c009000030421f00e5803141c1c0b50000d860a08191502c9454003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 828652122 1250 828650872 828650903
    0x70f0b061017010e0402150a120b01030e0a240f0903031116110d02030109050114060a1a0a0219051b220b0a050d0f140c0a03060f06170309040c031107 66
    0x3001c4142e94020001900d00e038940110700c00080c0300907244092031645600305a42d050180d4000d03c03418504d50370940c0603000001142c1c603400b000b03503564052030049420811003071801a10510800001030f001d80c030b0100b101c25403410300a00b0b945030816000c0b640380c402c003e640d0501100c10f00d00220135a00c0440c2000044038400003e005142c0844080e401d0350800850340200003040d8820400d4102d12010110240c903003500340078007034040307004841b402194008071f040182108406000440850300c100c1d855002e80d0b0300006c2c1e00d5001e8450441d00c6900040040401c210b0a00c0380350310501055030000440b181c1208000c2c0340301808030030642030694900c0484060307100c1503111400b500d0041d24003007540d503e9240c082d040041c01c807000e9407007120852000c2464203002c00e0484031808020b00303a840c0750303046417107810080c0a0340101e8020a42c0d6008009100700148000305076030346004024545070180d0509100559501c030f6030036001c0600c1c0c005080d2860b2a0b603025101105d402103680d0010310340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 828653372 1250 828652122 828652129
    0x5030d020403050a170a050906030402120a15050703110a030e01060f2304090f140a0219030b06030105160e0315010803040f0812031308070f0b061017010e0402 70
    0x118602115a180001000b00a000000034010b40291007468840003000a2803c2d2040c0350007004200310014404001d00c06041c5842809190498001000c041c204081041070516140f2024002c0f07920140320605104450386521442d5441515800c4c14055500709101c21085481031203005802d0540d035016501d101c0c0c2095100d54007502500281021003900d6214100c04114541c6503040046070030461941681003a00590640580c4520192004601a43c13041d1081205c4502e05800d071140100700d03c0565688075030a0400c00d02e0346124042b07a410b5003000003001070002c1405029a0401043c09060102c01122207c003900d540703070080c80700d07584500103403e2a08914081e90b10040c00c5001051a080100040c42220a40740040a659584143d83d0b910342610188200d0701940c103100141c10070f01d550444282c1544035030007803460001e2301d41e29a0307210000c80d01d0a0320354405010402c60503081c40d2004500408581c2020794075298694a00e080003001401a1500340e11080c020130110b46 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 828654622 1250 828653372 828653377
    0x100c0b1e0612101a0a1202030a06021c09200d02010806040533041b050327010c09050a080a050a080a020c060f0a02060f0c07020907140706061d100608040503 69
    0x20350441030100c0c6680c401130044400c0c803158100c4c819403614000280c01d52590301203444942c1d0140c040c0042e1240d40d150000290040041101d03170540b40440340e075918200d03100b05d800540c480c09044003840302c481526950321418101583c021002d10720900050703a001440181d028008407004107659641c00c0038003003040442c50030310817102088101307060b000b00e01c4105900b21400c00d46040120310400302411000b05101555200851030410120749000b034802011609040030298004000601c05041400c550b0043c405400103080b8200034400703481c103181ca54004214030001031290583c5526155100c4080402c000c20302100014004020380c02070103100c01d020001404680c640c1c3e04140080c040390711907201000140203400c00200e035a000c0045080c068050004820704007911507083c40600b1002034040c0c42442040083c2500c03005c4000c004180b039610500780800d6051a040f040c421654500301e03a003165408040401c00c891072039090701c0f4100d8050b4a8201440d0f103441c01e0281c11071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 828655872 1250 828654622 828654643
    0x15120403180303200d090314072102090c030105131a030703050f010506061e07030e0a080106090e120a21090606260309010c11100c0b1e0612 62
    0x5840e001c0c800014150004001200c1324001e061002c820980c10000946a5040322002004121224403d20105045806004403011500b080f80c1400c2e8403541450f05180da00101c1c0c1c1c4405441012080440c00e000c0704068000c0400d091740d1f07085504240000d5940755901050078035aa03035a058a0214110400c900e1543c0c00c4050180d949958403410031680750421480039414960030308000c1112800c00c201140da0303030640606441c8410b500d0390100e014540c80f0300030940800061900024032940c500caa1000200074400000900d145032610000036a9002040300300140c115081011003941500c088a640f24030f6480d2403900d01c240b04241c000b1850000300c4401d10b5501c6e00d03064030100203039513111100f510031680441138100000140c0212200140d880c80520707410a110b8219154021244514001d2080214800f000c100b40e005c109824194444000000c10244c40034080c01f070524002500000c1d5107072144010140110b5a04200002800703403801414506180c0604030018803001604 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 828657122 1250 828655872 828655907
    0x1404140109020a09080705100c03030e0d020d09060e0607020402031003080c0309010305091603060b03010b18160801120b1503030c01200408060606031312030606080615120403 77
    0x550310750008200940101c20b140c0e000c50604503000c40c0c4201e0025040707040740c40c01410004220740310081140c031051255011418035448642c1950048c8090000072104140c1d0360090a40e1110000c0081c440545a849401840800d01110101d0707261041192030441c0c05880150b500c1e25000755115090f060b07030307002405040003c24401390010003c8001c02d004c840c26602272107580c4403401a1a1201500c0c086005128000f9200300005811a04100782601004000050a50b0000c0100328091489840c0c00c40060031241040180d609450002641101c145002c121640c18840303e40c0688901c0a000f0f0801401c40380002c1071000d18000180086101509507030302c440008a20314080c200c0c401e003582c0d400007451102e001025a0005660443d24003000821300d60b05c4010a00c885540041c010342c0c512410000ea42c004a241c0043c980042d00290b0b400050a07482c2040003458444054100e62041c40c980d00f600401038541c005488103038410110a0480340c5851406542440108044194 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 828658372 1250 828657122 828657161
    0x4030f0222020309060a0507080708060f10050705192d0f080a08060909070519050405010f090f021918031401060806100e1609090516020f01060509011404 68
    0x1031501c242c0c003d140034501c0ca80031200a500c1e4040c04a0036904111001d400150745000002c2c2d0061190101c290804030180511f12a41c600344082065200505200004940000b8516080160402000111074441c01c8440c1e003510160743c6105103c411801139a8803200003803940118010140c078254a510b5004400b107181c1b81c0c0c240343c1100d003504110881c002040c100c0d000120030341410400644210100d801501040f8105400c10400801150103c0a8a1b41c605004541e83d1030324494140680318101e1604400385ca07000305181580c07040708400c0c0b001c0740140101c0c0c25498004214041c0140a400d01030341d22403070b5042c030b0b180a220340d505c0a02092000d00c410a01d038001980204259054902500c0e41da030341d00c4c0e01e80c00680c0310520070f03900360309107480004000b10003131031400b9407000d56480d00b10743d02c5070740300c003d80180c850540340116081c00e0b000755482c0071a0100105c1403200c1b1100000d00c501890100081c00d110170511a417041d044215000498503a2103038000c290b0314580998928 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 828659622 1250 828658372 828658429
    0x1536180313030501050703110d150e04050a0b130201051806070c090e1603020604050f0117010905070e01020f07050f0f03030309010f050f0408090d060219080412050f04030f02 77
    0x101c080d001c2c44152070380d503e060040341c1c5540c13003070080d0020404030703404c0e00345014141417403070700104901c0340b0341c03480a5480036002c01c203c0001b00c5503900540c0100001e0000d1113040c200308402840140080766031030301c52903102c001030740c210040d078690185844110740c914429101040c4a84100c1f0700041085403d04000310b880c0100d9804a05c200c0074280c2200c1c880718011150543d403140c60301019511000070321042000f49000c86042001600602d81000d41402003503500d803c4003030070303081260541d0b2904104144994080c409003480c4400348010205100d0800019498019602602d8094204c1c0c0302d1190540d00ca03030840c4907483e14082c0c2281d6a91809595881c0203001074907a200c603041c2800b02081e00803030005051030141c5d401c0b0000c01d180803051410401400c0900780121541358090020090750300d410b81d180c480c10403550300c2d45190361419103480c41d1010719005040060000501c480d1940c0b11000301130300e0940342d000c814004110f905000140e480784d1800060f00252072150f80d242d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 828660872 1250 828659622 828659647
    0x3120c0f05250501020d05071104021303142a0111030903070b1305100f030c0c0b091b0102031e0717041203110705100c0c0504020315361803 62
    0x401c100c072540d20b00321101d261101c0c01240c4640903a2000000a1010f001101c081441e04950300400d060041c001440c085029450070420a169030042ea0360180021202203209000d0012030540d10031190b90304000840c1301c2c203540c240c2c3c074034000290400c21015015440400f041080300e0449500500300d0b00d00f0760b92001c1e02c5013076138000e642c0f160107902085400101030a005808020610054503091101c003a0700c2c104a0050440945803000c2104200380c800100e03000441c1c05005040d000003519030041c2d89007134015811043c0308058110f40c0300308091481c003040e2800395a01d40c0642c3c24080c2c1c4e1181d4608001000002107500c044482d080010300003440700040d0a24200c0714032a03101c40541d41618044141c5a004502c00c0702d800101c84807210300301510030a8006590b038855141da51071941c0f16000308041340c2048951403081444010002298a00385501804003060a021303040c000014001e04428910808200140d148014002c60b10310f0110000070061500034000f10380c0c5620740600701 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 828662122 1250 828660872 828660913
    0x703091a0a020708030c060103080c0c0a1203180e060609040f1a01021e0319051209060612010b03120a02030408060915070e1011010b0d1b060903120c0f05 68
    0x4000140c0f28480d000134603c0c20100c00e40d0301101d4900040d1459a1a60f16040900d50055209070b000c1d000f194040d08280c1d40300350300000a042ca480c000405800107107030281c800642200454800b503001001040019403125840394070180079618162039840c403a01050207451016908590703282010039079010780aa40190122449091b03007150105000f41c07040983c3c0f47c14002030301c112600100504a2032042c81450701c045028079181a40c5841c001c0b00d8410414035040c1c071040e640381c1000090041c5c038602400310400720700140c07000b0000e0f402d003417000175a10710070594016590f040124070300803d00d00a00649004024040694130a03140c038101c11601c0701c43e250b0440c4c2e86c000502e00403580003841170000d01420307c40500480394444074804140e90454401c1b0f01d4844640d00d5588003141c50311003600b2802410300c2000118820060f043c1a00d21204840c0c010302c041200700081000442c0c40c00e040304045074140e082109842603c0c1c02d040110f138032446400303032891282411040c00700b01030051 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 828663372 1250 828662122 828662137
    0x31209010504020f0d080909070c0f050d080c0c060f06060417011b1e120f1a03010f1509020306031c11010b1c06020c0c0415090612030804080703091a 66
    0x14070b507403000c82500400c0740c02103405c038001e440210248090190f508000c082d00d50050b4140c10b11026449066440b550741110f400c0d42240e56070401928000d0b096006160b850304100341400755410a0b84224070150b503644014495003043c1d5900001c201d41307841c0e000072500500706c0510740907002160b180410740a440c0c4e40505c48003034a000d880b01003440788160315a892142d10781c0b405400074540340b0002c40305e600b40031103c00c11584e5200c5810802518510800502d814060101c942c1d1400c84010582102e4404841013492070400c95044000c2d202c001501040c0c5e0702c05000140c40c1c1d1584800f01c1e10342076910301c400301754040341e640525815030015200b1a522035860002d0244036255401c1c0481e450100c041e82d00c2011500b43e03c81c00081d0b66801031f0044200010032640388100e8140000c00703640b0542185a009000c0d40400c1c070107126503001e010050104880402a80d03d4140e6004204020042c0041e01904006c140c020806105084080007840050417080701c0e5400c401071522290b00070b04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 828664622 1250 828663372 828663379
    0x61e09061608130b0304022101110d15050d0309052116140f030303010504020f0d060e1006031820090f01180e0a23060109091203051003021203120901050402 69
    0xc500288200c1484c080724826540684420700740e0307007440e04081100b16401d030401c1d0f4554030b030f0100c000c2609240e0050710440324040c001180c0700ba10800000038494042d0130190040800d240d1042c042030300200e032a422560241c074111004882440000c0da8400d004c88901d00728000c80c40261203015941e110113044d0799001d0b891584d1404c150302008218800030010340d40640082c00100304c2ea04e0a980600440b061a283c81450311055114880856200380c10441458200c2c10600a102a0010394140030304000e003410000d20010418403d020407000c00002d101428010380c80e4500c5e41000d800c60040c01020300b0990550815401c0303e000701c031090155110031203400314230060302c03119400b4442d0524031400180510158a03181d00d032a030100c02e01245416103441c00e00b40c41c500001c1000394020300b07500780c0c0024420454540106060811001d800c105400e240500005202c1f041c0a1000ca03a03048418100068010070b0b8a0f0660203204840b2400d480c1c2c02041100d8024103403c4144640d100f02c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 828665872 1250 828664622 828664657
    0x50a03080f091506220216050d230901090918031e050d02070204090f05011505040e0d0305070333080619020903070909140606061e09061608 62
    0x606540743e12030750300040590203c0c004181c882c1410f08840d509003000449404050040110040070f0368410700300c000d1070007889010382e0280f10007880308083c820410324208620000d240c030304208640740d20300c0302401c030b9400140b9094107a0046640000610f8441c0090018007a000410500040349607000ea0200b24980200750b002500108058540d034401d841d0103042c40401d0005600a4102c020100d0304540d0340c03140c02c0003085d1018040030803117102d080017040c0500d40d4442901003c05590005003d01d042c010f6401460703001194810720000c1c6468001210380d45d00c0001c902800c8044441c841c1c0251001d03040300084841d00ca940741e07a0b004100819501e60381c6002e000d980341030407645909402e030b40d201440c0c4114801d800138040801c0040480700500d40310521482250810141200c840c14403082403103110b0b00601c0403e81c04181203c41070b04000304c0c50324498044c0c100101c010422800000c030044583d840700140d400e558400400e044a00000380742c80e0815a0103060385801c06d00c0b60 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 828667122 1250 828665872 828665881
    0x1e06010f060c02060f120106090f0f0324110d060b0f0f0a090b160501051305190c1802130902070f02060a02033609091b010c050a03080f 60
    0x5416412518400e09464109280010489000b0b0180c0000c84c2d00403400c002d03c66192401c2c0018090021210f0000000e80d4944203000d02500d026502c500c40c0f02c0c2203500108080f8488480c42021a40c0280c01d80703011001c00d840c1902c5480e1588000001180f0f8014a084010304e014040e0000c0c10b00140d08100b00340d210390340490b203809104e004c2a6070460030449409220614409002c01250606051140940f01e4542095507040500c18402d114031041d07a42c82805024010250044020300081401c0740c0703d611910b0b111101006d81c0c4403000310000c000000c02c800803000c0c10092158141801c0806e00498001c406940f101880580c140e44000d4041044a543e1084903040e95000100080240442e428841243c110318041006d5010034040800525145049103016a0035450458000301300401e018000f042a5182640100c1d105001c10118140000702c0c40080391246010600d04680d840c0100d440207100c0310000d045001c3c548a400415400c0302c24140503450400380d64501c1e40e503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 828668372 1250 828667122 828667183
    0x20c070906050f0a0806010512070e0705031006030905061828030306050a18090809130906150b0913021e07020a0509090d080a0608011406040c1103041503020702040e 73
    0x41c0aa0340240d0006e00c0104402d2907c1600052010780402c1a940681c1e5a101c40b411306c448215111800704500004024082c1c01041001300600402c0c24108840350b030540301c055841c003008181c05c165040000145003001c108200504202640e070302800748001d00807240e001d404d886188120046814004049242d103000300c80f1a06070340c214690340b0343d100da9001300e100c05040b1204050322a180200040200d58907540002c04580c0800403000c82c0c0701d070070f925001d811034040c141e1a11605d0b6152106002c491030010854440010460786a03d0007945030088000a10454006400c0d0b01d04501440a0001b4084090b1070b90500844084010650301d006005c90b070b850440702104a6000844002c0d03046d8000c0108540040410340005051754440c3d018a007104c6034604010130f9606280c0411030546001e01030100a950207103802000100c0c803801c0340d43e43e80100d0040040a40c200c21164800301e110f80e041d02c004a0f0018024000c11000403070345a290742668140d640c5c3e0141404d8460100c42 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 828669622 1250 828668372 828668389
    0xf08010f1107032a0f0503130801060b09061b1906051e061009080f010207060b0609060f0c010b0a030804170109022b080c010606110c0904060906020c070906050f 71
    0xd0b0192200e4444164440001888100f2004107080340300d100240038003c9076a403840b010340130781b140c0c0c000c0da41c507040a15240d1001c01c0d69485248240c0c1003807414420b600004042d50781c41a816100345444000402c2e28404e810b540280d03000c2c036071040d0203980301564201a00903041d54000c5504022a4072650038004181c1042e403c80c1d06100b0301580442d84a0401040b1600402414030b8100070f581d4491400c01e04064180030b4070b8550ba900420000103010b040d20540e1200c290440382c03075103000f507620f020400c0c40c0a0407241c80c0c01c250004c9825a01180203402034450a0002040441001e460389048015a001400b0341c51051290640c00f0800c540140318000c480b0b60010444004d5505888412504404038090354030301c00d0040c0046800525800007405000441e4000410041d0400200030840e821000e0310600715400001c040c005921080c08190700250440c10200f8500d21904002c006032140038901040340c42400c400042d0f820702c0394803401c00d0303070802c5503c120041c1c81c4404000c40390 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 828670872 1250 828669622 828669637
    0x62e03082d0a020c12010b0429120a0620030421051e0d020702041112060603011d220f0b1b0f031503030304060b01120e0c0f06040f08010f11 62
    0x180c2c815024000d50b4034017150702c240b85c01040400450400e101c84040340c2958813210141c500250005003507240e0115521200180d401d0a03103011003400c0641c0d000c40c1d584c030fa03c074101903c030642d644418003103100b1043d100004400155401556130400d03181203101115114100e02010562140d0800303e94424000c0b0740810f10150769164002c0b0034140b41c20903951200355451400ca0703003000ba82c0010b0f191402a912424161000103448005050000314038401c014030841c4250010001840030700d50340c060f969207400754041d0800320b03a0350340030b031084608802ea184160742d00c06400107070b410030203c0000c0348034442c810440c50820381c480d048001c0b0b03011007010144540c00300500210049801c2000616807112600780c04030406440040407a00b146d000f82da0649056445000384502541c11408008000440b80400c01800320002d00154442e00b8480c03265100700c0d01c205c1a01c403a40e413070000340d03000340140200c06001c46d42d0b0f44c01040d00070b000c02150410400d023400d4000341d00340d9018064030b0300b5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 828672122 1250 828670872 828670877
    0x30123060901030c02100f0b0405070e01140c071a0c0706140403020909070f030506090606220b0d080a110c040603030e0123031017062e03082d0a 64
    0x1484080c1006401600d1590744c13140441c4030b00f022000701030b0f815005071100368403000c0000130081140020300003540c800804400c14402c0301c45c01084c4d00e980c4000040f80041c00d94410503200d0100740f907070f1030404081d5813007101e040c080c526400c00a45880c00c01404443c0c903450440308055030381c0105560326091291103014500f4248030400160418001131076001381e02405a8640c95100c600c202d107110031170b410a8495900000810011710400c11203160000c03011102d20003440c81c280c4000007025030221007800c1554403040940325039180c1a8101454942c40090580c035801211401440b043c2c1c3c9911425092045485030007060806108440580b5010780d00c540c0015103440040d40c400d0400c410940c3c0d00c0010710f1170302454080400281d409102c8072450034006500d0100700c80800003000e141d11029070054014010000900751035030141e100c40c015854a24085140396a004c202c5c3c03644050549680001c0c007002d2214410041003226001c0b40421550010503130a80e000c43c0143d0804002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 828673372 1250 828672122 828672127
    0x13150603020a030f050406060503070605040f0b0f0c010c020f0c090f04030f0c060911150c061b09030105100509090303010f060e040b061c0f020a020705120a0b070503012306 76
    0x2118480d070000c0c6682c120340d0401058402210b0000c1040320300480c0e059501c240d03540c00c24400346c9002c1c031450b401003d1a00c3d04508042c14410040f0100d0344511500c40708000000d50301001c2e800c00c0c01a240085d40f40c0c402080800700e4070401940300d00c1014522651400340300340400b40e074502500d42ca4011002420030026a558580c1c00783c45000040b00c6500901131030b900148000740e060301070000d4252050b41c0c500e030400c0c1c16206005203540c00201a00303244006101e50102ca800020710039034440d082001040350700c0d50800703643c00c451061310203464043d420a0100000c4010041c4001c0845009031040c000d10703610b11003150785a0000703005425220b01c9040c001c2000b20321504c40700805041c000e100181c0b04031480d00080082c0e200c041e12000d072543c41510f48e0546045840b501d0340200c01d4100546c078003040a18029280c4465000300e501c16070310000540b224800400800b085546e2005a20455050000000e407846d04248038095110b070100700440306c030152030081d81c1d5100001500346070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 828674622 1250 828673372 828673379
    0x30d11010b061e07061512060c0c050c130b04020c011401050102010525171f0b090607061806090f11181314030307030b01020c0d03170c0403051b1315 66
    0x403844e4003002041d90301c540c4920320000b00701c072402400001000100740304030058101c3c5c589030381520421b00b901c0e410f00030480e0205c00030501c04108000650070468402e040d05206038a054000c0552114094000348040341d8002d4018055009241410741e00761110b10aa03607480c012400c3e107a00311130003400c00c00070f004003101c1c0e610794550409046070345040519070a000307003015002d480c1e012110011083c40d10100c2000c18000400000003178542002c03000d107081050404103040c0c2c410188010512540e880c4250340e0b5401980c2501650365020405010303c0d2500d08100301d100324031413816a0742d00003090940101d0f00d440c230360722018000c1d1404c0100803542c0b4904240c00d0180c0440056511161400310104403c005100442c442e6525031400030b09012580002858094445070301406420420500c0d4040781e0021030416049405d942801010b941c1c14451071094003455100400354442c0c143c6580e60560740040c181002c07072090b260085d00c0c0402c014500141c5d14581d40550a51020f9003051 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 828675872 1250 828674622 828674677
    0x10e03071d0a11070b070f1403070f050c0316120905150a03020702040e010e101a060307200a0605061804080d0b1503040c0806010e0601031a030d11010b06 68
    0x70340d8410400303400000e030f510b610945101158800c0104803031401003007003081242d54100031560300c402c2d12840c1200d480240001c03045143d20020300300b070781480900725009810920800c2102c034030050601c00e80740c85211503d02d4902d55400305408480402c44c0c028840141442208000704407200203180c512641040030a0342090fa1000741d07201c0815400300700c4c000c0036860b280248000400ca50340001050400d40e5201800e10007000b041c010085d0814103502d103032200d000c190800d00e280481701c4a0b030700e40f2020710542c0d4a0066001c03501100d800103800c05448c00000c1030300d85090f0301501040c021540c6280c10001c2c6450305d071501055943c09003010401103400000940750b0001c044c20f000510403030b00000030700b09038560284005407134800401c00003000303080c410600040c621080103210035414890a4800301c00020407850405544000440301c90089040d0726202c054083c060740c005a1880304010183e6800c60205041c560074490790740d0040c00c0c54011560124048000384546c50b00e4210507 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 828677122 1250 828675872 828675929
    0x60603061212140d1e180c090b120609070501141603030f0e0f012004030f0f080f0a0c1109070f3203090607090e0402130f020301060509010e0307 64
    0x9640089018401280460b0303541c4250300c604000c0d58100101166400e0a2170b0a660b2641800344c0310340c100c605032100140700143c01c0c900342c0785640b10201c0c40341640d40100b082c41c10703c412030b0141e510820f41408880b80c00450403000f91042070380d0f580340c07004990b503a0b041c19105150210350300e0354080040a010030700c01d41c030442403043d4400002c582c15420884580c60300e00c81c81443c0740d0a035542c200d0036007030045070304400d00f941c102c9030031540c10949551241d092501c0070203406800e01075040c086804128407141102c6807020844242034903000f00030402810404c0d04203040301c0100940402e04098070700510100e1007807440307a581120115406404031241000900306e450b500100c0b1000b52440000c44070b0b09600d42d51040440307038680c50004041440c1c041c01400907018402420814803401110030740483d44150103468602185e41d080504000900400c0308450000784044008500300f58010020b040a8200b40c1c3e03004900310340c000405449407401c0c403c4013805004000301c2e49051601055 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 828678372 1250 828677122 828677147
    0x5060409020d090203011a01030518060f072604020f0103090b010b0f07082d090609120c091503011a0303040510180f03020a06030506090f062101060603061212 70
    0x180070981d030030f0584c04642582d09010403000c25035071041d0040392a50341845016401680014241004160045042c0e04e07100c01604c040c4455102100040d419401418801381403513405405544c0f040380023800b001011000c3e0b504034807031520a0b603004a41c2d0b20901030011401d41103040c4021507445d003005e01406a0041c4c005800070b000900c8480003299010005e80403041014600000a4030103a202c00210000ca4144000014060000c590203880c3d03c010b60f40c1400d0151400c06030410700b0000540342c02c00c60001183c2c0401c0e8001044a035a2480301080c103811400d50003030116110003605104a00a0940065015841404200100c0c5032100000c0306036650781c00c0186040b50b1007408040405055001003140c0c902012080017107080401305c0c103006100c58075007001682070080000300c0c01000501a4280e2079a0750307002c54080d03507681000007034400ca0042c0c0502102d00003a059406008503101d964003280c601600000c0d0491501890070b00c250340900c1040411618070003e0380d40150103417 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 828679622 1250 828678372 828678397
    0x120c0611161e03020a0b091c03020c01030f09060e0106061107050d081614010912050a020c0108191d100b10080901061206151e090b2e0212040506040902 67
    0x800040076840d0161030102a02c121800c0c01d41e01c440900502c0000235041c00180c03000120007039044040703540400c0f12400440e003440c000c106d1016203900300024148020001d041903190001c80800f004c81503200a040b2034807500c0d5210000400c0c6c6105441c0c48040c0706060700304040c0c103117030800100310030020b250322441d040801c0c1c0808665250024000b044007050299a9910100c0406125440050f568040640c0c07a20f2450035552880003919130b01d034031203d541400781d0000481c81d2007500c982c800b50ba01c910b462080042d456108000300264001b611011014020b0b46803084044015014a80d4060380c06400700d4802d42c00000121480c1c5c03001401e10195560729070010400b64482091030030054080c0601203001941d40d50b0f50302c0600d915034060500400c0038a25030000010241303101d001c4070301131600082c00341e803c0c00c00704245052140e040c100c02e4486c8920b07036040d900e048808505011550382183d41248840c0300a01b102e04c250701030316500c03c41c00d100802500034a40c009001520582c1c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 828680872 1250 828679622 828679679
    0x11040e0a0e060403020f0c030622170a03150506130501081503010c0507060c0801080d0516150e120301050607060c0c02030f011a15070f0309120c061116 67
    0x1c00240c0c02d005064804400507008051001540c00040042d001158800c13030242c2480c1c10314185c4200c1e442a01541c0c800810040e01c10241031180014888142030381e2081c201c1c1c3d0f2a80c0c03011008004185c20340e400184000ca90101040074200700e019141c020b804414250741941c204001503a902000034204408a0345990306030340640c4080c055042020041c5e09c0b00703a11007105141c120f080d590480000010848090010050020700103081c0001908500707001d60741e0404400c0400c20a038200f8000307027808804040c9a40035260030380c04560600b14000542e808103440000088040c4420700c511070743704c0030030b01c00c1c3d20110365181d1051208589900b40140701e5602540840e0034070040a02ca900240d40d601c1840642d280c3c2881e81081c412411100c00341011491802a00310f40114500546002c1030031010100300360003014000050000003000d00c81c0d0600031301c0c1c0200420900d015420001d004004803c0b2803510001d001c03c04a140e2060407600b050800300b2400c004034043d1952920b89030304 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 828682122 1250 828680872 828680891
    0x24030209180c0f0d061d061f020a0507080706090b03040b0a150e090c010f0f09090f0e100c0f080411090912071a0105010908120c072d0911040e0a 64
    0x401c40204000d00e1a50000301d4080e03e03022024141d40d0a90003407a000d003041c4010408582c0d22548c0e08a1650b061680c039004000040d10101d02e48200d070340000f8414422480046010000080d0341407c6801d02c1e40e4410300d907a21100304a106002c1a07c0c01090203a00e2008596010301a42100c080101e01e000107034045903607890416a84802540c6001e180d0304100c51800707035541d20601e48100c61210782010b1a003e030380444010704000c228402d4a44842c0e543d205c042d0100d090390040d003d001c220500b02c4120850001100000f4905203140d640030500c40081d00c984240204151881103820440301d1004620080030310224880043c01064039000f500c402c400d0500c0d1740e401910002e401000540c4104034403d40d842c1079606c041e00107605111414404012007200003e80d50b81d44901c5030f0981c0c1d124516015118035201c51500300035040410340401c1d19044003910038080d1080010031001c10100d50750400703001110940c1604c200307090810401807002210303005549070424584500003d013100c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 828683372 1250 828682122 828682147
    0x6030c0203191e0c02011103040b09010c08040e100816051e0d050304060504050a0e091e010b0312030a050f061c03090e040b061014160f0c24030209180c 67
    0x140c1c1e1903124040340d0302201d89005c4d0350f444107180460302146030085241074108a103909080c020120028100100840c419080085500c10b68000301110341100c80306007003c96560b10281024001c40e006407090601440d12800c589481c941241c20190920050b8079100e21100005010f4501841d0802200d000c0a00010400c1004000030030242c4d4901d5160f9081c142000441070165000b1841c0b004a0f00602c44079540100e1403204101c1142d080030072031500b041f0310602501c00b0180c007542c1409600c3c24032005a24600041d446610f48003820441640c81c003114002006081d0344041d0012036240b0442d030220030381211000d002d230090410007600d1340d80b9071800100000c1203404460241091044c800e40d4104400121680b420905008010b1454484118083d0043c013401d5500d074404001040e050007442d00210800d81d41010b2030810b11615190400310076000f119026503003004800b1611551072091080e100915001404251141d902101a0310848000303070900240c0e21041001a403880c6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 828684622 1250 828683372 828683417
    0x51b03060907111501080d09081203150d0c0e040201030b090709060518150d060806130605040215030a0c0e0f01230f160303050a0516140d1401080706030c020319 71
    0x3011030700400c2c1d00c2801f8900140f50b04a550b1000003d50701030710074841820011400d403903226050107141201408410006070040d105400003600b52424484081041070004e103079544124000c4e2002c0c45000c00001c24070203490b00846442c40010150501406800c2c498802000e61804c90100300e054040303c0700000d83e000c51103000e41c80b4007040010f070000d80a0060b00030100205410340103480d440c5040005040c1c0001501402443c00350380e100010110b540b80c52108403100480c6495940301c1c5040a9201c0062030015101404184d001500c6600c52411880d44020920706a4070004440150008046100320f02c4804074480355052104200ca02490030161601403103000b33921074000000d00780034048900103006245424204010041342d41a8100c0d10401f170a520716003c04e081001d4000d541c0f00f4001c041807440383c1400d00000b1012916180850b5060300c1510091b180256690785060702100c0c5c0421240c400350b042404207028010144411020304c0c00241005203000ca10805001d100a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 828685872 1250 828684622 828684629
    0x190905010f0605190e030d270803032e030602090a05030102032e080d0504090e0a0f1101021f0c080c07020f100c020a0b0d0b0301060f05040f0609020c01051b03060907111501 76
    0x461140283c0d001c1c8230b201110541c1d8402100c200c1002500304034040fa124403000340031441c8108500103c2d0f100065001c5000c68510a005032980700a4492600304040c0d40101e225510840105001041c10719040c4201d0b40510070201e4070760149201003070901d2103c2250615142903104140340051003200900617801304440da075079075650300c900381410b00044a00100b5074905a51200354014005000708911640e21904508100e06804500d0300407494100710f0b12005940b5500d02c05003c800c9009500400404002c5454035552030b40c0756000000e807401078480203548048807005221035400e0911587c3d0482405103081005818250080f51710780c0c0d070305d5020801d101d000044004060b01540310320511050100c0081c040d4030315001c5801c596030520f005662080d5540c0c0510a883e4429500401c0107000681d01591a11284c1d043c40d402441c04481d58503c0b06504002418507042c1c50048a05c40c0c44000d101041c2c98032004011122100b0041d0070ba0f02501c1444012140035085600301d40c000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 828687122 1250 828685872 828685877
    0x60a110a0503300108060c1b0a0c170c0901270218040513030f03051008070806040507170601090507121a032517070302190905010f0605190e030d 64
    0x103140881010f03480d003040e8418040191007070060183c100c010500e590405010040151130b4006109011212840091200d10602c100341c21402003000c400041412640c1c0c0ca4084c9902c08108040d094889600841c55648240030f0b500500c102c00fa031410582c2c1d0b0758568011244a02c0c0040080d500b20303400a410656580348000e6603040034035103401816031000c41c2141030900b07408070381d90103014a183e2000301c90a00d901e510000384d440025005201c0100080c03c2240c4170590313610728541c0c641c18140c0d0152114019600c012480680b038000c80440100c400b00209032980c80d1059a400405000e083e02080041d80c230300c8018640107500440740c40c4a40c1841150301107088404162801950020f85d0700c2c0118203617049058544923060b09803c0b103c0c1c107451040e51400c110390060402c0c0107a00700075030102810506004040181040d107003601c681140c1002581d8072040c0b034000900d410720981000600c1001520444c0007044000075128040d81460070302c250300d80001a05202807084100c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 828688372 1250 828687122 828687157
    0xc0524040f06140a02180409020d0201030515030304030f1101032f070b25030b1c0804050d080406080601140f1b03030a0e060c0c0c01110f0601090c031a060a110a0503 73
    0x481c2080640340b68086c2c412034080005246650205030010440d00f0041d05241da00c20009014a112500e5030301e44036001002d41c0e90b5591203180c5021810402581900c040c0901c80d081611075000e4811803100c4c030020440710b404d284600207540050800344400f0000008140f101c0c90000b4a900b074107074002c0f1f890503150304010315041c0d44060640c2d40c00a9403000c00d030030a070400c00b15803507105042030710704e00410b1078960020b01800e2003040c52140364030054010150746c1c00c80c424041094082e10544583e40e42c2d0b0252905e41400441e032480c481f445007140450700f08a01140d881140700100800300a60070240f21181500032203d0840d00304490700100c542d11440040e94070b420038080341da07100407030700c0d100f9007082d860f0031543e40c0d560000701105042c040e00540450080b6403c00114800003804e401302da00c55a1608d00e04030140c2000609140440d043c4130f08248041c10308881d4042c5542c014008500f0020801c4003150352400920780c2d4105801030403115408240f080c4020414050304503c3c020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 828689622 1250 828688372 828688387
    0x201020408100c0305070e1e0409020303030a02210907270f051f21050a0506011d0703020a0819060306020301090c11030c0703060f0605100c0524040f06140a02 70
    0x3010345000074400b1b4100b15003d140c5c0072155a680f44940b00d071549180101f14286d2400000c02d0040221810181d0305120100402c50030340b20980040c240e6141c1c00122901941c0b41c500200c0340c4010646141c0b40e07540186400380042308004036a128900c0360310b40e07401c11800c82c103081c140c01c03580080d11110815807110100018105080c0300c1c00740744800110604866881c0000500c1d051a0b00f01c402a110580e940f1a001400000c110b651103554118040c1d80031541c0d0750000d0b12130300d10700a4038900104074070400a0aa18064030039501000314a0b1103070040c60340c500055184030210343c80fa8120940d0390345c1005c4041851440070314040c0031900d1002640079469070f400340040341c0481510130079a000700070032150f4210202d680c0040b40d500100204800609091050103007500b60070064010102c000d2840302203a10011101503240a4001d0f103850804100c448200007035102130840d40e120912000c500003e401070036940056004490000d40b00303062529140c0c8030201940d02402058000c00c0c0d86 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 828690872 1250 828689622 828689627
    0x70b011e0f05090604111603082d091009050f0111090321160308160504080a02090a020d050c070507060e100c0f060606020a0528120201020408100c 65
    0x89514035408116400d1a0426421100e055030103000c3c090800c2c1d501040040d111134102e0350b034020280b044203441d00c4410104d40380c1305280c880c0a0b00000c4c1c0c3c2c10040717070f000202c89208401c1c80845007440c4000c02c1c441d0314844c1c010000a0814580d0344070740c03804600c1c2030305248a890300f104e02c14405407103e84030040c0720b0ba003507924085101c9800f91081080c02c6181d5400906140030400d40140000c8801d00701044411034021003140045100240114404043e80300800500c10303074000c07902000e8041e01070001c44242c0204d010f10341440d0300c690f80c0b000152516044840d449a81d03100d0152500d559a10301400355401503504940720500800c05008200d030600c01000541154038006107110000c20000f48980c1000c1c100300c0c18000c3d00c1d00c000e410b01000c610394401c00c58024006112482d540c00000350b84800490081d10319004a4002200074409648240306010f6403d409060501c1d0703980b5201d0100018034582c40c1559800c000c006103581052189403218034070010b001401002c4024017 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 828692122 1250 828690872 828690899
    0x120a12030e07050603061f140f030402011b051e032a1e190f021207050a120f03050f0409090308010e0a0506010c11040209150d0b01020a15020d0b06070b01 68
    0x1e140718034130038420041ba0382c854a0000340f00d1400d00301200d82040201d1004e9401014984400c40344650004403481c440f89008000d5004a2003a42c070b8580e55486d800c03040c500000f02460081030754000900301031801c613001d103e0310045c1e011001900d103810410382a40c9600045100440c2221100c0a111205404144030500085442c1c094151000f451000380c15210100310300d81624405c000545030b018800f050754a4941181d015080d0f8200d07440f401010341d5244090f108003031003008103c4e004201c04020100442620f903129041400240c00340d034040d14550045070440c0c0100c1300c140302c0024480c105000c0d20248500940311140d0650605040c00400e09004051011250410702030200c540da0025212810641107080420f019200c800054068465246e00c1c962181005a0100900400b50020700402d412000200042200b0740016a01c8041a410143c00440400c038220401035a0380c006040d004910440000d902c070070980041c19581050301e0030759043c00054010702810100902 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 828693372 1250 828692122 828692129
    0x110a050a020f180a1416021c05090301020c01050901060602070e0c280c03080708041a19020a081e04030f1b0606061e08010506090d1502031906060801050f120a12030e07 74
    0x2401e002c01b1003040300030b5561201d003010300614000841000e04054441c03020740709200e034020700a56940403240b00701e40c06043d081d5000e54207075203805c000054013400003440004031100002c060480e5583c1e4038403d1481d13004107052012030703000400c2d2141c0351150500c80b42400e0303149855803400031480381002003550314000c0550083c005160b00348004a40e2ba849181c4552855030b424042075543d0100c990402040c135401c03060080e0000c611120234a82180015101e214241d4072100340000c50803541140d0070003038a0240100c0d15541320b2030505889032500325103104d0a0a9485a120b0542e508c0c03401300e80944d0b101d43c0016082c0c004800522010b030028402e00702091a082c4030315410500000e500380320320342e5018811944241d8413000c01402c0f0341c03079054083d8031a008548174a400c403801c01610300300c1d0070000e04d00b0340703080380105a081c0544003043c180c60000d0318280b10080a501403281c0f031581f0021005c0540f0503844103c0c0014050009582c2400c2155404108014540056417501e2070640 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 828694622 1250 828693372 828693391
    0x7050c09010518060301240602100203042a0f0e0a0e15060d0f170301080d05120106030b0619030e070f0b03150a0f0e07110a050a020f180a14 62
    0xc004000582c0e440010701142c11020410b1000394641d040000d0041014007c003031b002800141c8805000035401e1144000c07505c20340c003035880c803007038140000c02280b0049400504031007052440c0e0b41a1a080404006055110384900c2042a11120b41d00740d101c013607503c990821000c0d102085418085070103540f00203200b28004022007080600301413440c3c000184824012407100e0310325000d000d48401d01c00310f87c030341194210304130b40c07051501107109900074012201c16205180b488024244035200f11a2543c034804d601003030076420501304802814800b11403036070208091002c01f0518010040d0ba01d204102606d002551104040709141012083e45c442c0c1e55444100300100051a80081201e074425201c4d14400c0083d0301e43c000040040c19550003001400d50521800302c0c48100415106020354007546842c810011180e4002d035483c4030a4400401d650054602100181417200303c40c00c40c1c035402020441132010a110384255860300316805040140c8914610000541c2070966541028011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 828695872 1250 828694622 828694639
    0x21030301090f0c0c0201030c090b030c19020a0507050d14061003020f01020705060d020d09200301141e0703060512150601050f070809011b03050a0201060605090102101a0402070807050c 81
    0xa10300504a41300080010f4140341e190816450030510403108000944245c029903601c0b41003640705140290045240c544040c244d038070100f915240000b03008802c3c02c1e4004000d005c098200702c00d20400c600c0c00381040b2004850386081c03e04164052012034441c6e0100e01b00e0300c44452031401003082401003022083d0540d04910b505200c15100d5a0850317440c42181d050159940c44501c0d104001030070040d201401913528602c841c040015a040b420314403e80c12402403103000100c190610700810166140300a1108064404100300305107001d55a119010742400215a0b035a1004980b031081c0c1d0301030000b1503411503000503905407688040d564000e0b1083c6041d60034016104104600e510401c82c001d0310005020500c501960f2142a0607031013113a55a04440c0b0003071084c50050b000e50000560707500035500f8404042a03007031041082e541d628005030b004100705044000410024051058911030512400f0701c08115911103000815136540b2441560b595980917041c41400c0c00c000100039031250000c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 828697122 1250 828695872 828695891
    0x23040e04020907031109120c030a0302161a03040b04020a050312090316050108061309060f0e06091203150f03060720072702070c0b09010e010503130f0221030301090f 73
    0x241c01c6d120406000d9036038900c510040d0605528043d008407013150305d0b2145038004410554042070504000204110b0201c0641d01c4604907040c0100101348403210b5403003407000901003020302d030762141c1150000d890100c403551180086410023508100303034250b03490001980651030604005d01c2e040304030071008030040781d030600000a080000c0544428403429000d60581e1001e040d41c2d11501e48198044000c01c2460341140d011741c041e140450302660035003c1c010018040c01e201040310003040511070302007481c65880c0381c90030001141920b052a089141d0a2181025840030000c2c0740c091042d5841d1261030901c0d010121420254010240101ea0090002080842d0700441070404030041c1c00e402c40c5604403000800030003806400e0001d0141d281c49240003d055080e80c00422480308280e0311a442042048015902480b06848082281101030205004034282c003074a08100c1b0b00c000d00d000c0900c00c2c2d0024076500c0800084a0550a4000200402c594111485400d102114200062204516 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 828698372 1250 828697122 828697151
    0x3020702042a1d0a14010504090c08250228050111180d0b010b1e0a12050619150215071d0d05030d050c040b070b01081204030803040323040e0402090703 67
    0x45900c11171380c0c3c01d0303180c6101507500d0307009105540240070035002c1000340c4480780c2c0d0020301c141d03410b98a0507092022000c081d207103d1808601d00c1c100c240d40381c008019a48001000e00240710301d000c06010540140602440010002c0c0141c0b4000d542c0128481e49400c480400c0c01c0d01a1240b40c9403610910404040c2c20010b004040e03000d04485441d1039507a2188a0825803100c1405d0b0f408101c804400006510480f80340c003c030084a0561500504006075600d51091002c6181f450921803690040020204188454800110b60031300d503070310541d051260f5504083c0c84400d0103480d0000400c5e080302420155120441c0c502a00e00c200b110700f450040029283c15460f03129078071030100780644480000c0c40f5101d294088400410002c07001d95503409160620039020242070107905118043c14010250000409040d80c003600d411104592660710f45a030305641d03a02140050410a040401000000b131b000600600000c0c01410104111403900b0300c104084401300406080c03c4c0751400146081010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 828699622 1250 828698372 828698389
    0x14010e12091305091f15090b030109120903050c0409110120060702030a03150807440f120a030903020f030a0e0306070302091003020702042a1d 63
    0x1604a502a5691107048000c51030482d0103540c101c00460030081441020741c0b0009205015440314600107010310050452007050303c1c2644000b0020b40050102070103030107d907038001c0d41a81d00080000620856070350703686a4846c440303107810010448201c400c0040c00024403180e00c6400c4100c1c0c0400048580f070360355404d0500351140d442e0400401c020b1401c041d141d00c5446143c9a0304102c100d43d101c0c0340600d8000e5980c1d00460701c550004c0d0804620400509103038045c031041d69010400380801d141010402e01e40038448641440e1720305c44110700c0551154008980014000c6550700c2d00a0068001346c4080c6012418490803d40c0d03841017808090020002090710414201c03494081440201811308074a00280944000854080002c4400c20140c00007054106900281d003600c000d5500c0c08810b508038050a03860540001e695000080031310b00c640c1c01040f2a174402400007442c869201d01c2480012941c0c0342400c42455030310303101101d0541007034900c2d071210103000e04031202c81035200100720b144 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 828700872 1250 828699622 828699643
    0xc061e030b0d170d0e2503020a050d0c0b0309010218011d04110702120105010f0b040e16111e0105100b040302040b01110f011e09030516050c150714010e 67
    0xd604003010402541400d80840e0342c0000060024080314008079081034842d0040110340d841c4a69503c12819103501d1b0039144000c40c0d030000d1038408034510f450140013030850306c0141201c088022100c01b28281710020083c50092050100044c0c503074801400304808814051030709410b100c0c0403500c0c1e44140300301032a07213100e44009850106440d00b124040041078068030100039800300b241d4a2440c82e02005511081c1240d2100303d000301041e03524001022644214061100388038018030001e401c106800080d40c62206540c41d1000144010070881814590508440e40100400c1c03da6001189002d00400d0f4010340c001803180c030b0061a21518149600c11444000e004640390600100319a0103401400c1e0004022070a680d100c9208088030f9000f03201ca072041003104545129500c881c2051480f5002e509c980c181ca6003460504003052802030712008503002c541032b03c140642880d282d01d40b850424442a0741c17103211500c813503207441e02e142450540c00344900e0b0f507850210002081980064400002d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 828702122 1250 828700872 828700883
    0x311030f060f060f0a2106050102030a03020903120403121806020a060b0312120a050a020f04030624060207090e010903021c0c0203061015030902030d05160c061e030b0d 74
    0x302c01d0304002007061401607200882102070046040717081c840e0441402c81da100c400d0304040c10b00300c0142d28200c003100ca29004890040c1d1041c440382440e1790080d4001c2c0300e02d000c024201ca0007140b81043c2c1010950140d0001c640b0150b065903410521030704101d52040703d803c0d40341108000c5003000d01c000d50320311000c04c01900c8243c65008903c100c3d1002d00100321a00180305040344c0e0381c180450400b140407800e07148480030324034040002d51b040301580700b41e41c0ea00f10818901483c161640e1a92409005203042c840314542000c00156402c0104c40e5102c001480c450b006030858a04c2d04200e41c08540d00b001d0b024402d030b418005942700082d03000c40c075107100c0300241c090100d006a0f02c00c4119200300403201e0094140c46594140300032400e02d9101d040480303c203e0b82020a02c82d01100480c02e603000b200009406500c00614007000324024006400303415840441c0d0712112409898801310b07a03003554000b001241003806000003440303840c1015070704180f447c02c0c1070060480010114004641c51b01c4007600 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 828703372 1250 828702122 828702139
    0x1202040e010902100f091203020c0111030922021b1605010908030406140f0406122301060f0e0306040b0f0705030405070b090d06022109010b091803041707060311030f06 74
    0x1701c90340610489000380c40320118000f4544614a00a907480904d81200c41c045411404a40c1c04198000100c50203910064032854403038050400c1082c5805202d40d400e5100c40d0280031001c0c0340a48035498041244c000747c018000c00c1010761554205444a030407403410000e2190303043c0101c284c00030407901150044c2c60302c1030fa40d5062030b00c158114018030403031030301c42070000800041c501c1d0b108080302c4050b040c405d0204030710f0120110100216801c440b41400030440d5030010030404d0300410310441c614100d0f00340007011a1050001070b003001c0d01221708885414181082c400b16102d1b0f40751484d0300c03640504102c0d02c0c500345034079803540d181803500c2526107400001079031080684409500031041c950041c0d096455801c0d802540500f400d240c9508007803460070f0f90020354039407814090b09254010161045241d03842d40d50800c000e0880e01c0745902140e100420000800364040b200341e03418040d80b40043e2035404d062002c01820341720101000d0340e821781e0a009100c10500c50345d00050700207208070359520 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 828704622 1250 828703372 828703397
    0x130e03070b04020f10021005070905011d01021e032a0a0b0c040b03010305102a03020702040b0306190f09120f030f020c100b04050103110d08040803041202040e01090210 74
    0x726005410651306400402c080019500c60303800003800138a02a4244085c8151398a46000725522141441082d002551113103c500c804400c8051040804806106480b0354400b07019440025001c02e1a5410803076000080d2031051a10340750321000031080351403060702e451004131041e0f50340e000c20a070090041c10b5000003041500049004550082000c10b240075269a524144542c64030003218603040c1060400718810f40d14040b4440340007000c400717000c04000307181440408170025004014202d070425a641c0788100c039580c00f0004a0f2240c1003071005128001601c1c0004000e448034100d601d03d010741040705010001e40143d82c9117603e804a482d108075412000c08088010300000c000000d030562000407102d100d01004200d41650380c1c03545409104100344c0c40284400c4400900c0041c2c400015407800314030070715007200c040c44420701455056003048e440382d5815003140c2c4268841c2d070764480c042c51a00c04508241c054414068030080007000100b0740ea40100e07000c008940b666100708007500b213001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 828705872 1250 828704622 828704629
    0xf18030705060a060303030e160b130519030c0e0408090f0103180606060906050414040b01020f12040e0606090a0b22120203070806070e01030b01050d051302130e03070b0402 76
    0x19080c0d9a04032046502d98100a078160700204140c1c042a40002c0c1000701404e5002c0300080d60a0341c0c044026444480c0c6850700d40910240d0308000d9103040d0308801d1050000d069a24842c00000e0094100d2542c507001b0700e985010002c20800f90b01c4808220210b40420011484880641e0210b1000396041006080903c0c0124000c5c00e000041c0350003880140366140c148005ca5000209440741ca46501007a6134031800103444074000c41c89a45070079604c40305071f01c040d401c094100302c645070018012541c3c0d07829850711460030300704503500900c41d03c00d0200d0100308100f80d0540b007030707003005007543c1461600f100039010588030700305e50095100d8410300040d9940b032003100249140025845d112040201500e4000d0001d08003101c0c40240c0c440e2080d29000315042c1004541d05000b89242d0301c40750b112000b020015800b038100c907a583c50600c44c082c41080d00c1c400240c05618402e002e00c5510080ca19400d10400c524800200301946030145403d0040c414410000304503400250809501a029501c030f2000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 828707122 1250 828705872 828705877
    0x1e0507120e04021306090b070b22141605060408060a0b0f0301020f031e01060915020a06060602030c120313230f03030708070e10030e010609051f0e0f1803 68
    0x200e5070440c0c0300041384142d405404181c034041d20380c00d81d07034090700c1c175038900d0712000901914074045c00d0b14400c0780104204680d10305019948400706103000381d041d43c00d40c4410890705c0d1946211402e50b0085031200c0c005614180c1c851002d002d08840241c1014180a030041d6a604000e0211034582e40e106114100c50f600c00c1c4140d41c02410080080d9500e00c100300300b0503415041943c4a080d03810b4100c0320885c09080940780503041c1c40e00c40c0e54003440341c0d16104084001c95811183c1d50294068001c005001c20300728000e0b64040c00c0c1d01d03002075036525074245000d03241a620001c90b05036218140b0920100310015544030000715007003c80d00c401201a480d40b00c03005c004070300101a0310301c58040c44c520001e501102851180c601070301e43c020a551017560560b00081500b800741d07404401c1860520242d4000d522400000149900010343c407502e40d4800402c480c802e890724030841550102060391429021440c401034550300540001d0b505000c81140c00406000d049600c0940170a43c0e151003000c0100306 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 828708372 1250 828707122 828707147
    0x1090c0c120c06052a1e180108060102120a03020903030d0f0c08010905011202060d0b09010311040f1a1203070506070320210a0b130c1e050712 63
    0x100034603484851500039081c1d0000e00740c01c40d0340504000005c0c2c21a00d1554948940703c00507051442912003901811696500841c5600080c085280300300c0c0c071900104014003034100d500c481841250450600150a5800c0201054115405074aa150001034404203a81d200e60041c1000743c0c0791018240060f00f5401100c50910030280340c44a11070010031181c112940034012500c07500081e98071260241c003620802d0181b26207a82007418014011308250008214100c0f0000001580c0703010040010400603007a4000e03030304280e9102c2444014030f42803241210841400000704403072070801c0c51100b00b908a420070703184140e04601d210480720000340101c2e00702e81d034400c00303950861810100140040c04502480141c1081045039800007510f500111541c03070296148100202c000384415806555005082003296901c90b00f801da07854890380800030401c144650080350102201800501081150599161503950b28040c00c140d281c10a0071100c03081d82010f02d180d10907140685c1511024040f54 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 828709622 1250 828708372 828708383
    0x190b0309010b0a290310051e04050903180d030302040308310b0d050a0f0903031a010905010818011805030717090f120a020411070b1b0301090c0c 64
    0x100300000d040041d4000c1ca9020011225550b500e82c844940c1c0c20340c021a2140c1e15580300d03191042d0344c90480f4807809903a020003a54881000241c031140410064684420321911028215184802c0d601c2c1c10302800303078494494002541040003401d40005154a8011554002ca00261704c030002d140c42038048802460300820010350380c02081c040f5054000450007007001d100c90849000c0c0001c07040c50740000803200d100c811a400e00424503044401004050b001d40b119664801110035180300b9070044c1041a1700070b4030000750b0b80c052042c070101d810b0702c0c0060460400400210500c050380c0c0284003550040141c03107615a1121a960b040c83c01812400080640005c0c504100710400c0700000c018805184910942e511001c00c444404280c0d015404c64035a02a40c000740b0b49031036003000e2103031001c00b403070400407645204000d4010804640c08000c4121300c040300040c180c814020f04d00d600343c2d0801604900d0072003500d00d00100245030700040c020b410b00542c490a20040c2c803881001202600c80d00031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 828710872 1250 828709622 828709627
    0x30711040603060e033103030e120f060412090b0d050720071802040806010e0915041416061407020f0612010e10030506071d1f02120306030703030f021207050a0201170402030c190b 79
    0x2118cc1d603848200d0302128802859a0401d06241c0301d20070b0041103c00ca0301c482070820403600d040c40042c1100400c20000c024212001003030082c1c10701400c0100c2038510020300741607820190741c20351040061120102140c0100810004943d00003004d07811503441060001e03031078907411440ca0601c1d1514910044046800045c001400714146c6283d448070308000885445245540c2000440d5415104120110700866000702402d80c2d21801818040c1c0b009040d250a0100100086c500c3c6d0070500ca0041d00840000040c00301d103001441460304112510030038808585543d40f05070395032200410034001c0040c0c02454440302007040f411121a04001003c04905440c80601c40c2400189569441c0c0184501c0d18441ea058031843c0490b4000c402c050040d00714181140c60a40e590040324003141708500c80d22000002c0d202c1c8001c0640101403150000d808401d00c2400018410311301c281c3c41d001c0c11400c07130090000607900055803604200041da40048412403034150000724082c035612495251500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 828712122 1250 828710872 828710893
    0xb1909020604120c15021e211317010902122811040911041d060402090c1e121006211814060c040305030711040603060e033103030e12 59
    0x1040181e0311804c00d1540100070300c01f101c0c01958450582c800a224450b01d003a0f007480c1c0c41900300007026901071030900d980c401c2e41d840c80c007081078504400007692140d544070718850440c6000c1d6400081101511b004220600090004449001c0360010944070100d030030600702c1c10804207400c44065140000c0080188200500700a4040c401090803144524070f0045681e01c000303070710030282e45400c80c032134002c20060b5200e90038030000c0c50008e004001501d00034401d4116800040c0c41118940d07402400060b12003110f00301d0f021707004102034903030228056200001e20003641e01403203c0e09145032012954002501d02d02c80b0310b004140c88070504584c22038010103001030182c00c2012404481109044412954800010b00071902903808003c1440c1c2041043c84007042545000d08544074008000156855581d5a400111810030824482c076410101e10303140311020f01220b203502220b6452510544450002810010304160300009090000508000d2116126440c0c40d4901072000012203540301003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 828713372 1250 828712122 828712127
    0x17030c030f0a02030c07031206050301090f05060c091005090d23060f16050328051501020705012312090304081c080403141201030b1909020604120c15 66
    0x110740540d403907140c000100e8070340006803003140e00c202988000340d81048840d9074100d4444030100d842d074075120344440f0007050715542803045240c007501c02c10f000c070ba23800b50901d000303818641c005104400004050060300d60b03170307140c2c1c2c0300750031413044585003d5590b0808180050501020144094042200c000e803150b1a0606c50421003179860122080318040d94614100d401d000d50102c4036040b001c4286900b007a0064007030030217180c22041d8074984500360a00301e0040201e40000314031131902c1070703100c40c20701c03a01c40c2e04400d50f0f031010082840607101090501c0700107806007a00300c10008a82c803280070001051400e003019a90380d400c03816134011341c509014144582d603800c103008080f50390142c10245209200110710780c481071038407915080c0d440d6072035441c05ea40341c103d40e40501000a03410030012200141d02d440740c6001e103209003030450036030034201078464416849500c80b0760fa1a1422004c0300260380d0b03c0b01031b00d08480049403a586100342520b0503655000c040ea10480c00b5000518155040d2074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 828714622 1250 828713372 828713377
    0x2b0c210f0201180c0506091c0302060f070f211e02190203040315050a241e08060408030705040503070306020702090a09081803030c0d0c050c0102030a0906080417030c 73
    0x1400780d0080c0508012003480810000c4a0300c0e0060010411110401c030600b0304001030000281c00034601c901103000a452141c0025480d101100142c10940410002c1c0a5200c5980c2c0c02192074505080c002405182c060801e8000300c40b090000f1003500c0c07107050500384ca604040b0440820345000300f030a525082d0400c0280d00704001800c41650300c41d010040c4a44000301b0342d822690000036803440b0050442ca42c000504000c0c208003400e076180c24011231070074220b600700d43d40450002c0709452a98900030f45006822182a280310261245190400c03002600085980d009074005001a540391100c03d030986092080380d00088e018001d0300000801e00c100d036406014404c0c0242e0300c1007100e0369030110b8401152808034005200d4101444030740c1284d0302c0395000b90502000030741128501003183c40061300d0505880c64842c00100c8840d55074041203000d100720213030300500303000450030803001550203031600c9054082c840c00c00090400050170300c00b950740355205040c00080307616500d0505011841056 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 828715872 1250 828714622 828714647
    0x906181d03030a0b180906060108191e0608010b01080711160e1b04120305091f0503010e0c09180907181d0309091f0308040b0a0e010e09070f09090e0703052b0c21 71
    0x1601c1cdc408001042d14042c09460800e0005035114490303551290305c00e4801581c0006500783c2ea00c546a0400311200a8032120780240074214000903070ba1424030943c682c00b0f40c0f001080f0a0341c80c13040c4420480e64054480e0b98044680c1810481c1d15034000401080d058100f101c40708041f0200307000d8940c0c11607086401141a00d074076946840e002e6480000d061414420078104a41000c040c9548001c01042c29803d2504400000240e403c90750740c0c0d0300d00c4010003c5080104882654594448240d0340b510308035410501420801341d070612102c440091561300c002400114070700e950000d00d104070003603011000c02443c0e0025442e51030780d450f01c00741201d6402c003038400e80220304188032000d03042d0701808410101d4480107084010640e240e07102265903000304450141480007860011170803070b02034003841185c0400b410040002c3c4c4c0c03460500a141030211004102c800030f040c0701c1d0614902545800c00c404000e03e0404c2c034590b14061912a035582d805014a01500d040c500400e40c036681d03c6250350403007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 828717122 1250 828715872 828715931
    0x50f0709051015020c0d060b04050c0a02010c0e06090f130203040302010605090f1b090301020903100e1905060f070e031501030b010906181d03030a0b18090606010819 73
    0x550303443d84500c0c0c91088a15035408050f031701492140003a4a4091307040c070303500c9110340e402141101c02c22011070156a0b0540f880ca0110b0400b0504007042e9a0912030849007881c2890860211134240010801910800da0828010004140a0308c004c0d100c4100c18000307606aa0300446d542d14040c14003d000380b9460094502c1500c0c040301251020140e00c031320f60700440001050442c424440707610441140c0c000d03041381d5010354003071003058010795052010078092000b41001003440c1195080003030411a4111703035281050050818000801c900007107459211a9440f4809070503182c5c0303c070a8440b03441c802d01030390341441480d0351120140c001ca284130781264807500400c2d240740d0725000710b0f0301a02c5450252442c1c12116120700480455241c0241109012701300081c0c004104081c0f10303d0035540202c80d82c1108030786641003d07031141008074401c2050b0b00c04d80280122814111135842e2114406041103040000e54130104041c8201003c00000c0fa00040d5010000c3c0501400312200d00250350104451 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 828718372 1250 828717122 828717151
    0x1c08040b310e060405100b0a020115091b1209020402030126030f0d1113080303090c0d0b0a0f0b061602010305060907020a1b0819140d0e010309050f070905 68
    0x1c481c4114000703058401c4007450101580c0c031a01404018070000340000b4000e1811000080d40c90132400051584551550020440c101078043e40c2e0184241e5a010070000c0307140090321100c440350168101c50703007111460a20030402e00310290b18050604424045c0d44140700100000d004407480c010808000ea02c0000c20490141c44803115469000c0e401c070310250312004110078408204154041c2d039000344800107440c10311041d0300c00c0300394003e401d4102201c50743c8000103015032101c041001902d17001c0200c174141107601e59580d40c1514154085c000d00455034403181321025110b50b83c2c0102210700009482a910b600517041c24000c0310030041426800700e46810301241c0f880c10404403041c403460254000709440c520903641c4251a4400c0000181c80c400380c1c00000c41c2031013003031003603032801c07070b8203001051300d00d030150074068040c0c040d50000341200c0d4004042e81e000580c000c60303410f406031024200000c0c0c207038440c00e00038208a1901c2c0019500e0140f16400700e20380240794400c60050039640502c1d103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 828719622 1250 828718372 828718447
    0x9060806130b1b0c0a030305040b0c090d1212091113140403080402030a051515090f01170703020418060615122c07180b1c08040b 57
    0x140308403111001500d40115000060443d40712504289503d1955105080ca0100701d41905030500008020407400030380c17560700388002c0c80b4140700b14036006043c104071503103483d250200241c112000858010203480c0a221800c40c0c16003e08000542c44502d0138041c0460030161408803510112030021754400c3c2c000d2507114224035118460040300304d00c40351a014031380c3ca07591000d444101004104991500c1520f18110000b1424005c043c058070a40300c6c00c001030309010142c131000105120b6147c0c090f641da50300b0402a980401502c6044031688030041480c41c2c0b0382d80f911030070709000360806504241032081c0c0b513006040810100c0115402403804001c0c56440b481d420361000c42860144001841c41ca150401c004100da01c450401250410802c0c2d44540c41c9002e0303003461210b00d40b2585990030140041122242054070300540781c00c030b088100004400107002807141c000301000c1000700c10302407040604001c3d418044070064000f4003022612421070a0402a8241800d8105002c994254540b44c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 828720872 1250 828719622 828719641
    0x3050c090a03022404091a010806090a2c070e1e011a070c03030c03030c050a0c15230115030b06030a02070c05060301300f08030405010b060409060806 66
    0x12410004001c00903032009145408018119481480076802e00b40d81c90201d2002c45841002800141119030000c42ea1001400d0499074045440c02814140624101000295600c4528455001102c000009034001d0401840310442c140400070800650720159800d500c0c0e600012403a049030787e0f01005658603540d03590030149901090303d0041c4200307030500041c01800141c460740019880208a000d05281c0c60340c0f01d4403410402c41c0d01c00d40102d0702203074005090603403602a02103100720f181802884c5c01d91409000303003040c052000141c000089950f404059072069042403000e03600f44c81b1003911741b10b0304280040b0151401e200382c000759202580b105080c98000d00074054954401400d05085584900c440c10280d405050b04072403820503014080b0712030b41e5a00c05140038144008404082e02602520010340012907444c249020322450301e0300000800801c440901958080340464036903d41d858280d005d06600d041d100e034440e90105000c5004a21944032004851442c021110715032607201d041d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 828722122 1250 828720872 828720877
    0x9020c0f060921030c09030d09031a01030203030d11120a23090c22091b0503030306090109021605010c0e0a061e050f04030203011109031c021b010e130c03050c 70
    0x10f2010104651000e40040f40850f00510390040398000b81ca8a41040580064100041e240c041008500c1c10702c01070082c044650028004080703020000401c41d4110703000260340340a0560410106501c3e02c0444503007908140a40f01091000d01c80e51001d420300181000c042c0c17200a410325145d003a400c588143c14508403071303094007600b0b290019050481c004011312640c40c0301d92204481d6041521a100c134486000c0c400c60907100d000e4a00d1a01c40b480d80b14010a840c1441c1d400380384280d000b03000b40001643e403000c40030f0450f00c5410005a5540030342042e594152000c5001a1581d46815405100c20b60031104584c12044122824225280c40743c1080c0c0b1400356410598900742700b01e00203804854001c00007071201000b40500381d401c1954980c006425a4042d400a4018000104c2c2d41e207424102000a040000002008007010504d1400d00035035802160340110f4030030761076103a480c3c5a6405614001c566900c00751a83c0400c07440300c00d801c13000e07103c48e600c2840080d16080015a012144a0a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 828723372 1250 828722122 828722143
    0x509130b0a0b030c06070c060e15120a0b10021203040212060115030b0619080a02131403280303090f060e2406030307060207080d0903021609020901050d0f0609020c0f0609 75
    0x2a47c0740701810108111660400072207096000350080002103461604040035020040710040002110300d040d07140c02082c0c1e00c0480b170203400740d10144070341607440740c0106eaa0940301070000150ba84956a40c000182030445503003d061942c01100e0010641700e85060030b0310103c15803500e0a00a8600e803100340459840f07020046084c4540d09010111230511444119030404d42c010005800c00040e11115150f85c2541d9200c4101150496180c40083c01c00f07006040148120780005c1e900301d910b2100c000c00c02110003000a04056440d1240030412071180b29100289800003001c004a60f00c2c081030507501c0703040740c081046906082d80c480b04603907610001c0c18855007024001e14205280c5654581c042e422014013111400c60500c00c90f00441d080f1b1040040c2140a40d00804d5406195000c6851000198104401d401d004010621a40c0d8020301241c1550f080140001140080c8413801002041c194000b886d680c0d00005180c94200c00015610b048010444c0a580c4151621404039580c1d61311800b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 828724622 1250 828723372 828723383
    0xd020417030a260a0504050a08041e05301002030c04060e3a1a071202120c09040b030115051905030a0602091f090e01050d0302070509130b0a0b030c0607 67
    0x16a07001e55504021b0b0030a1286003100c91484680e5120034081d0043c2e0800c0e52044219000d28a03a00b01d204441d400a1400752610031868000c00c07400903048035140b4840803001041001026144410001c80c6005207003840c0454590828048000b06613000f80700301d800150132080b41d505076107840d088907405945586004050800d000c1d01a1a40c800c03802c0741a40008103007600c4101180002034014880130007501006440d10f40302502801c45a48201e010826520601142d60143c450401641d000725000c206140c54100540c0010094055160080e4165080c0350306810701d503030301075400006d44d8800c0718469071044101800ea2040c615901c102036260b4841e86c00d41c0082001640180784800000c2c11602c2003841050000ea003c6601d601d0020029040c4c070b104005441041c090716001d4030302211420082481d545000707598840c42d0044e203100d11500000f117107101d01200d010304081d90b8041d00d030f03000902e40080e40900030159510b540303000780552605200585040d0302281d4100d940039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 828725872 1250 828724622 828724697
    0x60901022503050601080102071b0807140a1d01090f0c0801031506080307030203090117070c03081012050f160605030f2d0a0b030309060a050d020417030a 68
    0x1003400c44903078144490088198052100031000c504103204a0f4081d104c07140000d0380c1c59409150892110881c0100d43da0303100302b400e005010705c40d00460620110b465520300310f80f0950860000910500d01c5030310258000500d030141203407001010310700a040780c2d5039003010001c08111403086c2040e10303504041c4000080b405001880050f4034910101010086103800041e05500e5000c440d01d19400890160b000da84046083c10007983e10220301c08104e414207040341800e0412600141140300000c0d40142032001400009440c4621128500014500384503a040003030951f040964403a0181c400070b40701c0b4064404180c007480d07031040f5524121582d650b1210b24542e19032a039000020405001200e0080103d400803004103a400c52100000d071000d8484201030500400c0d5008a82c1c8100c41240603410038405840140d44c1d540644c1c1c130b02c900508115a42e28001c90390a40280b103142c10180410550213644180c01310000302a11554400341c5454525031a81d107441701100040303c441c42e07881d0850 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 828727122 1250 828725872 828725893
    0x10e0d23070b0f010f05010c020d1103061504060807270e01020a080105030c0f22110c03070302120c07090e10061418040c1e030f15060506090102 64
    0x80250a100ea14440d0618500100c01000e49546034429036040c0e4001144030b0070302035032090031403515004150b04c2c0300320000d02e0b03d8600041c05004803400c0203031140d0007118000062014052850152003001420b40700e983c41c04103c008501900003d95600992501c04041032034040000e107081624140615259078013201592184600f0301c40c40d901030416100c070350400d0740c21000d001504030343c0c03001e1311410425030426050514252802400500c54180500007030281c2c1c0700ca0200016241d428403040d03001400c4c8000d82000b5121112403c0c01d10900000c240741400c1000c00070300b1900e0300c070360700f65a004148048420340b03901460803280c82d55040b102c410040d0030001d9010203460038483c003e440350b8504e951902400c6448580c80b660500c1e51385042c0146900e4a4000c10300035040c5592800042d0520351200d2000301118001e440c0803034202c00720a05a4042401200001c690100511420780403070f14040c0c05550311790b1200d428543c00c10703002140903e40001554090034041e402070088a81 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 828728372 1250 828727122 828727127
    0x8100905071a130e0105152a120f0d18050705130e030c1b0414061003020405100f0807090e0f100b0a09150813120e120a030809010e0d 59
    0x7500416240b0010003044601524200144009220071441ea604541c940010b100580038030b00c4140c4c807911000c0040401c120002c01e15090860485803c40004400b0701c2c030300030301c0c040413001d11800c0c0c2c64002c2001c4564044060082078941c00c2ca0302c00307220080c0740c51424256000d01c0c000080082d0414101448642080d040342d1000300400d00000c01c404038404292411039001000402c40d85d00300a009a402801810401d00001804e650403c2206000308450301001c5025003c680b09641002810184921030f030150780181c80c00420050901143c0c0e0800b404000c0d61820307080216080780000750010740070301ca0303c034126540c2c0e801104543e6607020900340d10034001094034034806d2a0860110304012202d002d00b81081003921549007050410440c815030180882801e030410000004111644418401003540c09a000311000b43c5410a101c0c19200141f96424941e0824610003242d403040c0400554610175501a8840c2c14260300c0781890203090f1071403180c80c40d940b0ba1005d480019500d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 828729622 1250 828728372 828728399
    0x10b0a0e04061208070308010b1602010e0d1707050708150408070f0c120b010f06141c1a01030f090309060c050c03010507050a080108070302030c15090d0305040810090507 75
    0x1100078400148141c5494480034248001c80c01900c4015000c038041c0c2c100341c1c1014816014110710b07031243e4144540c030400500c106541420080c1044115410400c20351504103460644c15402144941c5600400d2000d50454001150907170b024420220b0004e9070342c2c00400c1c1c01030001c01521000001d070740c968803010820791103448200c4444140070103000c0440c00c0051414090850713010304000c80050b508080d41c0810040e0007400300d808070640100040c9070440ea142e80303400b00e030426079615049246458060780300c1000403a0700441c107082c001e102c44050030000822581090300c08010616501c202e03c011142e5100700140414241c1006000d40c902504808081d903102d80103c0380f1080c2204c011900b5100d081c1d87c0034002c41c401040e10000b1a8003c15110301405d01d08004000d110b103542c00003036803014000031032409482d602c060200c01012480c202c5000c0000070b030a540300c20305a89401015035100c2c5c850701890303000d0328107400030b085003034041c5041240e000001842c1080c00d103a106120f50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 828730872 1250 828729622 828729647
    0x30c2406130203130c1707061b3306030b0a1811030127021206074a0102160e0a020f0c25054603050a0614010b0a 50
    0x1400c3e134030100c000041c0107804200240080c180c501c1201a2814036007842c01c1c41e02c0d0004402c2c410840580000004803400e40e000c0c081d00b22a04599040d5041002c00200131603c51648a509072404424403e40d01a080001101e10444418405640300b80381c110403143d02500446070380e000080c0c1080440c08200c881854205d00400000c0c000d503c00041105400d01c1005040820b20405895820341c606400c601c203006a0902c0904082c0c81c126400a24144c202c20b910700c20703000d4411513040c1c090000130151040c00e04509002c220744031275110400780329640c0040c050041c441e0b01d12484002c030b101c0301d5040898074a0741c8500096220303c95000065003040740203101c100014410f81103880b1040001070101d4007882808203840030350304000c0301030b400d142e0003080c0184085c43e00000c604041c144030b00a05c00040401400d013240703000d0340064000c40c14101c01f1000d04109808400c0c40004144002d140c0d21608003040800c040780c104801544091040b010b159006000d2203050b24054021140c0d0b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 828732122 1250 828730872 828730891
    0x40609060209060424050c191a0f19060b090405041104051e0a050412110f0303010f09061202030d081305160501032a0f02010905030c2406130203 64
    0x20b00050340040740090b0030a40c01500c081c48290a01e0002d040103540c1d5490080c01454a185030001010001e541d0300010070b9140340380c0140501c0101030001c010784d0030000086512800c13005040000d242040d09500381d45c1c403114400610400c80340340d00d107841501c04940851000c10300345242402007000030b00d0000c00960703121140348a0781443d5521849141d10601c1e020f488040884120b2500c0d2980d004020726500d000340c0760030240000310f240c0211660444c1d05a28112540245803a11306082080340034841d8a14840030001081c40c165400d500000c1d50000c0d03a0402a01d9035400c01d68401c15100d080194040e04080c0810a0171403003455401d500c95180c92140008001d2a0380e035914202c0c803508032080031000080c09000344e6a05000340d4140910319130b855840700c1c10360f24418040310140b4940c1b01c148004841c10f09a03d034001c0d0440c01c0e01940000c00d8030380b14024040c00684900300c2190b040c3c540d554501c481005510101c0c09030307010301005005800c070b404520310030100940c0301510b505030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 828733372 1250 828732122 828732127
    0xf01060c15050901021b010b0105030a0906091a1f0e010b0f0c12250c090507030908030a0515010f05040b1c05090c130605011b1a0103030c03091505030406090602 71
    0x40e504803405043e000f90701c1c41c03000580d00c804440c2407152081c4e00071400c0e9042d07410892461000c1c2e92102c02d07a60404d0304c080c00000e400c0038074a8482c0040c40072081c01001c82090b00048000c4a10b0440e11a00c120b02200c0f4100f6640ca1030140740c40810a1070060001940c24400141f11501103103016149051961056620b0301c2c44040c040752400707012000c144d8140c4400694170a4040b0650b0008078100700045582400b0340d45903850005090f15801510803c59545e000140110310a80102c680c180c0c20080c015501e06146c41e2000c0a080c007203945c002203054040c0400100c2d449541d03030445071003856a0710350404d42085a112016844105299001f1158101030b80b103641003441018010306170100202212040002070014030030388c40d260031084515003d410801a40c12800151000b000c58030103241d00c445515100a501003154410300d1694503c40006c0209504503142d18141c1e030280d11803404080c0ea45c4400c42d038402d0400c15600c00640c003800440d002401c43c1d000045580c5c4506005030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 828734622 1250 828733372 828733403
    0x5030604150c11063d0f050a0b0703080901111206040605061c0911063105030d182601111603080712110a030b0405040b0c0c0309030307200301050f01060c 68
    0x10300c440d1007891a0780c1c101290503410054034001141402c02840d0580313070324448c10714102c0a08490701510038084c00b4004a04001364800d0020b501240c1810940c03c42c0a85070550300c005040c42d40ea081307039400d01139858801c02144ea46803c80c181d40d1400c40f01c5500199030b40c280b2030080d0146c00c8c0310700c04464042140d540300380c0961301d50000e46811401c4412004002a100030355200f140426a20406030345403c04040c0311a03280810003568078102401c001c1211034206084005c03214080c0c2c000054256100d5480824514010814400416007002806240c02d16849180144240c4160b441e0001105004500203030007803c0007507120300c01d0308003c2905082c24500805580354030945142c017900001e200c44000703400d8070944040000030f9808000ca8646640d03008114a40a00038050b805804548040744000c100116403408101405494580303041e843e0210506040c014001344100c01c12812034668141485500c0c840c21142006001603440c15200b55213030800c02c40c050710f00f0b284c85942d10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 828735872 1250 828734622 828734701
    0x15120c0a05193b01030201021b190b1e0f03010608070c060501080c03190521040816061407050703060b0f09010f0f08030414010f0905030604150c1106 66
    0x9626040440000e40c04500c0078250f1020958100200510b000c5014001400940d900082c1c6031742403290010018100423580002070040c11507243d0385e1107030304031100380403c003440c8a0f07000d81328500d40d020b10814450b074034000030f003000c3c0a1200280d9010b0000e000400013030748a00041d82d0000d0250030201c08840301a1910001d917042600040d411342c0c40807017483c039242410401ca10004040c0c2e002071058101c0f603078400b526115445030342522101030b44a140d80c009166030444004000c0042100d01c02d00c0d80030414401c0303041601c00c1401241d145250403a800001400300e4441a80c00702c080c08450341180c0c0c0d40070081003404031098000740c4046c81800c09803140304915000c0c060010980071568509034491000803850b4008091940041c030082014030050606030b06041d03001d0a1004802c01d0900040700d110001e0761000b9458420b1a040c0001d114660700c1000d281c000485082c8459144004203070743c0c084810b501911154001720000b081105001d001d150018058051b4000009502d10b04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 828737122 1250 828735872 828735899
    0x4050402012001090b0a1514220b0415050d03080a1104030303050118020c0607080903120a0b0a050f0a03231f0c0e0108040602070302011415120c0a0519 67
    0x74aa549550400070b000381c0721035403a4016800c1405210003540f00d10f900b95280d41f1841660000d122100c840d10f825034401c80d011b000c0300500d0b040345180c0b61000c0703c414058111014041e010320308c2e040b26111003141e441c200d2025180d018050b0002e03e20f6a6800f111b00f80f000500d00e07105581e40e2131202d14989a1000100001c60003079501044950516400c40100c2d140e01484201c139070b10400580a4824001c903c0503807040d11420040c549954840301c0500310b2041c0c0c1d000034507a0352070314100034407152181d000b000005420b840801c5000c2d140c109008104055451a56211805040810016080d0002501409022800e1303081e4050f908035902c1c0340c50b0554402083d9454541e1117000c401c055481018042080e034500592020b4090b030000c0d2147d503000d0800761101e5000030710b00b01414000d4002c01081c004524000c00a45802c408910040640009c040d21503540c0e044410002d800c0018600101c02c0d000f080342821a1605041080e140003074282d5001030b181006000503070740c1e00d2240 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 828738372 1250 828737122 828737177
    0x110f1023180108060406140d050f0304090c1205010e130c0305030703090303110604030f031a09150114250c08031c0b0603040302060604051e0112052107020405040201 73
    0x140404100a04070016000724401444280103602d010003c102c120f205201d0802030010550f03482c0d01c2044281460350400800b1a40404244800a0b00140d1004640e0050402e40d95503999481e49060340b030703002c0065038020301c1041c012980400110f410265030160901c03440788907100c11202d031703503495403902d0443c2c110300c00660124034160401c10a0640080e84110f01140b21000f4208916147c1d03006002003144483e05c4c020541d9070500100d024050000030484280c0c0140000d41c280380210144101c4500c0c1004035001408610300d483c8804200415101e40020504072800c00080c00c60f105a5502c440c000c05840d15a02990000f8605d03009000400300c140d01350301448190320b24445c815043e03400394004c084c02010704004000c082640410250b070044012034010855464008565a02c045041c0030705d509200f4050002801040a80c901c0e949a0300c1407081c0c40c071038403525483d1009000012500b284a1900300501e00040ca010340c04258001e20504001d808140350580100c0061314a00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 828739622 1250 828738372 828738397
    0xb1905090607090602120a0c030905130e0f070f0e070311030a05011d0106050a140d0606110106060207030305190210061220010903020d0501090b0f04110f1023 70
    0xc140004503903c0741c9881c0c041c00050006220040041c00030748164070505014008105802e6080c0c01003506c115412402040010440a404c5610040c150010080408600458800e98940305c0450310041055005c4615942845030380c64501600d141700d05500070b1100c01010f40d980180e4205500c02c001542c02900c800000141940c180240b00780c51721382101070955900c0380d240c0100a07140e400300860b1100300f51454030705401700702c0480740e030228010b40004141c5036040c880c01041107903020541040d030b012400024800030b55900d4060742ca48180c0c0c04042c000580800607002440c03031058903160745107031601c1216145014035043d0012074005801160741c0c0e10760381104006204102a001d050012903138200b803000300c2c500c030010740000703d01c2c40000d0040c1200100101413100070341c8041c0216801c05109450307444d010780c00d121140400c980480307180b030000da9004c0d06400d100541a000c000081c0038ac1c504094002c000342d810160b100400711003140421814030610840d00098188403100380c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 828740872 1250 828739622 828739633
    0x80709050c090a150206060303030f01051c0236090303010b031306090311060709290904020d1b020102090102030904051f03060c0906080402030a0b04150204080303011814040b190509 80
    0x80344c0c02403c01d140601440c1c8203a200b407041c000b1075510b4807072141c11100215100245d601000e0a40780d28001c10050113903010805484140300c0386000c2410b0f1290b83d10501c0203015809030117060005803042500c1070f4444e0761045c801485944482001960000031001140c915000c09954503000c4d42c40156041f0300042c2100f03000b11090104101054021030f480c101086180c4c01c0070451507108030034144081c0c203101a00c81c500f000b0389000049404051000d00705540d52041c5045040c09032140622558080809010044d050f500c1031080c8d80680c1d0f0141c1c0030f03610300041001044081d01003d40405a82841c01250501c148880381c6002d0085200c2c1e90f0228507101c803200c014020540302c3c0c0c00042070011641c20000140d50100340d607860164800c0d0201d600d40c9a0342401540ea070140d8042c41c03645880024080b4421300004041c50484103100e00310014a0400c3e17034504181d40cac00506407100000c002e404500098882142103500c810400e40710f40641e130f0103400203800d03104141e803001c001e60400e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 828742122 1250 828740872 828740909
    0x3090609060f28030203040b040213022115090f042d03030f05091612051c2d0e0f013c0c02130e210919080709050c090a 53
    0x501c90f54410121181c1801c40c1146840d03103c0315161100100028400c000406e076202c6070b41101e0b815035003485a0056500c8038441100b1040c25804400d407070440300384420014500440c035100040354400e0034035000d05100e07500c495440803481c0200302c00030400010550102601ea001d0026000c440a001c0d68000c1071855450b4000402c60b100a04160b1954108003003900340126100042d10840f400d0020171003581c000760601c0c60a0400d414a4415001d629403400c3c6a010b50003075248508228188510881c104110060002020101101c0022488500c22503840c1d240410417024600c00c1814140001c404800e54900311100c403c0195650014100c50000354030000104110440d115060510001384140c0004c0e00d043c004030444039445455001300306120f01e007405840b1000500402e4941c0485105080c25030a401c0715003064040ca01c04c50082600b1512a40f25804660b00d110240c0781490070140350f0009020001c00010b0f814100304003121058691014040003009240000d041d083c10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 828743372 1250 828742122 828742177
    0x10212040515160914030f0703030801080d050a09051207211a01060503060d1113050405010f05060a30050304060f210522080406031d03090609060f 65
    0x10090201c141c149440302c2c842c03030104d4210181809075000c50000450107400d40c00001e14200c40005003142c00d02449500108254200402a050b40d0901059607200c140c030b50f400b10b642e401000c19200016220020401c094144054162580b9506006950802d5210a11700c5000d0f105150151201c01e05c3c080f0708400d0151442e1315007106038079407440d000c840d4580400103100c0e000140c0b0651145400009020411000c0b00c01d44291882c050403a44026480c0001c2c0b100512044406440a500f0041c22503001c960510405210310f40080c01e00100d14144449500c040313000900c070199541291a019aa40602d40c056000451140d001541d80f541014002010b4848812004042c420045003070132003a004100b2001036070160300c400299030f94441c0954000741c40d2001e03031030000b9a500100c800500c48220000c00c10303165280c40500100d04e050082000c500304400217449135400c10310040c601d0746400d030000c1298800c024105420321405070602d01e00d99008003084490074041d224009403421 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 828744622 1250 828743372 828743413
    0xb0c101104080c0306090d0806190b1c050f2a0415030c0512061504030b1303030506030a020915060f0f07050712150b040f02040e040203160305071401020102120405 72
    0x110913006011300f400d114510321b03030790498105081c003440f00080000741d55489040510f41c02e4820b18000a0800d5901d80d020512039100b03484001e81c0002c400346c4070013590340c02d019880c0a1103201c00480d42079681d820540103440d2000048003c1074644011500c451900c110161014000b42d10861460400e1503030040c085502142c0103400340901030103213412007100712010590101c0706031100c0e50f0110070098288454452508020210150081401112480079603c00f003880e00c0f90324104001c0c0c540c1c40030190f5460702500300a5003e00d074600000c0441414100d4440300b5a400f9181500b040700040320580640c120ba02d80215005000c50110140402044078000600904400c00d85140b81d5841e610301c403012420700720b0025034544043c01380d0383e01d940e40b00803000303007030080300710b4035183c03104159044d00b082600c069109200c0c1280211807203200b0390456045a601c00010404070b4a0007480e211507215006003141955820f004101f01c811055103200e100d90b00c81c50140c042c0003010082041c518 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 828745872 1250 828744622 828744643
    0x150a0b120109050613020f0403080a05030f0f09250503120a031a06040909031202041710020a0f08100e0a0506040c020c0112020721050304200a0b0c10110408 69
    0x881c105001c0c8403031384e2944c841010829090502c00340e901e8507013150741141445143d00081003580c00068405a1903407040c061801a000c1030501c10f1039494444c2001a038146c15210300744150031250f103c181c80481c6038030010104000b50300010704181d564000070305090407c0c2d1219001d92000801045040c2e15100b81003540c80010040005510010085030050146001e030b01c3e0460340c2ca481181c285130141c40c00c1d4640c1d41a8446c02c1d07540715114100000f01601c10241c0812500c00d9004800b1114010700a803030242e0540d640310034000c81680b20403614540b020b400c0c81d80c85102c1900c04514021640c907500d02c00c0d011000e0109032030409806100868200050705000c5401404c441c42c0b45a81c041001804103503281e40158440c089800e008034503109400300c015190043c085540c00503074000f0091445640907594401c40381c07401044000706081c040884903808000390a0901544101402030281040c2d4201102c02c1600e164a148044541c9501c002c4180e00300410208a660b800308034000a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 828747122 1250 828745872 828745889
    0x906140702010e060703021b06010602070f05150708031003050102191403070c080309010e030706150b03130b0703090f030801290f0d020c030a090f050f01080609150a0b1201 76
    0x161540e40c1003c0c0d2190009403403007081580004000c560000f20100303120040f8086402d9500f6540c0d100e5010b55604401d00c140742030810b490000041900d05442d41d440745e00e040040161404885640700351407a400280081c40c80340000700080301050003403010b086920620160b41c04420750004010740304580200c240e42e800c031000c004020341c180c0e010100c403003c164004519912511201c0a060251910500c1c1240c00e00c0081070308801e20025810140c60108051040c082c9a41c6800c00700d000c2d44422141000b0740ea029150080000f0107503202254003411510340050440c14513519843c28001d1890305900040740940103004400d000076680c241501183c02e08008030200034495455806aa400031141000214506c600d415158045600440800301540d5407503085290242c43c000250243c0c01841200c80030109003410948c0040d43d541038141c442000c10b6891000304030691100401c0345912000341c00c008a5a625821030715000381045213040c945540441d041110f00c03050581c403501c0e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 828748372 1250 828747122 828747131
    0x40f02040501090c0c12110a0501060f0501050426010b12030c010f0b0d030e0a0b040605030a051018051003020406060903060b030312010302090a02040b1c4506090614070201 76
    0x11312503000759400109940c403407034113403100399820020f540e140c1c8003055170600b40c01071a844404008042d0301c00f00c10b44110b030681281d56a102c07001140d00e8040c44c0500502200204410140101d0860442601e02074003030010403826001e401081c2c904040075404800d039400071503038181420080c0030708406010072001c01c21241042e03c00095442116000c040d007803100640d00c01507e034030341c4a082d00141c03402c1d011140d41e0360713540d150040159100711603040141c0d2030440800e50900c2048200720441700c21000c802445005046001c0c01400050001c01c10f00510500020042e180c0b0302500e00102820f4039152902403541c20702c0002d65152400851007a002000f03c107201c1003401d01e51505490301034884141c107559000600000b031003903800c215440e02c804214541c205c00005110b142c8000c0c6084284104851088415000e0851140d09685604101c200407021500e440d0411a910b0410300c110742200d03004d4581400302d0310720003019980c06880d155851420650385122a4114405200820 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 828749622 1250 828748372 828748391
    0x506030109030828050405030403021005030f07120f0c02011b0e0a0603180f050c15070b0703020307050706060914060a1d060103021b0a0c09150911070803040f0204050109 75
    0x3d04030440200400041c0704250703030304048080d29180034504600b40000400040c01c2c81c4c101a40e9a4000b48400c81c407c00c2c00903070301da07002c43c0f044007501c0c081d1005203000b640383d80b03503940185c60014805c84000c6040d40d4400001c003008410740100020304030142c000080c0c03851105003503030200382007000c60000c0c40300d04402d6144640301c120605046a42034600050628003048030716064600b0308070081e202510905c1480180100810070070b213401c0084a07045032100d980402040c15000e030f000c0141c80c4011003000186968001e4004560214841c82c25a103031200c1075a807a02110059044030b25050b0b507820314042c400000c500d0340380c0c1003801140e034280482c0c0350500e48000c1501a500030002a08a100441c0d4164013135016510b01c1003100c0407000340e180c480017542e135851040c40c5040e182d503040581c0000d902082d62280100e081c40444200c0b0103103060146400c082c1030b40d40100355074400c3c1000702001084451000d10300940c030a601c0343d08081e600380100400c0e92010703040390144500d03124458 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 828750872 1250 828749622 828749627
    0xe030c0310050a0908030406061508190b0102100c05040e060d020901060302212a0c0a020f150408060a0b040c0806190302031002070203011a010516080d06030f0501050603010903 78
    0x80ca000d000e0800c001c510b960300d0401c0340c8094140c80c14020716000010040c40104005a003001c003e542030f0f402402e40e40000048202e03030300070081e103404400100c801d40703c0050200c44d8106032040c4c18180121413107071042001440845a5400b01c1c20002040070800740840c880d800412504004221215004c641080c0c00040f5050810700c24036050660008000c3c01c04010080c40211550485a480d019483c0400c0c011161429052490b003041e60780070280c5c000100d00c5000d603903081113071f00d0003800820010703030910000210300a071881d40f01d050800140d0100400c0c034000d00141200c030018040c94204060000c040e1105000f00030701c03c4d410850b9080d607040d4041515640417404a454481140039101f00e82510721184d00040d4060140e6080d100f01190b85400611881d031080d4005c011040403c030702e0300d070125009180030b8005801000500c41d0709a0240d200513903180956003440c41e0148520f4414204c43c4198001ca4200e51244190710034800d00384500342d071001040c2c00a2000c1c0c00c02d540c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 828752122 1250 828750872 828750883
    0x6030209130515130213090201020d0809070605071112010e15040302100b0607020909010b0123030f0415090f0210030510030210050c010f051f06020312040204090b0a05070e030c03 79
    0x5460320341402e20004041c4c4010250407000303660082e05c1d80c0c8498820392610400713000807100581c05445064441542e031441050000d10a000b058081c4c2401814200100c40540c0300c10420b5400712590117240c600d6030784120000035260404000012002c20303140c656414040c48a8904010880c0300040002094010540700b280d0311072500c0025588010800140c200d01039500080d400c113204608100809030f056200e801040e07000d80300c0c108008140c21001800c2402c0d0b080e1303000f07119401e0022803030b4194400401500244649581c101391401d10050b0740c100c42502c101035400c455446000c0081d0700b815031002e10802d000b840c0c180030341d140a40c5200c4211a080c407000340288c3e890000080c0302c500c6130741903a4030002c0003030090107442d5100d403c0170094003060b2900d0f0340c50300020000c00b03088840010800b0448015801540c2080340c0d4442d54600c460700200701361f800507240c440440004980c000114855192004009002d08150b04014500c040c10044540681d011400c1500303e5a00042d2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 828753372 1250 828752122 828752143
    0x211514030d050c061b0f210a090f0b0408071403190512072708010906060504062102060702090901020307180819050c121b090c0d09140d03060302091305 67
    0x1000d010200032051185c40520552004142c3c001c4041040440740d16025040c0b201c074000800c0c1c258403a181c150f00c2104a9141c590b000f401e0b040c05440742c200207030309007007240d61043c01000700760b0904490b51070b0710007810b030094088601c903003000407401c034028000c00c003055a441e0702d072801e40c1c100f041c4040c5101071194003625071400c0c0301411502407810001e901c07038015a00381c400303203100d80d03641c1e10204039020f000030070000c48145050402c04521410103200b16000c5400000da8410400c010440c0703001c0b0415550001e03030b00514200688005a1111007038079000d681d1210005a8a241c880c034000c250710f20008010102c540501d40c10000c010000503030b01888650840015001c441078504a0315100d60b035001c4503004144448600303015100812404900d40f01100c40c0841c9030120010408045002c5502002c0120244405200700d91190302c10709035148543c848400421040b13049628103c00e03c205080004e1b2a104107000310305242d20800d42202e08802c2c0c0c1c080c5e110451740c1ea5511007884a1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 828754622 1250 828753372 828753391
    0xc040b073206160918150e041406010f051207091109190609121104060e01080d021911150c031b0d211514030d050c06 52
    0x2248401c0c4400c0058000303180e940c01500850074001240206510030500380660414007402c2c00048188035290f002c416032041d40d41d07405441c6820f15103440350303491604045050540d907910a0805003100c0d150000c001d80450f6098000c5450a4601034085964215502d14070b90000c00041082d94050085807040d5041152442942c070401c54890b03142036040d600c406002070a01e2880c2c0f0000c20032030014134031004207071240b4000d890400d40c030016180c5c413403250200080c000a0100140e02031400110005071044808000d54961200007a00359911500054440c8400c0c0c40100b040c0707a0200034048004040c2e00140c48090280c002005600307840000141c203c030030911840f502d03a07030303403680808914441e03507401d40c1c4607064080540d949030021241c1d0840040c080110381103c0d940091a85800c021582d60f8900c404200301855a040d4001c00c0880c0c621510b03201c00048004640c11030501800750b20304030700300c54204181018544080460a9030031f000e01003246840908011491a07031081044 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 828755872 1250 828754622 828754627
    0x10e0d17090303120402030c0d0b060d030c080a0905011e02120d0b092d0105130c1806020a150c05030a0504030c02150a110d1227290c040b 61
    0x1500c1015291056120190b414080020450b03e00e070041c030b85090080c1d0007503003180c5a190705202802030400d5009000b9064128080025859291118140e5800d41c0f0903e40840c00f4543d940c0c50380155041805444003185c1e0850342840740d940d02c0194900c045010f42030841c40b4800b0224041d40318000140400020b40c1c00184541c5141e0042e00704480c6d0702c5002d42050154a0182056040b418201030b03503100502c60b9056200b4054608040c16040e038030020903200e068080c0c044d2010041c80000340d84402d2003071100001103c0285664400300a0007160003920360300d94a85000c00a08103075544284546182030100c81e440c0798007400b80c2e035101465180c0010306485a003415200c151048200a610401c4141c840f4060100707040600038000903925008802c0c1c68895103183c07202000c61160001800e5120900c00c03100c1c240d0402c1c40c80030b56001503168103d5281c52a080740310a400d00a4552a500000083d9400b445044030f5072402c0c1203203805141401e010005407120301c00d5200d00701b40741101 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 828757122 1250 828755872 828755903
    0x1002041404020d1404150e12091306090513301d04020f1c090201080613061e1a0301050105070209040221070f0e0405030406111f0b0a05010e0d 63
    0x640e440394180705194003e030b141e5072506182c10400705000c404494803050400703d90007e000400100c0803144003c5030400c500b08540e10042c01420071a410720602440d4690f103000400803400e101e050300a0300d03681e075003401c1c541c81c50801142220100c40301c43d89038030b40c6040c0e200b084540e086812008008a24048085506005c55460301c566a444072660140c400219403c5245101c00103108191071905206901003014943c3c0007141c1c60f450001e4041001540040d40c546061100a10760403a1301c000002c103192a03800c4540d845031496a005c00c0080c0f200f1003806000401c00071b03040045654403416155604000000302103000e074030780090003580440080780455480b2107201002040030405a00c824442c8600345603102018445c0701a85082d0140210f0600603280c0a41d00c9260031000840c03034070380307003c0342111101d080c60700c0110540200040c0c0081d02a8503003c80e0003e5403101c03008940d40c2ca449040100b42c030100c2e0f0003c0d05225007007602c80c41d01d0b2261304141900e00d40000103014146030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 828758372 1250 828757122 828757147
    0x106021614061b0f06041703040c0b09060f04140406080a05100c03061e0e061c0807030c080703030203061c21020102210a11122a070303090203100204140402 69
    0x400112000a000d00341504c140c01350300043c020b11480c000c1d03241d9030541c2001900c0d05d03001d10081c3c034040c0034100d0009040c800c841443d0024032340b010001e001d540c904000341c46e10300c000c1c5e00681c1128103140c400c202040810702e000c1c0144c201510b00c8070701410591080d5920b043e61414640c0002482a4403603181070f200302e001358400c0c1c001b040d024800c900c0f2001c4141c2500080da0103030192425400840380031074100d0804001004040311443e038804840c0c485901d40d052140c01015046003000342c44101d0360002203440024203000f5200e40c82c050307103a0034544108068900344507550b116910840700a000483c60312191340d1001000e50040505000d40400200e029100380202c40311031060081070752440c40203000c0900d1213007529410800c200e030042d02807080e0503c911f4019005180003080030405a00f401c3d00c60b2030300205c80c000d240d19a01c885120940a64105a00580200341d0361110081542420712000c02c054503401811803408c1d0401166101011490041e507020340e90200b000c1032203c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 828759622 1250 828758372 828758407
    0xb190504031217010b0c070b0d02090d1b080a031e02012403030e0604060e01260f010e0f0405100c020f031902070f05010c0816120206010602161406 65
    0x60b040709002605646210001c1c0c55184040c0c200d80c01c68008900020f403203031914042e58000c40500d4050040b0fa0316240424445400685042501c17030340c01c210340301e26a95081d21443c0498815494801460503d00b8203903480c034250341c40041241c01c0034005800003540074012104901810718505100034034150100d0040400d01003080000200080162103040f107005840100c0b40300f0380d107210750340107180140402d501480c854080480c0e820045500304d503000700448a0542000a17451030440c1a001c850550003030103440480320081980300502c0000c40b032006007903002000c04000344007410665a002e0b640c1160701c0101c15965514105400700038800e2055904805481c0e084940340c900321654458441c01070202d4001511030410001120560800c0810441d207058652210341c522646401070150302036000114121240550394002580da14101d43c25180140c0c004d00ba00e40c100040072b80b41c602c40c1c49140c04410340a0004108100007214420340c520b606a64039902d480201c4d845500c4035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 828760872 1250 828759622 828759629
    0xc1f0b0306090303060a0801061208070312090c050109060c020f060f0d15090e0f030d0506040f020711040c1812060b210d14090d1410150509010b190504 67
    0x41c01201e050001a0800001841c0198001c07912030105564407417005003215454810140c00c002d014981d0070104200030040c0231000d01034142a465692b40040c1d01c01200c071415000c55460850722024000c0c0d5030701c400404043c0c03400e82490101400107400203080e0358080c1503040d201d080009035817910025110195204150707055001e20072204000041a030b0061a409406012441c120723600e400d4a100041d40e40c00b50900c0c801039481c01503058104805404002c0050350420346844070300014050a20007000304a00071940f1031400c024190400c02541c2000034a881045a090354070208903c404014900701c490004100048054038036124010303044c180310440c0e002c041c1401807070240e103800c4030200e0341d00040d6040e20b90041c403000c016619400e000d000720f118101c05211603003a81c1400c0341c44e03200701402980c6001400c01d00c0c9501c1031800c81100a03c55820380c503409045452102585101d010304002c40300b40001c1d606000d02d4000d2030140c4450f6007041820b0740c81482007079000d903080fa0040c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 828762122 1250 828760872 828760879
    0x5070b0405130b01021c0302040503010f180602070309051302030708161403040203120301030f050106090207031d0a0e160815030a030f09030803011d0708040302120d1401090b01140c1f0b 82
    0x40342e40e188400b40003900b003481003a02a500702940903780c0340c168401c0d07030080388140b00f007483c41d10b44d0340d103400c0002e4010040131014400282e5010445698092041031007000111003d40e80386401607004011100213004050300c21968030035000025000a0385200502d41d1080180e200e40d02c50000902c0c01c8022441d140c03000b00008004802d108818020340390b40da0190740280003403550703514010101d104100340a40041c44071007070102d8025003a4140700819000400c1500b8140e01d45100c3c00440500b501e07000382014840050b0a401c0307800020aa610598490707102c447c642c0134101007629206010b80090400c01a041c01d101541d000d4104040615000f110f9251651303106c00034240403000c5a041c1391701d111041d00008120900c03a01099116980c5039001d4a40140e040342c83c81c031680c009000c04c3e0450740e100c4030440c0340c0042000c0418024050480003003111102d100c002341481d5099003a035621a01c00708000c800d9901e0000da040307200408010b86002070a1002d22000040c400c00261650 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 828763372 1250 828762122 828762163
    0x504020a17070207140609030a050615042d0e070b0a08010303141306050d020d05340512060a0b0a0207240917030c0a030206010305070b0405130b0102 66
    0x207907208070112900d241c1c00400580c0798036421020383c3d890440380b24105002c00b0004400c1041e04218002d080c106a010382200c42d00c1080d50344075418030000300c684998581c03070140d0414062030140501501120241d6640000200c1d00b00c000c60440c0003000800c0c8410f844030801030308000100400d00c0104004202030780c9454084800400c03c06007844140c00080b40c41003150b43e407408010858001119600b1010b203a40d140c8103043c1c0b01f41e00039005c02211140d003070119906480700c0b4018240304941400d54100c5c80c80f02003005034256818660314105040a0760b03020344200303410900719840e2524101030302102c3e07541d420010340ca0036180d400c449403549001c03480c4154a50000b906005031a400ea01101100c015440c240c200b40d98810440000904040002c21402c038101c02c2c1207910704081e10179a440d040c1c50f07100072858080d45900807001644184e00402c1404014010f02c0054401806103502e00340c6004001015003410400858005644040c0701200307a000300050b03030b00b031008081c0003072 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 828764622 1250 828763372 828763387
    0xc02060d020c070f05100e1302070f050615092806080606010e031c050d14040302030d0f05010e07050c0f060a0903110f0a080c010b04060e07030e010c0e0d0804050402 73
    0x1020703400c400d0102d4100d02c83c000300841c0d2a40541c0c0d04000303807007020b0210869080360789411502040b01c11a45900000000640c0c50322203a18001405607034012100701b60188550318000f894100001e142c0e404440840c400300d40c45541e40042d8980200042030368003418200500f0101a00007224180e00001d89002c0000488e1200450001e110344400d80780c40d413403403d03013605040c0c840300c81d0800042c02da85940403003034000d80250050700c62641ca003940080c1307500c1039103d05851080107a6041c0d0140c0e00228000780440700d43e0241c00e84002c0c83c0d08040c0910b500d071803280002420003a254070203002000c16401031801e010005070341c00509010444000d400c100d01040c00510156000380e0009010010030303040c901c1c0024903a0b04488205008208a400c03e0300d6601079030708440d0b851001952204e494150a9545000761409020001d00061079400d0203000581110100e80c3c00d240c1d540d041510f1440040d8008003076502034181a108150ba9038824501603071203214982055a0051004c82c070340c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 828765872 1250 828764622 828764647
    0x180309090a0b040b0a06140f0f04080609060c0705060610110105040303060602101e111309020405091f21060510171c030902010915030e0d0e0915010c0206 68
    0x1d040c04025101005100300000a1080850080c010b0b1400b140d81111880700e1201f940000344030090384030007001e0504529250b20fa420f40d01951103c13449a0003403051000141052001c507801c01052440c5070b00c2d04556603111501d80350020041e078407601200311074060150158105241050000000300607a04c1e1a01d03014000b441e450080c600140724222104106460034820b220002841080c0321261100d030802d1a0f0203055401480c1840100911010f50703003003503c4004002424242c01e015031103a041c02c0502034182c0004010401c002450350755a00d0090603800081c3c103503000d843d91b40016022145010070801300a6100802c1f81b89000308204500200d04440d02c2561100740c0b4016041004000459031090000380f03902c812100e0782d03211113065000780e101c0c180852040c100054040c1e5103a4080320314445c41d800000100751950702044801000740443c030900501d81c10a00740740d03400413021985a1500600c03064100082c60a0702142e42e0044bc0302c15211079004040c1580c40a905010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 828767122 1250 828765872 828765881
    0x9010e040510150201230705091305091204031e060e0f0705040c050c06010b07051c0239151312030305010e041106030a1508010e070803070209180309090a 68
    0x210500c07403084030080e00f0058418003403009002c40c0311101520b044800b6184143c00b8001502120a202040080f103809484850303a521032159603082c000707980d140030700550741442608541000f510504200600024601c180c0e080341145620420410340c1e5403916181005100040d80303440e8901c20840490305c0c04c1070016000040e1034050707030184000d044001043c1c480d401030204a440d1500810018048071030013a000e81011400356040364070200650f00380c80e440c081da0410200058005402141d2502c0f002c080d00d1544040e030203044c070030300c1c2210310b800e441d00e4819002c00c2e0b12940c1b805011264079501c1c0307001d44241541c00004202c415a5481098030f01d0040c2050880c00320341440c000085ca080d87c0139404e4410303a00500d60140e01c40010041000c0c540c002011410710340c2d910400c241e941c10b9000140c80c081c16040000082ea0454114000d103011642c2c0d00c0700300c85500800510700180c41304240d03244c11000b155101211070300110f0703150b42103000782f2140d5601700a0740020003640061a410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 828768372 1250 828767122 828767129
    0x8010204090b280e04030201090c410d06060305070b0915120a050613050f07030609200a231207020a050a111825020a031409010e040510 60
    0x40c8840d600c100310010f04103846044100168000c40240200000400c130044103910610034400010303030540a994014050119800504400c3c0381940e130120040400316841c4035884c5c1c1c0700a9501c0708914211001140049061340e24012003190007503a08015a6030401c201855108043c2d03840c89841d140c03200a1a040200038a21842d8900c1d014480b20060380101e80c1c50300d8280800501540e1541080000391001a10054201c2d500f2440c3c200c2c2c404551080c1d6000d071080008000c0e00d0f00700700100609507442c40d0400004a0300e440c0440741440032510301403d800c11548001c50720340030390380c1099079008400300b21300180700350b2028100d0201400340002d100071080707241c0c01d070000d40714010200c0e914030700702c08010060b80c854502e80000c5820902000c5080000802603005070a03100e0381015805000d4800c41c2c00000c00c0301e0b442c4030055412004d011040c45503c000d054512060324018100e1070040c00e0220034140000e1000d46503441003040200c0481c01030430a005608010040040c0e41c2482e20 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 828769622 1250 828768372 828768379
    0x3030901051b0a0807030914010c08090c041503020d0611220614070321061409150102030a0c0602040e0103050a11030d05120a020c1912020a08030403030b030708010204090b 76
    0x1002c04005020003c0c1c8440c1c07401680c031040a9070300c460068004000e1180241e400f0042d003a45908415024010482400240e580d11246410002009131078072030032140c194031850501d44c001141704810344000080344e40454492450400500f0003500074900340a012500510020340304181c00c1c26520060310400062502c2d00c01c0e0f6583d19001c8a0401c4201605100a00100183d0f030200344a220311481c00c00c400c0c548140e088100c0c0782c10385e00301d8480303a0080c4c2c0180209080000c103407820b00166603201203601c4104442282100000f5160f102e00886417040c01803144002d000c5c4401541600d01504e049000714080b035849080096070b400c20b0843c1103c0440451140710901c0c2008104c0c0303641e0185c0f1f62503060601c0e0704504405100d0310000e004808182e420310891250580c1044800c1c988050041c4d2044011158245032410070744018403801503501003010038000907900c0084035032094151a00280348208900060b04040381c580c0542415800860013160300003030b176130001c02c6904084 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 828770872 1250 828769622 828769651
    0xd080316090501090e010902070213050a150f050102030403120c02040c0905030d09050f1216060504150e130507110706030606090504051014010212040306091403190f09080303090105 80
    0x100d0046840c130103940502d100041d200001000410202e4001c0c010991000788025a000c40c68416602124802c40d4801461a04e400c44415601c0200c20741e90090500d6851000c5030030300b407a0000c0d680c5e104511004064401290f030901300181300e00035017450298010800d21004241c43c4005011903032a0103001d01c01d0040710b04e485081401900208121040980507181e801862420010000300d0f66081202c10b0180b44010120f001b07003c95850003800b51a115580c072281080850510250030420200a00404013100c00669841d9608502d0404030302e40f0200b00341c0d88102080301c1401d104c1c41811000d22903100c02282c500d030180c101d44180c0d0700c0c656a07031a0003941c4100700070603140282c84006249000e0700080c007a08541d84032908000342c040c011115203455000035800985d015500944000b07179552291410409082105400c03000c842008500301032660111a904500d06c45a1005020586201074002401028104020800b03001681d40fa4504405c12234083d2004403801008a41e14 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 828772122 1250 828770872 828770879
    0xb0408071103150f0709030c0b0304050120040302041e020319150b160519050a030210061409041e0501050603150c04090203070905120c18240d08031609 67
    0xa00c40040e41400c0f030500105445002109001d540007a200c401000014440440818078160442c0000c004240203da80ea25160501c43e0842d41840140c2103612400714071031001821183c203640c11303240c040b0390002e41061070b804101e0ba05180210358108150004c01080110b407841c403c418400341c00304405201c840f41c0103144a04c4040d00d4080c0c02081d100078840100303000070f09440d9010141c4560115006d02510b04070100c208001c0407401c0f103540d84041c48402c10035a042c006010220f07404c0310140015800c00241041910310540503d01139131030080060240003000c154204003400080d07816020094504009020f0074040b11458001d05c01d840003c1c0885204040452040301c50960345401c01e424184000301940c009407101c4100000710b81c022440e580c4c1d4a0451842c04c40f00d500500da41000c1d582408004000b42c0c01e0310548441c0002004207206003038515000e6074074400e81030980d28440100260b5400d41c140c401a008150110402100608050b000c1c080715600e5211400016607 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 828773372 1250 828772122 828772129
    0x2304060e060c07060b040b120d140a1b02010201090605010b04080c0f0108060105070501061a070302100504030f032403050c090a0516141e0910020f1c0c0b04080711 72
    0x39904040b4144080140c64041a240d501506032100000d001084e030703002d40400100e0340c0d1010005481503801001e105c60a01e41c01000c10010307030300881d0b0b4260501114120107407090003010400042c040301c6602007021a0310039404800c00b01d9102c90104081d50712201102d103d6005401b40d202c840c880da010032100d51074288800c40001030140d44113511603950400449442e0403454046071150340f90038010440ba03c1c0940c220f04800103141140d5212140c904000b07250078801c640c09042c0d98500400d00c0040781d84513070803500060140c20046019031034010030800413082c00409145203400a04003008000010400d051840402c6510006584820102d401110810f503806207130f14102e58401a40507006e2414100103000001006044c40c10f40020b21580c111241c4041c1040a0000380003c200d00c4c2c0300c00c2403084c03400103100604040c0b0910705d000f1707960003000c500c007503040c820584680203141c4a01065141c00d98800c2c0d240e0720700c1c2000e190405c041c0e0058001125401c1c59100c281200d4103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 828774622 1250 828773372 828773383
    0x120106091d0603060c070c170a0606050d0b072003041203080603281103100606022e1d0d0903030305010902031e1b0406180803030405060711012304060e 67
    0xd02c024040c0c03c0540b2030399800192603200780320884141c0303041c40001803a040c8101500044845690180c0079800c03191510710112607450304454843c014648580011461056880d58070030618202900c00c4942216010203100030103561140c035210014000c9001c2c0c0004442942c40c070b1094660f5800b60311910105911079041840314034608481641d281d85042d0910304510420b8010802a410b852141001c41d081c88085041001c1160301c502c010001541c0c1004080400180705130101004200408104c45039055528101141500c2d85008240041b002c04000c02c4000c1450445e1f40000000b60042c00d0b0380301c1c030703c001d6000c00d1414000250322140ea0007101c0c0701e203601b008140341c0094040e0f0200b00f1003030040c20380956074aa104400c14089400320080c005000aa100d4060304070743c40e4000e100c084a00c2e0006402c90b0030500a200c00100001140c5800001a060003150800c1d02d4945c42d004008034a10300412107802e01200c002c00801c5007000d40038601403501448003030303100e50101e9a41c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 828775872 1250 828774622 828774631
    0x709060b0a05131d15031b01030504051c0908010b09100308220f08060c1612211b0e03120d0906060b041d070206010501080c120106091d 60
    0x161030400200700e03400d2056000b4804007200b0045410f1858440101c408005101140070000d5090754040c03040104c070503e640595080308800801e0890704403a0114151984240147e041c151200c01040800c00248a980d9103012003c3d10f849070031059240c02031803800580300700c82c415460030110f107009080c031800c00d40c4150070b80c4198a1350a4615907078040313598840084455850040340e0400303c010504887e00009144202000340d00c079007418103c50904402503e0b84c14009ca00b0415000a0703903408568903021070b005050300e6400c10b8014000d46528901c1d0311031440c2441305000d424036209559001d082c0d900704506e55245200c0c1d020009851210b207101c00300d540742d40541d14051000d00e0342801040c0828002034042a0240da580c0c0d41c000752201c6803c43d0912500c0403400348222680c0c007100010b201d0a000b550181c50500b690003031340361501070080a04101d001d80000c2c0f0400c40c0e42c0215080c0038520040c0d96640d69490500400d49000d03801880450010300030180000001c41c03403501d004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 828776978 1106 828775872 828775889
    0x41214070b0a0e040209130207020303120f0709080610290705060906130f030806061909080606010c1a041a04060b18090a3c0203070906 60
    0x19000f4600000d4026403051000c65620b0707650160301c4800c4100c1810040e603807486400807a0540c41b40c00f20010300c0c6d8010000340b02401e0103402c0303114030424130755441e03025042d203c591a179101c000664440da8110090350090251055440300181c101402c10401c414a000d822511101d54020407000c3e14a80c0001c8100001340009105080e0f0045541042e50480152951015030340f8031252000b4007042121300000c1d002d515280300f01c4080050b035040481d00b10300f80480090002d1168068600580a1200892501d502420860805507801014510340091680c084160960010815504000c83c0d2400d00d44413040ba600413030180e4010700300880c907140e0300800d00a40180500c045501129504c0400a03102c2d008141c00c0401035201c100080000d450411040f814500452542d00b800303450751000444c9030301c009110560394401e400b900c0e25990344900a4080b1141403041181 = true := by decide +kernel

theorem cover : BRFrame.Cov 828597122 828776978 := by
  have h0 := BRFrame.cov_init 828597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 828597122 ≤ n) (h2 : n < 828776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
