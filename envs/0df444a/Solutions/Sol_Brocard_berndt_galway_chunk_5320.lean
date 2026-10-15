-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5320
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:28:46.906511+00:00
-- url     : https://prove2.me/submissions/ed082c6a-70e6-4ad2-965d-fdb47d809b4d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 956654676 ≤ n < 956834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 956655926 1250 956654676 956654689
    0x15040602031f030615080d0813060e24070e010c0605090118050309091008100f0b0301060e0f010f0b0a0e0d020d2003010225150908040e0901060b0d0b 66
    0x403510081c07100303220302c00001c1041c00e13400b04501d40c0c4100f996146060b228146943c8602240c001c080009520801251501710780c0503040c10047d2050000181c49500d0708200350414030391000038412186503038405442542401e151592100d41843e0940415414100103802c0c2c040004e40904420347d2075000480c0b580007540703c24941c0a540280601143c02d9113400c65072a4850007002d0b015801c3c2602148805125401500a0768000301c0074121401031940004014208084c0c4140740e04d8459141c0003003910b0030b03c21100a0712004656010301d20340040b104000e254180d0114a08a5903845c003000b0882080c815540740c00494500013550600c42c10000e02008520035020390b11010302145042081030041c2ca036190780e85440e402d41d0803002203034209400c034010320306d94402c2c1ca401b540c1c051508900210751075615074411040030340800107110700e400880d009250201c0300c1e120300240c244084900c5040f02c60340140c48000901c20103051568140c80f078002c440004101075150a1416545d56030311 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 956657176 1250 956655926 956655961
    0x307080c0a0c17010f05040b130219060f08090c0d15110d0501060807020f100b03190506010812090f090703020c100b012703080702030f030a080411031504060203 71
    0xb11800039600d4064022407010007032015503c540c07810400701c50304101406803070310032504140121115512000f2038200c5030b0340d0410480c1d0109103c0c40c1d82e400a1443e4251002811182c0c2e9400c210000440d070140025001a10244169200c1d140c005a159030302c40503207407480c1c0d1114003100d401144d4035042e03025280e14080c400e503e040c0401c664243c00700c1a80f02c039048034203a582c2c45000340c95400e801d9840d403528440000d0b0981088000f038104801581040d400c007040541103030404008510003c1d0440d901200403a0107402c40001040038402c10007050710203002e2a155240b4140b8020000f5403c2855909620b0040000c01c0000310141d000f90b06590048010030282c6c0c1e0613100117140345000f00141540316002c00c480e07403041d580000d103038284000f088a82c2041d0345600d504644410103150001d075012a070500c269841c0391a04030003803000e00412070b01d5441d05c000c00d060500c1e0401c6161100c1071030034060351010703002000c2101c1009585130801e03001308005a9a454810341c100540d02070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 956658426 1250 956657176 956657183
    0x18070513080d02010903090b0a090b0309190c0302010905060f27061603200a020609040227090105100806040e030d02070302070e0a0903080a1a0a0e1006020607020307080c0a 76
    0x201440910119010740280014905c01d68940707c01d5030b1941a0081c6070f0280d00c420380000303802c130171040c042e00941d040103681141e000000c503498100b000b5480b10305c1600d604011507100d603005200f0821035030006d9180018000c21a03030181460000c0c0c0074440140030740020100040c001c4100b054080c007402403140c01d1014060f0a055403135054000c0b908014251420481c00115003c000c1d00119120b6520701c07038613000800141c02100c103550200856504400310311030f8081d03400c00201140c845c40544440c204c901c410a00681701c030b4000d0821221070816030155015001b10521004e0b503540c00902c882d80001c044a001400a4070070040c02d04d1405060304048000c0d1000074070781c046c1a00001e0382030440d0200003540500703644448029003510703035050000700441c2c1d00c070000c103050007070903006610940c0d068134580707688032015000034110065551248004040750014080b585007030b03d03081c40c040c00c03041c0018400b50402500c025035038400c14001418880000c070328201001000d002c0e0f07414a681 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 956659676 1250 956658426 956658433
    0x120c02010c1406100e1302190e040c0801060803090f09090a061d0127031d040203160305091b2403090f100c120e010914010506010e1807051308 63
    0x711540c1d1640e071000244c6444c0d6a542c803401c00011504200b21a141c450b842900701520220b0159003404070802850085400002000001058040310072242c40e115a01460000f41003d150521050844030550004403241c2c10400404445444d5400c40401c05c80c0240c60781d01385540c4440c62142808540d5038000c04032400c0c0076034203140085144201a0031311700340d402000030055807090b070354410001070904030703455001044510100e40901c2c80c4400221040c3c003040d40d803044201c0094100d0780211203101c0454400c0c04c01d0b600c103c2e0725104480d8010001001400e8601007542200b1148030035140052181001d11134a81e08011000750380c210700900c0c0b002c0c854036030507c541740c90344650360710400540e135200d03001050019114034058004002c1940c0c40d000b0040600406040160210160041d255901c6802940002e044200032003004400781000080c24201000010910099480024440c0500d414a2a085130000442541007905828000c1d03980c08030000400d01403150794880807841c007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 956660926 1250 956659676 956659703
    0xd09050102040609060c05070b0306010c06090309091a130509010906060906050f032a0d15050f0105030c0f2106100806010f08030a110106120602120a09120c02010c 72
    0x2a0540241058032410303120000642d0315540d00701c2c1c4503020b91001828030f034042c0c18108006100900155000301e0306140070b035092119038460030184d8801d00740440005414160030403540640b4820902e80100d4464204a04000200000c1010001081e181c007c1a92140030845100007540310307104041c1d22020620030913695114007401880310b8131880d40101030300d041c1d141261601155a406880858200144000711b200c0300e112007080b6012610b0f040000340c0d42003030118200ca0940c40c0c1402c50740c60080750380c0c075000503441f003120011307801903000303a00010a14444c1e5032101d4824a41950030344040e01d00c10203030000e020320310003d400200101e0013844140f0120750050140710741a1000441240d4460342ea41c2d080d041220710501c50440242c006100034100e03075108038070740d0401e4040d080001c81c002d51034500da41d5084922800896240d6400541280780e501200400c03940701d85085800c00890001e070f143c24002e8690b040381c4000b00a1441007203421607000d0360300c0040c0c0d81d0b040700310b6843d0704 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 956662176 1250 956660926 956660933
    0x51f1a18101a19050c03030f0601020a0f11040b04020c0a0303021e04181a0a0302060a032a12060f06080c0c010515040e07030233030403020a140303010b0315060d09 72
    0x15031141002c8800d0740650508045080e009004642d031000c00a03000b50301d523555050003010204005044c19045000d982000000310745c8480e1440341d624080c41c0f050140024000400088503d500002c5008500610076254200380201e03018030825058100580d4545e207000b81a50565103052403698901800300d40420328001e034010144884202030401c1058040b0106440c2c07402c40d54035111a40212110028801401c00c3c2024202014a500300807400081000d4400800205072003038a00ba0280910309900c102c0d40700d600e0300300e442070300c1c03034100300b00d0381082071199034400c0e1070085005100100d408210400790010032201030180c850001c11040c180000700300074811000c40740781c5c4141c0c1010144000d0b2100807400c8000c40b540140885001d2402010a4484c5c40101143c144100a00c191490565801100440c400c9210f0f074041d04410300c01e46041c15074994003240261803a8414401408a07039035941c00c03240c2002400282001072544d0b4000100e180c1308990b21207010500303045803641007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 956663426 1250 956662176 956662229
    0x8150702070905040236090f0712110f061207020a02180f0105010807200606090f070c023c100201020a05031f03051f1a1810 55
    0x904055400c1e10203240e035440420060310710584001c1e512100d00d2401e24600c81e240700031500d8100991200002d0908030903000d00307401c441180c48a1080c1c106160107400408140010300107029800c45c2000c2e2118280c80d513411300d050010f42c090160804282e000031556581c01a41e03170308541c0807080c0000b490840e40080d01c451106c4c500724050a54a4041250302450524003407051802c2181148075a107800011590510041c0010062010011408820754500b600301000b9504000050099083c03100502132385000050501048007010000d00c00f00d036a00452800e0817030340488080f50100b042000c100d00e9601c07021089540c03105079a01840600354880362310b0900e4601200d40c0c0e0403111070f581040e4241e1154064a00c0001d0f020400509208403040c00c03404448030300100e030744071141c41e56103281c1317060108880c55a400400800c9546540a140039548088003a810b45ca4190390768034011484480464141d081d2640c840d4002807819422512000028402211200c115513107070f03c007400b407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 956664676 1250 956663426 956663431
    0xa1d0304060e041b08061e0a0e1902041d0402012a12031a060706020d0c020336040509010f0606050403110f011b06020d0207060501140d020303031605040815 69
    0x5682848240e80d000c07a00308030606010324445c1c842d2055a41c8100422188195204140762221215080b18007107407a0201c014001e0000301c0710500786030821601000ca0045144040300103140104802d01c81c094109610782e501c2412485002c1c00d40c0c4540c0700507200c44100704070b4003002c3c2101310b201c426060040021035481e540103010719000100107050440550b00600c140c4d0540303c0c9494894021410044000c010701801944010f04000d040c070898020703144649850030050b4000f04448030111020b504800034011a403102d00300300030300300070411158442c030100588203035664000966040801e40080c064000131020812030309031151000340540d00b1038002910145001100031070b46082030072680b0005803058450390320568641803e4481c60b006036000f04c622540071702648808910300d0010701241b80c4640c002144560505401e80c1c902e5030001d10f80c511034544501d0311380250301c000c401c03030350441500c10400301d5031034280c6401e541a1107581d00c096464420129109204a003002c825030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 956665926 1250 956664676 956664679
    0xb0a0c120f12060e130204020d0c18090e06010302060c0a0c06050c070b040503061302010c12031407231305131a06040602070902090f120d0f0c0b0a1d0304060e 70
    0x1010012109203100442d00f460007034111114650021811150b45c4450201141d480240702514218491400c40146d5410f2020040454600401c0c1007d0840c82100c00e005070181c080b040126100d030a40b1070340d407028180b0010740100d03400a8009011141400b64018054014070030300c500b11f564240040040d030240e0147d020700c1c0101070020846d205404111011182d004008007095110341e00c0b4136001150280040f0305006000d0002070008904845100c0003001035280018544481070f0811014070340102810308001208071a100000c402410b01c08401304003103240303900ca2414150300c920a84440e009603074090300d60540c0c40030141e82e03a04000d10300c2d2055000b21045001220621a940c01580190740140e0000f01d0140420840c0e0b9016161a00e0001c00154070810700c88041408400c54843d421180c0d00045a000281ea41018000461011a1070200c10644250311740100a0704007400c0424219120607900905c1d0240d0b00c900a030310110201600d949655a120180140c0b00d908440c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 956667176 1250 956665926 956665937
    0x10e1c0b13030206181c0806030d0503010323011107080319110f13050a06021b0a0b1c0207021804050c0102030f032e090605010e190b0a0c120f 63
    0x20300c0c00c807544841200c1807a0b06070020495034440c4d42d019419402d85940410003407003841403440c608004a20526010103a9890301c1b101030074003105050824000c5166901848000c100410004101e09071941192644024a46110680c0e011140c05042003655403c2c2000780822220144480840254024005660809154030341540c0c580c050720186a00800703002d10602001051181850050440303860701080d40e660103440d04001882c1d4080c540001d4016480030b800c04006944130700d454206a14101c079200720881c60080c2c24040b6226201615032a102071111030f411800d6071350165521164000c045004a40040e5160707400301008a5044d00c10740314400034460554004000c441c14000c03514820380c0b0303556907d5803000c003e04a25000c1e000425003c08003c2055012010020203070002c10004280c40e403a020006080340c2040490502c0b8000061044d1410f000103668001114035482078191140c540000664500c80030345ea002c0c1946140c4a0b098040c164480c204401c1002aa00d41 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 956668426 1250 956667176 956667181
    0x4151a041a030c12010f14040209091b130b032e0c020604030e0f092502010608030a0806190f031202030c070e0c1b0d09060c051209010e1c0b 62
    0x24206103401d401c010303038160b0800c2901c903409041080300103400d1640180041226142030518400701c40d07006e500300e1580844001030008510f0306400281e00102c2d02001454038801000300c80302038103500a03002d4441c0c80091021900309055400c00c7d030b0717020401410b4601c1e014481c0060720300745000c0320145c00282241308860b80118241e104046d60103255078003c0444d03580c2c0366429240141c802a11540c0441c4125500d845980c4544085201e03106c4c600d03984214110044c00c80c401c0100b005001030569060560612141000100f80c0751100340c1880c106210703803200e00209185035800b01002c50300f003400b41f9000c1800d4280c014814101c07440703500e031003407a004400d100301d80b2406580d1030b244242c0c02c400e07000c02a40c10030812850f04800315603840f92414169002d0107084409610041040342c100307030b0a0b0300311160021030400062115040017007481415076252a02d40d400e442d41688480d40101f0a40d00c9648207800d24903c120015114040c0300a03c0d2642060850385400200d511250b41d400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 956669676 1250 956668426 956668451
    0x403170603250f05150d0f020c0f0d030b010314040209101206020a021204030807060c050c03160c050306100b180604030f060507140f0304080931020406120504151a04 73
    0x1400901407145c3c20050810515400b000c019100b0010903c034000d40174008191003060600c5252041c44124008080c101c450700400340036198200c0210341414981a89800d00030201280603901c507504440302c007040c0d51580e41401c00d2588503044200004040c098050401078564000e048000c01c5408444039001308541181852280c1d000040007a4014407040000826582002d00300c0c20035800c1c00d0382462481220103196800c05a5a500843e0200b0001c0041c09000e81d16070300603000540141141c0d2800d03d14542c1c440348644249085c50800054100d000d41110700c41c140024001003426540b5650b034200000300702d06080301a10114a030030040317031849000d00c1c00c8140030100e4000c11818031b8540701d41031285400041c400d545124040051980c19640c403503200c11315500096242d03600c08444080464903000d1815208440c510400040c0120b030b8103d9018804140d04907400704480ea00c038078000040740c440810400205081516401649055440c240300b07625041d03030b040010303881400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 956670926 1250 956669676 956669689
    0x518030a0f0503040602100513030e0406030b0a020d06150c0b0a14040614070e0f060915030a050708130b01031205070b0a020c010c090e06010f0c0f0b010911030403170603250f05 78
    0xc811820658005c107189c40040d00802d40b150420800909c00901d040d030380e840300801000c1c1198101c1c1700035400124120030b5189403058001428007040420340304110420058603043c100300015140145a40006540d10807075000400c0300310041d11000000d05081c5071400c080d00b510105041e00780c82000015481a206800c0c104984000804040f503919a0034240009544412100d43e0041500050b1009043d4050b0045000306004000083c651408000c018481071020304000d8591818a0302440400d988030041d0303054a810800351a1064090b80b0103072094400c520004090120b65001c0180c005840d5001e4032080664000038000301c0503140b0100d03a03010046c05520342c0445004e010071010f5103c0d0000b220742c800d007810288400005603d5158070340d1456030044030705c01c0786140107000d4021140208802811012040e80c11030074035039030207400c8005840b0300441d00b03c003200004210b41d5041041c28900040708600c52078406040c10b8402071416103001b000a6100040d100152504112 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 956672176 1250 956670926 956670931
    0x6140901080115030204050c04080703080c0c06070c1a0721020601120206042912060a05010c0521160f0b06011115040507090c020d0e030106060518030a0f05030406021005 75
    0x1240f80001600f5075080100401000c2c020035410b102c240300204c0c410b10700308038440295000304042600d68211014a03480c00e510403603414014441401030300002100c10740d000c000c2c2d81c4800d100380000382d2112880038a40c080c0035400341c0b0304c200800f491b80345c4450181e526492002c0a9003551903980c2c0b9610003c0759001c590308020b410070b5003004104152207612841c071602800321000c0040108540b5607410707540d000458404043d000c000b050003001d10f04003611a0042200f0f00705948040019111b40e600c84c2d0b1001040324400030000c00c0043c20240031021500039a00002081c0c02c4110282482e41349400146002c40310000300d10042a25980228200581c00c08407000a143d18821400c602c200038030080d200315420311820300c021980c802c075400b9200400400c1d80c014080b0034882d00c2c008010503420018a8026490002d0520816074050111103150b0311814620201a00c1c0b000460b2607d009444040c1c51034000c448100c0406c50040b004008594130f40d400c4400e9403e40d0304116080302c03000d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 956673426 1250 956672176 956672201
    0x120e0601081b0d0807081c06030c0915030206031905090312180319030209041808030a090f02090a0c110c01080103140a140d030c0201110318030d061409010801 70
    0x1004038900b5a42c102d10510503145018181e442880c2c102d0760380000e10340050404444031980414010f80b00b000303072201048132041c05041480003500c0d54503020f40d5126140260040365841c1c2404880b8504040000d200450340900500d81c0c0745407030320143d0340c2d180c0005404841c82e41440702046040d2000411f0b14110303030304980b2140498a601d48050712002c5204528500b0740400e00200d0900780c510102032150700015100076a880f01c46008000031180c0015400104252400080021442800507a40d01120103c0006260b800a04100304080c0384481c00070340c8040003100304240050b9a801407800500300d610345441e03000760318500b0364503210080c0c501400202c20701c00420104828114000c0f04010402c1550f52418564480b0300e05240c4e016403094541e407003c0e0800801d02e900d8442c4000754039062008001d00d1400403e000d00901c40602295102c1c1c030803441d02c4016040038021544101c4000f842001a259603200c00b0041100580c03009101d1110305000045100060242c030280c45030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 956674676 1250 956673426 956673433
    0x1020f04050f15070614090607020706030b0307050a0b04080c0604080c0108040807060c0809100204060212070507170105040b01050d110904140d09030204060f2402010209040903120e060108 83
    0x2403005000100c941480410342c018802c58410700640d075140000d0003050f00440b80890050304203207104000070306c003404a403181e500178800c0040541c1d001c504041030b50010324000c2942080740340040d1402c1042d41055a000b1485a40080d0b1362101c1002082114041d0701940d030228110010001d00380030790311039000c45400182e456109584a40101e50703205220744501030405000741c40d5901181d07a64110b150100d41d8032001e220b41c0c00c40c00c01c642c1c00020344d00b14003035180c1400c004000b900c0b036900f94404400c1d0540440c0c104100b103020b0251401600070042c9000d0480c2c42c00c02c21b540600303c1a6402d407042160000041118109114901d00e41604460381b0141600b042090081c9218000c1041e540955a45200b520404050006030240e25180e512200d2072401c40c0104021141280d004507088000503c04002c00c4040d011502d08d42c44510f010008013403124101030340a840b03918581a402890100440d04040d04886c554120604a140c104488160002c40555440d428050f46100781d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 956675926 1250 956674676 956674679
    0x20d030e010f021c050a0216060b240301060806030c22090c090b040b04060e04020d0327080c041103060402090a030c08060708070f09030312150f051201020f04 70
    0x140650030004030142040e000082c040141d001000890708050030a1428909640107900e810321240106504104010400c40c0303060f140b000c000902020640c0700408443d2119408074041e514140c80b8401c0500d000c00d4900205a16060340078198824080e01e4042500d50000c41e4903800c0004211f44900303c00750402803020841c4806d42400d141000d0350320300c0b480e00d941000c00017401010a440c0200701c08003011850241540410090711811162240110b207041410030000c64034000e12500103130155000d08488003542030403207041001c040c00010524050400080411040d0741d003e007103a02ca5415070743c040d0202010002038a205e40703000d81380800c0920100341646082d50080140300b0006080e4140c90303940b0744d10f0700e010b1400c640c05143c40350080001c0040c0c094002007944d40c071420314034000b188810303c508060040400c0d8000501009030038075506114142560040e8603070004482e24844140c0c0e110000401800c0c00c2c01a10b000310058066007506203014000c0e6031503e58001081410b26 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 956677176 1250 956675926 956675953
    0x30a0c0201020f03040315181407090b040905100c1403040f02120312060418051504141204180b1c051014150a030209013f0b04140d090807050402070302 67
    0xb408c2c02e692842a1407248220f180c0051103140041050904c410060706801e071821901000f00d90001c0156800346091403514000100301255401c0c40749840d41c400590b110380c035901220f205030044d074286c100c00c00001c244811f21554130400028217100f2241040004600d01e02c0c1926400b8025081ca002034003a4045005803405410024006035009950350703140006454481c079025a1040d07030306141d2b02240074001400401c400d00040040201c004100c040b00c0018405594455849002421500c461010222201c5a000388801c620000e20317420f0596400b09114481600006080750540b01e0700c159410100d000e409400d20b00035080003401820395540e03052546502d400241254091b0040d2000300050742d40080c1c00c0c0c041c205040441c05c2413461080b40c881303002c0180c0e003045404110b120f0503199110030301c5002c402041d4403010881c1d1a89844c03a203080c602c6c540b001c003007115001e4190701d00d591076440440141200c410004a50003607a51344244000c038410b0759070141c0160000079150303501 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 956678426 1250 956677176 956677181
    0xc010309050c04060b030114060703050a0807120f2c1e0f0105091f140604090203160611070e01060e090421031e05060a1503020408030a0c0201020f03040315 69
    0x1954007910075288095145800182280c00c160401c1c220240040018080103c121611000c02102075603107518048064401030124083c440040c01040400b00020700c245100345843c554039070400b07000f409110030000c030840203840e81100d80c000b002001180c0f1288000c031811400d6260201c00003500307241005104800c414640000d150f084d40c8120050b20401e04003d00c0b61078454590071001d0281003000c2032800100c090310b2030300203003407a090101001001800b001c0c6941c00c071604603000505000381f0320110341010000700c41e00542401c0c0e100e00282c4103810103001c81d241d070400401c1d01d1a103503c0b00d107004503c076000c1c0111400540c4a000c0d948090822044664000b4000d0740200d4081c45c4460307644540403002861140065162000c942c0c0042103d40c0200c400c500c40401441b5906e089404100300d040c580c403900141c1034500340d15549081c003a13412100a000c40c9020b49564084130352020301050006203080f401440340340445181c0356408420748054aa000c50b0f03003000407111840f81c402 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 956679676 1250 956678426 956678441
    0x30f050c0313061509061802030c0d05040615030b0a0605061315020304080d022b020c01030b01121103040218010e0c0901110d0c050607181a090d2609030c0103 70
    0x1115640c03072242d400d0690340301604d4030040c505040003041c050f0400c1040c040c0c0d20364003485400068014000d0020004070381d02034540d00f030310301203001404d6960ba04208000d80705030401e0b4220f0880f13190300482401404082288180c10441060007010350310b05c24005244140024131140307420100041c801c40318007103403d42800e4080d2040382d04198072039140b6403d24086a0043d4090391240a10708040c1442401d041240c0d4003016102800300004500039403120580c0011034101540d450486150740c1c014a0f1500c014034010000300b01e540c812500b280015402550107900c10304a46c50003008200c2c91101032810b03074506102c90030254954141000c03568001101c2c481c14464907030300100003a40308125014281c05150b56071988124942003960601001421103000c00640e40080d4003803421301c0d202c1100f15141d1030068201000c403402100d030203005662600e644a5280320ba202c041c081084644018050700c0d205c030a1302c4001c1c002c450800c1c0d01c03d541e940394040c1c0021403d41036642c003c1c0e1200d034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 956680926 1250 956679676 956679683
    0x3030608030301060c022106132109030501060b03070512101206021201082e0b1c0506061e0f010306150203070302071403060c1813020901030f050c0313 67
    0x282162203038151800c0d500260000400a00b04421190075894058248510b9020f0246018822404502e5107600c5d042c00801180c1031913540f000f413804203c00c01102113a00640b6090712a07280103031040040c45801e403032105403925800e284001c184070f00c00030100c0f4010100750b100c0030f2a180e0f82c0c039464650824020304020050074030309030024443c012404010701041c07140c0780042e42d5107000140480b2070001a00010925840f204450f00f10075200050041440c0b8407030350070500d20990382c1c3c01a010f0a0708191141d0070028550114061004a460039411700c1d1040c0c0640d0400e0303480f803050158410803540800c110b01d2580b400c80b596410500c60700c807500031062501080c00e42d11072007002c1044856003001d00041e8000201403040c1641405600040c100b240303403006d42c0e8003c0000096070760714064014800303903d0000340901946200c4050300301048014100e240000900c3c1c0400009410102000d40030074189161300f4500601845a288120041440b2904540343c0f403e0010300095080381c201c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 956682176 1250 956680926 956680931
    0xd0206270a0b071701050303030109020702040f0903080f0a020f0711011112031801061d181f0506061315050d0204090506030d14040e0601090b030a0b120c010909090303 74
    0x14100420301010401e5405800e20380d00c035041040000f40480928060b02d070306802450018000e90f5070110449046902554000d40c80c0d01d00b0740005802010019a0b5100305454440c01e10308143c0c0000d8014402c2260b240802080d80e600c079030540503446500792b007084490040103140c0014030150641da50009041c984001d03074090f5540814504501c95000640c01a404010881000d44003801040041c041c14002c0c032105143c580801d0240140a9245507c410980c000480799400b541c90080740072a9402141e1441d51007420702c00c0d4400300242d41820107420000002d0303641c1407803811104110038184400010519100e11887c040398101c007040200b0000300819208048940040c0003d0101104000745600b4000c0c00c1600d041003c100041c1403104501d02e80000000c680107440031030b44d07070f85401e1000ea500c500040710f45464641122820140110a0001c001e0965000061046042d5500c4049008200d61166182d010081281c0000c503614401d100000c210341108020500c2414007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 956683426 1250 956682176 956682241
    0x4150c11071a0408060a0e010e01060b0f090301090506070e03060109090201050a0f053a062d050603130b010e01050307091a1002062202060702040c2f0f0d0206 70
    0x3c13908045050782d0301150280c495400100030f110a104280d041031031079008001e40381c90040207148501806810b030515600100e0301040e00c0d242904004c02099115041d100d02d841c080c00064810002c40e0070b640d00034401c410002c1000d81280c071407a4115901611031500301400c4a04c02c59840e00d81c10040c104000c01482408403100010050030721101c0641417090b07495083c402a015005806800700000300d0900004210400c0031411500140301d0f0850813000044000e21181030006196100304e0b001140041088044a501c0d2000440c0c1c2d1300c0348045a003145d0380c5440c803440c000003c1c081c0c542d268000795410040410507900a181001402400b10300d44401080020490409281004050380000b01003103c0040788424400c142440e00001203210040d640101d425400740d628024019a034a6540c5070209024440c0480203c2c1e9240c8a60401020510b8140c200811619a4841c920882848070002d43c4080342c00d0207480380715802445075036103d02196510440170f0000c1080400880300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 956684676 1250 956683426 956683439
    0x60f0d0b0a060507030210060522140c0306030d0c08161407060c050d091d04050307020a08031e09030303040f0c090203010b040e07020a050604060507031404150c11071a04 75
    0x1c0c004024015034680d00d03203c0030305080190402c003021443c0e0040e50318003541800560f03243d40d1010682c288040101081841540340c04008000c6444032030b0704e0903400300c108400706e2207a40c021071240c0750075070603030300898981d40041d9140003a449000700310140500c1b610b404402c44001d404030b40750050700d1000110020341d81d1141065496088480002c0c80a00f5140c280300003040044400b00a61030702d2011949080c83c511140c5d5900d2068020f0381d80f03454049824024100142c4082540080cd1186800c0d44c0d41a00ca1f41c0b42d00074600052849880307603010030b2043c6510165482610050059840c5960b266185010b505a50400b118643d071171032008140c030050303403010f14060800e88508680c0e4500300351200c001aa4024104011544900038040018030b01164103600310b5806031003c41e41343c41d001130982c090300500b29409184524102084184000300103491400c080582c010030031040807081c12610f20f02003106641d4540d1058404002110004008002c1c140712260441d003042e0b120303403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 956685926 1250 956684676 956684689
    0x801051918061a0307150801030f150c0e1e0108010b0306061611031606022d0a0c05090f0c1b03090d031d0a141311040303080117010209060f0d0b 64
    0x2d40c2d0074150f41a5400c411090400b00441070240035581c40c503460400c0d614800511001c0c05000c010084c00d41c022844040001c400410a00445166001c1c080403c844100900c90389a1100c000e100c2c84000b111035642c400070f07003450490071406941f01e1109a003400d04d05100380d03201410440d006003080000305070040f01416808400341c850024910001c040d941010310f801f807580d5046524510b041010401207400140c3c4080e11100b0510303c0c11140f000300c03200c2410b24050405440580201d801c039904100c4290121030503528120342c06605c41d02d0301101c0030140310b411105000e110004200b10142402103018444400c2400d030704407072800c40f0b034030042486055a43c0c1d0403004142000315030a0484504000509642d4080c2c580410007407a0000c031580d201401c210207801900000100f2000146542200160020548400750303030700e5407490010b120503000d01c1040f03152081080741c10b14440060084445174000140442d003080640300381005650310502100d0100d990701d044901c5603803201d5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 956687176 1250 956685926 956685941
    0xf0a08011113090519151802040603050a0204210503071a160c02010504091e05010e0105150705100b011803030531030f05030c06100f080105191806 65
    0x2a007a168549401c01189a60803400382c01a0b410b442c10141081072064000803148044402c0507008240650b0b03e458004520b1055088171020313445030f1020315803a818035001882141c6150f54200595035414002004070700035400b500411050342c01e071001240d2114900410580d000c1c80c01c1c0c07441c3c001c41d507603a108031104010304460b042295004014503010090740a030303240712540c00c1c032005948803580000e04038480e03409003480e5140e99000b445084c96400c100c100180404482c00c009550319100c0040da0400240304461103400440300c0a03402d80c8162055452a84e48400146440e04100c16250040c1c81407101c0340b81000105000f0a10505c0e034250040020350103500c4407640e4000715a2070040d9840210440601800d08007d00660031102c80300f19800c807034001803006844c500c5881c0c418214450300d0710002d420b21400742405116a40084c07403c04841945a4951400c0d654541207803e0303c80480e001d0540200b00803860b003400c0364640006510900c01c2450a02511085d0b99610403103210 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 956688426 1250 956687176 956687201
    0x1030e030f180a080102070c17010605031902100513030605070c020d120e011403060603090a02030f0d09060908060703091b0f0513020403020a212306100b04050f0a0801 74
    0x501407150141c00c1901140d0007a004c04802580b1b00640c80d03e408000204a114a081051614010b583e0540d400e5001d0700207058000c081c3c4030350800d600b6512203040742039001030384582d0180c0812078446000e541114004840900490342c150310b50340701e01000788001800301060140c401900001a5901994031032039910074074107420407000c000c038000d02800c160b071502c034103121566020358195100d4106607a0302c0302040318142e5695840984041c01c2c102181c02c02901845211100702c1b1140c000300d1a00400800341d80d80496003503458000b00d80d4801c0c50302c2030242541001000c81c0817248241c00404003140903100e420034403051008151002102c0e031707012090440c110300041c8100e280c60386889100392410541581403d04580000d400005548151301e5801d516a81014803140040000e44820340c00c1442041c00c042d6101a4880e180d5031034894017140e0051400203446c003c2c40004240c182d908014950307007010b081005100342141815501680b0040c10385001070038440c24003442802d4a107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 956689676 1250 956688426 956688457
    0x6210604050c0f01140306060702040e0601241e0908160e06100f1b020901030b0a150e1906090e0a021008061302030606070b01062105040f0201030e030f 67
    0x303280c00c015007416259248640b181c00c607540d2446181c1e078044090075148803001c01440e9a501e50b0300c0060594810000000d4103d4102540e90391089400309a0324100c801401d141c003409544c4207908800c08860469110102c0e0403403001c6142c03c10b00b84001401c00000341001e001060710744240510f4031120a0407240e661440c0a0144000da12907806070f81c0000341924404512904120058954107900d52920104050281c030b0030b00103001c50082caa11a50068240d100e196140d0a01031503400c4100e40a20116007001d0682540030000241603045900d0b00c2032424164450100c084103004081c1c405610090b100c40c00811034080074030581d400200b840005000d880303d988140140c0c000545403000c1400001d00030031003241c0707403500c2100d41c42c1d0b0300c8240141c0e2030b942c0303030f00050550150a8000d410051310034000b150780ca822032202812654505800443d0079820090f81c2c00b501c004450007400480107a114100550080e04400b50280412040d00e00b882c0b041c440044458201008100d040341 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 956690926 1250 956689676 956689681
    0x2010b18070906140a0e01021903020606090f04121d03031603020c09090d141207030c1407050703020d060e06150103060b0a050720030321060603060117062106 70
    0x25003240c082c200a050b00c0c1801c3d00074540c8002c924000e802025079100c10300010309080303a043d80c402d014595485107403612010b05440b071800d0003559164212003032401006260302080c1c603600c8481000e80b0503940300725040b41d14010500c0440d0004035106580f0501c001c3c0700c64800c00ea9074140040c0c0180d0300a001032101c0e100482c10000d2400300c44075010750040200310144920203c011514140061960401f800e00c1c031101e920541442c03003480d0b01405004565018000e1a640c1a0004039041000e41e0700c0c1e01da4080c907401c0c0440e80d441074000c01016a0b200390401c0005040002007581c0c0036004030b400154483d0785a52060410100f107070500c1035204080650005036800d40301c0d42020b01000d07150ba505000c861400a0503034401c2c01e00150800c03030300000e449410705083c54154551100681625103a6107489484140107905441a00320390010400050807420f2400590348034007016501c144000204c0e0f00414040c0402034a00ad170803076860700d505500200c0c1d140c56902c500010100a00d02071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 956692176 1250 956690926 956690941
    0xe040c08160b0a182111180f090307060218010237140604140609070f030f0609050106180b03011401060503040507050d030f0806010306030209061207051c1e080f070302010b18 77
    0x10262001c5288030b07e020340010703031000d1200101e4079030190000071100c829494280c840da1944c010b090004111900000701c032134042d003199001510054003038085a0b40c1401c1d074441c084038500c02c002d03c401c540d400500d441a00c2c00404141000d240d000e040744141300ca01d1002c005062110460382a216101d84035981c0714100c00401810354403c01c050068000f0f541401c4409210701e081d0301c0040c111610f80305429084c0b0030a070703016610a81d441030080012540d034220400d4850040484000020300d05021151a07040c18083c901041040005003441c582c20150180c0b00c0c5d402c0600191094460000e021680391905d0031300344029806519428034420603100001e05400c801822203040504041081005031128a4031a0b04414200d507a51989146024440e01d010084d500aa92185500303004204c0111070f41c0004031014025801c1c1050719500300707074800665403c0d13503009122840c10402000c2080700c01028103010b610030310004c41c00b0254500007490350960020259226107561040c800031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 956693426 1250 956692176 956692193
    0x9280605030109060c080709140409150f0c0207080601030b07050c210304020405010801020c070b0903161202091810090c15090f0824060a0e040c08160b0a1821 70
    0x3000f088e141c480540c44c1042d40403024000c5e40b10141d401291941c00f20400c0040750059855078065041007049840815146400541040821000540141400401c0e025404100103040c0c0340c101d40c40005940b5081400c40c1d0641c4a041a00c54901170f0908054050004015486d00d40c0c001c0145241c40303041a00402c0115241a80003141580c810016056040004078040080381c1c5140c00103615001d000001c0780c100b40300d100720071070310128011000c240c07034160407031300c0050600a648a807242e84e5001c560040b80001440d0402507607011681070710f0110401d400c01845a4894840c01d100243e680231142042442050320002186440360240a40c00f03000f80100000c003054002004840c40840545103400b586003100b607030701d41c01500040d0030350322000c60601c004e00c0848d4107129036180500303181408001a00402d001030107000c038144100604094030b94141d6144206180c07900d00002019154040d42ca0109501500004e500040c0318450078204680e400461818005951061400510 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 956694676 1250 956693426 956693431
    0x7050f03390306090c0c0c040b0105090a0f140d1a07020102211b03010b2a0f0307210801151119020a051c0f05100207080a080609280605030109060c08 66
    0x500c0700381440305541b0810300182e001490a400e503000191440381200480d02c0e841162031300368208082c81e40000e00c0c5010704445100702c03031304501030501c0d0744890310405c41080c425500c09000804318880c0a0098850040d440760000024000103280440c100d408a52401400540300c5560400e6402c100f004103000341074180210313040507410f1542d03040a100c0d254500400c89655907420424217840c007024032554480c1a00500c0d00c0484041c09a50303400726980b944035202c201d8814142c1354140350640c9404884107046286511003682c60380c240780c02c42840c0b403440320b440020803840048106a64a0134480c500451076280001c1c00146030754014840c046007158040742c002c01440b90f13003501403a12003e841c0e08495001d044015960454240a490301c0c1d83c102000052620029016041103400f00c0100034a914548486010390b81d91801c000c0c01201c11100708043c2e8040d00301c02c151028091500269081d80c1e12800107069440700007181c215005030b20122412035a8010010b03c25130440305565 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 956695926 1250 956694676 956694691
    0x1c0c0c0515010303080a0b04060b030405071805070c35220f030201050c160e16020c1305060d050f0604030e0909030a030203130f1a07050f0339030609 66
    0x450a503d90340d801401c2680041a1910341c5a5601d0749a401ea81c60b50000c0c00184604200281c8900306420040d8035030100f40f18240c1c1c0d55810101c00e54152102d8000c180c420301e159111240c0b444021340312400826490340c0c030319001012408480c03c3d46090050510303811408850001e44400f1207910911032641d68a28461110f070a030f8100700300581c1441017403411b50394280392268590b061600104d203000c01c000c40207050703a05450808200c025540c24824400c4103100c030030302980201d000e07090381c5485900407042d4001d590703810710344503400c6650444c68000700e01030507255000215807609070400403e142c2081e0944c00500a000c14036a00000c00000320034200d43c0585a03041901c1103035502c0c030409201c54281900840024085281c0c050380420700303a00310f03a034907106002514008120056582e02514000c1d9040041195184150103581c104a001e441380c030302e952a8154550201d01c0d420000b20030900701a020903408840f2510004070f941d111030707400c076140d042845c01c03c99404401001007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 956697176 1250 956695926 956695963
    0xa060c0306051e2b080c2802031b010c020f0609220b040b090a0f150303030f0c0219020609030a02120a060525030f0f060b09130b0d081c0c0c05 63
    0x320310010154180125103501190349992451b205100b00d040409000380040e41203251880c03915211245060707030354003074800c800381ca0001d074100b48101700a010300d96040b400240088160001428100603090460b41e00a05050509040e2400201c01074001d00c4000700300304145586c4491480540030795400307190112001d1120200c58400f180902c0300c0201200d00f0315403a040c8031580c0801ea980007609402081c1c140304080f94a034280a03000d01010320003494614509039081d10000d00c00b10700031440001d000040800061260200100ca40095041c0c586c1409440100001a038421119650454825000d4200706c50641015001c40d0360041002071ba21544404100441c018080034081d03059140c20300088130b4900303800752801800380e0720f49c8105441c0b400c60003190302203a00d0040c003200681124201040d0140a0b4a04180c81a0101d04c0ba0032441200795100090070900151540b140b5007107079030360400103480e01c10040d80d03448911440441e031300c1c81c6c4550034020107106102041c49c009020b07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 956698426 1250 956697176 956697229
    0x90702102d09121d031c08070f081801020d0507210b0d0b090c1809071a07020420030c041403010209090103060b010926011d0a060c0306051e 62
    0x28841803880c82c0700030701c080002c2c010a0100003180b0380c6031315154110143c12030f503408040078017030065850705034564404105034100044900c3e204165400c3e6400380c5a0716104580c407003044030a030700c4640d05800a02950203000c10403560700380c1e10560340300d003c00e40c1d0348041e0380101c642c4c03040314600d03801510891281090205101511003601940c0c0f1241e001c400c00403180d41d40c0c1034a40c01c000c11030b08201d510400448808000050a540090180b120300d0192410f540c2d41e000c4140c8001e02d8900c07082c140d01000d000c020050700d000d80c4010045030b801207400070203110039a0303659010361044910100c40b11000c9400d00010703c4403d4820240744042e402140f030318540500049041205200041003240c441d41cbc0c3c00c0d81c076417240010000402103101480045180d9100400e071540f44c4008450503580307072802c2d204403404070083e006500c8030406c0181c400da03e065158900900709900038101456100e140c009a039840d40b901907540d640b500b1072405910001c1c4400c001c40d07240c07100194018114215007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 956699676 1250 956698426 956698433
    0x1326030403030e120f250501140f041206090605010902030c1c0617030903010e060610051812010504030314240f10021c1409090702102d09 61
    0x2200c050300d81600340340d5801d00d00710000803880c9541c006212440c1c02444007418186100244d0b064604c440d1942c0e0705180c00d00031000c1804103409100f0203000612100098014140340801400812140c0000a20301503c034580c504421100c1d2404030382d21603480342001c081c018140b29083c00f424260405510b10f042014050f030740c44c0100810031400bc85169500c0d0a068440c0c0d0200c0010002c070b4402007003012401490303070703121b8000404950281d42080100b010300e0101040d03280c82144000c00c0c01020380c44036502115540c20140e22000008401e100000c0c00d543c6032800c0810040e403110000c40e2915191400805079403541c26011038002040c41400102503a419250b9031803041d00500898400110000851001c811412260880c10155400078036030f5001c110419240010300c0304110803000e1000844200038400140b5801d400248405041ea1400000306c6401c06030703510440301d0079900310000e00101c42e2000c0120358001d0102030155951a100c41107030703507601801c07901001080c3c1b2585 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 956700926 1250 956699676 956699683
    0xf15141e181e040506060a02030703120b03060c0d1802030d03110d060e0f1b0901110c0a0602480604080601080105221a1b1326 56
    0x24003855034210045200710940112980c0038120807401400c00c0100b021041410064110500d0068000c2e0b090400184450404a0443e0070010300380d401103140500700d4400f140c400c8088120401215160701c0b41d102555001c1040d24041e500c0e0303d0810355141c400c04181c40886104507003502084800418210140e5400707d40881d844606040104008200304928007082c40382240800d13401c3d20344080800c000c020231031038070711070704056219200c15200d42064105414008074000802c5808008851095100c0d074100e08010300400102c0d00c0010800000550554180c1c00010041c0c4c401c4091600d00f458841002e0901c0e1a003119050904d010f00800c4400004281c0010140c1403041095a441d51a20001c443c01080004165140f07541c4444a60b40a00002e071034010400d820500c2005030310303403003100580006a000620788080d40301d80d20700c0c03400707110010b003410f81c40f241880500b070b01551650010030001c01c03091036801501e070912000d80c1203030122011183c01a0609410303a41c5002000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 956702176 1250 956700926 956700967
    0x206091203092b0f0203043503030f07030c1b080901090f0f090c03060b070f0203030c0312011d0405060109020c07030c1503050a02031b070c0f1514 65
    0x24540c507a40d5641240b850719082d007420340031885040c0446581c410001410034498200c845a60301c08030516a02d804070b85c0c90040b4042c41012411194214400c000002c40c00318034590034000300940301c450030310380a085402c2110100310105030340c82045880c079450300c5042210011030610703842800400384501000c20390b400c0e00178548800016130100a0380140c840000038004200e001d8034450702c4006402c010346a912844030110309101b01001524000e00a082c10380e07510203541400c2c0240754a134081e841c10300303100c03e903054001080920043c1c1000d08c001d00120180345810071040d4501a1802004440c10b10a00364903a0081c080c400080e40104203e81160004c0c50302503142d20040c0c0881e42410b04513400102414458180010030b809030154240c80584243c500704441e581e0030745844268402200d4001d00c00401500c2c1e600c2141180020f03001c1d01d0701800d0260107a070f031608410801500c49402a44484e2184568650300c01e52189455805900380d80e032090400d011030074001c46002c0308 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 956703426 1250 956702176 956702203
    0x110d061a0a141e0603040f060c0c080f030712050a0b010206063c0a03152004050d06021207093305160507060809210706050402060f0a0f0f020609 64
    0x2c20154201065107a412104904030013020320f503680c00c10340313004201607900000403140c407810145910400f6000384003078803038160000310003031800c80303001c0c2031001135030004182d1170903c104484031405940042c80307958860003903901d00060380079603807001918290000300302a10500c50050f0100c0d0201e00e00848800303a490b0303006e48000101d440a8800c0005100100240d0000c400807000400e101c155040c2a0507a85c1c4480c0c1040840440e481071380c240c064202e0f0f03038100d0110400c4100024100340f40e40c0c1c0c0c0210b0154000500b4034503410031100e40410240e92038800a6030280c2d09000240d2003407002c075217079a13150b002c6014200c0b04054060300351000504403803d00c00085440750042903d400642501903000041c0d4030420344035040608003020030749120440c1d106078901609281303e02d00507424101e18280d103aa051190980e02c030009054001c004031380007102405042c500181c0d10002d13201e61400b90301e4500000c040c0d02d900a10300e4088941c2c0c0c00c03c540c4864240210f042011507031130b030070202 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 956704676 1250 956703426 956703439
    0x60503190b04080c0d0314010806090706050f0f0f0301060216030c0b07021c03020a140a1110031b0c171c050c160c05151213110d061a0a14 61
    0x41e50b0420f03c985028407241c046480c05004000150550b140c1c0c0f200300301200403c0e1212050341c840030080d60300c1c0d4089036141e40701e5110070020302c80c1e103001c0c502500e004900501c185280122410400301c0c1508200c0c440c2090040c0480180080358062180707248210000710300048541c51351301c603414080760601c603440711030760002022810b5446140c0e000e4480368503401e01d40049807141c9070080d0f8401500d8000e07280d0740f07440c3d5900d020703280d40031402244483e00301003d0002d5504040070400d080030481c521200b41a952050b401941120049804200c036031600c4442c50189141400d904c803c03140404a00c036594108110380e81502c195209a008280310940001c44c0c1c0d441c03500085091017603560b040c02087d140c51646040044900d016816a04161045055813400c40c004080c280104680200144e9101001640b18000311000b412900c2c019109422f60b802a0b401203003a050384050300361341081c0c43d01030b8251083d036801c0d201f03119020140d4145502031303d440c4e400000d8440300440c3d0303485040c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 956705926 1250 956704676 956704681
    0x90601050f0327030307030614030c010809070906060f0206100b190c0212010b13050f0105012709050103030f08010605042120011d030a060e1005070e04060503190b 72
    0xa154074020f1010110440c07441404004503841541e81e80c1003201c901d40080d003050b8001c00c045c01b000d00000d5685801030020480104030b0710064a5807440140080d40134858010005003101203400381600420003900c60030510144010000d041140c02800140c5d0034441050820841d03078510111000983d98446881820060b440200d440003803100c40a90700100240981c01c0303d031419030140c0582c030000c0b60038002480d400030341c2c501524800c54440a01c00c9a02004100079405061100c00301100204500c4050001031058086107810703030081021107070b84500600400d5004154140c08000398109840c00c0c5d89400780003000c0d8407035801000c0305d00e0702420100308503042420032008080ea00100401d056984181290301c21408540e400d40000d00120800361349218441000100030400703806409100d08a44501010f0b1a40100c02c90703e612901c2080c107140b816912075039004058a54406244440c940100001d40b10f42e9000f503840b03170308031100282c4401d240796520a10540d00c1100014140d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 956707176 1250 956705926 956705941
    0xf0614071418060c0f060108151e13081201031515060e0a0906140f0910051507050d0804060c030b03030702150708070317071b15061d1005090601050f03 67
    0x103001307078040ca1403244224040c50a0040f07020442034140c0da400300032903001c164040603801144200f5101710784e020020341005c0700c440d080b42440c181d0080c0040c0130141800342c680d03114403143d40030790034402c00c4c001c0c1d010040c800c02c803c080d4080090401c001082c096402c29091900c02156035204607020f0103007032420003040c1c0d280c0d104020002c01c10304400b000006e598620068cd454800c0008603c83c245080c618040c2e03152900740f02d8051800000031048a90801043c4040124646520b514591050140000084041061510048007076461789854142840c00ca01541c1307161012005050500a0351602c5440000a503181150100d440c0d810600c0541c01b40c060500c17a00708094146c03240010642c05241e0490105100914030b207940c01541c1e611040d044030b04141070031480c44585018404000440e1516550000c0d00d10601000600e50f952424900b06503002c00b64900c0000316408100090100c83c9040c01005200a85a500c5a40781040000380684180211404a00703800300118810 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 956708426 1250 956707176 956707189
    0x303030619090e030d0f20031e130b070302030615070f0c1509060509060a05031807090902041b0c02091b0310240504120f0f0614071418 60
    0x6241e54207080000014190859860381e021065041070a41080481001c0b803200d840342c2e038040c50f076580030650707d10580354990b00164400b80c801288942d1001d007030030100344213094881c01a5810a00003c03882c02a107030400344220010000c0003803610500c1000603c0c0c44109940d041c0701d0311011a00da40759002d24010b6186c0102a1018061000e1010041140c01080c44100980115a01c0c3c0c03142e41591275000f16014400d0041c000d400450a01880140300d005101460300b002601c1600001016034139110352920382d00e54441500355840d08030702c10950074107200340c1030300303c00300b4110001000b9014400f0b400c950385d8400007030207421604001100b00501c2c10704402182e80c0c0001180d036030b041092890340030380b17018060300201c0b5400038003a02da1003251848441c80300085071140350a00d07241c80880300d0404c003120401d48005580d400c4810014101c08460140c00744500800988000005100c030b85141c0018220018001c86000e0b50007038520403800c1e5070f40403090f10f03007162a040014011840 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 956709676 1250 956708426 956708429
    0xa0b10052109121e03090f0601121e0f0f0602040f08060907061b050115051e01021b0a09060b030109060509010b030402040c11030a0801080607021204033e040501060e0303030619 78
    0x843e060007005005400c6c90118052402c2d41001c03089807403903621424072011402c98064010020b00501c0913402d41d010809040e035000e24001c1c101d808100d00f0640352064412989003044800c0d82e80080e0500c9011104d0031190007509490004000f1450300000b6113039240c00502808041c080b480600305081c0e40c3c0ca00c0b0509985501c04001e00c0b05412185c411241c0c0c1155008041c404c00e00c8401100c1c0315100d02e141c042c0c0d803560590003061300ca003a0700a1882d020140d9417201d07030001001c2d400848e040503507000e01c400400101d4039242ea00d42c94288041c0c1282c401e030308818403642454004101c14070720303001642d40003601101d0014805500d85001c1c0d506480007102310f802800041681c03039030540c100e20824100c550f140b040e00c040d43c1e16a60100d8071030031205090300c2d6040040c0700c1480415924000440c0032429201e400106800d280c5103a01c0c804d01031010036802c1414400f4003c07441c109802001c1c014101c0b4100400c040101000003500c03808010056030241d8100b140c1881c15045002440d130 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 956710926 1250 956709676 956709727
    0xf031a060a031e03020c100c1103100c0905030c041503061104090515130b0303040924030c030524010e04022b230d080a0b1005210912 59
    0x2103d10b030310040d2041c4100c03403c40c00341c02500a500c044000c60400000320700081c0f405d90f4400c1c051344140d55038090344030002e4482c2c540520500f035540160f621f4030303c29400540751b00e0b01e82241c9145001c04062810b180582c019000e02d081c554103802100380c0e580c103001a65031000340810300d1007141b480020381c2d016540c4540b030700e10300b031405201d4102c5184080c2c18844205036000f0f800c6c0030210303200d601510260103050b909031b84100400c00a41e8421340c80400c0540f02d41107080040011040d020b2000c0300c0a4200340c804130040d150802c2005400c0080105480442c0c460a914041c96141c140100c841403044403004903071400082d01b15a21505c00300e00c00d000d15240d03000c030509003540b0300c1c0c5054040342c011500e00c940100e00ea0410108881820700d06000c19000f0402c0b203040150440b0109009001c4400094580d100008a0340d506001404000041d44d11992108050680000300084e12102004101841c50034400d1404000c66108000100341500c0d030356416407026042106202c100090 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 956712176 1250 956710926 956710943
    0x1a0c06070305040317010509070f020a20010801090b0d0f020612010f0503070819060903140d05041707050a03080c13030c0521100c0c02100201050109060f031a060a03 73
    0x140c603806901071401070b8000d5640b800c5407611040b076050f02030000e000760395000c0c0320300300000e6030b20740f10b00f40410f0020b020748103403a464402a540d08003501d00d1204014040b41c3d01140038055541d1045207580144110325061001480340008030f0b2201c150b41750064072005401c80c007581591078440c1100c1d03c0c7c2d81c05d4183c4110940e034461104400ba146405800e10078007139240009001400041c0c140e03025008000c500b848504665107810050212032021030a11040c0582c0e0010b1841610240641d25509400800c5600e06440d001c14450405002d5409d00031043c0b14200228500141d40205658941441a5a51202c81a281e864010030b4103010380d600c1c51001c04000c01420006450403501e0684c0c030031101c0312a0b4040d6442004c2c0124100507594040c4c0d41c6440c0f0403850b6084030b200350400e42130a0755502d9003a008240c2d0b1111161040015030344500041110210138450303030004120010204200e1402e660781e044c2103944504404000444d81000301c0d815a5400005100460f44080b86 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 956713426 1250 956712176 956712181
    0x809010306080f06011707030215090301110d0203060102060708040305220f0320030a0213020f090d1406061f05030a022116030902090115112505040c0503011a0c06 72
    0x29907a2513009000b11145d81071a4820001d10304030005102c41500d80c020801d85441900d06144001d80d0407003020340d40e056403111708443c8003845001c01045400c2e40c1d40d40c090b80c0c0b840c051001a1500101171b00038410000128100401302c2ea001050f40e0041d5090342c4e90a44505003482d0f10b0007039140c59040a107126950f04000410032800e1403640c040c40c0090303006c04a680e1110000c03d80c82c0e086281002c1d401015000d10000b85041c60b500078a648080504c8842c103042100700415411550b40f4070484c4d24140d02c0d81c00d5800320400b040f1648d80098222414030704808000c90b03141c0c070340f10707202e006009216011010441c0c01149805480244180136420030f415090300c204001034800c00c0c0e030550940c40e543c41882130500c3c4240030314803182d40c0191600316140d00c1c01e00d09140300300250300314408020070b890030401403100a01506200c03003410100c1c0c014200c9103841d40f1494802c0783e0302c110300c03807403404c1e005495003038001099a04540711180039201e1218602c4115102c0c1c41a248034515038002d4204 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 956714676 1250 956713426 956713453
    0x71104051302191a0d06080a11090f01140409030903050a0803160f021e10090c050127030212070803030f070e040c020c150708040b0705060f010e04080901030608 71
    0x5401c1d1440b402202d1181003241840c2c02407200c0311a034026070030311044001100500c0e000141c010320900d1411400010400e60700c000c07040c200044090100c4003903000da034400307165241c100ac1581d040440c41e45c605040e03501d0b00182e800c00c0c2e491515418060340e101c80d00743c002d26004003101c000643d009401c1d90b901452030724282e5600d9004035039160b04c4030001134020361800d10410340840e50303c02d143c0080c01d031824000070a0042d801040240c900d1482002d50050114503680101640c40f403062020040032410080090484500468907521980c611614100c00e40210104241203075019591204a402901550b50510240e03400084881c800081030040380341000641601c02c0304c459503504842c965010420050725a120b00b800c1c0181c2c04000c0201c018074100e80705000121603e40c49074685800c56444085c20b4109500c0a4003111022404000348482404010740c48454400005001c1d030502d04421840d10010304003030980603010502d0541039000e03910110240c01c1d1362048440c0998040e4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 956715926 1250 956714676 956714701
    0xc0e0f27010e2e0e0c0f1305040b010e061603050c0609071a0a05031819030809060f060a030b0402030102120a0b010906320f070c1a0307080c07110405 66
    0xf20883c3c4454111580c181c022501d000b01d2000c0c9a0b4491240d44200345085221080c10760040c103c05807115041050200c0b034060381008246003440d01e2211004a840e0404100c101c0e0710200c4800e052180041d521409680d500c000c40b842c2c40c0702c0c82e02c140429285030600b142e244c0500c4034ad108241c8900300a11086040000b0b4400841e9523401c40b858003045103599021507800340001d48408a482403011940d0200644001c03258040b07c2c4080300e001e00c65084043c800ca080e840d90940208a0100c10702c5001c2000784800c9038050030b083c543c4545d42c142400803650316a840d201c0600944541c8004c9403c540c3e0a40440700c12001c0080c01400c1d90600681c0c4000508043d8000e501084109000162950090103015042a1181c85810b62646489a22074040c45142c4411082070020498802443c441c0744c098424640941e4109035228246501c0030000c890740509211900d00c10300400403840e6101c140036a20058003030040e51103d0140c50207a503440300d070300c0241d03074080d040c90100800301d80c082 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 956717176 1250 956715926 956715931
    0x6130305031303110402040612090f080307050d050f0c0406051c060b251509111002010507021902030c010c14010629120c070f0b090a060c0e0f27010e 66
    0x540403403107408251310810040f1b1140b48580c01c04164083c480344035480055000d600c1c5c1600460301494040105d6a581c00030360700444000002c140c002c90305370701c0d8001da0b100b000d90001c01c100200660307041c4040c0170082800755215031000c00070001941c410150001916220183c0007102c18001d043e00c412b0740343e095412141d40c001d40c2010070140441000014209070800c90b0300a44600d00e482d02e00b04c2800007034000c00700c09a070411009000e52540380c80700d4a8004007100582d000003058144074038000e04180105c0c0c2c003016826030307440081c0c0240e50041002c1c03038200002d007402c0c40d02d05182c1ca001d0385000d0038042446606e5180c00400500780201c92074110680365620f80420550705401041070380c034000c076003d0b003910348607002c0040d60808007030000700400c5014440017181b0085c19524041c0e616000c40b43c50030755400842600342080424024074101281f41c3c20846240027030703100460485203a03800d0f0f10b4801c6011001d0710441d942c41c500803100c0039070b602c40200c40540e140c196031308003200d09 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 956718426 1250 956717176 956717183
    0x60309030e0d1a1302130504060e06071d01030b0316030201020c0a0e04060506180709030314030f060f15040803070b160c060510240f0f0c0206130305031303 69
    0x140d00120305034940ba034240e016540c3d010f8401c035480c2d05000000c00a010005205040c4040036107688009039848200d641c1507240c01c0c480100c7c40b460146040b10903244000032000480e4029000e10044580050440811070001101c8102c4da20742080101c001d000010302054250198074510b8000210314044002928000c6e000c40c0d0b02022900c081c130070041040d220342c607036000c0c10002160002e0300726000b058109100403c9460a50119124841103010503141c4a000c0340700d44504208168000b055040000c0e68560f82c103081d40343c200e411121010000380520310402c500b4040341c050f940c40200302c0c08200404604203072100d0700e410b03940c1d41e60b9122820a4520055210018541140c83e0000c004c030203000d990f4045220007542d031554054200908150401c141d00040414080040f83c0c032401842820001030a607010580e4016040d8812074160704100310300c0c1c4402140b5a600501d80b107614690644030941e0b00c6d010403441d45800e01070382d0030040c1035000002d80b401d0204101c91221003500d00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 956719676 1250 956718426 956718437
    0x60b150a080106090b09010311090613030606050105030408030103021207030510060f12020a1203051207030614120622150e0d0c030e010c080702030105240906130203180706030903 79
    0x203d410081c0c034000358a116038032030b428081081e4032095200c1d4105500d103a602d0300c0d10380e040c641c1a00003e44250000020b40700b0700202c124040040c05014000c5800400007824001d00c0e5017040d8850032000d200500020b8005c8c8156054139031207800c10007002c3c00442d0050165480c5440d000c40301c202402080c8611000540300138004518451548814140940e00a2401c0c62b81c81c501100e020700018507400580c2401030600c03a02141941ea8101b1620591482d9000102181400400780f524500c02c503015002d50700805c180703200d442c800100345400c403600710507a2b51101e480d1001c61210000504004008c480d0a410348054091150425041c0710700d400c0c00c0d51100200110112080b42d1600c60142c00601d00349103650b02940030f5804030380c01c00e003d0b1b4140c903c0c2030b0440d0042800d5071001e4800c00094402404108006c04c42d81c00000c100344000c40e28a40750307085c070000140c00240c0c45100c1c0e114040d03001002c43d049442c07840703a40e800301000600b03503055a655950043c0041604100685c0400c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 956720926 1250 956719676 956719679
    0x11071406011d01080d30051b07020d03031109030f070503060c12060d0c03051c030615080109051f03151401060f0c05071a1b07061b060b150a0801 64
    0x50b00444600d0580d20741100400c807000794140c00b250841010366003101c40002031052980281148000e800030050a002e000c81c05041902108291700281c0d101009046014408000103035222a03112003d140c042c9170101e1281c528040c02081840f503008280d626200303006017607803201070100b4135a00b290004c41c00d64181d990b4038a402070007407091186a000e41092040058101d1410342050601c117401009080b00c030f03603100c1e50380c5454030210a401d10021480d61a00b00c180c035605002d800c014106055030b482c2e0b03d2a4902001d0080c88040c05800700d29912080022856030200744120396807400c081c0c1d1182d40c29600c2c10190120030303a81208007031080c1403514407400a190001c1741c1d81200d401d030380d441c1505580b90300f00b1075401401c0c541c102c41078001d5070f07000150745800f159560310b58035000c07420640e10100050140944900c0e80d0200d0f54030b4015a4003008075541058890030b10001261414014080c00d14002d401070944c0e0b14115401340e0740c0c0102400c0c401000015003c0302d00f49455204007079 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 956722176 1250 956720926 956720969
    0x10c052e0b10091a0f0408100b06090307060804020414040b0106080a0506150a020f01021801120e030f0c0a0f141911060706060e0106170c040506030103061107140601 73
    0x1544005242000b04400e00400c104d0300c1401058802182c5402500c1410720070615001902980640e03c0801d06902a030004042a500da02c01d5007502041119101d280c10030b002d010a440c1e50b181d00c94001481007120004040d52143d40158409101100901d0031030f203841e00c0c1c0034071003000a010312000a100000043e4890007107105550207000014000c000440000204581c56446401080114040d001c2c0d20902d0340e500740050002c0c0920004448542e40b0a400010120584407100c1d126003403d0805141809a000c000c03913441e0034812188035a00d2009607000703444d02024290061041e00004404410b01604100d07510661a00c0750549012000c04240c82040754000c0b600900001c5128041c0c280a140110003094254458400441e004e030b0b54201da0440a4401d80c0658041003442100c3c0c2407150100440e030b41e00041c4c015446042505042c00300da0f060205000062203107998110b280040c00c44601602c0304554443c1c084c900042203404016112902807140341e003852a0401c030344680e03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 956723426 1250 956722176 956722189
    0x70303140702090a0c050c070e06010f050304110105090312120a0b1e010809070909050a051e1b060d02210108120d050601030902060c0a031403070c02010c052e0b 71
    0xd0540040c8030f00c0d00e03600c441c0300800051418525020030301c2000c2002101c002c0341030141200900444607481090f152010014000105a003117900421408100f00000100402001c40c1c00300740a1030f141da220035444010901e018541c5111906c200703004a010356031444411202445849811402d0014603031070410b21002801d114019102c2128400c0504007551040d01055804031541003140d28003070387c4043c03907002c80c0c540c0f44064805800003102c1c1e4003841410805100300540040c2004c8070307500600001904c42c5d2000c2c0200c600c003401c0342002e60036036880005a0300c0c0f0b0341800d5811980c44c60000d80b0400b285c9049100301c1e805400d0302c17000140c000b00104180c610784d081e103154549022a840040d4001303080c02026641031683d200801c502580310240a041461180c41c01408210b101d410090884032404107120402c0c1810010411071a601ca00411aa56070a00f402202c01d649407408a00b46070300216540302c20580e40242c001d4460911014001c00c490742042045070345645000e0184 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 956724676 1250 956723426 956723437
    0x1106120910180b0f060105041d16021c14070618061b0e0114040906030b0708011e03030c03030b040c0f1403061507060605060313031e0909110c0f07030314 68
    0xe03006083d4006040d20310080769483d88100c0514001d131400da100d40040c10b2240070381300c3e60112480080308002c0c92107207002540c01444403d00007070a0b42441802c0f000084140402030204001e92170314244021110b19003a2034205030700020a110b0700c03422071a0000121061001540c0190410000c1140002c50030601c1e948040c203641d842800e40c8002d001900d80751143c4940e0300d82c900c0c0410000a52007050700c0350320301451258402d0700c40f905110390b00924000c0c040c2c1241401c40c2148007440000f1410080380d400700c9516050205039541d5078141940204200d41c002900942800128003a40b80d0111803011000b030681c0301d5100845c03c0101c40001030004071889500a0b14000035015100031030300203007030030304c0c801c440100d08241c4a0021858540058814041d00b08802e00d80604054001100031200100c0c080c06a04541e1107840041001c84544103248900e0750740c0f83d0000780d00d5440011103040c508041d08640e000070211142c142d4134a05440260001031010300022001d9071100c04591 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 956725926 1250 956724676 956724683
    0x2012715050c04090e070506030c0909100f090c110d0509040e0309130b0d0606140a050405190b0103061a0c0609030a05070305090a03060e010906180f110612091018 72
    0x50520b130038140144001c0007101e1242c1054420030303500041d60b40d585001544038408d11200140c40300208010b00c00c03a8030000e84203040105a00e07100740308023070364044280c04444058201245040062906a4090160401300140d900840301852107460300324006040c05142503d0800400543c10b49003600d0740a40c624035a40002c201d010315940c2031090f08044400000100300311418480740d0364003000ca42456001c04d40144000c1116521842d0501c0c540c80141401d9a082c03100d440c00c0340441454595029255150f5661164900403070792107640044043c01d0030620404101a14080344009a0007a41001c6085c0c4208800035942200100565281c080140c6070103081500c6aa8241c4540d0410108180c00003140031001020540d28020342c15801c01e48800003420303051b2824100c0c00c3d1400000000c603154004410640080da04185001e03d661f081024588040ea150700020040e21400091903484020141840310241c00415000d02c0da0a04d071408010742c0d001410801da40400d80744002c4c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 956727176 1250 956725926 956725951
    0x2010e012307030207150f0f081501030f15030818030d050712031407050d0501050a050a090b1c0c060f02120304081b120c06012907030201271505 64
    0x50807005695014140c054468015651502d84071901380880c1c040607981c980c002040d8090780c58440ba08101240308418640c504041c032460080e01e032140c41410844a1810160780d20a2900c00c07080d130b50302048070404803120000c510b0340d50342417000c1e06070070510541e0520440f40307801a080b89070000300c07c3c80140064590504021194513150414501c3d91144414075403558042119030018044d201d2140c402529031607125089502c000c2d003190780c144c0003103010b81c0006005010036a510034840302202c00c0c2c04408243d0700165000700b400c813945c00510150084070040044104010a9010b00560700140e6901e03e070341d03c103508104c1c1d48406412a01078203280801c0070401140152005102c2181c00301c0344404440003100d02c5d03510b081c3d9200d00da920380c5000400c403c11b44450600400b80140840c1022040d20700540809901680d01c602441808020014062042500030340000b01030610000745885e65140c2600c0401600050140031150801040070303000b00c0110520510340103490402c50b4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 956728426 1250 956727176 956727227
    0x30b06090901150f0314160513020d0501031406090106062f070303082403120c10020d02040501031404030e100c050703061a06040608190207150902010e01 68
    0x10300020303200190844820b952644030070492141c600309031000404100c000306140a1940c20a44558500c4041090260300940c1d40c03e0601544074440405035042200c10580484012943c00b000340308100c0f2410000b800c0100010502074554550001c800200d4152070480d540c94145500701d4aa9000308404614010703800032030f00e41d0582d02d228207a03485100c903181c010114420302e441c003900c5600480008080c0300c108403201148010000020000200e006540340038480000c0e00c690085440d004a94800704103099040700800a00c90a206442021556085501d410b00065401805602d000c6400d011000b410600c0729000940720381d0f0560380390b40c04505a0b130304110f40340148030011070402014040c0f0ba0003081c0180a100010351007840700160111000d01400d90142c0b0441240380300b103c2c10300040000680086246500804c041c0c00700f82183c0313800c80c42600034050044060b0215140d0a0079800e4032003150b01251400d4000d80b9031420f42d030310300001160307401008807140c0303044840c0084 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 956729676 1250 956728426 956728429
    0x103060f0e0118060819062003040f0503090a0f0f0e3304020d0905120304030207270e0309030105060415030609080c030c0714041b0c02130507050d15030b06 69
    0x82c0c10380d003d8403054020603056540d0000900c1d1070785580700420f01e54002000c050070070403988a40c00410740071020001d0030b94020b00541d6002d00004201500002020b0b0440e01000018401c6801d08600101581e08054030340014102d90110b03401500f00d54070700304501090f001720381d0503028855114000c09910701105c440c1070050000820f0400d6802141e007200ca0985551617001610a611091000180c0c44010f41070051401d5100b031441c2e2030f0240300b0020b20012a601140e040306891042108008803105509101d040541c8900207000c1c5a150141c0d040c04c50b0310210080c4801c503011002400a511004104401c403003034040d0134480790415400400010b161a008195818020000d42c0e00300b070002512981542d21000c1c9605040e001a0400d01c072003100c031000308803010300a0303c042101d200c000c03901d100480c0354550700b1001e010080b040d2070b08554031807101140e007522403103041c031240c180800302030882c0e04465844a000e03410720f400901c40c08030b440d151108072030300a00001c00c4c1d501c4540 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 956730926 1250 956729676 956729699
    0x270d0210030f0c0c0218160507030c0803041a09010c3002030a050115020d0c11190602030a0306170a03030b01231803061e0703061806050103060f0e01 66
    0x5051580701d503a640d081c0c80440c4503d6526070f00310b4032407642e8400c2510402554043e0000c000d4052003614050100d0003e400b440800300070301d0f82c00c129554403554242595100c0c80342c00e004049000000c100301c100302100c0d18801648120000c2030786a0b40b64500368070709856045080e00f000a4400f003101c5000580b4003180600b035095102691410b030400c408541c1030740c0c405c5503e4142161940010040340c1c01000300307030140000030f01c09800340f6401000f0003480d801900c00c0150426130f0f000c6941143d581c0703816048034898540f400e907003401035640001035281d402c080080408245084400179030000d5030113182884203a1040035200b09040d035a0158010020311070030604101c142918141c2e4049400e00c9903100c0c0c0a506e200507140ea080351091035030102841c031124000e0b000801440400f2420304800b0208580602900c0410303900c15404400070701300fa601200211010003607150501c041a44158140d81c000e0743c05120041c0c035030740f0000610303c06201c3e0310354009000004100705030703d54 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 956732176 1250 956730926 956730949
    0x6031505015d1109100e04060b090a090506130503041701152709020d060b0411070303050f0a0504080a03090f020d080307030501080c03070605160512270d02 69
    0x2100303603408801400790603116088440e07098540380034140c0000c105108107a0260f48440f402114242d100e0310745210140701d00481845a00085800c03038010404003d0103810078850304401500d034180a180c0400f0000107003240c5d640507161405a03002280c0700083c06180c501c41180c2100c000d502c4c2c5440d12031100b890b5124844a8400c95507075100c20f000710060422000e000786212948982001e42c1c502e4441450b0041c5a9100106442c1c194000c005845290b03060b05843d800400025540c11044041000f5041c100c100002d1041c0000f2010105a019801180214101c1c0070604055540e03003903007030440b00e0070750f00601558021b000c8a28014843d8101000706c6101d20b100b03840c030315030316804101a1043c000d011245004080108040f65505125060043c00140010958008210f02207034481d281ca014110401c040010035a480c48084485500c000e64403508031025124505030314281a0801c2000d11590250112034460f04030036010400b020301801090103007011150707820030020944c4c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 956733426 1250 956732176 956732279
    0x90702030c0a1b05062206030527280308010e102106020a0302030a0506040603150c0302040506030103060204080d050c0601050d020d050d0908070e040c0b0304050f010603150501 78
    0x1d1100482c642d1910350181403480c032401c0d0f09034004592804000c6c401d208941041c070805145c401004200060007c036010000c2450503a115000d814504a0341400444844c0340645060010000702241c1401d43d2181c0c0e40e13000c3e55501d50701d42d88545462031092025074107a540a003003075006100407040d801d18000c907501d0005018850305865900c0a0681e04080303200710100f40d007c42040344c00c880038003075030768480e104503010442581141d40e0b18440c01032041d01103040035030700c114010400f4041c0d41101c0190030010b241d19140d42c0e686ca460000b07540940540c1a0b1400b5040304855118003070400e440701d441c010b001030019a824401442003000c401403040c1d0744014040201d80200b202800101c181090039a604107d00c1d003420759030752628070141c3c0982901c0418000704808507412000395400c0c2d83d1500c4041e40d40e91900d0902914010110282c04042e519129001040190200070300d185504496024441682d0702c40a4581e001440483c00c074032820402c200017401c22510314126615940c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 956734676 1250 956733426 956733473
    0x30315091306110d06150210020a110a0b01150503040b131712010e0115051603030902032e0b130902011e1101140610140f0a0806090702030c0a 63
    0x1c2d456040940c2c0948041d0101e00700001520030200d0842d00524014082c3c0f41620401c440700303150003d545a00a070341c401803441e808202108251b2140c04400d802c1c1ca000400c540c000c0a02d070411645c010300a2003021804d020001c880d8840e14022003c2c0d034070403038200c12041c06990fa00b0040f981c00030f51700f8104890071003034920007030032b004840400b80240041640120003d9130400f080c004e117402040e00882075180704481d51090390380d44030048030380054243e140c0100c141841e01d400c0d4040c00213a00002c0d0316024200c2c1d141801c03800a003440c00c0c0c01580d0b07013100740400c140d10600d40071500300e000e01c01d1b040400070822030f40602c07150300300303000703192045c580714110810080d04104181c14244c1d05800045c040792081c00688400d000c1d94000b007199010755000e6040c44000940390100500b0160144640642e10044052084090791659054100c40d0f954411b4410002000a0021140a445880710340003041c1a144000282c5210b250711000810090600b500c80440c078100c2d613601140f40d81c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 956735926 1250 956734676 956734711
    0x120f0216030503070201140c19050c0d140606040b01050306010c170a0203070219060f08130b0114190b0a18091815050c09040905030904061707060203031509 69
    0x8080d1022040114000e0000c0c58842c2c1c981e1000410301c96503009007400580d0b0031f2005890321075000c0303070f0440b10710a003050100250009140050070440c10707000080e0f000c001c018014003401070942c1c1803040044c014003a41c4142d030354401004100c0c0c801000070340c0007543c00d000041155014448084456019085117900b00701c2c5181c001e00e45034072002c0a900181c00102e2050304506200006c9481091017141c21480503040440041101c00d944207190104480017011843e03804840d04c1343c111441d0080403c2c0709035a103031093310b8004810b2420460280480c01346090304550762010007019280c2d14580c80f8500294080e0071a0b90f10b1848402c610540d90303202000804100703510900b82e01d000285035900b0100c0040c10f01c46c11103140054401e5825080408100c2d00305c003030304125000020122000101070300e490504030310714041c81400c260094500003021668140344410001c2810301c13001200c48194071003400301d880c0c2c003050b60b02c41c00c0c1d4001c0c500b0703810306485c001c10400e0344400c04000004054 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 956737176 1250 956735926 956735953
    0x10f02031006051603120207150b040614030a06050408191d04151502010b060c010f05060907020304052b030905031b010507060209011704080d0c050705060f0402031f02030919120f02 80
    0x83d281d691a14070141d982b8220316820317041c280502001020207290900021002c000070949442c0011802420b4940d00c400103420000542e0a881c02006c0d0340225860006d403e000140000203c407101407000e40c81c80800d1100c0c2cac9040d0140e615040016a40c05034602d282003d0f10b030b084e203018030b9184203554072080700e81c0d4a41c03128006040012600b80000c108030b80922005d008544014210f6802600740104111b005500081203c2c2102e030260b84e108510841000401181c645100c00e00303010041c941805d40601d64003c080c0020744008400341c1350784416034401c40c10320301000e40c80d01d4003040e0700b40b05c910b000c2180d9078080e0103105018108a8028000d6407405c14070b80c5011641154032032004110b1074816a07551044030a61901070906078a005510344450390355000082c0a00302c074503000c0c00000c04540b03050100d104640503801840707081004001c0d16602070b4001319040c0c4030310300c600d0034a42c2c541d8441104030a40c035a0408190142040c3d000b00407034000200707245110952146013020704d641c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 956738426 1250 956737176 956737193
    0x70509040e2a190b0304030c0f12020105090d0203031018150b0d0c030c09090911030f030901080f0402090f09010621121d10020a05010f02031006051603120207 70
    0x2c0c40001641c2d00300c4000308525800a0300c101c2021600003071042c0070200565003102d40146c0c15040c1660080600d01e812031f445a55030000911681c03420855075400b90301500200d00445ca544291004a45000807ca0360717404212800d44c80c4810b1381804024a03000008142c140e540d1300180480c60511841480700012205c0d400071003103500c0051a003040842a00c14040410201d18080c01171210030800101041000d00402c400c003a0786122503410814405240d4481c6600a81561b80019440000f641c43e50003009840d408909800c00161549907200b5100d44203680c002d002c036a0740e40303416842040300c140050074182650750b2002c001c41c1d0704100000c15a0381d805492060386010311a0b01d0101c11941e0f1502080b42804a41e408244406600c5841d13603030250742c10f40d6034007104941da0108034608882d100000d02035502e889076018040e42240c004500c160800c1c01440070311940d45000301d81c140b04181111600110903e40400000e10588004288490284015090001540b00d40c00c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 956739676 1250 956738426 956738473
    0x11060d02160f031403040b0708060d06330f06030e0313030c03140c090105040218090a0218120309060a0c080a18051035010306060302041103070509040e 67
    0x78154910b19244042607480030303070304c0984040300c0e80b041c2c01e42c00c0a541d802900390000e0805414040a84001000d0352241004010711607001401440089401c94180300713a140c1404e0250720b41c0191071465800304c500c05e05500c04403081121100109171034520120010150001c17154198001006980d40d4080b0b0b6a101c40090741c010058442246d00c0c601c0c0c0301c1d010342028064610b054000d00100e201503030701d0b0605181180d00071307100542c0d544e256107002c400e840c610342151940b000000c000c0c84083c6840754007403d0b9040c03581404402412440c410010750070004a03406c041648200180c5200b4101000907058109880c00e03c4101001690b0b600d0351107411241458000400403403010382d01c41501d1400324018442581c4492070107802150040c41500004c07480d0102c1018a5406030300506201e09060580303010f041e0051031944c50b403038844003070001c070b102c26440b503030410650817008425601202c1c020034540e11050311f0490941c040c000a841c0181c0e08101d1409030510800ca028004c5034000c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 956740926 1250 956739676 956739683
    0x60b010504080d02240402030606240a0302300103081c090516140102030a0503180307120e040b01120b0d020907030e0708030316140f0d0b01020c0d11060d0216 70
    0x80d030101c5800d14101080040741721034550340e90001400007580300031a83d070b500810b003507900044c1c280082c01c0d9021142c41c1a01c4c0900209c41c000342050303110b1703450ba014005480700f0140301030345004100180c503070562407131290544038442140104000366111001349044c0541501080ca0540310100e40ca00b241c205800584607a0802c00807040a01450380c184d40143c610b04940c1100c1080810000750b8a008100041c4180f01d000000314851030440d5a0940b11010f8120849903140c50620b0031a95085d4200e08000101d40455035a90080c50075024080303aa0f04182e6a81c0302542c000d00d1100e024040d8200e08640200034035003c0e00141c1c583c4800d6500c240c190703031004a07500d021a000285059a1640151240e40042c424410780d140990b080f054001d1043c44d011181d02c1d183c0d40703091041c1c49401070702d2540e8100041c0c0d0f01c0c3c0c0626180c2003159005001d800b90745c00c0b000d041007804070f000e00a960050581c000d1a4407030a444c03130000003800c1c000441560050030000000e40800c403030305480800340c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 956742176 1250 956740926 956740933
    0x207260a0828050301090c0c02031c0210050105063403030218040b0f04020a110706091403010c02071809200f011d01140d1e051305030304060b010504080d02 69
    0x207900c14442041d440c06a40048039003080101c0400c2c1d0010700500060040080e02619100405003003881a045203520710340060035648035005280c0d0700d00c2400220130101000d401600f5000e41d00d10105d2180904a540c05810382c0e14141481381c07016444100c00007440c1407449002003440c2c08500e403076170b030802e1648240c0f00143d56500440714141c0d101100c2601a100e21300340100c0654075180d20840d49940c1d0000c0e0350140e1505a60001a00e0b15000c009140e0894030801e080010102e1f03120710010304507402c3c03902410300402c01c00181803c0c1c0f02c544401401691110360100800170078524942d00b4041c4960b000600b03858aa03490403180c00424449a100100700c5904040074640a54009200314007400d10a00004c8035102c0d034041454500c085605111903017000140641c00401201c6820031805c004028805181005410b660304180034425590718100000c0d051607001102590070075003000c02107086a55640e98507000c3c043d038204a0341000010b11002601c2c000400c0440c003038a603160080d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 956743426 1250 956742176 956742187
    0x81606021c09060f1218140309030705041d1903080a05010e070c0c080111040f12030c0b0c040509160212032e090603030c051002091f020a080c011e0603030207260a08 73
    0x40350200c42c8843c880c0d01d01d0702300f00140c44081d5000594001100c4043d075000c68909856035040003404188450b0310a140030744d00f01502089428148800945d21a860703103000741d00c448001800320bc8090080740c00c07001040000c660454081d1000c0d4030b10358840c401d442c00b04d90b03c600c076050958468000c0c84403101d6010400b4841803c403108000040c020007036030382c4000c1c00a914010201400c89001a152003000030100e2145004003041754043d0501a1040070981004115446407000ca0f101003401805a030034841d800b090413000f1280a9640c190240d0b425442004500100b03500300c03401035585102064001508220034000c0c6402107001e921188201f5466003000c5051481c16800360b9465413040004140a648410030304040705004480410b10180d01c0a0070707032a01008400c094404070000c00d21840c498415040001c9920781ca03c0b000c0c041214201c840344c1911078500008002d604032000078815580340c03e41d020040550f14503100c64803881503914138200845020241c03000c0800040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 956744676 1250 956743426 956743433
    0x801060b0417010509060c0703030e03040608090d170a0e0f0a232b03020702040518010b1804030804020303270901140102060103110406081606021c09060f1218 70
    0x1114200e0102e40009010718074280c8002c0c0c3e00d03101e00900ba0649041c0100340181458481d0344400039180d0000c0c226a074036078603500c01510f840c00454486540d8402c00d0804a000d40c07040e08901d80150681c3c00c62500c076250120b001d0040e10350042c1d054078074840c00c80080c9043c107040001c0129503000d0520f400711700c00c1c04c6080e000b03050205c070440e25480c0d01800c5071650342d1314000d6030398400210145e02503801248000e0304902a102d26040a075001d401c02062282c1d4140882486141d00c040c0b0b8001c10890350b5070000c3c07100404610010307440000c0300c01c0019000c039004106055020f440101500e01c0c210300c0741c07000340c914032401e01c0200740c4a40b460820542c500f031450310280542000031019001151650000b980ea10050000400c0050150071a500ca502d5903000070014000100941d008075600402e01180300c685031181c0001441601c2482c1000761000c1810800b618507075940321445400c110003610030741801094042001001c00c0005690100751181015259082d401c0ca60154220308 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 956745926 1250 956744676 956744699
    0xb121b10020d09050409030e040509010b0924060703200609011406060714070b2808041707020d021315080f10110c0601030f060609020405060a11070801060b04 70
    0x40c4100030740d4405900c002842c0d0300403000004a500c21100070401001d503140c112080981c1400c0e00e9006410303c4188504050107402652168205440305902d6544881141013650564140b0000401c281241580b032400e240004182030390203414114581d044241d44500f4584044500388415006a0203001035400207006155660003102c03038480d0541445000902c803403103121001051211074070300b0461a81d006102c080010302081e10099150000c14442d14044d40c0704102282c3c445200c059801e480b14045c05d051401980c12405049803841001014102588850410b991014807900d5800050ba01e003808090a003212500100e14541d6082e6411081c0c1c210360030004032a0410b84044100c54030000300c0c103200b10105180844e9800c51814040b1030351003000381954032802400008402e01c60001c12505a4503c07580040080d0f9076200403940881c0244d000d283c0d07101000300810000184120080100080e80030f06a5035010b558003803071809c450782644071303144001e40440e003042100c0904 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 956747176 1250 956745926 956745949
    0x30c0605180a031505041403030a090b09070311060a1407060b0301050a27020a180204080d23030c0c06040b090c09161b12030219020d09030201030b121b 67
    0x544280842c10300355580c13000452540f100c140d04141d50381000a061202d024041040500340744d003683d41e42d04004290001504030b4481c1034800c0100310b800300b510128001054012a80c000800b440301040b2a800c0004a40c0400c145da030400003080f03619010513803607000420b80702d40b18503c0040d01c1c9030140241400d5882c01002e0b4507485141a01031414150030442c140040c0100c5003640f00f120450340300080803c54150014404102c0d80601c501c80440243d0041c41074854100c1107a5115122000403254148259a4001082c3c20000c6134a046803080b0040c642192130400c0781030400b404164102e01d0100c08450a84214a0041c24407281080a01042804400a407a0003080c1d15114408000d140403455030b1904201c0c40004a400c411860982c101d0101c0d0712010300356521f582684000d0180d0403c0c0c444801101c40c0c4104010903500018110303044e4a440d031603020394036183d0b4006400614040320040c0d0043c41500051500340b00a110b0580030103884c602d09480111040b09012030f50b0001c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 956748426 1250 956747176 956747179
    0xb07020118020f010504082a10140901120e1006060306030206040302090a1407020106060806060403050d03051503010e031b06010e0a0e01091a0a05221407030c060518 73
    0x10080c50000400040e80210240c0d034043d20b40500c00002c41c00100c85502c07496009401038040d10603000c6003003108840d20a42d1206040714600c130b02c02c50070200001c1072041c0d5651700c0400c0c4100b490000160400000e40304c0400141021159000d144128030213a030381114401c107072608100422002824603101c0d420103415507250400ca0b150440d804034215104500002c0e108900590024410071a240c006104008a041640e2041c0c00c0c07800002e80a003865011390b002281c0007000144650419006560850350418000d201d4a440c00700154004c0c8070280861761004e40d20500140703e524240150708241c906000103507a2400d00503103564100501c0213251449402800040100e983e050740001c1c2c024181000002d0200743d151280c0d03004086000000f02821540d14060b101c0d25014502144103100705482032125984404104a42c06006440003002060400e040380101e480c0e40c019101517000c0303200f04c859030380e165104c2c88101d00c0c2d03550000000403030006104000d148284908842e6400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 956749676 1250 956748426 956748431
    0xf090603020f09060f07080c0a2001050d0c020f0102040f0f050402071728050306040c18060f020f01060b030907090203060f2b050f1902060f0f0c0304120b070201 71
    0x810048102d9602c10304031220f2180e01c0c08650401059203110449180541c0b1040c42d99407a11206c20150311032120390400c0d00c0703c3c070002c941e42501340c0030081c0104031001c05950b1a841c01480d4440c7c000182000b02c0c254045119420800032924400d10060000d02030141b02800b44030b240541c1943c140c0b078203421280c082d6005100b950005003101c41818a03180c10114107a4451554403101500b040340d000014508010341c81d50300034115040801140240d00c1901c3c00c0c4107800b05140e058450245c8162500001e510361001046260f00c140c0304c02a02035002c0c4140c0c0c220400208400c1d09641075508940044074000080c0825800200704620003820111019811881c01c0340009482140c689051070042e94046c0401501214034415070b002c1a0b00140d211101c201c42e810203a50b1070b42c02c1d0b003043c01244503000e0201c0c10612140c030f243c00c0055004080703d20341040d240c4141c16a401c80a0b40d10079900040c41080c4011000f13002800107400040310b034015040c5c482c1000d21408001500040a591 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 956750926 1250 956749676 956749687
    0x60907050114030c0903030f070804060e1e06030a1e1d0706171909060506090c090d060207050304080a050d30240e04020f0307061d0d0803070f09060302 67
    0x20307840141c1340e210010078082d039105c3c03481c100481e0840c4100d4903024a001000a005010084000c0103402030711015030f9407160110200d4184244401d61032000405401c0349034949840d07181c040001e517401072100601103465000c0d540340b0340c00c451492000d041c07107070b844d16101c012020f41100b5000b80740916500824410b450244060840c000030b426404290401d4000590310100d040040c000d5507d0040003003201070311030b0038900d0003000241e400034403450301781c4003190300c4600300c400f500c0300300d1401004200749030100e035281d00c004d41c031452b011281404140000240c010007031120300c4519028601802c103209107003500400020121241c000120380da4040c15442644191407a4841c014581f000640c084099032080c210145203c41c070042c100203002c001c20b03c03841034042075000b03500c20703101001c41e24101e8007055100c5c4164012880080c040c07520300300b00150190740c6100c07040c030058960072648000d916110001d40c0b08582e5040856203200d03044050541c000c04000040401d8a011420003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 956752176 1250 956750926 956750957
    0x50f04020906041a070f080c07270f060509103201050724020a0e030105010b0a1d03030f0306010e010804110409140709091214030f07020a02120609070501 68
    0x80c000e500904c141c1861002c0c2800d10704001030115450150408034a0251140910300011558407141032556940946800022205287c85a140381c121a140700c04817060601d8881d03100620624005c00700040d202d000004441e1102108a4040d0907501c668189041c18002d92201c001c100c18103940ea11f143e01c0d0890f044003029030b4110750848209180031591605542010f0a0440c01c0c810308005c0c11466540180700c800c0c4e20f40c000d080c10041c41c1c5407200d20740c03042c20806d400c031102440323203449002c070030080c03c0c540520440b05146000140006100e15240300c03404280366410054110014a000106000c0d80d0360700008c1840a4031002d2070880f410303191546d50f10507848141c03003015010b540c0f241c01a0042203852400288000c0c036600c21284850b5903001c3c4003000d4800080f065401c0c2c5d1000342d034507060780d2140160b444070441015126245d41c4500d00301030f1445000400c24001c44c01041c0c0e00300d00594480721506001803500004280c54101880c00504000c181e5000d1030603c4100011003004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 956753426 1250 956752176 956752189
    0x5070302040504050309040608010b0f01030614100521240312030c070501052e080616030605180f16020a0213060e010e040b10060c110f0402070c050f040209 69
    0x65036030599000c11661210701c0c02510314000c903628140d00504004001c5025401503010101e4070b00c045880070340041a0600540481e1000c1c00340e0052a111540b0042490070003c503082860a045d203006d80c508400401c1c0c00400340c04070f00d0800c4051218000744450302c07801d010f00d000c030f440f62501242e10385030060340081ea80b916609001400700d180400010380c3c440040d001d95a900d0f130000024051881d00c0c201e017107941500004548240000c4c00901102059100c40d40c07070903180e111004001c180c44030708100e40c481e9800540281090b403122408101a290700c0312007040038103900007110050600100d10014890020b14081000907030041c000001640000c01e000304075010b440085144034010a04070140050390444281706081000008100040c10102e5200d81c4c0521110807041d2200903a009904000788281d00c000780d28021858041000400c140c181c00b08000c01200c0b0409141c80800c060342c0004005443d41c00030b08034100818100300c20030400a0008450451409441d440020301 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 956754676 1250 956753426 956753429
    0xc050f030f060103020415020a0b070c020102150a1e09030e06030c07020904150204030f061a010c060c030b040c0509271305010906021818040c090b1309030c120c0507 73
    0x1c0d41401101054659000364111000340a10340f070300910b03102c00203002a6950005400481d50008070f100000d0303000d840b03414110700c02907050380603080041e450941c201c50858042c2c0705003c2603a1380d034903980c01c11200c40361554031754684c01c1c0c020404180340d0501400c0358800b8040240201020806c0005001e0401c5c201c40d0f0855044500e452183c59906040c030301052010300c10040320788000b41c0407052012180ca807659680c4903074424005490b882003c80400704450701e1032804038000e8085c10340020010f8020428070300c82440c000400300044c00005054601503803200f008101c00154001d40d07801d100c070300b60900000d040d1100a444a101d414040010b00c0180903414082c1110841c000b080029040015070381d401400540d111410045405084a0366814062140b03103c40d2143c180d2200300808180300d107070007002c0c08004c0d5191000740d101600044441c182d2080001107981e09401951040e5801035010365580d020340d808519000d15050300d02c040000c14000c50202080c00504002044030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 956755926 1250 956754676 956754691
    0x71e02160b0d06080307030507020a08030c19050a0204052503050f1503030d050118050f07200a0819031404150f09022106070c050a14070e010f090c050f03 68
    0x166101050b0b00c0600040c075090700034054038000000c149040c95031000c09010140d000321b506605e2966039400b02a034a04c1081c0c8400202e070010120000d2039070850090061083c0690701750353341c1d215a58002412950204c0b03400001c90a041e0004840b14281e1404031a204803030300301007106080c004002c42484030700800105000501030302041345501c050055945041e0015414005d41d615030342c0c0280c0c1014030007221080d45280c50000740f0424100c0741040e0048201c0c0c0c880394400d1030200c01d10b401c94541500100541d00c6445400000509a0710040186410801c1c01e5009008015401401c0d10407002482081c46459004d100c0890005807813a036244042c01c50001c0c000c251040807401171322074040061b5001004107204000d4492003000384020100710403d8030030554a840080d1008903140310050701d0365100c2d4042800107946210032032495a4002c007180d000c2d86d80e5403822000050241c20541440030102e000708021403403800b0300c00c81460b45040c201c1c11704000302c500d460300307000060200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 956757176 1250 956755926 956755949
    0x81501110a0813150801050f011b030305040206040f03081803010605012718020c060919060510050910150e0607120c05030f09090a092117071e0216 65
    0xf03034440c100f044019008084100180c1032800c1c1c00c58000c1c0000c43d007403103424003039142d14180225642c41112000101c407481817403081144c01980b800c90080500401c1281c012100300408500040343c04004c0c001148a5041540d561108012400300602401c41c1180039078189007003800242c0c1c02083c158840c070821940b44102c5190740f0f12030503444403154410f2103d081035118128464607075800400c40700003040c0c111481512645e41881c0e8801c90800c07010400d9a04105500009001c0c2d08000d030098514681e41c1c0c0700a0b2540c0c0055410302d0280c8110100d1100c10f0410002c903100c4902c020000c028030304100b92042c5060000c01c0161041050003040c04540c0800381e001e05001e18102e002302a00700c022252a6564050120500c1d8411148503106458040010345061120f000f20a44da50b80a01d00d1603502e1985610006024802d503807103130900c04a50402082030007218078a500c120816504c104d9000700c0d6040e00c240b0202d00d070108800b150007110791400b1038080103030b0420495060f403810 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 956758426 1250 956757176 956757187
    0x6091d030f0d0204050904210918020d060e0a090507080303090d030203071139100e01171303030501120b1b070605011d01050604060c060207020f0301020703081501110a08 75
    0x110b0000d1040381c120031380c4500c001041c4410310109600d0003032540006000243d052100980035106040d40744109000c0e050500089005050582c011f007d4090b0341e01c0300426002d4039000035814044007181c0b1000740390ba545004406000341006150028440c0e4006580780d070400112403a16641002400d8080c190000041550325200d49031b03841120340820140c69019111110f07a042e01c92103403081c110241910b2102c47d03541e0085071147c60781000010200300d4491400c0100391488507404002d2414058502d03400042d0040c4168918881c035a006203202c4a0f8001e071a01038121038040e004074802c040104040d50026141800c44c603000000c0807083e005080f420450070080f4403030703020018900d17814030000107a0b44000d001081104003081c030741c001e0f042c0c7c0c07550140007007400b8078440c9030005800c031500c04000c19404c1c0c0c01041202e00140c01c4040201a00c000700e420380e846002c04900095044c41004600251014072011214003440d1143c802900d08440c2c9a40f00c01040010b019500300083c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 956759676 1250 956758426 956758447
    0x304060c020a05040e0f010515010801122402130909080306190b130503060c07150c0509060c0c101b030e040b0a0602060103170f190c02040f06091d030f 67
    0x1841d0000f810020414010812820407140e110012070b4900c100075803d1501080442032460b2107a0ba81d520103a440007050b80c68440000031603910307642c0507100300503030f010b25040c102180c184056031120480c002503611310398207103032140103007481e03010781d4600740781c0140700703000956080889800a10446140f21412100e0202c4445503100c1c1c0c0c0034114003040000c844801c00c4c1c06a13001c0b01111812000c0d00d19680c0c0e5079080c054140b0620070020b001000e030a00c040c02611555004140781a190310705142040e44003000f0030301c1680300407101d0f00706078030000031511140340c9100380c180d80c41c82c1c80c035080200034001200d4494200280d00300406002d01c5448200185d107455108020800000f00350b5a0100d560b600d010391220028002035841e02c0080b8946680d0704aa0340403a10a851800e83c85454491a204420004001d02c1103001c20030005007964005651203014024503029020000200c061034503070707040c013100c42d03412502075a2280b40102c0c5c0803120010060341e540180e050103c580e103c2d83d100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 956760926 1250 956759676 956759689
    0x60608150f030d1101180f2019030b060d020121020708071a01080a03050910020313030c15020f0606010503061c1a0a0912050a18290a020304060c02 65
    0x20032003601881840040e40700c06a20443c4055484c40c1c6200810010714817150304c045a1403c1e6801030414002081d034070000a03c0d40544c40401c60a50751403c483e49031000001e0803408580311011b42c5000101e4080c800d000400c214543c01200c01c4504411a00003940040c0421200025112120b40c10707042c2108416540d4040741c4526170300c29a160350701c1440b8a030801003160b510107841210710f2a94008100078034006060000f071074160710b51500303010f558810001740800841507401140824400c85815501240c8490060340c880c50814144500701502e480181005007030000c1158012440d540311340d0b8010134102e400010070b1800ca40d1360341e40e1101062402c4c424032085201607002c15120014801804007031103c00c1085008405142c559024040035213000910240c954000e8410803c1c2e064064401071107107035102e041c0b0418008d5070749682d42101815500c11440d4014460444113807010000f0302440d44042c0080150602caa2220000c2d0344c0c2c0201c0c0500c0f0305000180d10110255540c84 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 956762176 1250 956760926 956760949
    0x50f071d03030304210801030b0105091008012906040f0e090712030e0a1403030a0c060e0d0e100201020307140f0d23060a0503100b060d0516090906060815 68
    0x2034112962130403e4a41a030650082200c401c013a415003c44054a0307902c1618514100e075000601d28074103908282c03c000720200054000504880b82020009243e81c0c207005400c24400c4c1040d03035180b484070841070424048807002c1114401d0702d00b00400c0c05801c000303c078207809841d07040c0340050041da43e542c1c01d1450240039030004c01c5900401c009003c1090351141042c500c01030181c484e83c039010b554441c3c2e8052000c4504e005581504280411840d0620480a00c000745014070000300d1040090020f59003002c1060020f20000307885840e4413480e07400d1418054964102d6403008525615100b400107110356403420300c1c90340010b80054100d090644000944080c0c01c5901c01c10401442c0d400c00c01c1c82203001c41d804291000e5400000240c0c58034020204404848025010f403d5115582c1c20050050440c00c8200d50712883c01c0c410b06802c4100352042034440c1612904401136543d10700c07805001a140c6600400c41217040030800d01c4016400038005030022480c541c54600348101d00001404143e00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 956763426 1250 956762176 956762179
    0xe010b0619080a1d1f11220b030c0c06180316082205010e0f0105220b1812010204081216060e0322080c010e06041701090303050901050f071d 62
    0xc043c0200340c482c0040781c03502c00c8001c002c0040c003e001701070301c404050782c80582100d04130200c2401003100002c2c0980300d0900e09184803181b00b8420b40c85290040840e0016181c2403031001c030225004092030010071259400c0b41402450003141c824800c1c10341e40c0e0307220f40340d1000b410150402449007040031540c141c03548a07440d0040d0070001c42e0440d010b10200c0649120f4140055511401a20175041401e4840c03910714040e5261440d11241d400c0d0315030104c42821912407035031041d660000e40303030542002074000000b01d03401c001c802c081c0150402c64450540400110140d204201c100726400002440320080035440d0070554850b50408104500c007240c600020f04541e0506250020301070022000300742001182c0000341210003074445012a1558500500c81185c2c40015294140e6002d09081800e0810083c001c03850540c44e0031641054000000c19451969100c050502c100360309405410760046143d8001c00c00c51801044405518002410041c14000a1384056501d640319140c400c4102d0b50 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 956764676 1250 956763426 956763461
    0x1101050c01091209210605190608060604060b030c030411010c050105270f07140415030302011e0b060306010807050409060e190b0607080c0313090e010b0619080a 71
    0x40c504105220038180900e801c00038403d0240400d111a205e503042081c040703800c600d035545051715602c01009020140982c01c040315a0071800b40d035160302e801842e018201203405049070f424024240019070f0b034590011001d11205100f04414107841d1015030740d00c40c1d040108142c180c00c0c108016680d0481c15a0090091350904040080c280015500042d000c1e43c0c210304d055094603a5007403540c49807045000460340350011203040004e1401a24190701084c8014000900b00c500c21038a82410081c2da442140940d4482e5203901550401015501400d1414202805100d500400003407662100800c25814410200301086401e8486c4083d1000740070a408100161521200060b00d2003404071803601150b14201d00d50540c00c0068024003c1007840949450b00701b00d00740d95070b806907070807000b2860b5848c40f080c8090745048290390016001001b2800000a40741d40a40381c80d82503d800f1080540200c0d4100980126026806205400410a1300d04034045031101e8800c503016044620021503c0d12 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 956765926 1250 956764676 956764691
    0x30c06111327050601020c040b0a0806070210050105010e0f0103020313080a02071e1a0f0f0409050a180209010b09060705030f2a070e191b091d041101050c01 69
    0x5041c410908070110000d001c8040700080140c2c503400d403042195401d0040e08200c0001c00c05c0c1c103241c1c00041d403c400043c20b1b130846a865a410f140f4010b412a0b01c54016031003080c0316070308040c1c0c2e0722541c0d01400e400e00e0b0103044c0308100d4000c01c0405138040700040c101603002000400003001075607038403c05030b0f0100302150740341100080203540e80724501030301003440740c3d00b10060445801800800100c070880320ba51980408491207010305604210340300103510300c04110042c5250500c0c001400503010a80002900e4144880140b003100c10308884404080d5540c07414001594a040c0102e045030300720128180d4548152000c20098010703080f00a100d8400499600342105010b03020701b14505103160407882e40007900281202e81c07080d2000c054500d4001c1c440511010302da8940c0300d030340210426920034000c03488223009400c0701c441281c0c01ea1156182c01035800724541c4480c0700f42c000c01105e071154206411170000700201c0e00010340028480801254210843c1c0d000300c05440c42c00c1c41d440020030086 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 956767176 1250 956765926 956765939
    0x1060f09030f12110a0b0a0b040b0a0902091207060207210b060603091204030b0402042009100e030a0b09070602120910020115120213050705030a090201030612082104030c061113 78
    0x1809a5240007c54103100c81c0d400d181c01c0c10310810a0340301c8010a441403182c0307015540b10083d40b1102034039070000302040c60340d0942c00041000800a050300c0d13004004840c074002d04600000d127060324011624a2800300764003c20240b000b2030350000000c0701c481e03642e51a0090030902d050741070a010615000302080000c01d100920301e216119031300170b0f07906118421135044081c0340003450107824200c401d0180079000c0300b0b04041d24401d419806500306100d141d130039040006d10b80300c0c10040440d107003560501000000141486203400410060000b400c0c03c2c4610700c01800316000c3c2c0c424960282c8040ca40543c2810301c03d4004da0f0143c0d00d21704925860588680300d85001d4244410b0a03402140c07001400c540d404020700c101440b40d15aa0b40301c90035030b03c4400c00341e4044c1c05401402d81c1010344810004c9075030310300b40b0504640c40e441000700e982d89075060515144802201082821342c0c284400c1000b02080d0007106041c035069000d100000d003202d0f148822919070060030140b604c050742c0c910005c01e10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 956768426 1250 956767176 956767193
    0x10120e030408190209150607080c01021e0a0e15040f0618051009140d050709020909160507150f0501030c360b030a0b04050601060f09030f12110a 64
    0x69940b600c0c10f40d2040c3c40f0084501100c500d807050000e400c10b5020b0000342d8190700302c0611100808000300000c1c07901000b0740302c81485401c034100c1c4003101d950008483d1941110041850345243e042103a00381000c00c100f0011700f40200031080c0c1e6000d0b81060720f10b664604491000c45015140c0700c001d050b409600c55800801004014851042d1005040000718281c0b4191441941e6000281c0d02d42040034140f0240794200580e4030201c5e40c01080c401400c4d0002541444104060b12001e46d0050710340c1ca1550402c89100c0300945403210300fa940c4c4403410440b56004044405280c0c100030b070341e210041c075502d071000280040ca072180030fa680380500100c10055080d098800301c5010110f401c41581102e4002036510010a1030200649400c16141e4582d37140384d0818084507400405031804607001e030300c90403003a030000c50701128070383c2007000144155a00010014001c1e481c3d403a261000d0b50450b510b00c12040d44107a03003d407082401d980400a0140314030707040c100c0e5001110907200350010501c0c04100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 956769676 1250 956768426 956768429
    0x8041d15010c03030906051317030c030105061c0e030a201902031c0906030c051206010e0307030611071208011805040212030a0f2a02041a0a0315050f040203030910120e0304 76
    0x100815100e01d003104280b038049c03e07240950180788009245918160400103d944031310360030162242c034416030701e0841000b845911034108084000d180da074803c4086c02440c00b24641c0340000150f84004015142c0080014410361220300040681010700040c00007a24040d04600c694015035019214046102d80c001c117502c0403640d15403801e202c2e080c00c40780142c1d840c0c06003d0031001071444100020307825600c82c01b081c200242015054851480d1030b07466220540b10b1a121229200d5000503080082100c1d004101c1c0482030245080541d55041401c40c01da208248000e09a68540f580007044c2950707a1003d6030400c0010403000c50f9a4ac00552901a00c2e0681403011103000c43c1d9000324000f54049081f40c00555042d144083c060b610302d0a070700304002040d801000a01900fa14180c000041d2039200c8800c020714010040c54060710102c802c1c01c03096642c0180311764030401c6481c1c1800010303280041501c070795000c21a40001c10600c0f101c801c0741c400001c60b109550b0142410a64120603030040001d00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 956770926 1250 956769676 956769683
    0xb0706020310080d261e040c15050403020f15070803090114042102010b0d02060309120c0a050c04060608011401030e031303170901021c03090f08041d15010c030309060513 75
    0x82810f0f030040e0244000c2d81c0126030b02d401d5002d0004c0544e418006c006050360b4440c1c070a500e0084180c0d1100c10841070b42d00c0320348070310010541c00a414000e501d17000ca00503002031021a001020003a8007541d02c00d040c06100c00080484030003101003000c00c0029040764000f0000e401000030301c2d1134681484050010049499501081d030b0b003e031090500d00c103008007180201e001d00829100d603119401d00c0004e500c01802418a4003941c1c401d10591164407004101ca240001e005107000310407400d04501700b0349040d25191155140550030000f0540000380141100d0300248007039a400310031001a03010301182c548202e852700000521072600d46911b040d04050700d005039002009402214800701403032140e05c4030280540e115942e1110915801d401038540e41d80a854003107891981940c03000240d03041d80714105c825580c041420710107143c0d43e203a18000000ea645d1500024105090351007100b0124110040c10070140d03192541c103250198108200b070341e070701044c20001441d0003080b6050002e0010713000c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 956772176 1250 956770926 956770967
    0xe1e0f0703051006020c060d0e071d100f061b0203060420180a090c0f03051e0a150c051c0209010305060904050d08131b05040c05040b0706020310080d 66
    0x108460403c49812040d01d0185c0c00606031400b11004000c60703904022420307910181c0300d180c005810002803165000501e003101304005184040c03414030b401d0f150014001601c890035010104084031444910f50100c84003070400104101903440581e484501c1410017a4052160303105100400c030140b01100042015050510380d13460540080010a0240403e508403095000700440c07020242a401fa134003a903c5108000f040991b140c020004060705075005840f40e40040c034a400101d11032411180703510344801c02420304a00903036240c0024a0b00d05003c88002a5681812aa03560041017116081d000341504621941c10380780e003800196001800e01c9000034208404284941803892682c4e00807030340300d4040c1115050032001141e000100411002420340c662040c3c0000c1550b0b154540c090b040b07011404440e440c1040103120649410384006000c124080104005000000b81901d03003140e4009409640c0361a498009460b6030303900d404c45250760241b075030405182c90308482e0f101d11000c807030100e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 956773426 1250 956772176 956772181
    0xc0703020118050102030f0f040f09050f0f04050d141c06080f0303061f021009050c0102060c0f0d0e070b0406090828030804060e060a0603020a0902030408040e1e0f070305 75
    0x1240d22010b9a0b00c1101c0c00340c2c0c014407489080070031a4001e4080000500d098900782595440780030124122648a17140c101e6071fa500f80104409240002030b0300440c030b0403007030742503007400e0756099500c810f513241c540100004004101400102e1100715100d240f03482544220003000b9144080c010f040314480c05c002403081541c0141e0b00300021064911440700246520710110f00e120401c20801a1280084114011802d24281c009024803542d651a4021402030080d02e420b80700291900c84090314041d4002030900c01e80c060b200e0407104940c0200315514000c103842408181070743c40d08500f03400c40312030003401080100b03100b6801000d02045920042c211030502c1805a130000b001442c1c070755000508010320040e40d01103030046d007000d41c00c80c0c400c400c00614100007081244c1007c1069a01b034a0198503020f0403c25880d1a40041003d003c8040d0110f02e1410701e41d4038101180300e20301c240380650001e100026031205e0029550034640003c48401c0d0400e00d07054100c8009100c04036426808603190401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 956774676 1250 956773426 956773457
    0x3130209010611102c010f020d0912021c030e0a0c03030305270304060507082107140909060108040c03080c10061707230612041208090601051302040305030c07030201 73
    0xd10860303a101c4100803501d00900c0301400309200c0300400b505e0710542d02d9807007030090744075075100038120a940d8030000100c80d00366142c043d00107889440000b0841d800803c12514194201580501075284c03130500003001807a4074011424002141c01c09080901d50400000a141d0103030401d40c1710340304070b40c0c1e0300e9101140c0010201e0280d5080500050a50051109011460088000307009441c000c1c02600c1c103010807004002c0042d84291a1800543c040d0750500a03519000000100c0b10300d407500f8443d00380012040441d002450003400035040180c10404901400b1045e44044051030708103055035a5010104190365403500f20505200140e032070b1040024000e040301e00701a24001c03455015210380c2c1e1801420a001072088140754004030f40d000320349103080e501c98000b424260030003819282e0503c0c00c1d08001131041503420203074084c40710040401c280c8517030105100b4190344084403c207202c0c040300c0700114001e01407900010428840021682407144c0d00140d0784080743d200340c0c0e4000c0740031482603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 956775926 1250 956774676 956774681
    0x17010b0120150109051e1e1008030304030f020d02070605090d11210705060c1c030e0307030c020f2209050a02100c15020c1203060613231f050313020901061110 70
    0x7561f6a5030445181c24101c0c241d030041d000c0903046010203901c1c2c26441e0302c038081d040c00d40d03000341ca0840129400f2000c02c00c540340c043c0800f00b0208110300103480c103140b81c1078001c0d04034401d003034005100703c090b00c0000f0b0401100a110440e074803805001c00208004d00c19541e192030020100820f01442584000642464000d08442c400c0801c64041c002c4803403000200428540c2180a1000780b58030350100c00c033030340010009441c2c06e900a90398211100d120b40103020102c0300b02c0107034500807885500413184420404460b020400030103540003410714443e0510398100810303140020b502490100c0c00c0820258000d50070003400340660360035010840d98030b80d007404a1203514142070043d0400c109017403001c150700c07003c0d41e804100034005503d04400c0300905100c2c2101c80e00a943c0b0031074a031580e078001003078012020000940c00c1d6005d401c040c076841032000011800d90041c0042003000000903100c500c2044401d550a64050b0920b005561114030141c24000b03140e008a10034481c5004171284440b660 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 956777176 1250 956775926 956775931
    0x20307060f09060213170a032f06161b080a14040b07060504230615060d05090105180a050a0210030b03100203160305100b03181617010b0120150109051e 67
    0x54036401c030011001c0c0c1103c20080c0f4442c00720800059004272007a8000c0c03043c00201d11a5982401066007544190000741501018070500c07000c054803949a04c00040c28001112101402800c18050f41c0c26503ca51201d60300c125004180e003c580400e42e0345c104110740d001a8050781c0300f204da41c00b1007145a58a5010090300400692860b8007000100c1d600d2281201e03103000400703015100c203141040050000090319025503150301c882e07548404020284450705460924800c2900c060140340c03866444440e40d41c21001d40c0a4402c0851519040f04680030340e1203419254800380944503010030b0708400100039001242c032a424242100a00c006107480303440b0786031091090841c05140740d81840202100780d00000e205558200c0700010344c4440340c06c02c005150860020030030360810702e414106903103041c0f0044080184140e0508a044807982e070041100030340034084519280101084821162401c0943e0083c008a000c90310004142e000041d0020f901c034080c82490915150b000075404249200d08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 956778426 1250 956777176 956777183
    0xb041107030e0f03191110090308030109020a0c0609050703112704060e07090501140a080c040527070e1614160b0115090603020a020307060f09060213170a 68
    0x120001080e0503c2c1900008410900c0503040310ba00358001c944001e011010710109032000300103580711041502c0d001802000d01c1c1e00794501229410f207144d42da91214081070042c41007003038004c648035032074a10841120200541100040c0860006030405549408150005440b0000301c06004601e03030500844041206104404046060504848083c2e6011000d4421140320b501d130a61200c1240041102ca00944108500002c0c65454910040c500044d030300a1280151580c420812154102191110003114107540110b070765a5055500951146080c0041080505101c40d0301c40102c0c000880d40c058400300c42c040035440e180e009441411000700030311140001c4e5000136007292a0300d14009000300381400352240340901d050b65104030584400360001c0000c000800781c01d9100d150b00000c828003c21980c00c0840c0b90014500009499108081d40039000949410001c80b600400d03a010420b0305400240440d150a50403500513a01c0150744036081440940030020300314243c01044040c0b100b81c0c07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 956779676 1250 956778426 956778437
    0x603130c0816061805060403140601141c03140d020d0e0f0a080d020f07060209030114010305191410060518070507060e0307020d06020306010207061b020625060b04110703 75
    0x50110100c0f4014a0800d9100904200b40c5000411b0b48440000e40043c600c034003026445200307aa00c4040c13070b083c8140c0c044c0101c00c5a901085074552550541515208a410150614a11542800c1d5a0740c00104620441c03084001600401c0d148164090103009010003028018400312207000c0341d07182d00c0e1102c00600b0750845420360300050b81c60703401080000f85541c4098140710032204240034a400441082c0d940c181c00081c99061440c013841100300c80c5660a9006406504503100d10340d1300c4038100300d00c803042404030396100144002c50b4503441908a081c0112040e00c07016100c8400a0a01f9101d101d000b40039681e602050007800c0032009201d41159a60325081c1a03407034807900068081c001c4038100b00d001c100306000160321618503804031940100d2016a4a0800200080c90f1040e01d80c0548108416900c00c840311101c1100c001205680441c0d000342c42c0c140c2c0b440c040400b980d03ca2400500c0f050346e00f03024410010660020700006a048600300310801003071605c003002d4410a10010001071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 956780926 1250 956779676 956779679
    0x5090c030c09012706030c1d1006140d0203100f06020d0e04050703020403020306041b0b0403150905010e190c0f06020d1103091c060612081801030b0603130c0816 71
    0xa2002c40380c1d036040d129401c203100314645204c0b02c2011102282c0040d1180c00501d5414408031030070614a00e00d410154080503464034001400402000c0700f13004480801000760007101c840c02d4200203850304070f811088119500d060280603860f42d0402e42c4103255101d00c1180c40040c00f14004203030415141030a89a01190581d0101000b0081400800110034943e0a00c00407026172420449103110b9440f40c071141c10200c2801744100c0200220f54080e40e4170003c202300502c002148002000e0306500c4403400030441e09803030f2600c2070160910080f80f005900c0382c04440d442e074441c0341020108043c090f010300790426131075200c4c1d0b045048840c0107900141e8806800c0303850803441a80d41b1481000b00354140c0c0e041041650004103100c1410510802201a5450103002d1001c1031060340006c0824284108a00205558802150040112094039000c21000d1401c059000341c118801415004106684e40e1501002181060300021000c2d182100a1600031441c8070000540454450030b0b50484500316 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 956782176 1250 956780926 956780939
    0x170307080115090e0a0c08061507020402250c060e061e0d0e120729010b030406110403151401050a052e050a0f0e010816030e0d0305090c030c0901 64
    0xdaa02c1e9800030108101d422000404261050a0600030000b051002c141c0141e8908001c092601c040d0041344102c3d462414407064a0740c180460b041f40750b06070740240c2c40d0f5280001001040c0c013840c0c15440c01a1040310242c00704031041c10a241511072640300e0403003070341c00b031001e1240e54041c40c903210b03040000c0740d00144005115000174000d40514400042203901100c00c84a04000180d040c401c555480415441c040000c4050402e009800d2100045100300c1001150140d13440103116400060300c0001c0498180803968108a40502c9850001503449940340390204030351001600c031098040c0381a650110f010600120a4126400145030705131540c201800c200c16907106041151121141040c0101d0659121074110425170b00c42e12003e4841c014908082d0441100166010811400620824890b07801807542a04a00d0703007002c08410717020f690416401022500503040c41c070310130268000402c0e5410b8000610486209042d640a1100b810515580300001030855504c0445000184100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 956783426 1250 956782176 956782199
    0x1e0102160308090d11040f0c0908060f0c2101060e1509030a0201030f150f170f190303020409090c08121810030b1507051504031e030609020c0a1703070801 68
    0x201401422a01294245c4100040c229035604e214520b03a591a0726031205e0458000918400601021001c0c010a1520b44e01c0d2202c0010020001d0388200d03000325501c50f0b002d0704e0740b0000742d0b00c03040a04400c075696101d01019008101c0013403030030310984c11580318a500302014410b036000d1010140041030302050b164019005800c0340d0302c600c9003542e5540c08130f0000380c2d01c4104540040c10b083c10400e0704c01e41412300001482c544401001d01e140e001205070a451100042c140c01821000011000e040d4411b01e411406442030340c0c40020410304050242041c804184000c1e000ca03808031080355282044500728000f02e000350004844200b03080003401c6421305090450903410700081c98002065000500002c0702103454400480c0d22241c0800c480c81001420400c1c2d04a6900022041101c2e10b01a03500501400c0342018800300d0081e01210640450700a2304030501404010760300755200c100096545568580c03c0c030040c1c075980510003001caa8403090038103c0740526a0340d03886000c10384c05d00c460800d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 956784676 1250 956783426 956783449
    0x4060509013002030a0e01050f01120206040e0a02030703061401020c120f0f060f01060c0213022a10050610081b0702090c071a010627051e010216030809 67
    0x250142c0c0d5002d07101c80395102049016102d00300c480140c0740c0c200480090215013562007901d0050f85805c09006480c40ba80701080c1c1100c406a210701c64560741c91002c038000e030040358454407103a03103004140704c8189010f40145110303081e07540e03041288030b980381c40214000e002c48000a015030404c080d8240c40d420036455441c0e2040b4901c0440b0440c00880030003a2808460340700801c819000340091198003000e2206035030051040d850409000c00413034001810b4200c1040600808035030005000004001f00305240100c00703a50300341076000c0c07501c44c92255280c140d00104034059a280000049a524000110384203062055032040130683d81c800c4007000d64106104503405c030902c14411440140e64141e80300e48a2803c24503020346454a500e49100083c110036101c0503100c03036400050005642c466180e5002c044c08141603c08581c03105554414941d840c3c22a0f9080040299840061080d01c2c00d9501d0702d40003a03080301c52130340029800e03a08441c0d450000a10140040202c06a01d10781140ba089 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 956785926 1250 956784676 956784707
    0x210f09010c0c030501050103170c10020c100507080106030f0e1e030706111321081b0307080c060609040f0b0627040501061706041403090a03030305011a0406050901 72
    0x941c032125a407110015a034143e442113502d81e44030300060082054070310004403030410200a0071704100100301540d4943c1301c0a00341d491040e0b804900350104090820424641202d000420003541c00c228100500094003400b6900201e810580c0c0c00c200521107115580f1a080c1c144050991401c42c0556160308182d10340c041c07182d9100c140405004582c00d031003004599a6074095595540419200308a41c000617540b00b14107112090360000010b08042c1080a00d459000208558901d041da01c0198541449400f0000c1c5110205800c0c04104c801001008010b80303c00c210313115550b4003070400685a070708480003040608800d020b070002030f0501c8131991304488000c00b4003e030115994400441200744140c0398103800c0b032600a200c28084203104910141c00031003c1d0309001000f10402503910a0080d10040030b00c44150b560511280060041d5807201c2c00082c45010600d9807810010013800d0700b1701400100c1107002d21040f140016181c1100c04a806940310a81405c0c0c0000040d91130074484200790 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 956787176 1250 956785926 956785937
    0xf02130e12040f05010e030c0f060408071214010b060d020307030b0d03020c04050a1503110409050a08120c0301050d060b03010b03010204060f0e12120715060611210f0901 75
    0x10502034034107004100030312404076241520b6925100001441e43c0c0740394805414060202c8100310a034030007041c92559400d007a24694500101d0351301261081c429548961352602440c08042804506094036400141c0240390b00c00d030001c0801600c030308031591007000c50341c4405c3c03c105081d10310203240c014690040ea40d0400050710000b40003c5034074040840d10071801a0400c828080480c60f151088030341005110034208110140144031b0030711803204e8040070380500820702c8401110303601c1d900012501075001c030031b50342585d665103410070160b04900a8840ea80054800099403120240103881c12524000c000081c16403003a2141c5008103400c030100f54042d500c1d00c0340001039490074001003004100c40c1c1d95007071030013441f0a8002d00d0307400a2542d81d8072591803401104008000000c00c02c201102c506a05036444486140001c869428485064480c034201740000075100c0e0010f600208000900c0c1c286e0b0840c0315090842c2c0c48840e01c04401504072542440a260101c9902000c0c00501806040c039 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 956788426 1250 956787176 956787191
    0x907050a0c2f031614060702040f180213020906030c032706090106050604150311040e011217070201080f18030c210a020706031806050703050f0601020a0f0213 70
    0x38444030301c4000c00c602d031554400d14440e001d04040080701c0091840400c00501c150900440c1814003000051051103a0804a0260b00355911544070b078148140c541410011039900d4000c2c02c0040b66103c0069104d07400584a0340b2a0751000d0084400341c0c0b1000b031401d880c5950b1140c0c0c0302100c1e000680b200300c03400380c804461810745400e0300154620580da80c00402c9103207400d02101d401c0d500c03030360400760203038001b0f1208201c118000c0c000790220300c2680c01c01141c4180d81100c00c114a0003668019840588087c00025040101c4000c404145020742446014104020841303200c0b48076180c002070020f400303180045c04801c010840c654210302c40b60400640b485d10588594a0740d00700301e102ca80d854014210b042c051214010900310b00d01510030b09282030103280030020f921000288610402d04d51036941d0400703555200c03001c04500a620240802c5070341801d880c01001003100f221030510300a122804240b05600000320400071691010707080424001950038000b0301c0c14004050301c0c100d501e401c032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 956789676 1250 956788426 956788463
    0x11030c1509010e07080705010c21120b04140a0f020f0427020f0304060507050c15010e1501080403050d06030623010504200c0a06020c0d08100b030112110301020a1d0907050a0c 77
    0x803440c403c0650380e00602d588050309038810cc4602100e007903c2640780420620210003400011603001c520b41c43c00040d882c0c100703005400030740300714910243e003840001000f1616911040b142c0301914000840c600320310400000c803008a00c1180301d03881d0002024000200040ca190b0481c0e58816818503200d4103161002d0611843e0011103186000f0714540c1c000103202400440e010315178851101145195840000c034000384c103844002d00302600f0070000103101403805800f030300000005c40d4440d04c200817648840e20048103e0000780b40d03000f04804180f00000b05850603000c0c0c603140c007070340400c0101400d4025140140c075070f008160082640c084c40041e0404200c1c02e1001d46000b0030007101a1180c0300c0c9104c4000c107040002006481c1c60f0a00300024171881000030166815544203002c800703080800b90030800700410140d00c1c559410343c00000c4080516610868040f402c44200c40c0c03180c8170301e03054802c20400400842e10040015400d00c5100000740c4202010349600307014000c142900305154a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 956790926 1250 956789676 956789723
    0x50d0311010f1409070323010b13050106030f05040c050d0219081501090c0914030c0a080705030f012a0c05070e011a1911030c1509010e07080705010c 66
    0x40000342007030756400030035494801c48003183d50f0140f41c1401600005045540b141110712150300c100798800744041b140b0504e042c00b54008402504002c101c503822400c031115510141c00240155030000b402e016684900b001940109801554044043c01307803203050a060000303402da0020700340e0b401400883d03140504980c02c00594058000c110290124070030140c3d4030205140d0681c04996440d250412080d50203038000c00503007c2c1c40140e040c0e0381940d0b0040740040d00c0e00c180c1400440e80070070200c100180741d00e00025510b0403910306406440d00c0000c4128500e08035102900400d9401000009004802c6c00400349500380400e80d040404120707160340c50705450030b2030a41250030031005210040c01707000742c600c4141c083c4000001f42c2c14900007940b03200041c0e0001180d084070034000402302020b6100350031f00a0300d454081305011105401000c008484c0c503404292400152540f0307104801d0102c500c0031501d071060311840b00c0103259040c5402d0044412284161085c2e4090010404140340e08903000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 956792176 1250 956790926 956790941
    0x91e020c0f0c010f0e15040305100b010810061d0a081207030905121b040f0e070312030204032102010b270609061804050703170d0e0610050d031101 65
    0x100925401d045003048901e030980e0004020b052000700d9000014060344a02503104004040d206068205449500d0403282d002d19003000703101c1d0160b40c0858401d1a1107520518540009984680e45910340301c003040100d100324001e0f00d001442041b0114142c10101e0245412810045e2200000e1079030f43d040a42021540720005128a90000d030300414981d200e1aa000548400c94202044285c15882c4554890705d0207110100710b02c5002c80701255a43d10381c0310244440c0034a2040c0003a40f54440701d1501c488040c0001c94072501700e5401c1c0d482c9036109200703035002e403540181221034060040c2d400c403c0c140c407080381e01e01c115903c86290f000703e07440b083c1d000c0319460450f400444405003c0c41c0c08a040c0c0f10010100780c019046202000100c3d6105010703078210700420900c0108681b101e0402c1414203260780c00c0074040b40a00c09210004109c508010551100b407079604011101031042d440c7d032503c41c15640d211703050100d020305110620b801070118641c503220341402d03003252041d40d0240e401d40300c0c031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 956793426 1250 956792176 956792197
    0x10b0408060609010f2108040801020a1205060a0e0924010513200a05090306040f0308090a030c140114090d1b080f091903210f020601091e02 62
    0x20408200251040100980004084402508560409441251041040c821480784058024603443d00d104081002c0c01282c2e00011a41c1d900c5440380c0429010754040096030000849800c145410303c040c1c0d00c44c1c0c0f030190030000d11114403d484c050901c400c041002d00b0031182c0d401a0208020000802103900e01000004800c00041d9803505c0c3c1002280c0134281e40781038046082c81031980c1c11021848004540c01c4000350190b8a6a0005008407603500840400680601c140010310040c0000c2c49e16a034030b1644a44d80b0368402d03682d03804001e91038050078040140800c90011100d070015170071a483c502100000e500014003070b10b410784805c000036019200e82019030448410f2218030390784540f0501242d101e94100840d03015450796009000e1142e14102c920000011403d11001d50780d9402800c5a404602c007401415522414030020483c0300b80d115604e1204100580f00e80c0c02c0c092804c1560142c0f0580180c003151386403061131009007229428505c40c00d505e83c1a030603200145407000d06245c82c0b8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 956794676 1250 956793426 956793449
    0x120705070504110721090302040e07080106060c05070311010e1e0306130503030112050102090d03030204240f080603012903011109090115090e071107151d120601 71
    0x3618040c40121485803c4070121140b0400010001c990001110919410300407041016422003840c1210f41e618503400c000c3d4490b0420380c152140203800590340b4280c40010000300012030740c81c9001c2d02c008289180c000d14076000352000308081a2081c047c50148a410b0400114404000000452002c8459005003c010103003000115601382000015030014000417448480200e50301c61a55070300051280502d03990241a09508201c000c0d010341794040000303810301e20a6810740ca07014021750003e01a024000311003554410440804020a03c18942c141c0c0351104000c0c510b000c2140c040350000c00540e055034a500102d00f000713075989404511010903c1200f040e524202c0105801e60303540c1d82200c5140e5000380a140c4595440c0c0c0b108904503011000d01210081d180401500c010405500c002088140f4200b000a501e8006480d0070b41e580e010020b8541b081d44a040c90b60001c11048010400205010b035112032549071300501c40429000281040c032445075555032686811400d80000790f2410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 956795926 1250 956794676 956794679
    0x11e03090b0103050f0c01031509051003050105010f1406040518450601030201092d060c060b040c05030c0d110d090203100b03120304060b1e03070e0c030a0e12070507 73
    0x207418454038000060074642400a2901a6004027401d4828062501165920400724140d00207230300022005560003070080c042980d5810448480e86850b03c501e40108000780007a800030300e07284080b0340542d80700410710300213150f001001003000e580c000c0c00c940c004e80b03282c0750301d490500c400314800c10551407032004180c1c0c182c2010a90080c0d0031b1101c040340c605500c19401440141e0708072510704241c03402810018ad03202400b1080901c0e0a28541016104850303a0b000460b0300e80e4447c030745d4078145010300c01c1445040824003d02013191145800440000d10074000324160000d000001c0c071100ea00202c011440408803002860079906c20b80caa42c04c5281c3d1044448118102409421030009018200300541070440d0301080c0c4800382c0e2100c1c0284100000700241c10014181e202e0700030400302902044203031000c0f44264610300e4035885403610905c180000001c110058035400e0f44561320502caa03a0854680c10380d501d01900c800b06815a140c050b05062b00400d50100001d0403496000350014043c0b10b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 956797176 1250 956795926 956795953
    0x705160f0905101710230108150115120203150406120f06020d020c1e0f1b0d110d061b0801030305160204180602071b0302011e03090b010305 62
    0xc4030075400015030a0811040101030956a040e030021100908000d0601d100c1c08a0b1240c04c0c07900d8009090f00652401e0504000c5000b0729640c0d191007500c0d005801101c2e6202c1c20300c20b035143d000410340c2842c4034615005200d012108986a40e00800c2c5040110250110f400028143d81003103034601c1c0391800400c007007216803a250180d440142400b40540504400e0380c2c4a4940c5204454405404281c00080020041130300d9070481e60100208416100c4883c40080c5070188002c0340810004e45104551184c001400042100c10720b40c41c0c01c04200d074011110809005607004120410350300c0460000181c055902c40340300120803d4490b980004950811140e4000c042440350215010009080f00502c0040c0d00502240d0008100c1060403c52800e18400034018014104001c00c03002c54140c0c0200070411290060702001e48541030407801c10640e0610303180075418034803019000a0610b05942491920111800030a03401840c000c204405140c548255a0300283d000316090f500184010815 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 956798426 1250 956797176 956797199
    0xb2d0d09200d0503121315091a100611030c010c05030403020d09030b06010809010b2d240d06090c09080d0e1e030106031a060108090606090a020c03070516 68
    0xa80030480301c140116a0b03a8564507541d004090383d00410805a0010079040c5800346602c210f030907800001902180302004030000603080311131003101d07540c03440c10b000c45444c10520390080c4a001003980e50b2000520f050001c6070307a0840b0303c1d4501100c1c0000c02c946c201124080c022015841502d484441e43c0b030501d858000e03c5d15060915030010480100e0051000481072981d20343c00c2202407810380035589070003641c14010b04840107649d038405120604c000030801c085507030702080384907154403191a003168000e01032504018129529140745442d00e07000a0070950019204c0d40c0c550b1040020300c103403120b10000841d4006200d00001c2a018903080219400400c2081104030043c50b0030104507059901150b0400380c002606036010095450f800c035107840075403003c0000c640040c1540c84000103181410074a0109844460008061000144034008000b980500405001e007000440d6940d0304a100000c1d002068070a805000c04c1080e040800c000300300000ca40c01c1480c00c1e144041d8a0304010300319 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 956799676 1250 956798426 956798483
    0x1201030b070c1205030910050403030b01170103020303041203020a050a3909020f1204150e030f0a0e0406150f120c020309060901031509020a090b2d0d09 67
    0x30030002080c0380700054040c880b050381c01d07001810050348a1b2210b814880c2000f0305500341c43e42c03140c07401c0e04001c10315074950010035401070280c82e03081c83c1c4502908101c039000c00900010707425a0041000b0410010984c84100206000344191843e03541d950f500c0300c2c200a0000320030346440c0c600d282d95a140180b201032040401104000e841e0f980d03035001702004581d124522030b9040c01c84d070101c2c105030425190411a150080000700f2058a442c040c501041820707141d550790745e60689400c00e50480c14900104031380005c1c009225550401881c2c000172170710388011800f51a049501c641001400e4400c180d040780842503691207d03201451001c8008000c147d103111481040350800c0c82c54030240380c002c4102c69051900b0390f03110740e82d458000c005030040c1405001c102040300000e640020030000c2603010385141c2d100e135030303c800c003450781c0310000c0d04580a50440c03ca480425a403281207650706031500d0100020900e002d07142481d078440d0b640022a40501d000b80d80c091440f030000444085500c00d400c1c07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 956800926 1250 956799676 956799691
    0xf0108010f020a020a11150a05071518080903070f12050d020c01090b0d1104031b080a11060a0c050f2112070f1206090f0c0c020f0d02040b061201030b 66
    0x1418480b9020000b5980d166105d0050300310940c4140c0f80c0c0c503e0f143e010058a40e0200c1c20300d81644d0310a40b0400802642c000c04054034000c100c104d45020000c6640201d078503902030a50080500710951310307001440e41c0046806ca174588980e110015540051409081c0240a1039151201c01211070130100d003070401039044803046400452666034903a801503c25016543c03843c400c59100c6410620480080c600103258010a03500440c0001c1040710350386021240010440b0350341c0c10341c1e03600c0c121281c1d0350012042c0108841d44c4070301c0e004001e08210000d042c0817801e1780341c940e01c0503070a9100d0304e05040003600360401503002000f452150b02c045294400001d040030064918060520040c100c051202400910800c082a032100413558860003c4050030f450203030082101c3c2d603480c03140324002c25580c10600b1401d4101140e00761490b004188900804d600906900c0105500b0f00c02c000780305c000044103d91141da500884240c0e510780380003400c03c2c03444041c00110594110301300750160a100810a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 956802176 1250 956800926 956800931
    0x6070807030e0606100c03020c041103010f0b030f040201300501090b010212181503130c050108060a140a1706072304031e2f0a05012f060f0108010f 65
    0x100f1309445070403103070035801c0891074489407a0031185400c904000902e404d1692250500d03503080041c2d070021008504882041c200402829961070743d03840a4041110002101d030300312070024025501480c449030340b6881e0050b2114841d403100381640500102401070440090b03032140184014032080c400c1c02c1d036411090004001d283c0341e1450030180792144010b00104210750a0700003100340c030ba4510f003280c041c401c0b0391000d0700c900c0c0c0280200c0c0c14000c03488003500d403607035803100c00501c1d540540030311802080040d2412110a06060f0f6940d140f00a01c014113411450004000841c4002c85080c00c800d41c1486004c0c00180c240124000c014001030f141002076200c0384541141c03105590703001c5400f200e603c0030b0a00200c056910b041129982031400142400b0b0444190b14000c0e1038400d50400444c604903404d20714029048280083c00d0000e01070b15000c82e001800e07090122003694035804500404c280c6404810f0040320245041c181c081d00ca18004d090240014400500c1c2070203500140849007408 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 956803426 1250 956802176 956802181
    0x120c1101210b0f06030a0906060906080d030c0504120503070506060103051306230903030405070e01060f050d020415080912030c07020906030f0118020f3a0506070807030e06 76
    0x8542903201008100311609a0b550b030b05040585402c40020311181c0000c040319160b140400e41400030741107204040750001d1500b90f01042c2c00c41c2520030a0260703450342008144504003580d0030b03001002c000c102441401814000002c800d650882c0c1d88826521840c0035607100c460500e000740c034100f00a82074a0526007007408106030a6005040c51001c5500001c000c14034030f03006041c01d413403c05010204800c502c0d0742020401504d1001000318003039840b0f01c04407182c240c0c0d140f00ca203c0140382030140800045540c060200168800c0001d0141e10151810040c0781555828840760f00c1c55801f01490041032500040001e0340038148082d03840b0b0801c070001989549401c5040c1030343c0f8070618400910800c000d0002c6440c98808004940095000500070400100115904d002c04c081c801000c0f4801c1174a82c4904003603042056141d000e203440c440c00c181d070034180500c60312040280070210029103810440701d04045a01000100e0080307a164540c1c4805d4103041c00002d00b80c40358840d4500703c55100105 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 956804676 1250 956803426 956803457
    0xa0e1e18070f05070816240b03030307030b180a050906070206061c0302030d0e010522021305090f01060311090121060c05090d0c080c09070207060e0d120c1101 70
    0xe01000c0781401e29100303607154443e01e041170305401501ca0b04071038900303903801d07070340400c5074041c240390745507044140e400d0842c40d4004080e829103541c0c01449806d41c0013880481e0f0164000d421601248400520000100d5100c0e10b81005580c800c9a0714010719407600706103d01e41c0b509010064101c8010f00c0a07162525120000c0f03030280309a8110007481040c00104003003858803d006540340141064410b010a801c0640082d0103404251080400c03584c1d421000c03484d4102000800600c0e5070301411060300030748072817030550003000020700d250007a014140d03e40c0d00c200428800c6002543c130406002700c4582c0c00c041842041d11058220004000704514040e00300d071400980031014079031005e00455000071402c0216550700440109a40110403000030004210000b10f03040255030598040b02d4882210b00f080211440042c3d07900800340c3c010100c1805010b10a0645841e100d4001e0100c9031810031540d50628800f0300700d80b014002401504a007001c11100d81d05a40e980e900900c0c16034624040d000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 956805926 1250 956804676 956804687
    0x70605180d050423060304031808150606070f0812040501060b2701052203060b09061e03010b06121b0a0e130b19030c0503160b0a0e1e1807 61
    0xd110072008900d01113204000b80d84440c2c0345090400381c40503842c3e0074103103405008222058454048a400000f001c11003050010341c451003040e881201c110320352203e00a200792680044020340d008514070f44060003203403421005000d0760450460341143c0e4901800e100c0d08490854201120000080001c10140c0c121a103000b0038201100151102851060005036510700c00c44030100c1030f86850b40c0e83d103800b440000d00d100c400c43e80942d0b02030003003044110410030400c20450740b0303580c800011030300031518241d0400301242c0203d0180000464040d9500003400c00c0c2c0080c014080c09030140320030030280488003401c0400c2c80d45e2880d01c140c20f144140b00081c01c2c00e0500c0907400d000e0300c1080e00324208407070646c00c58030b851079018013402184006210780c0401c5a24ad03000565100800d890001040e04000841d0b101000b4003501000310b0904210032811640c0c0004089400c0145912450045590380c180250720139214a1000040001400501151260b05d60000000e52400802c2085298010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 956807176 1250 956805926 956805929
    0x17070210180e0f07052a01060812030103050304030f06060306020315030f0a0201020c0103180b0f071116050d061410141e0616080307031d03031e060a03020303070605180d0504 77
    0x1070401c151a440c0c02045400031b4440006c50420707014400c40d100ca241c0300c065000c04242c070a21402c0e641600700105a1946c5440203100040240d8400c10040000c5401c01ca8031a040314070901004c07070a41d6a036155182a60800e031460800c1902c1c0403403104041c80c04005c020843ca80d100003504512425400203900c525040e10101d0625884080c00702c608244203511300a142e50201e4965030a003040d1103243d0352200300704c07540780100703145485511061a0008540d50355503081619025400d04000a101e00741c0c148000840c0c1c5036803142030071481a004840118072880c0188078000d8075502e010036840e440d54045a8007030091b62803150000e003e41903072a00240741c220540e03540340c1c3d07510f1460084039500e803411030203000902c1c04001c0c00195585604410841b08010034483c2000150100d00c1d9200d10065801040c8210b0807102481d0010340a4491988040020160041c055598010904507444030030101c55040c1c0d51810801480c0d40ea07158062502e10400050481064055014200e0300c5603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 956808426 1250 956807176 956807191
    0x60e06011d1e030609031911030708090f060d091203020c0c040b010527031501180905030d090606050a0f030f080d15180e030a090317070210180e0f 65
    0xc4042d64480c425500007207419100d4080c04441d80303481c0c01d003403064594000c04000c4840f0750312842940c044074414201c0c2c108041190001d140b41c02190340d40d034031081e030040325030b25003200100c00c11038160768408010b07100400c0205c0b0040307050b050500c1d2050032030500a84483c04c1c9803042c0807208001800040280c4043c6095a0000d01c0011400041c0d8040c0514030000e031208025145000ca0112000300b0020314500c10780845103440b0b1043c02c10300a1100c2400781d00014081d8072516440300c034864100003142070088003075914002825075a0025074915080982c0e0080c0c88400402c081e0601d400508002d0a403581100c04840c11aa00c410041072444030140148a0100382c05040410075480341c161f00343c204200e401402d541c0d65550590031204400071100c00d1400c40c603001e110002200301d9000d851243d40b0f8800880c25070351880c00000f541607080d511a9018050400141c03034110341c0111121544e2a040303140400600c00031404100340d04070389940300c048c07030502c440b681302c50a015401000c1c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 956809676 1250 956808426 956808439
    0x30c090e0d020f072102061917040b0a05040c03050d0f180e060d060b0604060f020c0a051f050d11091002010b0a0b0c0c10050d060f0e18071503060e06011d 68
    0x145102c60800c1e20102810295000c400017802001040d05034040802441081c2c5500d0080c800c0780c5c00c0c860141002b2200a403013007190034001440380c00c043c0d00940d8071034404c3c554400b4041e22038803003c3c5002060705400010481d130030016009a034102c42480c07455180c1ca4826914182800c040049030300b406814a0f00404038468500708005c499008401c2000c00548243c0c1c40d81d98815004083c1c034406800350026004080c0038011034101140e0030800d50b403000d8000c131110011041301c080740b0420600b1003402c004062054000c40115401642c4010391b504d2038498440150608200e80000500751090039a03150918101041e21940310300011a1500f0b042c0f181c80744a9013074001e0810820b8040e56911102e4a0075000606c2d4104014041e840442d1204002e1140c0b0307a40041c8130a19140220b00b84001024000b4105134107800451020007001000d907100c030741e6901e0040d1030460780d014198010035202c030000d00820904500265210400b4a00750710042e5460004030040407402820600662 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 956810926 1250 956809676 956809709
    0x1140a050d0b060d080c0304212d150e16030b010b09061603090306111c0b010302040f080a030f030c0c0201030b04020c07060503042603130c030c090e0d020f07 70
    0x42d54800c1360320481c1e030001d242c181d4529a0442464a9a0150040a031008042d44200d00a56410042141d0255009030314860f400c003403d580a01c003207204400c0903001041140002c00041101c020486041c4181101189030161207488030b04020b02c02e1184110240012810000304040042c49811912244182595180c2040100d02b15110b000440344034013070f04000c100d040581c05000d00080700d000d490704100162404012440714807a030341144100788140280e0b83c8480d0304e950302015140105040c01860640d07200040070303001300182c0c07020302c2503080310b0103032810306401541c407218500452808111003e10044040c00c0c0040400b0040d0405070307604011205501c3d140d04841d40b064012044400c3c5542d1038000074030960084804442e0304109425480f40d441c041100e45c482c103011882502d00310b0f502c40841d02100011044140d6411038469000004540703031035041c201800001c41c0208600c94460511450002c001c00510704551080c18074200c880c80210340702c425140340d14406c40412 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 956812176 1250 956810926 956810929
    0x1050f0f0907031a070806041a010305060604090c050a03051006140304170301270e0307080c0106093305030d0c031e030b150a200a1a01140a050d0b06 66
    0x200305400090409407840d0141000d201c13480c80d203c2c461400c903a614080750b03449101744410345a09500c40610844141030b2502258003940105621a00c080d00803800d003503903070032080262140300c3c9221002c501c0020340480d0b101ea141c005e050703001c20042d1070084564502440240300d030f8445032207500490004000f1900300000841c1c610540841810081c1d182c0d41c46a0202400611201a21044a10103078083e101035a05020b469040c12090340510305040b1241c032202590361141402002556840740c01291a0388a41f0500104038030400b034090400350140d401180a0b06c01900003260a1203907a4100010341d40010704c0308080c0414648040e1014580c075081d04d0030200c0b60003c82080c5070f540500d070b840d10760590210f924004200d80800742e0080f90100c40780207109070500e00001400304007203210110314a40d14803400318005d10442d61000915180c054494640e0034030f0900031201c440041080c0041c100312110403180803209208014509000100e4504c10040b000302141002800514036 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 956813426 1250 956812176 956812183
    0x90612060103140906010512012003060d050109030f0e18041203020c1203070306060816140c1509010f0b033706020712030e030919050a0f03120201050f0f09 69
    0xc60403201425041800c00c104182c0c0c886400b40101c6008148034000c0e40300c441070500a8000d04220b082c5c8010003525406c02b19401035000802c80742d0405444401180060024415210b4441c0079a0303c80d14030f0300c1410320051024040140039031044460f02d100b2005040700480c002c0e00550b02140192060384100e90641c081d002e818001e4041c0d005040464000072407803402180b00d8071031a941085559214502a5101c100940d03000b002040e13941a00c4410134090880902c007400079140c174a0038520341499030762401c89904844042d2609500c01d000a46400340148100070802c100305010390808500440c5c1d40f4074040840d90360311810340c0304900466a480e85001c1c040b880e40c5078012402da03614100700000c1e60000d8000c030790403802007030045071049c440d10840406503503a40280d807a00402000300400c070707000031380c5d0050700307c2070902c00050079503407d405000104070a9001d944511700c1d42c20800d81c000402c02c221307029641004108408250528442c60340403c0080740f41c9002e45841011a14 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 956814676 1250 956813426 956813441
    0x108060105010903020330070b220b0c0a03060f0b09150301080c1c1a0f07030606090e0405070e010807090e03040e01180e160302030f0c030d030e0f12070c0b090612060103 75
    0x551f280005408800e005410000c50701c194030810454810301003452032441e2184030020054002070310303038000c140c620f8003a00c010440a6060718001c14400e4480f00225051407c0d603100340801080082e600d03000f410304411172004640c40454107070031340d03240c180440d45a0544d090501e2056480001c101180c408122400250540140e0126441885c0c1010204440d50a50f07050540003850340c00138805600c240205815036201c2d54a6221842c80c0510010840d000a48101c81d1406500808584003966001c0c190003032101d14014412680340119410480304804040d0910b50010003007070010603018020641100e1340c00441c414078200f0104850020044089250458060744905502c0c008500e031002d01982d0003241601c0321068101c01d03044c1d81300041011160140c000e1001c10065500035403042080704021002da410b4030b054049264103040300c4007240e400d0030001042400501580c88081c0b40604102500b061400291800107030541c000c010b068081301c0c00c200001410ba074825044140c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 956815926 1250 956814676 956814763
    0x20702031c030c090e0705040303030b03150702070f060201020309060429010303051b010209130c0c0206041203140a0c08070609080d0902030f01020f18030c06030901020301080601050109030203 85
    0x41d00c200814800501905070f08800100044580001240c0700101c011254017459a039102d00f40381501d1940c00750050f00400c80201d9150050010743e00301405c051551502c41c2c1e40d258064880641412152080701049070046000c41e0f105200f00441c02d00700054094225804c1403800c21183c188018900202d0f0a981c0c030212642c1103580004101034000019010303138007019920514440b4401d103810301700d000349100554054280c01c20400c01e41d08039400301800c0c11251038008603500040c0c01040141d4080d50140c4207480669800806140e844440c8010f84501e0300201407401400f07041c0240740d1000384602406d81300d0006610020803c0990103403400c40c1d8001c891a44a04020312640001d2410000070f9009005045108504040603c2190003900d540100d06040510f200200d041218640c0c110a42510829490070301507a1070002070f6204080394030008d03a4941c1401c41c0f0b541404410fa1140f07040c0624200d042c00160360116800190348400305603101000c1c1d4105608103507006e10614003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 956817176 1250 956815926 956815963
    0x150706110a090801061d060f030102040b22080d08011e1212030501090227060906030c0a030612080a050d0b100906031109180c07051b0f18070302070203 67
    0x140d41c10b50486216801c44802d04002c01c0f80503a540d103003140211641d03c86600000800c800100f2919060760042000360f80036000600389515200190344503440302081e2010041c074015103803440b0483c04840405044c0b030300060070209080b04000380c072145040c0140c40103c818500d440114450341c50031040100030a1101900b48055400c1c0311071032041150380407000a06000002c100151076000302d80e6042110000c50045000c40c4850000040110921540c0b00d441046041c10564880014500411020300c5e201d40d987c01d49400a000ca4060754400380d1045000e0f83c020010450201c10703a49038460a04005a95101038600d020041049442c00c0e41d102525000001c4001e0380641d549042c3e03522501c0410181030703000c0388201c1a000d4505003ea01020060708030b00156545440140c11028820480d41004850360320f89082c20b404941140180300f2200110304c1d1880c101412107100740c0b007512342c031014540c001c2c2809030304103000302032005140c0c00040e8a001c5403402c200ca66020307803607464403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 956818426 1250 956817176 956817187
    0xa0b04211214091002090105090901172806182102010b090411010c030918020a030b0103050603072702130f0f0b0d181b06020d0e15070611 61
    0x640700140074100da124140c40e00703031202c2c50204002c1803103000b000244000c00501841403a41c201940c800e8440504104c0c0a00c03d4401070b032180705032139000c0d200e55018003d400140e8a8881d2510304403070302c181c041009648480d100d040c0100070b0400c0715500729002155175002c60580305039012408000170125100c079401c28580e241194250703080084143d000f0b00000d1461810045881d105903400b500102d20207454881640c007a100b1070b0011031090a001d000c0d00d6a81d1040409240c0032a2040301d40b640004030490000d606100300a682070090808101030b0034808003095403982c540c001d1a4040030b880040001d506450301182500d21820b0105540d54014061115030920b4a0b00c00d15034103603103550300442e0462041d03d0700401d99000044150400d91070000b000c0241c980804c03400c002c0102003042c2004134009102d920000001380320f044030280d181003802481c00d0002405003081042c5428880c0050f41d984c44880303188441140000d4480328681001001132840d06441100310300000340 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 956819676 1250 956818426 956818493
    0xc020d0c0503191101030902092a0c07030b10120f030e03030a051312170307030902060a0e03120405030a0b04110306010f06080a1a010c03020a120c02040501090207050a0b04 76
    0xb40c100f400d44244e140041131200400154203903030100f1002540414810f0004480714042c0306c418500c942c01311120a4001d0640400c034a256028614003256a0803100040c818080303658800343e081080d085841c0c40107803401700703241c00380514400c00801403185140c07042c040c5481408000121180202034075502d00c200304001d081984060b0200c01c043d02c251400040c58614100c8402c41940c10400544580c85200b002e01140d500041c034913810305507201c0c501c4000d41c8070302010300810307800794a40e540591040c1007050301e010001200792400483c1003000340044d4a0103d1900c130910b80c00a10512291505d252180c082000b60a80e160548035603400041d0405014000d07000302c2d005500e43c4410b51700c440548405440b990443d050038580e0420b1511015440b400c0310208031070007881901c0c440e10240d554550000b58001e1440001030b007850750501546401e210351801003851002c110314003105541c0f020307110740e03040c480034002e100460001820b21103104280c0c1141581009180080c0c1080003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 956820926 1250 956819676 956819713
    0xa03111f0e030f150708091204030b0a050a0603110111070905040803062103190e0405040303020d0c2102130905090304090b040903091518170d0507030c020d0c0503 72
    0x481e190300c644035207a2032803502080400c00d4400342482c2d084203403040d903856406440300000541408a9481042180c0001c0c060220140018522903c0341807058180603060138180c0e14003501c1002064a03008040000516030b81e42103902c03040030300b441c202905c3c40408441c01e2903103950000507031600b4003041104000034880114491a070440321002890b402c080800e410f41d40480030303110b26910401c1410270f0125841601480a80301d85400b5040c2e400c3c0c100418243c40b01500c0450100e500400c240e40103000318020309451001d0b61800c0e9691011444407030401304014241403410780d03800203885801d050000e40300006001c101e40c050010b403c003042016030300e60291244055281c50045410317064640380c00b4249640760190340c1c00b8001030134000443c0742d02e65498124000e10140780641e440e120524492040100781d82d100c41480a1070080c2201e0a0014405000c0c0801004004c0d44002079040b01c0280c0e5116015034518011318841e18107403009000917040310350305104481c2c020300e070503807104c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 956822176 1250 956820926 956820947
    0xf1503010e0c090a0624020d05030403050702060708161a180a0b07020c0604060f021006360c0e090c07080a1b06050f04020f0306190213120c080106140a03111f 70
    0x5174200c2340c110140c0c01c4101ca25000990b0300900140081282401501d040b4010309035030b07400751641c20318198442c4140300c03c81e664810201c407035601c0394640c2408589c0000100c0e5100000d1000d03140b50300d00302c0764081d44528560100400e0600340c1004180424420400e11907042000381c101a95107848040181016a40089280041c422007656800b604450301a0b03e0407a0052a100d80164182045c90400455411881350301c80d02c200031011008417942c040d0080488454882980e9400a01e0501141030001000854814010028100010080001c0310904141444d041e0343d41d14240d1201c4408035074880c4c010700410f041006100c19101c0710b0070245e01551080b10400d800407450424540c81c3d81c800c40d45440c40c0007050313425007480b12681d001800c2c4600200c04e4604455161403840e0f40000c6406415180380da11030400740b0078943d0912a50313028046440741c08400d0764620001500e407142a000c0180070301c1303210480e00296105e03075543c03e42c460303a07100c2c2c09003000210500003000200710 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 956823426 1250 956822176 956822249
    0x1005070b06010203091c050c22061707061808070e0a0b04060302060a0c0819030207021e1509010513170d0315030305130e0f1503010e0c090a06 63
    0x400e4082601c660000080310810340c0081c04146800e00d082009032841c2900308410359003400b8400c14009140d035000b00c101036201388444004070111030100500100d0302580c110f4498032404108003e5100710024008048422034a020701015a13500c00401660110368000921441000b1000c164540d0b852042441414501c0c000c0120031902c004100c280c0d0704911000e03400000030800c8400842c881e15a40032203900072510646011004a011003444148008400c0040d80c0410b9070402c41c9032290280c40241c1c4101001072480d24010001004003a0700c1901e01450840003805482d1a4000e10581d0306200103d4403481429903140c251620001020380e103001c01c3e00a00c000420700a000e4412a1150071110f841040010b040d59010b5a0b99405150b154180d50f21103000061410844041c02c0d114500d201c3c80d03008075003802035601e61045a210324082c030990610000c07050540b40019040e40108080302d4101c4075440b01c04102c2c008000070f40041c000d030b0042a11360b16040350507110942802d0413 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 956824676 1250 956823426 956823443
    0x32108060d0c0b0c011e050601020c0108160804032c1504230d08030406060f0b04051f0e04060b030414210f0d18052109041802100507 59
    0x1519800c21001ea48810002464100c69942c14040802e03110302030060002c88000004041182c52801d442c405c02d1740c90102e1a02d9220000c0100c0307940e05001002e1880f03020308081c0c00303904201c01d50605200760110403004001d40600064281485245640481c00901d00c10f102d8912048081c44034416012a009010b500030442da40c00740300c20f5a080b502100c0e8000d403070421080020743c20100c042618441c02390f01141011000d000b240c0f0800c000d40c0291300ca1540021107901d40381c4160b070000718960186002e44011320080020351900e500e170400140c603244c68600e1075003ca190694090845da045103170000d02d040004601e12100ca03000754019802504000944100b500240e980c13248a4120b0382518030228240c0800328070034002500341c8940031002d0f03900702400141217004880e0380340400300c034400ca681603050a08c8024030000101ca61401c180048012070307031a001e40d151003604429402556110700f02c0e80324080424460410340e40c02040040700103941c2100422540000c2c105803404207 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 956825926 1250 956824676 956824681
    0xf020f16110f03030405010c021206010b180102010b1e0a09050712050f0108120c250518043201020a03050601110a0f06020c100c1d01020610031b032108 67
    0x24110b9140319903418010002d42c41d00703082c440119150201050120303004202030b580c0c40012141071010b14040e0482d8000301c0e4440d60b0820300a012030580312881d81c15a40741815000c6e6544130424985080c04420751040312460421001c910b441180d68421010f49107440c0038002c0030759201d4502c0341c2c03020340030f0003e114a443e00e5a40f00c81c8004288200c9080d6801002114020303540c250103424521055410740d0310740081481310640c1e045280d400e400c0180e881c0fa80500c0a03103803915022002103024841700640d8500307640d5805604844d0a4080006002c0c0410340d200c0c110703980481152a403540c00255103d04501c50040c01410302522618003054504190b04080e1900141900340c20780c012a850401c5002c0e615000c00a501414060a86024540c849990410107005100c1c2c44a0b003503841c100ca88020342009200c41981700c2c0e4060440d082941882241c240b04850302042c7c1c2c0d000407219030700240b084100c151407612988020803590465811100c0045c0c00d40011a104655031140716656 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 956827176 1250 956825926 956825929
    0xb19090b011d0315070224070801170d030e0304050406080109030816021f0f0c0906030c0908060402102c030601091b03050a0b0a12060e060603030d0f020f1611 70
    0x40540c448540c050703102c0900b20b28884400d2a13000d80081150040d100280035070611b2103005001065200a84800074051100956125140d02d004100030840f0994803200d0038140c2d80c5841c141c1d2040804c05884082101e0030f4002482140d0003400028020840345a4030929240a400c80020540111300d4045c0001c40203206079400072500c4d4090b601400f00301390701d5410048001010f03c01c1d0903116550300f68051070b075032103489122007401c400e8803800c100d14a000030090980d40101009400c12070b240c1000c100c5140002900c50300545d045844500002d16a442114241e0300c07410b10810071001c001d8001e1182c00c04003521014001d003134007501c400f81c0c5c80d440303802c003076070384040030701e580c0340303141908441654481c1e4080ba0300580625004200410a05c000070b8002e0302c241c1000040c2c8245c10030000070460248a10210400070f00064415458000c000a4880c010700e08510065034a4825032920020203604032004007090010064403071445015503400030040c00f00c02c4800d0101d03803404074180d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 956828426 1250 956827176 956827217
    0x6060e04050a02121906031a3c0a150b1b0c011d03010b09070e0405011406030403050a110303040c080d030626070b030408092803060b19090b01 63
    0x40a8100e6000d204c0d850f030713400500084041c400c04040079a80c0d10342c0031000031602548140440c880d0810070700503040104421403c5030032180034811150041c000d0b903103003407260580e0040d01403031803040c0f0400d81d0b0b8034090700011304611125a2403c0214081c04211110700c44040d000310091103010846580e010b1440f0381e51146d10b40c0b40d003800300c1c0c5080101c0e90001c0c124036441d0441e4502500102d500d4109002040702540161400c2c0c02082e15290350000c10b0515100b1503005100300d214400110a0120200380d0612010300040c00704100040c078004200d0040380f41024079010901200e580b443c081c10a8441039285000380c100700e001c1d1600701038010744a40115419074560003480100300442410040d00c0300344019010780c52740210b1500060707643e20320024512076030048802c0c5a94140700c80400242c0480d40c41e0646804041d861052174000000350582d007942d61040c40058040c100c8400645142d500c46c5a00d4802100ca5002284e0f40a0f5508181d011020a803030300441c00150130400000b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 956829676 1250 956828426 956828437
    0x622080d1106010b161a04050105150607081603020a240f0e0709020d200d140103032a051006080c03010c050d0c09050a030803090c0904151505030106060e04050a02 72
    0x1d0180300f4051042c0356140c40d5000c45c0007903c51100603282d02450072281c40052000c403030940c0e540e5902c07004c0001c20186403140e0400550100c0340307280b85c00040d0fa10440c071401518425200e01818929139001c045c0208418040c143d0410001305501000e40d20f5220154030303807041d2000c0c0034104002410603110a015140c2005032030b1020300031460400405000a400032410700443d02e4503070352111514000d0010303203a146000c1901c00e99507090300180c8141510b005000c10781d202c00707040c40100302080c1d20001c00c0c44003488100700d1101c00c540700d154500512480300e4010f03142d130041000b06072034032940b07034085401c40341004269811030000740205400c07229850044400f04108000500010b520f03603002da521805d640c207040341c038640c4460108040c006d250300200d91903070b000014006894000c21007a055120f040f030b0501100d250680e6001410184240482100707a1500005000104207500300030103810068000c00942e555414010029404106c485008603e030201140042c1c2d81802240c8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 956830926 1250 956829676 956829689
    0x3030714010f050f0402150f13030c050d023303090a0b090d02030f0f040e04050313050609130c0c06020a031a2709190b0f1e01050622080d110601 64
    0x100301d50b0b150b03000d002c1154250b0541f040848000c0020012400a41019203070b5190300400e50b40d00d40b8150b1074603445469203a04158850700e0080b20790340040c0c0e2110402c8800e07a000d0300c2c0100c150701c0a0803100840c14640402881d45c914044108154000300040400c2c030140518928041501c88407202d544442d00805e80343d005030010805003c15507003003802403001030890303c0b040d8502036844000110040301500d00305d8443c3c1000404002c800c0514030840090320f0308aa03001d19000344000060f99aa9810030312021032601c6e28040c8035140d0007504600c4c00380703400c1070040d9500d28407400001c0090065901900e0b41031100842110542440c4510015404001c2008003400c02483c01508210b13000901755440c0d0b100f80c00c1201020000c03100c081d5141442004400b9072804c0090b030604130030a000300a102d41d0704c1c500603512050072204002504445060360341d282c2d682607041280e19075052040d0b1380355004200c03500005400340c0004142001e0a036039039030300b41803a0030005400d4a80400307100300c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 956832176 1250 956830926 956830951
    0x2b0603030801060f050702090103050c03120c0316021903061b050708030402091012050706120b010f03180611282c03060403020c1e012c03030714010f05 67
    0x18000e10703006240300d13070f00000c40b418081e0901034250700042c01460240c0007120b40e604669043c0750103040412101d48100c0102e444981840c5040e80301c00da681c05180c5207600074540d095003490035920f44008a20540e603d0000e0440940e4a90801501425428001e01180e0310f00b14a8070303060610460643c1c98040d445100d4034515195034081050301d06c00501000e031a0103504800040c0da461101f2002c0d41c0798842d0340640403041c40c108001e0a100c2c104442d8a40c283d0820300b407152580c1e8419104500740c4003600f40044c00000d149000880b4039038440c00100010b02c2c00342d1082d04000200c0c06000c6040710901140d00055803516070030491802d0b0051013000c502d444500c0400c039181034040a909a000007100b13a01400008002480d1810560b03040d0050313004440c1a8032a4148400c3c0007010000200400e50b00454000000f0154580407502e087d002c48030540c480b80d214110760042008410080c200d03a00e4800d103044c00b002d800c40c88840c1040c907620307240240c4400512030082c648904812142c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 956833426 1250 956832176 956832179
    0x3061a0f0d111303050a0c14010203120901020408030d06051203070b0c1c091b06111b0a05060403081809060904020103090302010f05182b050706020d022b0603030801 73
    0x2002521500344110001d80741802101403c201c0e8007040c4000358040c2c4018000c80c076903410055400c4e50503400c8400000140f0403650942c0e40c000040310804602001001c5040d0ba4010003203009004542014640380400180910300b11401c0c1c122a081e00d1044581c500f0385031500b00919528400c100c00104522860b000042d5084071758406003c03403d02e25240600340c103141568542c211000000c4c111031280003581e40020308400e40001d07601420807800d010958208428125661b100036044000c03a150001e07503a0401602c8503100c100c014600500310b603844035201d140414240d00300080541fa07401040000d1030040c075182501500403000a050769201e900d5540044020707006091042e4150f640f05c0c40580c2600f1820321410b8401c00550034000c103420000142941007000d40c1213108400022806005200104048006036082803414016a01d2011b49440303c0a8080d940b0f04804062000c622b030011a406442030710188800e0045580c1c10300000d0f0403181c11113009000140c00a0b080500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 956834532 1106 956833426 956833447
    0x20418050607020106141c02090c0408100204050a0612090b1008100515010305060111060408030f0606310503010203092b08040f0201030e060703061a0f 67
    0x2401428078002e102080e06c580c4850052043c00c43c0d050b610068031500c44440c2c06198090020b501904c3c00e840030300c28580003840307401114060300c02e5a000c840f4840c03003281e00b80c2e00018107070044c0701d040250444507010b242105051803582c0700c0c0c4000204040396103280c07294450070745070031040e030a09a2103800e0507541311800350118104002d100901001d0403940003200000e180001d80c1c4d580b81c100485d000011808803039451b018200a01080c0140803008511420740d0b001d28180540b580c80500009110b10001c000b50388801c0c030601d90204201c0c41c00d0707034965204556049002912600041c0c00c980c01a20b0000312603120710310304044058100842c030341140c0c00c1c12080c2034002d5411700181445400074801445c0407101007440c01113a000c0c0e0b220600d080400d2040f111540b80440d0003030002c09030b80c000d40c003072840c03e100042c07205043d207800c1312101881859000c2c2000361904 = true := by decide +kernel

theorem cover : BRFrame.Cov 956654676 956834532 := by
  have h0 := BRFrame.cov_init 956654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 956654676 ≤ n) (h2 : n < 956834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
