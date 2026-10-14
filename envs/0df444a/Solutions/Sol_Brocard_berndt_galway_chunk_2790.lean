-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2790
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:45:07.168007+00:00
-- url     : https://prove2.me/submissions/b1ec9435-127e-48b6-bcc0-13847cd26aa0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 501618705 ≤ n < 501798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 501619955 1250 501618705 501618737
    0x30d080705090a0303080115020303090604030503040204090818011e021b04020405040507020f01060905150d05070503060c0c0712170318060403112b030c03060308040e04120e06030601 81
    0x40b2480420003c222140043e100d18015201100a0203a50200e9a001c480300c08124000000c0f00c0c0540c02c40c50003010306554680d000c545035400204100d030007a8880700c00400049800c009000c120b0100142403201541c001c00040400003c0c814500140c100c031050940f45580101e4020140000220403406010b034003c04103010744a243d0100e43c00601d46010058950760200b80d450b0804400802030105a903141c5580042e60340c01c0e2108908481c1130125481707145450784918404a1043e0140e5140c2c559650001e070038240110b0381d070300344c03d0000582c1110011090000b10007410910009101010054554030f11142c000320384034808040020201d10180702c001a060311030103000341290f0040ca0300345802042c60346c5251030748207244a44002c01519108084502c0b0301e1240c4440030300241050061b044014144282030340c0c00345a0b0300c1401002044006000300041d24180c1d05900460800749841054182c51107031850400c141c80180803643d640b80d80c103c0f034102c00e0910b403540c500031990031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 501621205 1250 501619955 501619957
    0x60e060a0504030909090614090a2604050603130506090303101d06041104030f030c0605012106020306040e1e0d02160605031009021c0c110a0215130e16090302030d080705 75
    0x11035a03801381108c00400100f008006440b03110f00d4482d5240e1103154544181e03480c01541901c04c4440c40f00e034144018011420320030040c1d50f12800410000e00004201c1d2105424040b05840e60308054200200304844901c40429082c0100440c503c05025031540c0781c51603d1400024104074460b41c0c8031700e001140111403400759800307590030580c03100c200c0d0010f1601601e4202c0059080725074508100c000207105142c1e20040400049502242000c042e1650f1107000940c030082401d54000d6440c0c20041c4030520411000b6625029001c541d03440e0034049520b00d141c4081160540c003158409400c81050680c1d000010007140c070030b030400d6900c0f6121490a55401c1d05241c201c04501ea00c045074881168240d00f2101d00130301d40600c0108043d0743c0700c1e40c04440c040c003640c07299505548044cc0c00d40060a0107803001c5180e07038001ca000341c2001402e020f800d0302c0e007200790302c01d82c03002c0010b0081c0400305080c043c21002850b804e08001300c2513899a80442d4980c82c0c540b4945003400302c07000c00101028003401c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 501622455 1250 501621205 501621221
    0x12030c3209011e0305190b090a0b120703031101061502100509030f0a03150608070c080706020d0212010303090e010303090303110a02100f0e06070804260a060e060a05040309090906 79
    0x424000c0e40511400044c000c1c0070855041d0a51601c0042c840c5505820703100d11080500085e25800303141c1d4a641d80030b00a40801d816040d04000b00700e5980008031402e100c80406035100340e44400300b98100200103402d4442c542c01c88a1000354103152015601d400003000f0605030b54000b808507103595000e00d82400d41c01210b01c402c3c06244001407034100298154400d1081002400001304125102d07a01140d0400c800c41d400d1020900b40701400002c01ea031000039096281c0710f03820140c80c241c00004032000f6a00314001c2c440d80c04503c58010710400d500200440090849000c80183d81d40c0b550b200100f0480e1244405410302c0700c0f5200c00c0340e440ca024000750310815006020610f4038003084800030700184900c164200014134090401910b0324003c0700301ca484030b801001c81e600701030038450b03845074141c85c100800c1105425940b0302d0840302001e000b5034075514094200016a0691140d6490034810020403101e0003920b40410800040d40000030401034480381040002c2038000d134a00180106600 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 501623705 1250 501622455 501622487
    0x1e04080415050a1112161e0b011d0f070509010c050703080d0c0306080d030b180a05010914071706220204080c01051606020a0c12030c320901 62
    0xc1052907100d15008001840440305903507813192615840c40c2400e85654908080090b03c000401c0355104405044184058480c0103d5800480f40360300030030741a80c0c8906400468005000c000100144010040d000c048400d0100b5510070b10300c1c28800c91704180c0740080c44030381400310108650495901c03450000c0307003240d4010121000756451b420840a035800c0343d45030094040c08d06c3c01007915a0322034001d0300c040b03c1d8290000c00200740d140b50150043c26030314443d01c2d0050025400110111603500d4014000c10107000000f8032541030625890035620b00043c10404550f081080c0444168008050052074400c2620041c45894050014503002d000456039511881c0c150f40100320b6444503801030046030940011182100407480040d80c8134080e00c20507000340e60310b181408010510729001009204418604208980c496079103a000000c16000c0a10000380d4500e01c040e182c94002e42001c8038440d11403103243d1480c0720013404c1c040d13803450300545801075240880c1824180c3d018200b0900f8065031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 501624955 1250 501623705 501623729
    0x70b130b0f0903060a141b0d02033d06170402040e012405031b060406030b060409020409150501030b0a05040b0409020402030108150708040b0705181002010b1201051e040804 76
    0x805031710040e24441c0019445002c540000c203506240112081c4105250003518500345500601a1402900001c1041c052a41000c20030150f0421003000810122407951820385a103034400c0b204600303c0095003102c8180180e04568510f000091101150b006078100d4004c01e81d1044803010501401074206043e02d420344100d03400040c0f0400031700000c140c1d007040e01214091080c020581c01c0d11210000078039002a41003006100c0300d403080c0c00c506c89840d4003a08540c078040e603c1610400b268095400010490703900c058900340c00341c01d110044001c05007441d09010012221000548010080c425a44900d6842407011804d84580c2c20403803400703400070021516503948803107240c0c40b10141111805520a0800043c003164040c0d03810070f00660f041040c90800c0e60302c080050700d00d07501640c03060540e2034070f590f080c141582d034816104a0110b85a170001c5400c0740b00400b0710a041e6189c0c00042c07041d0b410315007048010603048003441e45014003180070701e035641c44504202d1854895508100e41c8061 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 501626205 1250 501624955 501624961
    0x141204120203101404150b060d05011508090c0d050a06020d05010e0916090902030f0d030c031116060902060c0709050105090c1305100302040b160203070b130b0f090306 74
    0x804120003540160003036094909034145a10b1460031165440e0760f0341002030b6940049404500c00e156001e00c1c01d204041c001600074120000945690803508582808a850f00c0052021091001c02089288640d080a0505045c87d01c0407580758201c0b03002d020b01800c0203403120014404100185220182c200d50704560b00d4181381520800341c80240034504000100300c000c125400c000180c0700c0030365441e20585055171400c0c000f664000c0c00d040341c0140d07454807580d007024001c480103001c108041c1030691000224003416400c064141c40c007829000324040c40501c01705076442c1446a40c166404c1c1e01c1040000d1054075440010040c4c040c0800031600d52190000102c0c0a404a07440329040e01c1f41100c00746032039038401c1003100c19481603da00442c04413545604000d03608048080080d009007a050150030552950070000203070f0011800055500e804090020a5007014000d5030081c3c4040d0f000c451800d0880d80c4246001c008900c1506851480000c00061039007900081d9a043c1c0c0004084d03d10b241 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 501627455 1250 501626205 501626219
    0x618071a090a2c1902160215070803011202010e060307020f010606050c031903090507030507031109040807110310090606170604050316020109090e030d06050306090c090a2c06070e0a03141204 84
    0x1040d0281c22405200309445103410b0f402c1d40d1080d681c1003030b80300602910358dc0c20011030407407103032a10004905100d1031990f503014a50b1060003440c4180d41541c000c20308140c00b1130743c9900b0340d58554018018000704110b800e01500c40402100d03401f1504102c1800c0103038403200c0c110028884408042d00c140101c200200c1000400300e80340d01203d00980269041ca44518100821b00c24180c43c0101080230400c240e41c0040c5202c03d803c5400328000b01518050344010b014032050300d0000008a0f04c965503040d00740840c014070141c4d1782c0882c240310004c10f0285050b50321a0f070b482c4a50942c001c0d8802e60f8403140001c5a2041c070b03464001d851070b10342c140704d0f08042003010f595a0308410200c2d4002428500042500e084c00211a0302c81c9103070344000d14080202809001420101800d1403088685a103840d00ca40301c0711501501c80300d140810102c16044c004401c590404002030908401c02002e401150026512856507000344c0360403448104924810201035803030505156007540031903001107000a818 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 501628705 1250 501627455 501627487
    0xf03070e0a0f1505041e0e030915090604030f051c0e0906010c02010806040c120c0905120c030d080903070b092d0618071a090a2c1902 59
    0x345007002020b000b0107081608040580d80440014256000c025004000c280740903001110314456072040751043c400002000c0c3c096441d440c0050600390b10014100100c0c2c2001040c4e035410440c419101400e0000c10350028005128070b00c4007078181c4204450003400e01205001d1005006001c800841c0c500e0045000078088001d254201e5208403c4d040000305194011f808008490754142d50317410305a40c90301c08100080890810803801c109503121644180442445150120307851034485410591403e01009041c1105072404c24041c0c0140800e4600c540380090341074204540742c14986025070b01c2e584540d186008011015201107480400d03c0090440890740300720010302c0a90f81d02d400070010750b103400705180340d0206a0491340220005a003080481440f20010060030050352926680c0354150180c0450a21544011080015a001540c03400d103515034020812034034442d406000b4900b100d40a490700742450380ca1183c4001c00184000943c082c4800401d1496108545940c0344081004070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 501629955 1250 501628705 501628711
    0x80a020a03020f1f021b011e0f0203070204150302030c15030f180a0303050702060903070c0b0a03021606060e161e090807060c0204051807060f030b041d01060b18010309020f03070e 79
    0x101809286c07004036952090050000d00501c69100b43c5801015907402c0340c6810141c43c00d182140014411440140c1d1a80100405000c107400114007060070b600406042400c0015814400c560011124048000b5282902e9010801c0c020110a5984511102000b03c2c00c11907081010b00840040d1003c050b0150310280c02603e07a81c2c2100c11503030310856007a0780c074800d10390f000d0105c04036003004010400c01d41d0000c1c2401030692801509146038a00b030901c54440000044884580790017050004c01609520036500c610a070340416035545850001405c0c00ca811002c0b0008104101c1001c99450f0140c1c1d0400004e00c0704070119444542d41d2000146814180e0504074812400c4c1001700326007003561011407940301107840242904515044040d910a60300c000420b06064440c1c500400704d1340c5920940480d500520903d511808040500a08684868000141003c018060303006400411502e41000640a00b03000940301d11900014800c1c4103100b048035410b10505d6004551401c2200d080c1d40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 501631205 1250 501629955 501629983
    0xa09030614100b090a030b060d050601030b1609050105040506030a090b0106051e12063606040f1e0e0111030408070209071b12050c01110a09080a020a03020f1f02 71
    0x2500689900305403e051181340c0281d03603c414070040c28800308180c20131640c0c02c418020040707140d5010980d5041e0a01c18240e100395880c0d12507400300801461075441402030140523107496034030740742800d001912900550181c907000745004000141c0c010703055805000c00e03a4000311f00302143c2d07950b000010200da03c201c103d01420b42c000701c050300a200903c002c0c2d843ea403c100d04008040d58502c0d00f4842c3c900001f402d000144804400e2055851782c42e0300c0c00c40704404007184040124501482844285c6400f040000c40d0140381c04170300780c1c0c05000c8124030b0f0259007103418003017280200102281e001d003140e03d47c008850303c40042404200841c1c40c00801165109541081095480e60300a4410f01516503869007040d424203056000543c04450300c00c0c1007002d60501e14185050081001c0c04c40300f840420f2030020354001020102c10b40c0000e00f60004040403002080141030300c4d4042010041113100c020b019240c0ca144140d0142e841500c2550701068003000b524036201d015800039034034640c03009641 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 501632455 1250 501631205 501631231
    0x516060f15150e09040f06021c09061506020d02070501080705090a08030301030b0c0c0718060e0f01090f0228020f0d080103021309050318210616110a080a09030614 72
    0x104034140300c030904c0c2c8616000502d0751800c01d00c07611018081c1d07000501d107998240f01c1003000200c2905030321882d40041d00407440040c002e80f0310b20b070704481954103400020556119914401286e540040c50714151802031030451042d441d4400e0030f50f418024141d010360302c5400340c840880c1c1600008040e45c100e07070049800d12082e4a0310708500b40b65100e50408903e03241c00c00700701400f4501044040395001e40307610300e0014006641d0f054024141310140c1e08c2c042d105200100420003100b0300d0143c0140040c4550003145009400f80c10041c0320f16007180304251000580541c0030420307001b441041680344809040e58140c40d58101d00400c0b0742001d02080b40300c1c4052a8207854651182e00c84d020410358030500440c43e01c00c1d81800c0c01e218030300d0301000c181c0c48603c507860b04440a0340d03101c01c2201700e11900c004080c6414802d11802d0303024084840340c02001a4a0710354014102d001680303800e030300d400000207669183c00c0030080320101500d8001030040c60408403002d0454a1180110b40b05550495290b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 501633705 1250 501632455 501632477
    0x603051006090b071e060c030c030e03131715270c0904080304020a05060a020a030801090e0706050a020c060315011b20040225020306070516060f1515 66
    0x740c50003030b10b90103242d000c14001d00c003000c00184a1a50350b403c88a014443c2211070525540d0741341034070305201d1207030006501c0d035042449050709800b5090070303c10644003850801e058040d0810740301030544a110701103000d10000c0322903401e082c444507500b5400b5042c0c0c5c01492074000c0340034808041c880702509075840303c0010780c907940602040c1b08015040c002c042c03c00307035100e6807035009150300090300030303607001c2001040020705c0c3e511940100304081c026006400c01380c0c00c0d82070182c1001c074140d11001c81d807070425081f0340403014003080c40001e948131070400b80d44a4002d07805c100c4c83c00b412100a150090f10000038030182b0340c03d5004210b80715009980e00c900360046005074402ea141c1d615402012100000701a02000d040c6682440311018090001070502d9100c0c951440455504905620b914140450290030f509040c00100d40c044424200245805a09005180c3c8400141c1e4007070155969441c159006a12940194001c0c0203c0480502055290300110b80103002c40610300e80407511942c02 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 501634955 1250 501633705 501633707
    0x30b0a02120105010e040e06090123010b07020603040f120507060e010b03070b0a14070605061f1407030c0b04051b120c04050402010306120c090b01031a1e06040603051006 75
    0x2240c01c0400c0003942038250340d29140040d600ca85031140c410754019102c91000c140c0403c100500381c4140e02d4a000070400c8078192107211801d1189a18807240291100e006001c8a425041210442075040d11400e07035030303070303460800061483d8085002070005075104111703001140e0260242070202e02580d01003280f5101e180307006080340c12510701da581603080b101e0200546030410000e040441c84d0781c24029501d0310007000203000341d403000310b08035a11070740d41e42405541c5c201001422050b444400110109a2805038040c2902a41c0766015007146400220807007098070a103150103542d40d007c1c401c41a14103062410035100c2e02d02c2d041c0c0c1d86101c9000200e0b8101d0780380c031440d000b844001c0100038010411185081c00040c12005105078140741e00c65900181c40180e4401e142441030142c05030315401420314403000259503d1440040c1094107140c03884208048a01001803611011140442d440503440804c1141803020f41e03251b6404a0041400540141c040d04480e2141d204102484000768803004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 501636205 1250 501634955 501634957
    0x30909070e0d1103010f11031f0b03010e100b0a020a02010e0a120b1510200703080d1505060307050d0506030d052b0624110d120b100207030b0a02 64
    0x40182d40710621003620700114011542204039008060004070340040c1d19044c0b24160361407038038030380211b513000000c1044408902007041c0900e50700389451400a8601103903000303680418060440034000f420003040740c0b9000c4042c1000200f403d0500c043c2c69000c248030194075a01a43c41c2640441c107000a16070f82e510f803d01c00c41055440c0c0420b020042e400381d403941c02485034010206502c0c04044030328000a070341c3d42154003220344070556030700326080400c00139401072240000b4400c0c0e503680440ca0038000140e0b51815242c9500b0002c60000301c6280c00ca1680d110b851144e40080c1d0031034000024004070390351100007403022a0700072900b4443c80e15901d09040c1d559500b100094001001070240b640072018610310541242c0300040c4000b0000040c006160454100341d03c0f03500c800ba0146441c1e551010310792204813440319641440400120f4242d5110740310f1802d040c10b0002c01030710001d0070540c00c01540c042e8000d0031014040104048407c3d101035551a62800240c070761041072000640746c01d440380 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 501637455 1250 501636205 501636227
    0x9140601030215090301150e07020d05190f030902101e08130605180708011508030a1e17180118031b03110607081801022b0204051203090907 62
    0x2411811140070076a0f090401500030f010310030782c55500c0d164507400011618a40030080c00f1180c40785015800c00c0714001e0704e440440c0b4a801c003806400c0c02442844942e088000c846800c06017807003411070059900c114010400c6000080d07020030403410650b0016842044018501107070b083c0030007801e03140c001c140c0b000f0104456040030310820410040000300182c03c00340d04180c81c030700000c3c40c10042035602802c04601b40c0000c0301c2a9983c00c6013074005400c080640d0002c081c800003941c64141d803060001c10860050070020250544c2d2110722807203a00c20a414042010035182c00d10190410b4151a04401d18000311380040b03600b02401c0c0000d10880c8014003082c144d26440c0c00002000d10240c17200002d0b400320050b02800210341d840902940141701d418030030166983c89003918501010712402410a01d140c0511980c818040e1805541200b44441800105da041c0c0324121420340c2c2c3d60001070303c20340d001550070200000c2c032008010b00c0007025041e07041040702c01ea01c5e5541d40c000d01702c6000c5040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 501638705 1250 501637455 501637459
    0x30c030c0d020301020c0303092515300204080d0e01051204051903020307060507080603100b040605041b1731020a120302061602030a110c0301050a091406010302 71
    0x5400c100140d00d03080d0101c07001e640c4094000b506140c1400151800d40e00101c0d0440d50036007000240d1040701452100740e041c411012080401154100845451346685520551040c40350841220402da80620203154116404c0003150810050001001d4043d421a01c55070402d4422000f9040131580101801a400c039010303502c1a0070090086c041c10a030050280c02034401740182800258101460000005100d009400856407030440c2c0c5003500848000914580402c020502030101580c0c0225400401030844c0b038001c01c03d110142e00040040840c2e500141e8868075294141c0c40043d916444003000141e0b42c1c0b92134181882c110b8080c0340c070003001c5400f0030480c03480d010080130400320030803640d2110040d00169400d601d5158007180380300001d034018511700f0000a12207810154100007456011118040d02c0d100c035940d0142c0a5a03e002d040d540c2030501c02d5500d02c100c0445010800a465003034014003d005608046424030020710101c401a20b0914500c281c0342c02c01d05000800504803580 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 501639955 1250 501638705 501638713
    0x150117010510050d02041d0405060906064519050105010509010f03020d061403012a0e0d050d0905040c0219030302030c0909010f060e3a050118030905030c03 69
    0x2c9150100c0d03003540441008070304a5800e00c00420801502c0f001051208196001440d66051500b00145000c0d00140090680d5211101f0000d5131380310600c1c0550200c1d0001145542c0805200141d20f01000844044274044006164505100d4880e21072500a003050f09002c581c00c0324654292090726002d0051b5400b0403002c100c040390700c0d441005a0105026036141c0103060501041021050707402a5201d10100340940381041c20504e000e01c2800c54101411000070020860640c031042e6030140b20302d01c40144001d9103207982d002e40b15141c104d83c04a6000040d03840303044030148080c0c140003007401039034050b500e00b00088820900004044c070784400201201031204415a40031006548020429a03101a041c45100d400341c855070305030350107089a05910061941403920040c444143d42c99040c0c498508511440700c44810f41401024040c8448104d0811402c662403502d0080444500103110358030f40b000c200343c20310840d031400c58000c2c46980e07004550387e07584080550706d182010b00550301d904 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 501641205 1250 501639955 501639979
    0x30a0b04080f09040207110103180c0b130302180901050601050a2102190302070515010f06030902010c0b0916050907050a080901090506091b040c09030b04020301090b1501170105 78
    0x151401c00362100700b42c40039669181040e000d000c10182d82045608803142d030000c4000804e5503805006802030b80394403854500b0225240d440d98079400450384a844021031000130801e1041042c81465009503401402104140300c000002141c60340003200c4a9001d5440c04010485640c4100c04460524465680d0410b99551103d21003032100c92180780301030301300e41c2000100c41491480d40c2d202e1b03400c0b0594400603102c01ca241045401c00440c00340f0000010b00c20401440501c100c29154807d0315001d00d0000703204a520b03c01a03c5542c1c4521001d044d604850042003081ea81c00104d000103059411140054182d0f00c0c014400c00304000c3e0351010114600740702401e0220300c01c60015a008007100b001190350503c5031122810000300f41d0b0107108540001018595410704116400b404880545003004402442100100504800e000051004002601107007d40d036094020708800c94200c01940c100d8180381030004009041c28844c203010452403020100f10000003040d042c12540c02805038480c0f44c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 501642455 1250 501641205 501641213
    0xc0c060901081603091401090323043803012607120312020c06070216051806040b0301060e06040b2b021302030a0b040f2c010f020c0d0806030a0b04 65
    0x3d0010b070b0001016655201d8101042c200121000c10905a400003d000300300b508000b0b01c414401039800c4840515207001104c1490072200b10743c200d0b08580038400500100c6845401c14200c4602c1c804985104106a00d0ba448204001903040360420a031019000c4a5891014a540c03104105925580c000c0307001084411134182483e04d41c240f19107000d0840b210b40320740c4035040f41c111100d91151030703000004004485030100400c1100200200c0c91440003441d00000541490f844500d80e03448000342070100c3c000e5103d40d000020344141c010024001e40e81c990382d9006640004072056841942080074100310b0f03040c4261600100f12844030f803c2d88140c15252810709600c0b014004a030040c10445155034460700030301c05103020b110b08000102d20303141100208415500701c00700e1845150320748071810800d08400b404e481c1c4800d8500860b20048406124010300401c101c07607481101f02c1c00054031916070440459514501c0010341c44020954603400d05250740c94040850040100300c08401140101e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 501643705 1250 501642455 501642481
    0x5010804200406090f05010501090807081b040b0d0b092a0d02011106010801053c06150a030914010903080a02030432061b070314130b0c0c06090108 65
    0x80c0c0c0002d80089031165541480c5001c40303d40b00a103421156561300140465a8400d40d40720080084500030032000381000600c903203e903183c489400848042c4104680d075515550040400c5c0d034001004141c00f040c49080035120400110b41c0d07041356002d00316102c02000c14580002d8041191229090703203e40180080c8140c800c0141c005a0602c2218000c1e8040d68500300907a0340601040070000c1582c0c241084205804d40e500000c590703402d28915900d18804144080e41c003171034404084900401c2c5c49250210307220540c40e90030b082944a0004400c5030040d00740c0c00c20b100c814422081d802c004006100c41500700e484000740100054510804038a0448580d00a541c005004914012081c1c010100e90700380c01d80340b5004004002d80301494881001002d00c0301591084091710340c4441d21404200c411028172070180000e0a1003140c2c20840c000800b5071b825207a440142e02c111a400d99110340d44090113401c085481910380c800c06026101c0d50030b029007030b20400c0341e041e1078210403034460081c10700203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 501644955 1250 501643705 501643763
    0x20a030e0610051c0b04080705121207081314010b013c03020408031308060a36050316020a1a070b0411030706210b060a080417030a0f0605010804 64
    0x4c40c0300000c034188089188005280c1c012441100d445035943e84e00e10b800e60611901c20060001507005000c590390840c4091a680d07130080c114504480a5a90108060145907a03044040e0072400e0b0b900607038154410541c000034043c5030980701d10301d055148807150900300030400034902400c403c1e200d0600c10041d4030000300790784041605000d030519403500721407841e6800006403100c10020b0f4100030401c81105100c110340040280308240300c0d000480c100f4203020440300d0210582c01034650102c43e8810b603190f0444003101d9100054a503031310052552000d80b03250300139080c0e10030b449480d40040d501c0c241e0800d800d644100c4002450901106444441400d1030040c01030315801400702c40c1507004d80d000d002200c05001780340c0301d0048007035104081d00c041c96490140221014a05407050031583e0b188400c2d54400c0840b440d249030517945510b088140700c0e0b61240c3ca455802e20101c144211800d26400000e02c0b2011000c3c20888d142c0d4410046070110310070350300039084520352040c50380800d80e00011092 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 501646205 1250 501644955 501644989
    0x18020d080f0f0a080a1a09040b0a02070f0b16080f070804290103110d020303040b0a090509070e03060a060b16141009050c03010209011e21020a030e061005 68
    0x400c00b03401e03205156055000c1084000028488420070044005a00ca60f040980c0b660f039601e448401c0180c086501d0003006840034000420740c60000300e0b5009560100c50805500102e5900b00c1241c1e4504410b40400070307100306622b0005035807a880c00c0c41c0300ba043e140c814450040040201c0e10760001c26164000e004e8030070754000390100c4035100c40c0c00c07000109100300e24000c000d441d0a5890740c03e200e0302d8141742980d072a10864800310803a01503500081620240c2e010007400030743c1e0302c412a50540e204d040f9a40015000740070070b4100400c880c0c004c000001400d80c2a0140ca44a5480d400c0420444405020f103100d200b02c02c0c031000000c400c6c1402c1d1517500d584940d0b82c002d50703d1011080039240c405060807480034a40c9a201c070340f00f01300050200c4254903505800035402c100d040000030f043e0840d50060f030401e114552902c0b007111361240640c042200e0b40c41300e20101021000d085440030354402110800842c1c00c00b401050207400002d0500e03c100d041a0350301340e05904103c10092074458200b0001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 501647455 1250 501646205 501646207
    0x50319120c080c060f07021c080a090501060303090e06040504030c12091e210f03080a0209100c03021c050409020a020309040c020c01090e010f09020306120109030801060318020d080f 80
    0x400010440001042d4401100009000601d407805c91070241140080c0307400215000301c0072404a07403110940e00494840207051815040d074646410800034043c1500244c125030130301400000f8981c0140d0b10340182c43c4142c007007880b2984c402c4188001c0d41c0e0103440060000fa064160600400c801034051032850703000c0d241c613004c015500c0c0c49a682c0200c914884000b0210168020070030703001c21185000314000c050764841d6103a042a03c9004000c01d1001015041c020700c0000a040b0f4411a811601076a8000380081300c15032100c10001c0201111100c100c001d441466040105441c2110641c204001c0c190744036407800b42020b16070342c0a9045080314000f980f0090100d03c2c02980d41d401950544039071035000300428003045000401148040e8080454100b0290052002c181e0b5544240103640d61030b01c01590307a8491002080e40c50034511808a0b1651818503c4800c01d5070041050381290816a000d00030310f2040340c1000c650896640000703601c0b403c504501e50008521202071b101c1080092050b0b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 501648705 1250 501647455 501647477
    0xe0118090f06050711120f0714030c0618060f04110609090c0d050c0301060206061c060c1205060a080c120705060712180b090103051906090e0705031912 67
    0x1030301400c56500703401c50b2001c1c1c4440030020300381d0380442d4100b521020f0030000c2000c500030101e8103607240304100070b1030740404001518905111610b0180b03441c10b910301003102c0d642d03d98078202c0f50329228103594583d0358582510254a00d2a40000d10600921a03614548241d072190741d502324100100c501c006400407801d00103810a5510707160703410311401500b440155191030b00000241100d10080109013180001d00042c000f140d40003c0c180d600401c1a21102070f02c03c404141010380310040e403001001d90781042108030b682e9a1041c0340302c0c2d44511080302401316031642001c00030920081d004500d40c507889140161198541107480003c0380c6898001d492148e41c03034001082903940301090035542401207072611962594081b0512804001100610f0a29801c01c0745482c864031500d02c170b0302c1c100b6807079002054003021401c0001310403110101e81080034581d11108040134115409401d41c00d07014988e0001824100407c400c9400442081d148039111140e13680c0d048140021032030380b030820034442d0741 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 501649955 1250 501648705 501648713
    0xa080a1a030f0f060c2502130f0e010614100806131d160e04030c050c09010611070911040e1306020a0302041e1505340203070f0e011809 60
    0x218104051020701518140d43e50007906403610380d0282c4154260541008036000d035088842c0143c403d05c21201c2042c5060381c0900014054a004241e56101240b52400e00f48400340c0d82da000b05002d4411078000d01a050f5504070394036440e19894003c83d0842406010102030501c1203400d141e0042c00100302c1d44124041c94900e0044822154450301722071580111120f8001c0f0030014101c401440600860060f4104948890341340300251000f400e200380c0410610400c44c05204105000c1406001301101e036a559000414900320008409402c0c041c23180c0105000c2e009010360740c60600108611072500e8940703102c90061000050240707212902400c160400114180020305890106a030056282ca041201c41d0b10300d100301000070105126068000c0000d42d44c0502c04079441d819900b045505c4801009803e02d5404148040710309001d1000d03640782c401080811044141030080d422a035802f61210324201c850041e40c01140c0150940d4001048800070001c400d54081c0d000402c0420450b0f0307a580c0f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 501651205 1250 501649955 501649963
    0x3090c1a0d0f0902090a0509210c060702100c05031311060f04030b01031a070c08090a0f0305030c0114190203060d0f240b0a030f020d200103050c0a080a1a03 69
    0x20b00c0105450f21590720000b503260203284143c01c1010400b0400541c280708a0b525990861003800420807101c04d125403598618103000c2c0e0701150f00130420780e003491811210080d01c5080f03100c4a48843c501c0d0040006c840c0e0310500a0768441d0040c0c41510000444035100c1c4107841a4004032258050000c008000100d68400090801035119449044840d4110300c1e102070403c400c03800101c107840e40e6404100c5020760081d01c542e00702c3e4100c54081d60701d05840c0c0110713412400a400440c615414110000704022001000f010410141c1d0000c02c00c4901c001090b000301d04041d12031014922079120341942d040519030095030441c200500700425040d10303584030b00a80585401c1a500d00d101502c44020f40650b001c40c08580c010145007c220200d503400020f803e004003804054520245003240b0b60031034490660102c0740c8e9411800030380242c00c3d8080c400b0010038040102500007800c00b404a105094101c040d11550109a01c400700386680304020480248480c030041b6102d4842112000c40e40d0314140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 501652455 1250 501651205 501651221
    0x180703080a020607090e040809040519021b16030c33051e0913020f04080604050618150118090c0b25020d0308040f080310051003090c1a0d 61
    0x14020f0212458940d038050300d0302c4201e0b8000308141221004001c0003c10850480b142c0e01f0049400040315110000c0f1401840444a0308040e50b0388002004a040c04110141400401d071503001c40d40c060403070140c02040d020f020300c801810026401c209011186007141800a00410200e103541c030070b100c600040300c100040d8a0143c01180700000d500c2080810310500020007100c0400152901c0f004101090fa000d0361010000d80f50b43c0e010461b0100010030608503001000303a078003110150b0405080036030b25107000343d9262002040c03010020005c0780c004141c205003c0034002c501ca1280c5c0c60f0a1004074012820240644140c0d5180543c0000a95080e07074000540f21060b090b40e241d81030000355500e59021500032140d8010720414a40050350380003441d0182980c1464039003280d4643e480c100c3c441c44c1241e01300400c4d402d008000c002d01d0f044d0108401b0201c2d6000c5848118000c241d1600764102e0340d000001401c4580b425209000b98000700d84640c00e200c080e901283d02d400c8a0300c003000200c840c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 501653705 1250 501652455 501652457
    0x180307060c0c0b090f030a05130906140315090a060b1c030906030c1814010c060501080a020922110f04150e010f06022116060f0f0212180703080a 64
    0x81d0000c8050241243c16070fa0300240f00300c010100301c00188015541c90241c1d420354404c010000034035041980c1c850031588000d1909090910000ea111400f400750b00030b030003940a00034802d00d41ca0320744d0004000102e07806400460701801200f0443d4403450b000d0300c407910865130003035031130318050701c2660710804603551050090361403103901410b013040103003075404103a002d80070450000740c83d1000780011201e6108540f40c0c0180341525080c21001a10341032607103403003d0446842c6c00300001e000f02012487c426032070b108461964555540e4a40c090206060f900c200c80d03988440c410700e0001a900d0344150800520081109140e2200080002d0550341d1405030741840b00182d060400c010a0712200070741c05404900c900450250400c0002941d54641003400b1041c2c01c624980b26080d50031000440d01e600010243d5200b010071075080c040068088040160b10706c03494860880c0c0340c1481c82c03007035807140e0038141d41021194032048d01c50250900031600b4403030303580125100000000e1540e40280341034601 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 501654955 1250 501653705 501653717
    0xd11160b0702061b0306041d0613110108070c171605070f06140a0509040605130504020a06031503031112070309030c0e040b06100c020a0915050307030209180307060c 73
    0x90740242855030180540c2c2c2d0200302224915401c1c8101e9060300c0c3c1c020380607100020010100f00a81840090b20100a007441c040d05090291205405c40400380e0305004040320114481c3c400f00441e2a003600301c40e01c4000984000d0104002401c0f1541c0c21555880d18a447c2d0420601d8820300c0b05010b45684103e4040c4e115002c2040702e044a14903503070040c0b0300ea0400c82e0810401d42030030b2a103403050500c05401c2110004810030641d0b1390350321840281c0720240c5690501c00041000744010501a00d003030340710344c601140006407280b19003e5240c807000244230a8103690701e143c1d000c0d5000c0d007106015501c03e028041280aa016040d006400c00c1030190795800c40007855800c1c01101d842d002d4001c0504e005c402800c020220300d108400135004142038034400b1075820311540440b9012a103c8000b0342c1703c1d0f0348240028540141d5008001d95a0f54103850042c525910801c2595a04140c8002500708600c10005040c66040ea01c5031591b504031003040c0c0386801c609a480c0401c8484c1c3c0c10744280800c2e8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 501656205 1250 501654955 501654961
    0xa110a05010c050c06163f09230c060703210914030930060709210f0f0c09060e0114010503040c03080901030906050c030405120403080d11160b 63
    0xa0400049811666811400c6040c1c10050801444041f0b4840d801c3e200419042c166450310301413440708021030002980e6000b40c6443c4600041c082d00c1d6002d01a110410407064001c1d4500c6444030102001900d84018080060303c0f00070700807207800904059040c418240a05021824414040d03d07810129200024100401f481d20051410f40003480d074056601c1840509187d03100d05185111400c03101f40200c20b0001d106050040c0c0c0c00381203051600a003e40c000340400541c01601c040161070458008030b1054090503516211004a100041c04907502c07d8002c1010886089240301110702503c0481e00c002c0d1640500004c0d20341035131222034228103100040102c000801052911018246030041c61420203480d80107e04203580405002c4050010702e03032000ea8000c2d030100c2c6880341d10a105005034640b6030b40040d2550000c4a003030b00c8074015045212203402d440070484050742d6101401604108400c06214002c1400c2e80d40c880f0b2280d41002107400b844070b2041d035a14028824002100b84d49 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 501657455 1250 501656205 501656227
    0xb0108162610020c16030b06150405130507031b020a0602090613060c062d050a0f0609051603020724021b0102070c08010506010c061802150403120f050a110a05010c05 73
    0x104418105d140084a5070005000180003440b00c603411820880303030b140d103500800d650000544182d074880da5001000314210702c00019190480f9100306d15585040101c009017541c868034038040c030450038005070002d00483c80060f200b070f0b028003002c0340050100380c10700341c00d100000900321040c2c01c5600032908451030b0104220082c0a03429a456950b28200d1f42c1e40d0380c00300c15840400822406075111034072500010030141e425482240c10700051401402215603464414004010039902d8a8040d00f01d0b01e0035031750b00c4d4040d008546420364040200c841c0c000c50030304007516400c000f41150039000d800700082c0ca400d5040e0000c1e03401c0b600114000682d035205078644066034880380d51100e0020f9040500b000101da07004a8140d2284d80c104601280760024206440758031070241e50000e50240f139135204103292100b48005032081c0e030f1095005030f013040e031a00c90035034017044000d040d800003480421803180b0a52041c2000340c0000f140c4000c45824410faa5561802d40f5228104580010008138040f11a0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 501658705 1250 501657455 501657463
    0xd0203030f07050703120c0e19051509060304020d050a051605040507090e010b0a090e090a12020307020901050d03120f0f0b01030207120e06040f0902070b0108162610020c 75
    0x200d00e0a0800f0351801030356503005031441013400d0502000d1a524034403003000130302454110311310040040090424030030300790b040f00800b1020301410b8082c505242c07d0801105000044a00313111000740002d05540e41c69082016822100c0c604403a203020718411400051010000c0307110003041e141c2c2e078203c07841c100000e0000b102c200904807410020310b460b0070004044003020301030545500e1044180da40c00440c000b40c0b8a40300c66400495a0242c01c0c01300043c204003c2443e00c40315104021b006941c0b01829012a40d9004404020354408030107001048945001082c85900301e00c2414200107203031581d4542b100304d4020140320040d441d224009242040320500c1030794801413013402c3c2181080c032142c4134410890040400d004c2403107451144030b0714558035501a14002e1040b81d940140641e110610b040207508920783c121580c5d200c03000080340203800840e00c490b101442d0707400002236a01e00030300c101c0d091a01030a140b0954102500c0300c1d0a5aa05002000c003a0342c2c54003000d6034607038025102d6858 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 501659955 1250 501658705 501658711
    0xf03110f150c0a0c0611040302030304030c0f0b041d040609060c0201050402010206090d050d020d020714030418020f0316090807060203041a0405060f090a090504060f050c090d060905010e0d0203030f 87
    0x100d20340800003611090741250b03404c9026500042c0000c1e071951603c101d40e645101c1c40c0c00295140c4408680001082a808004426a107603810841551a500d46011410740550b0090034000508016070441c440c490280d0355900c540100004030b19000f80b9101c90301250705c0e41c000034006035150000c1109558041004503000401580140f008511104008260f0b024440d0300c50680781e00013500181005541e0161010580c2000c042802180b5030040b43e9501e40c054410854801034105500d28120003910940ba111f0000d901c08038039580d510010182a5101c0c0d030403020078804034080c00309640504010100c05071485400031682c40e030500740800b01041c90010403215090007000705001c161641c0c4240c5054000340d110b05900c80e041c041c006000d540362a040200c0441c03422040005005a03a00041c004103141328041103140c0320a20a42420b20030011001d801c5120080380e0400600540d02030341c030803800362000050500d00900442d0602c01e500288a005134400310901190b41080005150 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 501661205 1250 501659955 501659971
    0xf110702090708310210080a060b0901320c0d351305011b11060c1e0f0304050a02090a06290c34120f03110f15 49
    0x740601c2e0040c44d01e406150a42208400c0a8040194520b4500a002d4034240503034002d00c6d4401020704031400070070b0a42c0440d80d0308a020704055000075140044000c40b040c1e040c0603941c262410b0b001000d00c0044100e02e80e1440303404601c400d80d03820380081200150040c80700c0100030780341c2d01c0100c01c0002c0c042e640e203c034102c1003107a018040c00c02c1c001074807007010f06012010402031007a940764051b81300c0319082070001a1280d42403000800030b071400d190300d45c1a0707000a902e800d4200080c0b03480c00c030340d0755404441901c5200001c2041d05001a6855054110030004000e0790346800b4904107548070980040d03d04581945c0042e0000e011450300404c0035030f1100006800b080501d2038034030f40014060340000b81e0805440c00188150300f4008035000c551600750030004503076004050b40c02141d510f454078040352025600c004035100d6202e04150b4528111518100713840403041d1035440ea21040401c1c100c04030300f030200314465981540014010b52a452203d03102812030a020651968401701c00105002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 501662455 1250 501661205 501661217
    0x30b01030513020d0203150f040c0e091b03070b16020405010803032503023709050112020903010902031603020a09021c0b1210091707080f090102010f1107020907 71
    0x442e00c42844519000460380480c0c055202e0866800820300302100140220040340c450130800150700301d01c10406018601c51f00030007038141c2d6920b040503800305c2c0030754500060303070404000700700341e4541c404e000781d14058000c069401d010355034010303260243c0c820f15024105642c00c1c44614150301d00f0b031042c0350040541c40055440d52a0000181441c030304400d035600e104000204440007194400d90644000c2600c3c0440508042c45000c0c4200c0e1542c60940c0c07031000030410318100c4510750721980f900011141d060311505000e0006d001003c2c00f07034000900c20358040d0f51790040d900c0541d808114204915442c02110f1110034114014402106c6031a04503942440c010000d40c1c10749401c07260450581540e106001600700c41400002e1440b46840b00e1154051103480b24bc0b80052000d40d01100307400f44074006140302142908800b6409006900000e4a104401e0010f64004400c1c64020b2840308014800003c2d1610b48498503011291090311580c4cc1200101d201411410001c1c48280c208000c0c1c1450 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 501663705 1250 501662455 501662461
    0x1c0b0907020a0b0f04031206060c060f1b0e2403160206070e0d0f0b180c0a12080315060a0c02031b0a090e0c0402071b0f051e19090606030b010305 64
    0x18042a0014080361104804d036000078052621504250340040d000001c244030300340c0da5020051108200e01c100342d555910340a104201e1480500c109a01c552003003080404410124000360340c0302c4030b400c04a0b60455030b5074411602c01040d14401000c2400b00584082e120300b01082c0f643c00506442c1030001c15588030106102c08103810290181c2c0c0c00c60221082c610145141c6031507101d084070700c1c400605500750705c000c1c024007096040504460f10000c804491828110350200813030b0003c240700d1780130307021391003111240070507001001158848a0001089903039a80c00300818415030100d050240014401140102140b8060104015415040b24042c0981240500142002c2c2e081d200d091241a90744c49241a901401d11074010112401801151101050700b0b100041d4410030003598542c1e400c505002c01c0c0000c00501e07040c15140c0c040c288401e0b00c0c09020740d48240460815940e54042150b1b40e06011008401620750003030040c80784041505440c018000d82070b250684071090500d403d103410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 501664955 1250 501663705 501663713
    0x30c0908010c02120d140c040611030715022116110102131e0f12050609030708161a0907090c090819111305070e06070b0403030c051c0b0907020a 64
    0x504c0050746100c003201303a961007001804400418000070720030314428840013080510001c110103003045902e01d454204499403106600c079100e00c50300d0002071242c00540d01c0045100d09503809400304400ca602d803503440030103000b004040c092080340c90205004210340864509648070114203800341084000f5402c110240c10200115203650050300758200ac051007541400c00503d0450008080d240051368217940c55403120014141801815074162064801080b1481000011900b00d150080c41583c1882c00c400c07551099101c41c01c1f02039500b4980c40d100024101c043c1070046005050400050071800c0c80c01002c001a50150070005040c454960741c20050980c2c049960186260b804400d0030b41c002c182d280141c840e03110350001e203812101d2500500f0707150400e980004c0c0180c0303041d20f4803101c0c04140000c001d103900c0707020b000500c5000040e005c00c00180c0603400c00c501c080348509042d03003004013100041000101b5040645a40f41d19041c41c007a060801c0d5201e140c000f103952002d06010034081e25 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 501666205 1250 501664955 501664963
    0xf0e390117042604030c0e10090b03160b1c0c0909090c0b031303031404150203070e031009030305060303090102121b0d08041104200904021306030c0908010c02 70
    0x4505901d0200c490006400c11102540d51080d4004400041003840c1c0401494010b80d0007a0001310b0f2a0031015401290407403020601a00c81d4484e10640090305081c0b40309040034020300b13403160340c16204242000c28a518400c42c075802500101184c141c030780381e500710101c1c4442410200010114500940380d0561507000d280030003034450050300400d0070340d814078002078040700d59484043c80716004014000008548296000308500a070380c24810a80c031480c1106032410151001401038103038461562500902e600a50b500c110582040b5031180c03d0100464202545003a9038103100765550380764000c2641521078290010410340c002e43c2031641180c0043d564000703004010b0b00d10200400d105400310501c810804c103c20381c0b0004e50341403900007100942201c1c7c0a490496480d0109030103481b290400d4801c07214214244880f09601c040b610300210003613813203220600d40142d000c20400d000b0a51031250b0100034220790741c0010786540c5001004080d81c105822060069040ca5210900141c0c001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 501667455 1250 501666205 501666227
    0x40219081602060c0906070f0305090a061106070f0c0b0403120f020306102a0b0115020105060a031203060e040f051e071406120403020c03070b040602030d0f0e3901 72
    0x101881e603603440d894000070500d007e00321009284a480310399074010180e200740501307098103080e541d007010750b9200ca40a076981d140c3c50581c100681d018400007501e16102d0310b090704074180c913800e2089080e8245e440b64920303c0c0d02214103a01007801102604c1c8150f1091040d4170b14422041402c6085081690010b0100400b00f441c0f9001c01510100311440c01d8036802d15140d0300c2c000511745030303540c082a1424040000003441180c8404204205084e0321900600030284540001052151f5450035591032020300d81c4101038000800d981d400340072410b403602003041400345000d0101e018044c45949003061808003c0643d4080c0b544030030400e40041600098100103444004200299501040010a90a0003062310301d107041403084003804240358021601c498403075800d0781620303412038542000c03504520940c414440141c0c010000300c3c2940c0070703581c00140c24050b0400089241458100e900b482c1c95000d1680031494501e401c400817600503100616891650310419802c0d0041101c00040d021000c54 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 501668705 1250 501667455 501667471
    0x607020d14040506071a01060c02091308070b09122a16090207051c0320030601090311040e010c02030301140910050144060901141e04021908160206 65
    0x8074841c42000041b6110103c030300c0480c110319040f176039158001061f48840c034000b680280c94040c0401d500780c0340444580207080d00302004074505400b950702c0500100c002411100c141c09120090f0341a00c9600004001e042d0b1110080306403009804800801d03050401e502c4030392580700960b071000c41001e16035001c0807120030401c0180c45040c1800c00f24202290014102c01304a60f0b0940084059016480203001c10203500b001d0210440c000140384051106444807070100e104410200b00190610140d4214801d028002050305030001c2c80e01070958005400700e00140e00701100601ca40e00b01c10825410740340023181c0d0100f0a0408451210000710280140d0381000840100c0030150342c4113a14902103081d1503502d5070541010003141510050304411201e9103102d910f00452002d11748484450f05950003d24140d401d00c6000c81044a6030120482c090022900c1c0d1202001968491025080b49192241e0856846140000040009034010f10000f4801900401181d00c10ba0000c1c03001d074003c0791 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 501669955 1250 501668705 501668707
    0xe0106081c0c0203030a050d0e150a0213051c0b07080606160201020c18011d04080912070810060521070501030b040b0d05010c021c0c0b06010306170607020d14040506 73
    0x500007003102c481c0074403100650075100004503010416400401400030308810481000396030008101241c40da141c21400c000540a4500450107440c1540d0040c40c001d0075a0000100703182d5240f0118205c03002c2c00222480403800d003200d200620040030707031065001d030152400701b074149031000002e00c4601440940460344d002c1d0791018401c59008015180207030500416005143c0c040384401d04d003c5400b4020b003140d0b403504031209960301180580071401a54400e0019092184640a018000c140600240c3d014411404006a06881800000114404020302065a83c00c04091280340c82c02135110440100c009005209600c0001c01c00d401586c20920300881c1d560a10380000d4060300f0141e016960000350342015a08000741503100050240580c0c00f55030840d03650100780002c0c0c00c04201d03020085103038034034100009259421103591160050500060b4103840b2802e00310349040000f040012940820705114109404101001d81c000c02841e0989040c4010110001240110b202c0e141c000c4d94 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 501671205 1250 501669955 501670003
    0xd050d081023030c0406030f060e01061205060726040b09010b04020f040305012d020702130f0507090f080d0c020301110f0a0305010b13050d030908160303030e010608 73
    0x10039144000142584540c1c150006101d0000100c0d03001d003010b00510a20400448841506003401003000b16908015800000c00094075090081c0000c9a104444d656840e40003180d28a1110501d900c1a80101d00402141c80d240318081c01c40180f1500d015003420307074940345c14428154201e00360b07445980802039040b40d403100183e45002d4481c8114541e03002c0d00200d10003203160174030b502032f100322070166009004110b0248070500c414840c20001a43c542d103844410b83d801c4c0c503503400500d003c07440a400400f80c84a107a02c0a400c0f5950a90310510301c0c6d0b11002800034841c0c0c080340201c00703000c2000c0d039040007a14100c1d41a9458079540e00c40c0082c080076420350002c0d03540a40c4400c0c00f0000501c1e01c29035603010103101d038450354081c03a00c49010920700380000c1038a00700141502c481118413940829007a090508114404060607021001c0003074550780402d911800344111071807140d03141c0700c54100b0341c2149806802e444030312403a01000d80c50140104105040010001003002d2194040c0d85010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 501672455 1250 501671205 501671221
    0x30112080904060f080d09090b0d02190f030606090c140d0c05090904050724020604060f021e041703091014070501290d05060f100f08030702030c0d050d08 68
    0x1021650080110b150340000001c2e1105e800b081d04075440e00c0b1079544210f610740329402c4038200c60441403e0f54015404007030301801824220010140604113481d00d00f00035541c0c0001890513291078104031a10b40d210882088020494064030f040c6000c1401c2010060142c282d04010501400c1c0c0ba65080c0b0f911340800d082c7e0035004904584d031a08024210000c64901414119550844d521071500011005152590105504c1d008040d843c400c9034003400b140d403502d850b000041c00a00c1c0c00301003001d03805c01c4050035254280c03104265014900544c0703615280b41010501403408410801800d580041214052640d41c1c0350245d1409402410140104000c40302c2c07411a0303000d603841c0201a076180071038842035501c801c601c0c0402d140022001c0110f52070441e0601002c40f140c004002d00e9a4060004128011011295217a00404c5420440d01503a5212035494680c08182c0c0441040e4100080020030f509080c84072012400341581c00703e01450940c0c1c0d89a50380c2c41d45010b601c00300149280412000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 501673705 1250 501672455 501672461
    0x4060c0c0510060305070501020616030c050f22090902060910051b0a0b0a09030e0d02040b06040e040b220308060a0509150306070914130b0301051f0501020102030112080904 76
    0x10358105040b81c804109a861141c0203007001d000c20f580d984074685002a56610000c0c540e88038140b1010f01c9223080c6c0d82e4000580242050070300383c0f01880018072515003610385c01805442080520840220342040b81a2a00d007944ca803904485c40315401c01c4140d01c050b0b01c490044815811095911024100d42c41d442100d1501804900c0030503c07109409105081c40d00058048115014189c2100300d40c0f0341c0c42d00709080f1407020900a001c07507520600c42100d440e0004041c035071140090400300c2c4880c08200055060780c0b06800002e17030440c04070706200a00c00440f1401c1e5121900007c10741d0303664094003800d8010b10780008018100080f5a0008000380c44500d207040041c0401b03003d00740603040002c0d2a100360450041c3c03040c00791084d10002074000d407240704039a00301e0341881c0b00e0888410392a814800c420600c0114049040d0316032803a404252401d11a1900c108404407800503050000c039180c016045e40c3d9400641168010710052040e5860801e0f9070ac90541e0004100f56107a81d100042005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 501674955 1250 501673705 501673727
    0x40303061a030f0a063c0806150d0c03060902030a08221409010302151c020901020c010201061a0d060b03090604051c1b020d061406040c081003141915050c1204060c 72
    0x51b10369400c00251a0600040c1680076104030203403000305402030002d0004070f076203048014040d2030042c1020408141d803075003c01001070001d400e4a205034410340701c0030600c0d40b214620078122840005d0b000c0e107515224a9541c0070302049034081c034425040d00000b810a102c10700001e440360040d4081c13440403041d80c008403880d030082d05480e000070742030000400b0002c0d00440255070260103a08500d0109600c107114010540f002403a0203162020444e08414054001145290010707036200e00220340416480081d500c0381000030014005403030946025030811400b0a002c00012600e03500031020700e078100100300d510000891080d06a6030f01400020b4042c070300300741d0160103149040401c001380010885118498041920244030490b0202003c5408003821100c1c2c868814000e113052000403948800b074209003100e50101c500c070b010a0303841c01029116202080355243c105a103000c64440c1d5030f00603564011584c601036404d11203000707913402e0008001040200040e81d40c1c3c0e000e262a034052450f000c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 501676205 1250 501674955 501675059
    0x70e270307150c121b080601110f010c1b0b010905070c1227030c03020f030f071205012318030d11030a0501080304060512040303061a030f0a06 63
    0x60003400080c60b40000708050101200019040803500140046900886000071900340b04c030102e80b111210201e07454140030307000074108601f0040c03002d800001080f80190000c480c0c40001078081c9000006803e080c0d20481003030320a4180c40001001c500103441044c11a540140041005d55035298100d500c02090300c0010f01074640540101141d944c0031580c540010101454441c100c200000841c450504920004102d400030360418030060406500156a0721005822984200d44802c0c0c0c1c0d5042500540100024956a02c86501401424054000400c0e00d141e2507100903040b070320581c0e058400042900442404800c44100c00e500108102e03650036030340440400056082000c500310a60081c3c0d104201c0d00c0c2483c00201d41480c0c040204c40443d0700c580c96041c41d0202601907103420f0000100150103040da0f600d40051102c7e10913140598042d850a007881d034034903140107420059074028100b06030440c40d152041c4402820682c00d03501c04441001400a0075840742007080405080b104101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 501677455 1250 501676205 501676223
    0x5040305120a061a0702040605032a09041a1b03070207061202040e04170f190f0207050306010b130f1509061701030b0402030312040b09070e270307 65
    0x100505a00801520100700144040d07801d5840740c000c910141c4460b801031850b05004550280000c2d610700c1c001302485031001d80003040f59a512000a03040076204105d5003500911a0b0403503c800c0980001e04800040484114060741060b03181d01d03000302003070203182c0b001942e00d0300030031a10a1030f2047c0c0ca1804480d014040e59074680f000000303454501342e1050b003001c2100740c0c01c00322820516009540581c0e0031804041c00c10f07070f204d44820520b030a0b00d00142d424100100002d1003124580401040000c03c0301ea04081c001621003002866051110440001c542080e032050145039000728259045481c0030b1000c0342c90b84148083d030b001f01031282d417041805003c0b88100007846003402440380b010103502d4541d4400c040d81c0b98425903844604034405280c0f00d070344c0e100600001d038016607540d4115001600302c1c0c1c1415410b5000800c000342c10b0790240d903507003620410050515400c01030303000a0074070580400d20b01d04103141401031018007400d41940210064211240a020810941c1c103c81d411003491 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 501678705 1250 501677455 501677461
    0x1120602090111070f1a030910020310030f06050414010c1d03010b1c06051006140f070501021206030d02070810050405010b03070f0e01050915123307020606031b030c0405 75
    0x178903041e026902c240d00720300d40c1c2098202441c0704180c0c03d683c446d6200c0c6d0701922002d1116000c0c1c10095100608040c0041d00303003d408404036947e036a180203500d114040005007820541442c42c04c4420301c00c801c00d81a030505a0b20a041580080c146505030300051030440e0744040040080d015041100506400c03100c007441502c000e00391808800c2070203000f42e00030041519510240c0340d03024030501540c1c0c00b04203400d11580d11080703400c000784540c0c0007a0341140d051131256616903080e603200e8880b580d000c0c0c20010610180e07250601c100c21005d41240000d003800c61400079407580715041d4a0150103c10b6031172001900b48002900090f0b107415009003031300c0000d6101c213540d40b80401c450058440d034400c520000f00d103900b0f04540340c0d405104413080b250b0b6280012000c0090445006e4807041c9139005045c215002c001e1304500d92101d42c100311120261581c849442090381001c018020f00440d480390040c440329880108691240d14a910143c0840c10810340c0400e10b0560140070345600701c1d25007410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 501679955 1250 501678705 501678719
    0x3010c0801050f04020c070b0a0c081605010b030304080a03031503140d02010605010309150e010605040f1d03070f0b07030b03030d0204080c03060402010f031a0402121902030112060209011107 84
    0x52141610300031220701034420145002d02c001c03400b031031401c0a45603000007014440350003003402a0034400d0071440c0001d1440040da5a07802f06400040d040142d6011401400c01042000c0c002e0440294003a00150704140c6065601c40da9164121009024143e407281d2009034008803e5100c005103411480d032482d0344020541407030b59030500c2c0d40c120006520b081000304003036119010f151070041d004555648200081024580109012454141c03150341c2e0302e00000346034896000b100c1e40caa8440800051051104a0080c00980343c910a0007064004011070400034080c14080c080842c5c0150300f03902c10f035a411409800900b0f003154602d40c144001b040901002d80141c00a100f95120503007550301d040009014199100c009a5009010683c0c007145481420310940c0510316210100c42c503000200000804541268480c41c050241e8504141c2000b5001d5004c62070340c840d00692450451540d898442d0340801501c080c44c00900c1c0f190001480005684644e0542c0c0700c85807990161a611035444031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 501681205 1250 501679955 501679967
    0x11040303020601063c1b030203030a060e01050604030807080f04031b1d060103050a140f0a0605010c031d0f18010e07030c080a09080705030a02070e182a03010c 70
    0x3c40c184c0042d951000e444c03c4422075030416180145102a03480c2034a14850043c500c14030410104d20421032000c1e070800d2140f9000101181440c040e8020795070b40e082c10805e2405660054018080c00c40c3c0e000d004201545684040b107040300d81000c409a181d00061410310341c20310403039100c41110980031802006000c003c14a5180020004030500c68045c0d48405118142186a804800c07120403c800100154000e41256034000c440d1500000c1041d0081407440180a042d02d40f05051000401003201030415486101d01403c0d0900b0881c4d1114890303034000b01910104d400310040e40039902c062810035101c5120b03821804400402d46201100003410752246030409201304010010a2004a41643d010f4419000b455001d03541d0b0b11180c1d45c0704070003070015040c05a0704036088c0a08000c92008240240060413a5001d00d60281002031f01d4a0b450044c01c41025045030b1041590701c02024a0700c0c2d00040c40d9494804845000b201d682000e0800c07418403c0c00003245405500300700320411400c2e401070b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 501682455 1250 501681205 501681209
    0x10207140d150c0905041413320c150417160303020307050c010f0509120304090c09060207330c050d030e060a140f1b04060804301211040303020601 65
    0x40c0d40c4020344d640d20402c00054031840742454118600e120b003c2a400092015501ca00c203018501608428a19601402810100400a00c01032100c004003144000c000d00031040c0c03030b4204a1f000240340b50004128180b520992003104120720740d6882e5541407150078440c640b1301401c0888401b08169807410701944030b42c007206080b075441c0601c0a0100d043c0d0b00420307114442c4115540d4039820016168103201c1e04610540940c1e080c0e20090200240e01203142c00384c0070890415603107946c2130342c2c070340340c806850016103401104241d804c4800d116090040c512151100d180c429494100a480c800070a0b20320400308200506a40503464680d0155a055000030030a4014282140c02aa540c1c0080d6421a11440902e40710000707014040f07888050345a40c0c1c9904403405a0500034140c07144403d03042c240e40700f54455000700301460204014030a44002086407803180c0c0e40428003c092049070788280400003800101480034001c05900c000d500c1e81c0c092680a046801d4403581d0f15100e0074082e554080074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 501683705 1250 501682455 501682457
    0x20c090c07051e030301060c03030204030501181e020f041a19083304050312091e010213030201030c050d0207060b19061d0411122202010207140d150c 66
    0x14000c40703e200318148554000781010382c80590300396420304204032200000701c01d080e41017540901c008004100c0030311074515546c03514444075284a8840c603004041400300d9442d410740340100000000540c40c1e20555404058040710b0001e000110400c10a28060100303e02a8001d00c0d403481403281c3e84000850310090b00c1e000b1007101d81444545568014820180b00e000300c403043c030b40d009500144c80b0020450f030014454400d580c100450052030782107125084036415140d5001100c500c2025805080392605600c10000035841e01000c0c881d00203280c0d9241c48000d040584e521114444a4420000d50300b00c0214807405540d18038013800c5c00b0b005440c03019809445070504031400144284403d40e114121001c60b11600c005110180d0800d9044e10426805600300e62280103881200d001300e4010710a894a0030305100d210f0420020b1290140b80389805000d00540100413200540c2c4c00090440c12039800120014081000602007410fa081501c4024501c5650107044603804940c1c0d0000c0c004c100d51 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 501684955 1250 501683705 501683713
    0x6090c0906062c150d050709030201081609081212060d0c0905130c031b050a050f120316200103051608090a0206030a0902011d03030f0a020c090c0705 66
    0x2500410300803100d491141a000c500054008140b449202e00180c0150805529100780c81c1000e40c003141c22042c0308180600c0d10640000d6080840406200d0346822150a1034401c407020300310346c00a1b00c83c0002034510403180304a59181a0400d114a503020040c3c168034080d1620402400d11040d408e4120450103103418007118002107881c1400340d4031180c000e8201c60700745240c502e0840782030001d01010f400d8280d1b10880e0b07115880820302ca0b01d601300086104890306190010303540d10700c580c40003598000e00d204040d900000c10551351180101b005d000c0c4100d130034001a000303480001c0d20394410f101002030341c114004210801c2c40708030311003042d9102c0c00141118a00e20390400440464102b115100e64007130450003108085403042c8030381640410140100c9a04c1120741e000141140c00403251041d43c1c6448281c400b04550f8041c2001e0400c03c01104490a980a4000060b49a00a0000e000080c05002c00e2048074288200800b88011802030043c00311810428401c100e26401414103591030f00c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 501686205 1250 501684955 501684959
    0x1f05040503190b040807140a0b040b16090513022a0f0604050d0333150e100503060a03080a0c030809030a0816050c060c180102060f0402040b0a03050a06090c 69
    0x80407030b40ca5070310395031241c004003c43d5103d580d240083d400c058810388045600683c004a010410002e010b20103000740c60400a916041ca410490060020055a614180200300c01d100c242c1045d02c5e00b00781d541c1203a161601607002260680207009803200d2607201d070010194241410388109000782000c2c03026041da601040c0d40c62034a0341c2c03828141d41c010303c140d0000002012251090780000c0741842005c00d40b0345059240d80344030b0300c14002283c0104000c202d4417010440ca40d070740300030b14014003d1401c1960403140c14800082c3c0c0700170140d100d130f01800b20000002c2c03032547c0c1c1d01c80002c1c044c1d940000c6150300d07032201b00001040032840620490100e504880414075051000040d40c001100964900d00941d9130025034801c9400d100d89203805000040c00344d02a1410180301c014826941c0c1710010b5141c2100c5030350044103004120025065400000a01c2620b811101f18543e10940556012400f03101000c040b030961051688050014041d4110940800c4031940200c40a03a0294184d00b044076 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 501687455 1250 501686205 501686233
    0x5010e0108070c1118100e070207030f1502070203030f03090607031814010b0604140f1002030d020c16080d030506030c0a12020612010b0c0706030506130b1f05040503 73
    0x1040c10b4505001180c040d510081c0020100f0701c90b481d000b80050810700711616800780045840ba02500d1051101c10001c400380071881088416951001c518401400c80c203246071500400300360990b02c040c081002c03540300685d00c0390441d01240d6005502900326643c5801c081d44a0409410540d850100c6028060100769020b2080c010604594803001e14200b01c402c1075540c0d030b020580c2c4a1008511552070355520009a6240400307800102050300c5420301700e2201a0411009015002403940702d20751808401c001543d000083d50b45982c205680180c1d600c19101d2410301d011885030900c2c81000e02078a02040122000c03c10074107440c0c042d1003e000f55104d100c109529218461489500800610010007000d1100804074500a001030321407403802c06003030500d084d203c900740c0140088200c005410402c21350200402c2004090074a8100998100300000070050014440b4040b099501c945000c2d030284d0b0351284045000b00020b925554014019401900301d4006108080c441d02410744041100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 501688705 1250 501687455 501687467
    0x4180b1609050a150f0c02040e03090a0e0c0304030804030c020d0c080d17130212070308090910030308040213140702011a010c11010809071a03040606090905060412030e030f0405010e01 81
    0x500c62440d00103009260703025003110745c43e45040015003003244254488002da22544100042c0780c0d911409590f5a4070440140300740281c0542c015201c12120718204131901000c4015a034200340d161811600603100c40c14122189081c2d040c0180d40032070000c40540070403000c01043d404454490781030b10b1a00e01d0f031440554003101c140309981ea071280c80b1000511840702403680400301c1480100160010b4181c20169458120f190300b044030116000560421245019185113900c005034a1000c1c4000b42969030043c607079500604000d0007a5000520750207001c0300c0e07030041c510341300342a0a030381903510340b82000a010300022460b000140d50000c111411551182c50141c1c03105422640e203601c0071800d0700044504210080c13009a1601038041c000c1949003000d0540b101c1c1c003004e61032032502e03410113050003000c0f0780d069441054040e1504990000042001ca0707603070341c001d0300004118204070248105402600d803080c414655800001400c400c03400c13090002e00180e602c00c0e61604120820080107480b6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 501689955 1250 501688705 501688709
    0x30308010b070507031412071b0f081009020d02040504030807080610090e130c030f0b01050603040506042a0b0301090c08090316081c0209041104050f04180b1609050a 73
    0x10f41c3c1180100340085480802191074180c00b0000722160000c103581c2c200c4450b0070000c400c80e440442803492840481c0c0d058140b101070221081401c0e4900d00d882c2c2d46654800040302c3d01504e042c1c5601200303082d59520707140d900c7c3c0580c020344140078600d0140b50040c07400c6001c80c1d904002c5005c00000c00c0c1d032420100188030f500041506d031021514285042c0302807041d4000c1c004044c0003916010400024044010100203600c540d071103000c4101076141901c00900d05812880c0910b10900811000c910001502034000740c0040c441641340c00620080c900d10340b002c0b004103118001880000403d440074500a504030b03071004c00100494521064200c60304401580e0180300341d8000d022018003055408020541588110440c03442e0034802241c014590b80f26621650949030301050985940c28135020307c0800520451000e460702c0d0521000810100c41e5007000c80c080c1c0d80c0c4983d118081014041032440d0190000009400e03490f203c4000745080d00b140c5080e800060003004002014148100701c682 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 501691205 1250 501689955 501689963
    0x5040c170c10030c2307290106032a0e191707030f0b0a091208160206040b1801060807080124060f0f02011407020c040c051c0903090e10030308010b07 66
    0xb00303540000070b0500001d0041c4204102001009240009115240d51f0302c1060004c0c0440224400003103181c0e40e180300142e000070145814204070200d00c80d1020f43c2d03540c00c2e00c140d8031901c6112109036021100036106001c1e00fa084010104c00c00c00304003000c210710044407040c588240039900c0641c111a02d41406202c002c01b403544102c10400040c2c0f4039602550f010000c094005500f800e41e4440300005412444100041401081070206601076050700750201441800200380900300781d52264400d642c01010070b09042d41d11003031012606401c4d0400d00007811283d084400840d1207a201c64003c1ca500c41044614140c01140c0c0300355000002c401004840250b1600600c0d400040d8003510a900c0c4103400c0d40c119582d4828a216854030081c10714014102c42d4000c1c014091928240300454410f0010403007840018030100440f202c0514101c80008045100460000418602501c1c0400550010350020b040d075400c00911602400001c411240a84e440c04620b07603940141090500c074034a0060 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 501692455 1250 501691205 501691217
    0x23060406090207020d140a050601060815030d090504020309010e030301030c050910030b0103031d0904030207060306080c06091003090203070b031b03040807060b0f120f1501061205040c170c10030c 86
    0xa40820035146e00d42002c034622505a403099200b5558403420403400f41c0100c008654502d0503c071a21143e040c5820008500380c00400108070034400142014149100e07491003281c0010002d2101d510a402c90b0010b8202041220b4880d612458174030104441801201d0091501000207129104840341c01822a40c00880386803069003907031801c4440310944035031400c00d080e00c1d544501d0b4507180c0d000c100f84110b0007940601006414014028180c411660284659601c040e0079009550355400c221010f044044411068023058881c2c2500601001c2c3e0011398140165840082d443e03c0d40002180310b461440d40c503050605003800654110700040c1c9000d02090b10512042c1c00040403a44244c1c4801001440b0520720440d50740016103101401c0750410b002c1d080340001c02040f40081004e0311000315240d00e22602c641c109800140080d04c0002041e140035150400b04040c4551101071402401500c030841c401c40241c4480640c0d29a16555094010b04200380d070380701e50724424440c248103903040d40c0d100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 501693705 1250 501692455 501692479
    0x3150307150314090d1b020a0b0409020717030108070605091306080a030e060301060f0c1a0705070c05030a0b0c0a0e060a030212090718091a0a050603160305150a2306040609020702 79
    0x81140d0640c6080788c00c002900d2020605441d02d101602c01014041c0700541d441620703103040d4204c2c40f40d2082039410102c0610040c0003004011900c80151602483d000303881d40c0400303001881e810b1011141552881c13074084041481c0d900419401a4640652030382c03105246404c0c10302a1501c0244581030014100d881030040192160744105021402a04255141e1100e80b0300c0c62070300081a40e44c0b001081000a00008110f6001307900f500030641100500440c400d5a1104c06100f60010034894070842e00243e104103290203944242180c41c805131415031110b6403180050008d40c1f00d8022101810200300c005407080500003420000c2d1a18a048400500d0344118842d0141841c8213040320f80c0790083c5400d1310b0810041014912811502c400802c003410050706141c00d14400c00f102a034507540200051010403400030f44820000e0011211001c08e0356030200ea0401030022010148600c2035a04880040c581c48100c140d005d40c2c13003194204800d44d80c50001c3ca040b1301c101746000f0340100c0003242c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 501694955 1250 501693705 501693737
    0x10e15010303143a0e0c03030f2101030c030b010b1306120906111902030c0606012303040f1106090307030807020105043b060603150307150314090d 65
    0x3428641e14013058458524852060607681c01da81c140e660001d60060744000c0c4c0307043c4800d00452002c1840d0602a141202d00e84010a03240d102e01525200a240d0019806464450031480c050961104681c800b00c40d5840345002600022148020348850404000210b0100c0100048581c04a11034808581c15441e01030300765031241d5800c00362000e0a0341c0e032180b400404c80c280074105101d194400da03da5181c038030780c030b14ac003d0840941180045520038407d9a01c034860010380c0d503400c11170074201198034820300b02c040001e00401c500344d4400c081000c014801000541c0b21000d035220b100312000100444000c061241c240950150181d0541c0f04501c1040400c9046008106079030042c034000f454191198011043ca40122004c0d0409424a04400c45d4a202c1d4581d080740712003040f5400001d40c20020000344035400041c1121046008014490540d0790b420040d19000f050412084007141c0103034070b406002000c3c816415a5010208000a60040d101207942004d40180340c403400210114080c1c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 501696205 1250 501694955 501694957
    0x5160503090d0c0503190e0a0f030302031b030f0a02160608160302030405010212010f030b010b0304020a0312090503060c0a0305100308030f091207060b100903051b0607080a02010e1501030314 84
    0x48203884a000c10003e4004a0320100411074070a001c6d03403103596401a0000c240504078004e80e00119503c800e0340c000380006540401202c1488141407900360589190400e00c50651207815114441007a0010703200120a8011580c4840700080562028216541e64021b07520031004940c1d090002d000c7e00d90403ca114003d84c080c681140c0100300041c20075490018660041c5d0080c0c00503410014030032410010010909481800b400340023041500750304050307011130111031441c0001460f91070031311107901c071042c4078400b584010000141143c8142c104400c030750ba4175174003034507040700007a04000c0020280003040c16041c08403176002c07108500d19590340404012204000d42070340310300d02030003100d03c03008202d0001070503403180504000a00600340c5002c0003845001181ca2806011700b94104001040c0b0108804010854581603100710003030160014800740300380040140091000716600070519070540c000c4811162030801c0304c5400749012162030700c000c000d200080000d14001025a82042240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 501697455 1250 501696205 501696227
    0x603061618030c0314100c080a020703170406021903230709080a0b070801060c0213050901020d06080109020f1519200d09060c0c140f0d0605160503090d 67
    0x1808a8200d0b074403640c038032681103d1a44103668510031442040305289051141c03002481c0c401c00204142e03510a00b000c3c01c00f100040c0190000ea0340407803081e09250107120a40d90b00d8140c3c6000c50b074240340610340350340250081c0040a0039034512034000109a40284a0107009813828440940d1415141d11103d515179001416030003003211030038000030411410481030300700d0307442461880020703c1d200724000e16a4105a01100800c1034a174080d0300562511601f8003203079141540086544c0c0d91b5a89014068030035840705a081c1032030310300700040780d10341075001c4080d5503c22602c413280c10152804005601041a40120725514104201b072400820b0010742c04c512600c40c02e0080b041544540e00820039084800c0712422900200c841740e41c85940140584003070082030410b03034207400d072544a59041c690f05004441c0c006400d882c207200c40350750b10302c0b01e03c0840c2c6004004d2060000c151600c00301411040d01c83d100040764007d0040502402079007901d00c2250300e42c0051104446000048032500301d06 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 501698705 1250 501697455 501697487
    0x1a0111030d022104031214190c0908070b071401020405090c0d06090e0a06140c0a050c011506020f0106050103060b07020405070e30060f13050102040b04091406030616 73
    0x4402480c3c04062042d81e1a8480d0780203458440b1251390a44401040c0c898151400b00b5449400c420041508400005400c81d4504030000141c1d4480c0304034241c5a400150700440a244201440000e0345000c03d03009050f484d204102ca036030740020007030b4072b80c0c203034000c0780211a8444081c100140305140e080b805040300c104134020210350b10780c0c3c44240c07504464815641c1c9110380c200410310018002c160007140c8454600056030000c1e8540f0100340340940c09560144400c001002604112500e400d41001c2c2c4843d4000c001c50065565808004c3c0d07407902c00b201c50701655420428001010b6020340304241c12510006441842e00c2210349c00c1100800c1c00074207240c24419040da1040c0c0300c3d294440d4082010b1200380e12100074484030a14140307500700c443e50408a0ba8032030702c1041044a656407005d6000355894a2000c81010645019030180c051604500007400020a0004030b1480355040184491034980c4401c03019114031007413640301c1c2000c80341c00d01500c0d0010191401c06100791700210b008060 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 501699955 1250 501698705 501698737
    0xa090e061b120403080103060c090b1b150a020415050f0403080307210c0e150a030b0d0602070b0613090b010e071404080309040e0708070521010c031a0111030d02 71
    0x26006400b9401d4020307502074000a007a000140b0410a052203448481d00b418102001428074010300c480d100e109824461111110f400c4598030002070070421036080300d43c0714400c21160700d01415120020340041c452000b0603441800c1d82d0005500071800c6888940044118500e00381c00c540700e000d0305034406007a0b1410480c06001480416018003400390301ca45401c4404a10740c0b8802c840101134519036202940b0410400706042220210641100c01d1840582000700c0d02c1c180b11000030b003102c640030201804079400050f25004001c8807441282c800c410480390052001044100203040b80c81d8018001d0008009034014010034080d050407640c00b440c0c500d01100d003101100291341d80b58010354440c40256102103010005403415004000184505000800d0450301c2d00030010741e44c607024856a4003074242ca17001049011034101425500390725400080c0400440e03110028001c2c02c04c0f4524441007540400900a1503119018191031080100019420502e40f405c0c154020761040790030400340340c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 501701205 1250 501699955 501699967
    0x30507080c030703020a03020c0612041704150c02031c02030304031206050d0b0103020901050f060f07150c0206070f091d0a140106051e07150203040203010902040e03090a090e061b 79
    0x74208020000d15209501620aa440c1403030042e107050104000c2910400c01880310381c8040050140d9070354032580090907078030101810540c4a0403403240703070418181002c100c568603101310f03000000420824401c1d400c448201740d03007404c44035001d03401c00c074040700503002080414040381c490640503005820882000850790303503460004882404151044030849100b00040080d8541003c040b4010f02c0300b80e4515075200c1c9448000b601c280300362050380102c0040400c03104248008005c09a0099000c010200b021007141d0324042d40c0c5050850351080060004900c03c541c00c0c1c4204594411562503941403071540c2e00003204650400c400408a803401ca540302002c000c80c0e595581e50a009042c141c84040c1e48000000080080c41c41c07060640d0034100c000c200036800141c883c50040c40d2074804400068494480b13200081c05450360000203540542400102e0b50580c0e000310091100e208110740c803036691aa250b10036419548d03441001101034105ca070029807009422130030a0b014488907006180361007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 501702455 1250 501701205 501701227
    0x7050705030d021617030922050c0319090506011746111c06090503180102010501050a060509150d1a030109050a060e0f060901050f1b030403050708 65
    0x2654116140c001a41302c43c0c01440000c840e82081000342c0061184612084d6101c114641c1c1c9200c1c920110707002e103029124040403045c69901031110001559400c1c040b5042c03005d55000d5640040c1c800020018129011140904451140a2149900c04041d14903a03107440e07214521210001a9510b0f180514411207000c500000d600d40300c02481940c120300c1e4030842d4003200c01310300388000103491401c10424208000c209200340c070408007682112454a20603d0b09400510304a220a00600740340c1090066020028040f01031704840c440c2035094a0751030601d07001207003a50802c0c030403c3d8000c014110180506803240d8000c02030a20060710b0ba0268240015900c030f880d6009422450710540da500400204417207005040c44140d03001c078001c0c00041c0c0715881d41600c40405550003007006581d1005402e01c4003003031020301030200040c002d43d1072074507020021034040d020489810400e9141e80340054007000c3c08012180410340c0c200901419581c4595041d0340c42e40c07117000251400001407186403650 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 501703705 1250 501702455 501702463
    0x12c0913020627010804200a08100501030b391b0609070f03111002010e0f0703142a0607020418020411030c070602130e0c1306170c0705070503 63
    0x2031030812860b040d042620800e5015142480f4103041101d03105c244000300304040303244960315403100c42040c51240e07034a0021780750402c00c0d440312900340291000e8518608641d40854101c81c060102500e8554a069a070754a550902c00100809a88425100700369007070034000f54203c1040c1041c00780341c00e640d00401100d00c44180c0c0d00f90308a0344000c00f0810305130014003154000f880000c540764885404c650754401c8600d0140800d41c0241120540045c045201b504440c82003080c000035034200c2c040220680703440d214240001d4505040d40b0896100002e0001900009020814050507240784c624101d07d0045a0322500d80b9403103035080c40780c074016a940748030301004110005918042e481c25841407000307840104c5480788101d48103108014807500ba030411200e0b0706501c10001070381c40c0305280300009100000d07000b40106080303038010409000d8110b8000d2444e42001812000c4803561054111451b5254042c04840804200d02003a450000880501140d07445101518480794544000ca854 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 501704955 1250 501703705 501703717
    0x7060216030201060b090f040513080418050606190c0606050306250c030e060703141801170c07020d1505040302010c1d0f091803070c05012c09130206 66
    0x4212030858046081540902c5004024040d1070b0381c0d1030600d90083c2c0000c52080849910a0049450fa40011601c0007100c03040c0c800c0d154403044040e01ca0351601d030709442d641c02c2032040711501403602c03003c62800d280c07410564400d1103c4008100d5041c1c4007001c201c0f0518140d510441c0c03415202c03440411a0340c0d081c400a4425000c5a4901c4100e45004103880500b00d2440952801d00c4800d01000010a510010314a542801591010782d9a6207a2404540c08540580032400414010803000da806c02c2144107964540001d03039800805000100740c0a2a212003651b00c6807a248080000c1c0006080c982d03400c00e1018040d0016014480c0e900941d00d0a580003120700310010b0355a9451a40500c0e00444405081d2000d4120103e641c1251030100d2050300c0245201846411480002503401181c0c12440c1e01d0340380340750140c0351600b400c4e2808801c00e0302036005903804a944041c1c0000603405406001d0404c01705082400303c0d10110f1410701100007000f501c4051400502d90b4190090780f00d0f1001440c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 501706205 1250 501704955 501704977
    0x105040f03032307060b010f0806100809101d06010f0f0909030c06090c05041d06010509040c150c0303110c031b030c1906050f060303070809030c090a02120612071802070602 76
    0x501b401d070400014200780da030191000038041400b048c089981c48500c62950304046a0800c11043c0d1079200c0c1840c03410754008030030078000b810030900e1450020070130b005144908005040740e00b566264800b001d2001001c5c003d58000c51300f07403802042505515000420158080d051892004460b0389178817054800641d42901d004460341c90030005070130544141e102e08480000081d039949400040e0548400c018400c16124034a80e10124007480303600c806180023060710100e4403140401c110400b4001c250395080680c003203490084070010350540b40040310030105003507002d58500202410150181c0c50f000b083c44005100610044070300440c1040840942c824150b006c000b001c2161600c1000c0d940300a01c2e0382c019101030f500b40402500c4c0041641c0d100e607403041c1525103078004500070074900000d01d000540e202d80803c0c10b1008a1006c0d500400100c945c1100454555840c4c01c02e0250700c2c1e040b04622542c0b81d05c8140c0401040c8110064144010300d00d41000d403500c940c13500c0780303804e9030402440301c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 501707455 1250 501706205 501706211
    0x60f0907050c06060f100309060f29060313081309050a061e0501090b0c01020d020301030f02121b0411040803030a06061d0d080703030b030a050313050105040f0303230706 75
    0xd46400c0400c009035000d507041312404545c4079450081048005041103420903d41c0303a201e201d04000303071900318400c6002d48c80004c100609044020072102400b183d0b006a81d24000303000300b0103504040d011280702d51550745294140441d0340c0d4030040f10341c1c06184017030032007a02d010020440d1001801080d004240d000c50120b4030b41c0c2051b020450200c00e004040900e1542014200800d0342c0011100c0b0865890500c0e891300c80b043da4020a01901c076144609290b580b0000010041003452201e01002e980240d50202130840d0681050795030303e1440c9400360b6500c00d50500b558840ca0503400c5903d400c903490a5450030659102da490b4031b5500f0941e1080009a241c0070b003070000c203521a40c0444180d540f504100070b6440d600010640700c0c1c44200740680010320004040040c54002c1c0c10180313041c04003400b1540c4400311824459229040320b004808820800e00d4000760380c0d8842c50658055460031502c504005103540e40948884644a401685045140740d2040c603500c0390501411009000745008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 501708705 1250 501707455 501707467
    0x60e0d020c060c0706030509030c0d05120903120a0e0312160215070903080d0b09040c050a0b07021804060902030d0f090906060e090a06180605040b0d0b070305060f090705 75
    0x1a08044109007601c0c040c80781070081c85040c42000070040708032642d900380041c079611106038a80c03c510440f034000a132840f074100f00701c01c020b0b4001300610b581e04209100f208951180405039840380b00705400c040c21044080042401d50b02c841c0d02a0340c0540c2100100e03881c003124520002d00701d0074210380148100c03c000140c01d83d115014440032040314a40805040145030804010340010750501024268600104420713101114a900c0b083c080031004010010034a0035145c0703800c481d40315004a90080807281d00002c0c906144000792a40c440c0d00814441c20011a0f018a650604000b4401e0b91041c2e1640ca021000d42ca050003074105507000d41c1d03164041c008440f440a071842034664800c1070b40034a010010803120f43c0c441035a03428110300f00c80140268403080910806848190014507220400440c031040c1070b280d59008004450060b282404014800d10070814150b007507078005042039200400182c9ca2500c260b00003544031070001c040c500034204038404101c00c00c80495500010410000d41 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 501709955 1250 501708705 501708707
    0xb040e0a0b0d080c0717010209030d0e0307060e0a0b041502240103120905060d23040816060f0903090e06090415020901090b0c15010e0105060a1b060e0d 67
    0x450390001124030244000c18280000c12598101c90034040d201c3d200120320003088520500200006106007500341300c81c602803410700c81c000e40c4150030261007403050000d01c004181c01354060050350200140a06120707860910280c4035400d070709000d01d070710000403480491108000702c0504090642e60f03401408079140e451029140000300302c415090030f50703402c5409a100300480301c6c180c1500c0c0e1081d041e060102081d00d0980340c03682c00e50081a4048408101c644400c5440c1c3e0001c0d80885040444400115010f0444011352800f564040c1414404000d04003500130985040400c0030b1141c1c0c40041e040c6150340444048401e40340c4100d001600b582804c1141e50050b8800ba604a00220b903443c4040c2050750b68030404800e14030014901c1600403030b100c0030710382c010740c000002090400d2400f562800c074410f0310351b1600101c0000350140198240007203486482102c8050503030341d018210f40d240a500c2c0400f900c040c441e0b90503442103d1809881c110011b4103d01519854202d100000e00b81d012000f90 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 501711205 1250 501709955 501709979
    0x9060d020a1106090c27010303121a150a0c0c09050a050703020a0e01180302120304090507050406090303050d060b0705060402040b1801170f0307050601140a14040c03150b04 76
    0xc01204968001c00c28080651000306502680170421a000361509014050444046405800c00e450300d1010200000030302d6080a034060901854002c00c00403082d5501500350500590340505400000c018150702c0320f8090040145801c05050074060300505d541d03903448056001c2500700c0741d540c40e1102c1c01d010101c2d03054011070b0b800110030b00f006c3d41050540407008004e500302010359810400940000c51a0307622480200340956000751020403003603404020f10ba0b030382d0b00500c10070100c0762070400041c841600c24070a0707034261081603980c0b50310f4500e0350700c046a00c1e0300540d02414a2664405000030005086801801400e10030b00281400d403405004120440c0c946610f50307400b680c440584ca11040003c080000d0554404481e80031f1580c0c400000c0c80d01c1c0482405445121f44400102041441b1001562504944e108001c4459000b40302c3d06100403010305105105039100300701784800c3d0500d41900198861900361900150008008143c50703107101c030a038424400100006030038030010060300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 501712455 1250 501711205 501711227
    0x705100f11040e0402040b211e06060907030504170a0e03010f022109010e010e100c090b190e1309021507080a1407060f0605191410030209060d020a 65
    0x6800030b081030300d44200800348010040c8001d216980d1108004550743ea08103c600c0a9035040d5600c600380001721185a40c0c61580103044000c2c0500c0003404d2a0b02e010000c0d42c1449640d02802004143d03d501034203030043d06d0084c0c401c644000303502c00c0280310100c2e154061301b0741d041d040d42d4051075000c409042c182183c111000e01c4500900401c41d0344248500c80701011290300324402c40c82c0340c5035501c1c0211401041c5101000c17015500300380a9400e560b000080168400c064160200002c43d030b8010155144c3c0d546100d00c1d4410b00092104041c010364119009110364045d040200d503854403800014088075006610800055503107d8080550030645950042050000d00c1e5a14207401521071400750f0003009103040400100d00d100c1044d0000d0401034414156011000303010348007200c1c032644007901e21030050707038043c62041078030b900c0c203c440c21082021a8030717004403000c01081c01e4081c41030b00c0244400d800c080c540c00300080c2d5415264031000342002d510100f8016102d5902e280020305040c400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 501713705 1250 501712455 501712481
    0x210d0e12010e061317070305130b0301030506040308060f093d030f020a17100b09060d0b150d080d061d010b030a1103090c100302071a04080705100f 65
    0x102d448510b00c0400014400d4008000401030b401c440303520b15008504600328003000001d03100110b1170b1020107811002030070242c00214181c503141a15601e040c9030501003440050216882003000c540481e01401086400c1600074000c0302d07403c50400085022b0160607500100082004441c071001c4904500c0f180f08041d9400c024110003483c1d20101916a00040c00040c1801504228510440d5501c3c4013041c020025401190030380055604116103e0f54000351031840c207424030742921503528082401912607400180451424205602c035580c14550050080710300c1030003049941681d90355101105105e40c4100c840315601d001d40824003041d0383e419484800804008a04a0300665800030080e064910510315640c890b1b490300e044802a10305841c1ca0901e604000052014040c03020031074440355074050b6800d1104207c0781c2d03000c8049209000c000350400800384c0440c1041c8015803022908240611145820001d998071402d0410190001014055507100c0c00750100301c02e0b90081141c540780c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 501714955 1250 501713705 501713711
    0x16150f09030903140717070302010206070c0209041101052217070b0304060b13020c0604020f060c030f160605101d040b0604091b0b070b06030c030c210d0e1201 70
    0x325500500914014040100031155803107844480500c02c00603100100303038414021704648096101151205480d00069005018020004009078007540313040a0381035002e800755925a580d61200d1545c150724003282410003200708291a4000010381008081e05101030340a0005403606002c0442d201502280c55402d8100423002c0028040d00829260700503003101c1c0104108030140000b034802180144400c4420b440840c07100c1604c40000303900340c1b02c0d52013580c6020440344440e0400140c4e000304100311903030750700401050100c640008050240303448440c41e101c0e24001c1c6540d4440540380102ca0035003400040100400034013003141d0034580300c114480d501110b0340c202070300c4a0706c610320020b002d0760145032201403280401065041c00c0001112440720901c0194071048000c030558088482520040e44040200f0386618000c9040110100300070010a0140c0707041062145601401e5103840d4a10024004c0c034401c3c00042c001e642202140c4d544503c400b010748400c0088041030205074490a0785 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 501716205 1250 501714955 501714971
    0x13050406080d081806040804140406031e0201030b0a123f051204140c19060305060607080c0307060e0114040b0903040f09050403030e1204061416150f 66
    0x2001252005040905291511859550801030b0040c44c4914048051501c100000c2005001e500c502600039030b182840000b07c3c3d5003205080000b50340c01c0b0701018105041424500071a8140c04910600c2d091060401103981c078200400038a40d015903511503c1852009034400c800c012006414080400e20b800149015010349000c5035050800122103207650b11003031040d000114061001d41d42d10340107003800c528291030a0b1603c0301a13958100810ba41c948100351904150b03240482503c0140401d40c42101041443d00000300c000d8030003c0d207642c4d0040001c20401c000300360840d00900094200900645d40c50005141c444d0445841002644d003a9240c664500260303004c03084001d40080c0c004103141c1050f110b1a0050b400c500c13a0350f0107002c1410043c840055031a10303036005280306d0b501a031400c110b420b0041c0303031082c0c54400440360b500517500e040005111140c0908400044018105840c900707204469807082e120004a075400d480307900806000c60404403c40c0104d95204c80002d1301809290 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 501717455 1250 501716205 501716219
    0x90603070612110403080703030c1e120f1104031103060112021807030e01060806010e070c082203020901091a0406050109051509032b0e01080c0d0f0c0513050406 71
    0x84607900b01124500c0c0c43e1524121140750308000e9901075038000c40c405030b54040303c0c0341c00350040412213600d402080000292441c006142040700d10440b4550300c0e500b108001a4501c03000800004d8142e00c4050303a56115105003070051400340c03020f103104405080700c54411404061030000e0503030081d0f507865000f101e901e0041e2280300c81c940710410310110307948590300c84204c10b601070940445081e84640c60800c000801c00000101c2038100d40c48284d2000840d12058000c47e00c04200c1031000c0d090300c06c1048165007812141c80301e041c22985a22001c28001d0300e03540000d003852400e82c4075040301511002d000343d5000303c040c40c00072104421030301081118900000a0040e11291194a1280c1e241c50401500412120111006544001c040e01c41600581c41c42c1d0381e00c071902e00c2d0700e28042201c0442d07404a490042411558850050311112820760b21581d0010031640a0110482031070f85804960649015a00038640a00381903290075840ea0110720303450003070300d4250b44010b204509061081102c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 501718705 1250 501717455 501717467
    0x80105150f04020904090206030c070c050609030d08070e03030304080c0d0207150f0e041b020615010c02060c01020c070e0105010f03111b0f0a030314060d11060d11030103060b0906030706 82
    0x1e01c4041d2800350302c9040c04000140141001da50180d04550300204008125400400804005104032100d050881c4c544090202c00d0169041d50740d0544d100d0220701c1ca0407402000055484440c45c505140e80000320030209045400030f8504684841c07000c6401440541d086c45103030302031a2644028402c55290070801c0c91600840900c0205120500b102e903041c1c640300f48903010581c03401900610a280c805004c0c1060003c404281c48014000d007004100c0c40b91101204a4940c1016592404040d41c160208541503008556100040d90300300f1444000c640217124243c010030070b0b990210001d40c94140003420000c040310001b4105898040c082c0303c620600c400760386c20900940081018403001c10b440500e0002c212207011720340d109070000281096419081003284001440c11581562540001d01040c5003511a00810704040a40211420700b480005006120100d20000c14103002c2d200804005030300a0f00161405071304c600f020380481c146007140b2a0010800d40081844511307020b401003130 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 501719955 1250 501718705 501718729
    0x30c030617150a2702012604080d140f0709060302040305190302030f120415060605070204050919030c060606050c0706050904060b0406180819030302300108010515 72
    0x202c58504003082c405a510341c49882c8403240100c98941498a18140701d40d0780d451660b0490021352403c0c8200f10f103000004a40b181551203520850668071182c2d5100d000343c20460b44e03041c10350b42e41c00c044c000340a0407090003801f82c950b4540700207c0d41801c0c0c40060040c40e0030380080303040c1401003000700300141000910341d40003c07480c5441c0c0c21601c02498228114810402c1c01401c4110200c0c0e90b400204555a000b401184130f101c032210b01d102c0c21601281501d50612941004c030300188160000360402d5000305601401141c261001c000981c45035034400f1910f00000c0d0f0001e00700d85210b030304010f040c6c0b00b01c101620f41c40c148035090480a45c5411b503a00407502601c02082004100140c0c2511141c00c0345016180c03c2c070400303455031f8842c0002481c4140040380c3c001000d11600d00001d1114005c120300008058060000c485400281c034103402075070104400e0f608890803449070000c90b8007040f103056804112112039503c00c3d451300044600390f03400981504041440488a07055a43d07895500c0d0752 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 501721205 1250 501719955 501719983
    0xc0602071b090f1a10181e090c0e01050a120905011104030212060105030a021003140f09011808040909020f100e0123030403110c13020a1215051915030c030617 70
    0x3c802d140340030086200a02e17981c07103072820b000901c1640e00e00c0061071f50700764161603021070100042403807910100c0702d9000091a0030b002c070718200404800c403846070362100384144218101241c00d9805544031801c4500c0088140318400010409100310318000624282d5010100020130039941041d0000e9111702540000901ca01090082014101c2c0203030043c1c034400103441540030440c9421468810b00850413101003040c1d52909050110300181c01450182a079001101c05046c07c4c1081036840040c074106406a03407040c1d8952120443d9a180c4046501c0c038191944c898041d480c4140024040d4003045980040000d003044000e0b11441c0c05009490b0f00c181c240c60003040340103840520504046032000b8640e00506041e014906d0322829800610003500035995520007000e11005030411500d110581980c14441e81c3c02c00c025610389800b0300580d000c506a16014111394500010310489103c69103d0040f030340b2000c5840c041601885035100512000014016410781c12405507112422462204 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 501722455 1250 501721205 501721217
    0x606080f0a0518070306231006030e0a0203010f06030204060b03010617041406090604030f051c0b0f03071d01150804060f06080a1b06050a0c0602071b090f1a10 70
    0x161507001c0322a807111616590300151504e081e12400e280e000307460000c031039125260074814100f14080c91076103001d215103416020204902e042a8040303014105881c0d80d8000c40c840c80d00d105000d640c080c45103000403c0c644000150440c038500c1440103413203040c0e1000480c2101440104081600490000682c01101d00d4894807507455103401c2c0d103400701107040b14444d485428104500f00c0c00020f0301c54001c6001e030316160300ca800c1c0380c0e508582504c070750308030281c0040c1c801c0315543c10648607400000d20201d00401c5c0c640d40100d90b001082c40c20016600401c807070b90101c030b4404807050000c584240941a40c0e140381c503206048150180440c1009407006200310307070310501c80400841c20340c402c0700508403540c190317003040d11703036040c5405107040005400076100245480041d40030701580c200c40035141e59864101881040e5151a8000d411000d803e4402c60f8420980003001202002c0e0b4801a16054030000744100c0b03012442d800301e0b42c20705800340120140c46804505503807110040f810f001d011740780c07030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 501723705 1250 501722455 501722461
    0x30b030a0b040c0f060e1206010807051c0b0c0a030f05010608070e030a0804081f0501060912080d05180c01020109110f120d0f02060c09131109030f100606080f0a05 72
    0x300c040a00b00d0b60001c031104c010800c01158481d030201c844044224115044100355000d0404140c40d0802071140f810301e41e0054408100354103102044141800c049803010003013a40a48030a000c0c00d030100c0c3d2070002d03a240010710504440d090721842c0e00b06003405004115541c100800074101c040044c060030240090207024102e2980e081200e00b404c0d6a1016045850350394800009544064914040c0010041007442003c10f03045071040764101c44455a44504461424204041c1415000d00980b0b4410307040007090740070b4100e40101f80c02008202e4000403401481011f00b82008600a1054116410030f800000841c0a40841040000041b0b5005074040102c0c0001841e41c0d498102119240c01781203100c0c040c40b500b03c0301f503c0e0220b80c1c94080c1c40e02ca5450b40c21355000e5228000250303038825168440441584220b078842080c1000f01d58010313180000950000b860407100c2065081103038807800000754048032600800d0001e01490038143d610303061034078040c3d800348001044008000d94580c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 501724955 1250 501723705 501723713
    0xf040b120606090916050d14010c052508090105070503070c0e0a0c030c3609090b10120803040f020315100504060f0b070512041e0b090d030c1b08010b040c030b030a0b04 74
    0x1400d9030300560300004c020ac12240b20b0042c0c030302d40100c0400710340b4441030a2040f1034201c10039008a90103901403100351402c1001d40041d134041d08440800c0d19107110234094400000c05482e00702018188010800b8038501c0e052030b80c3e40544540031603030402c05080c00d0301000304580102c0310311490034021000202400517800c240c0d10030006002d4000c0c4011042400003101200c580c40403150720700035000201039580ea50b5080360360703800d50f1284030609000c10030608086045140030f190440d210317100050907403203150002403a021080084090284029091004000752001848024442540c3c103001103440d102092140c0683c5100c0c1c18503ca0001a00d03804000003401140b00d020748107510140c5481e00d07104448400041403a02c240c0401c0080b070049924030804d8191002e01c480201050818201d650b0101c8051443d10800c496110306101c86403468650344c1c0011000d024040f000080c4048050104400d41d03401e03c4c0440107152800c809a4000c1c0c402040c00d00c04150051180800703500c0e2450 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 501726205 1250 501724955 501724973
    0x90a02092b0f02040f0f241512090c15120b03031b0f01060f0801050702191101020f1002090418030906050a021002180f04050609060f040b120606090916050d 69
    0x280303903141c0386d260813a04182c40d00c07654402c455640010001107004010120442400740540c014800d9000c0d400500d075200c1d82c800c0c001d032910110481000314144000350742d1001c00854507000001c041a1010420624550111000300071f4031203035009002943c9048003080d00c0c0d1180c2d0303140c4025000e00c07403840a24040c0030400400c5004c402c0008206c0ca595440a12200703d07500e001d442c8140d42028041740720380c1e200203909a00f024201160f001021966626182c81e0f8103203050460542c020100c1480000000780100070200c01c000c2800743e0b50740c1142e4200021500824040c581180300a504400820b0303010309240240c0d0b501e400c00550700c1d11480010391801ca00990031900c480c1c0000750040f11441040c4011054410a585104005004078100010340c0c4c0b003110600d8105581c903000440c1890030307201d552240a0094070000303250380306001041c1d6188280207140b4050340b10205010440c24120843d5034015249005000ca006400c44d410403c59000d12a4602c50b00707aa01601003400b0480d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 501727455 1250 501726205 501726221
    0x121020f100c0b0a0b03100c120c0503010f050402180904050a080a02071706091b0f060403060917030403020c0d08040b031014060a05070f03030b090a02092b0f0204 72
    0x200500020310103014020400c102d82482100d03401c080c02c0200315007141600035134a50540050150910a000392a01d400070f00c441d400013002c10900c621181c4000a080c0310b2958541e000d90b8070306559606241040d000c100255000310300441c410007a0400b5000361009010700c0e1201242d2b6101c107603d403400c2091400b051600080c046000c001403d44110360005102c0d0111490a801c1c040000d01c40c0404940710a0b0444010801d504171400818004900e603211400001008045081d074980300c5000c5151034005030030846415659a42220a025004458131014841c50740610b10b9840c01da07800135203d02d64136070018054404401060100710400096034040d03e00d203042030b81c9038605407044014068a0344201d138403140c1da20700240c400e424000c0c100e44e40c10005481d11803500b41c050342c6942000b10201c2c0305504140e9541c8044030107a54a07281c2c94054013155901613201c400d00e4003084002c0c601542a149062030090803116102c80300c0249048407600090700032070071145800445d01a110700 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 501728705 1250 501727455 501727459
    0x13090204091707060c2a03051c0f0e010203310209070314070e0321040902040303090f140d02040b0f09070207030b0a060f0b0a02030903060103060b180121020f 70
    0x42101c2e00c0107240032001819200e070140100740304402d580c00d01071760030707070400c4055042407810000b1070940c2c00900807030700c0500d40c0729151481c41d1922032030f40003103504403000140341901e1310307001e152042c1c612502130541030302e407160021491401d2000926400c0340e4a02012043d80b0b5240018100443d45002c4040210350007a004240e1442d01030001402003002003521000381c00f410001c00e090601c18001840407420150081c10b0f0015080d0345a064100040b00440120000704800701d40b600741030001d440150b100340c42d810005410f041285031003403100d4010f00e03500e280c120740002d99a542c00c03500014098050311300003044244500840c018002050740030b90020300312014000940d90001d1260b044a000740804030a0f40c072091140320940d06a44504103803c012458180000c444100c002d1044030003034012685807082c2c1002103824840264001e80d200e55444800c1e2040d030901d40441c104a080c8100d100000c2e60401d101c03454602000386007a241540348206040c219103c0c2040c016841d030340 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 501729955 1250 501728705 501728723
    0xb190c0303060b030f091b060f13080a1406010626060402070c15030e03070803010303110304030510270201120c03020f040321020a0b01030809042403021504051309020409 75
    0x842405c0701071000060310054500d20034824914509560700c64800f41d801d0004158901e041c103104160710482e0000c542803030009800d10310005002d8070411803d1040c52103803116594805941d41c19038104101680031000b884603ca02c101c442207986088a81c0310f074014044c0b10301e20b40311100071a000307009100c070051460100c14008201080440031400e261070055400303014002c0812101c03a201e00031010001c1038500306000500009001c0e0390911040c1d003008007145e05150f500e40303420f440c06a80421941d04d080d0f48000d8107560041d00851420340750320390260030305d04d03501c2780c2e000900068017402402d40f07541e9140780c1462980c1c40307901290f8071149a002c100b0344440e01c2e400c02c80040c08060003000c02c9110b40180e81003186c1c1c000b25001d1005900011020070503807841d21070f04825440f041301594801c2d5111203180014000c1d40b07440101c1902e0301e8202c0f4440b41103105000310a41070240d1140d5509091004104543d0f41c1c0344100800000420046002d404038404200a010094802031072480 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 501731205 1250 501729955 501729961
    0x3220309090c02011109130b090a0e0601060809030712261501030b1003090302031603020d021e0c0613120803190b1c020a0306110d060b190c0303060b03 67
    0xd4400140c106841200c07004000c840c804038401da00301c804a00d0012200881030144040a1601070585c1e41c10082601000c540c0400c0280002c0c9480c00444003192201e43e54200c441150404100040c007602450400c565642401104280d0307074041c106008086031140209130003180d00c11105011010a0703039050441c01001c020480c808100d080b24040300341400940c0a50803036100740602261450040e10000c101c400d0000d04501410070417006405520040141c0b0450f950010052180d260107507002d010544030203503000381428100e00c0402501d03d592510081c10550202e440c4107170487c111130031680d40c40014210034040e00c1e5540005030080440310700006100444c4000c521403010340401d1151256200c051404850750000c040350800b001d201c0c41c0d603640310380000d40e814890008007031040c1c0c05d60b40e50b101070986541e2007c4400351070b000301e6003609602c00b60042c28040d0028600c4282004200ba84002d11102a4040741c020001c800152206050080e80018050000c0e089101d59a20b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 501732455 1250 501731205 501731207
    0x306120609150f0106140304060b0a032001021204141c0c05090a0c0c11061b011a0d0b1b0403080310150201140a0b040213171c05070206032203 63
    0x300c05502c2109096507600000791889807182c0b14907040c2c90317083e20744580c0c0c81c00c20014400039401c01881111550307a15103141d062584d81c40c035138034011031040071407000c003103144081000d00020014441e81558003450a01f1441a80c14064a0540e4a07540300361900d41c0030380001a800e5040c000c42019140d8202014070140070340003044409507881a1744805444c0c42d1110480e080350500c41d00b60300015116806500026036508040700c1d045d40003442107003406101280f0525207105c80a281ca803da66032886e418034841002c0f0410034002044945480768102a165000c005000a080307120000403c000224a92070070425140034681240c001612454403544070000d8a0304c0b801104800d11000102ca034920303105004808460540f03420f995116240c0842e008040c08a0707408580d0300c16024801c400d000100600e68000800c00c20140c01d107625804480301e400d0400592803070100d21107414034424215040022101c0655040d59501d81d03940c0c03445010104403448000c034010780441200094289 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 501733705 1250 501732455 501732463
    0x50f041e02180a05090a03020a0b0a1b0f02070914010b031314010605030601151e0e36090304032d11030115060c0327120611120c0306120609 62
    0xc2c542d8040801160300e400d074401d981d980506c00c0c01001640200450400500d00b40600e03904aa00e880012030500d000c0c2055480d6000d0f0750700fa01002030610603103c924560704010840080404c41010440040704440206032550140110001c0000000205030001d019441d2618a59002408840040162600319000e86414030460303119110300700000c40ca4010042c00d440b0801043e80700d02e00240c5a4911806110808088500900041e2070b0b1103080c64540c1410600f21910222010982c00108543e0316240e180c40c0c94280764119401c42040f46030302c000002c940c10f89411410441c03000d040038109000c122040007444500c4130400c81c5000402c04844000701d41250100c009210488031503100a00701685813003800c00040e0742110100119004c0d2100390140e004002c05100001c408400c1c1450219280d40101c130781c1e5001d0791084d0113100b601e100e811b032014800b484451504020f401c03d0b90904901034080c010024001010958965440c0041e00d45c02581c50290340b03842c6424009a611 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 501734955 1250 501733705 501733711
    0x7050607020d231c0c0303180c15021015060815040c030203090114060a0b1308030a05040f150e04052205060603070f0b031303090e0c07120201050f041e0218 69
    0x141e4410342002c612412104c2840d06122903c039a20500c00d11201d0304e049020b4900303040d9074000c00100c00d103110045007818030920003a2280b86550f51040c003c10000a145c0300001c0d040c00031240ca0301c1104056905903824002c01c9481c6450300542540f1401503007000341428441c01e075401440c008100000a4240e00036511501c0401e0003048554030b01c0900495600b800c8070b490fa80152002001d0003c4131540700a07141602122120304c041e140c550803c0381c030310f501c100b1060f4041800800c0400900210400d18406005009000c0c40104100c840241c0744080901400303100c1c41e25200064010356903400c1e018a030319032201c0c0c0c540000c0e409041080d10707402c0a07100c50740030b4056440003055001919820108856041907010b02d5940c4498403145000200c20007101084584c100000d61102400721460040b0103070a21250384078490300d0300d01813039141241c205007564146400c00c03010200d025070046d44260001c0586c055a02e10706010030a120010170000e511107505500c0042247d2440384c0144 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 501736205 1250 501734955 501735023
    0x308040b0f09060609090a020306010f030215040308160212030703031505040908091009050d0305030f0f0105061c02190509090106140f0a18060305040b0a050907050607020d 76
    0x800c0380ca411a402600060482d8111840da0194022981c01d052014519501c44110415142152100d50001e420000c1c203078054484a25002d4081c420f6280a40890304036080290001e0314003880e6590314032150050700a02d0450003c4d0000010654540e00c00c0d00175001c4001c4142c99641d000c0b4900030b0010103044070021070005036a40c0c00308080c102489440e09290300a483d8904201131070041001860b00001043c0030490040e2000465403181c40c3c40c0c1007140e11a4550755107901e450788401c0b0500c0c60041c0140c001c50f11540040100351114004c8038000c81c4540000f5440000c0010080b01a1040400c414425003034114a061650350040161101c0c180480340124166078a40046507600f079403507518504901c0030003c01c0c0c4040c104400402c04404a41040365440403610110408040030345d200300080381e2281e042004201d84001183c7e88807048202c10030540c01d007150601d079541302600845000e02030008084d030640d65146000e012199000b2581c207900c0380d55015031003400000c090031003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 501737455 1250 501736205 501736223
    0x70c060615030f020a0c11061902150c04120f060e101d12120a0f2307090f0b0a021f140901270305071505150f28080703030804 56
    0x504500064021161781c1e80f41c2e669090070b2400c0340e44480303180f24046e548480c0c0c0054104800f0040700c0031948505e10344042d80e005400030503020306075410400c000600c0001c6c036400410003405410180c040800c2100c0d00300703441801c1c0742c400b4500500101032132204000039220341c20255011005542243c0070720f4030b10501d000d13801540b40c8061540c80e07040b19842c00711002d0505c01d031501d11070040d28150788440382c10380100700b070302c081a101c808940300342c15020f01501c0c1c000285410341c05040c04a5400c1072261420b050203624110700c4010004a5000751422180c0000ba4844654420130a032811000110190051241000c403032400501c202011500300881b0500020075101046c03040165451224041180c960440f888038001c05001c55001ca0501c0414480e080c0440c070303a80311a0324480e0510724006940c3c04c020615000a0b5216000c8074811400c0001c400920f07102e14803440110150351048001403841e000c0783e000e5100542e00109002d104010000040c194800d01f05402140608440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 501738705 1250 501737455 501737471
    0x8010e0f0604080f0a1e020a0605010b1314061e0429160204060e0712060f030206180a03050a050607030c050f16061d03040f06020a020d0b070c06061503 67
    0x91074407200100d030040e020310004e00102c0301020b040700080001d201c151511014261039009481c1d44101035055000c0140d1000d1180801c10123184540d90240c030316040400e083c56686000f1691102e2a1302901c110401404d00040047e02c03028140c902c00c4101d621001602c00d84100070494640191045030710a000c000c0c2804400070840184025551000300345520342401803690101011030301004a0f002652400d00041c460082c2c0086c0d40501caa940e500585031040f294450203a44140c0c019100072024024104010307034500049401d1050420390b2440c0c036120403000116804030760390000e4014040e16820008028012409a00c00c3c05d02e510300304080a10200101c41e070307004008144003941c0042112144500c0d0030004000d080340b00b030380c2c0441e441c9841d04089548030103403a6820415400414141300c4080310a503404040d241900c0200320311100b0350000303000030031910009081c425130704020800d40c0380718580985032590000d5081c00703201e68500102d500381410100c0500024501110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 501739955 1250 501738705 501738733
    0x210030203160e03100608032109070303120209030f10060e130201120e1006140319080315091518011a2203050a0b0a090507090c020f0708010e 63
    0xd4074011451525645500461848255021a8030261440d403600c03c0480385d2181d0b08642c002c6002500318040650303143c101d1345229807515480f0550165051002008010504030000b0380001102c0c1c240c6041031610440604c250002e1180f500b00b19010b001c0e000c50000c0183c2c4c0028522160f0600500c10040d082e41c0d40368000c0000d00030344840071621385006107135001d984104001428140c1c150000188d40460600d101d1601000365410600c094991600304040c10070105403950701c440540251620741d98030342000d0300030030f819a00145603540101c0440c2d99031001d804421404070303002e010075882d03052208031820754944002000788140380030f62000d6021070040e100c481c100d80021004800c0c0100702d00b0420a05c1d004202200c03081c88007507001542c00310408803070030300850140d03003e07124416241c140b46502d4500240b0041e1aa814001074000090000484004844803000006108455054103d05041c10060a41d503036105040000c100340c003041d4011041d010151040710500582c0300701e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 501741205 1250 501739955 501739957
    0xe0f0108030a02060412121a0a081b04020f0d0c090f091415030a0b0c0c0f1b010509060721020c1c0609050703020306100503210304031d06070f02100302 67
    0x250580141c201901003400500050a8010102d13402e040418003103680c813803000221070a4010110081209048d21081d41c141401400081e00c6190060304007400d0810316551390a040c2c20540c0d002d154001000320a00c1c5200c0145c44204c0e407075000034855130700043c000502c0c0c07440c00c1c06070401e028850070002400f2000c9101d00c0340b00d05520321003007600350f0700d4010311260440801380d50f40d05401024054000688205212071007200e900c0c00d41034031500d4001c03480380781a1403c49000d00c103034001d410741040243c4102d0305020518003460041e07510400c000100c0c249005190004044d528101d40c07000e551010b2040c00c440c40c2806600721100c11480c48d040041d03c10f1052990141081448a05800302d285038020884140c011400caa040603030380d41c00b01e85049421211040c0807208003105101a14003480708103140980381d209140b00d071659210f110400d03c0081c00003020320061240720541c0703102030000900b40f0070b4000c11190b00da01c5141001a01041050310072485144c0d0003034200300700f9000f44 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 501742455 1250 501741205 501741217
    0x2120403050c040506150a0201051504060608010b031b0a02010e01050c0414040e01090f0b010906080705150c0c10020c011407050601050d14070311030f0105010315020715060e0f010803 81
    0x70041079030701040000d000040402402090300003040c0ba440051628524001780724100302a40000380610304203400003c1e8050b004505440380e82495020052141d1100c2035606585407203503282e50381d840d100307030b80f07580700c455444410301d03d180201340c40040d5138066020742c00b00e03110030303001f44410307500d650000b00345200740c0c0640c45411001702e402c0c0001e420a5845180006450700001400da0001d40310000c0d400c6500800b200c000703541e00014800c000650284000030001040203114450800d0001414141000801901004042801031014100704090b1802c50400f40001c42032541c020710081d02c070f1081814042c0072484444c00c0d8480b40340c0a40499140c150403201801041e402c0404020210520400030b441100f0092001072440c0c601303202c440000c5125a8104d018800d006040c5420800b20b24546803090345468010004603400d03103c40c0c1c3c42145403460050380c9000a14180b00008100080c0c400058500000801e0045190149030b001381d03141a00b4480d1aa6120740e1550703a44103130 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 501743705 1250 501742455 501742463
    0x5131104060c030504120c0810060b190e101e020a1a0403021005090c01110114040210050f1b2505040c0903050d0207060807020109020315091c0302070302120403 71
    0x80004000300c41c03040c02e0000c0000c0c80381c41d18503d000d5484005000b00c80310240140c038182c6d1011800c0100c5a01000341542004001d0001d0250526010303e81d21140607043c400d0240020340e0140001441c0706082650010500403e00c0c6014040004000c215401e0740c00302401100c80000318040040c00010180716080e80450540158514071448002c1d488014000301c09600c1260b405803800d080701c3c05801c6c440c410650042c0f41d0b03810824001403041d000d11121a1035039240248000382c3d01084151355510070b0b01078030015a180c425134012101c0d030dc80e805240d5081c6002050b01325154400540b002c040039201821510134004010850003083c5074034400c1d008090010b1402c2019040c150808100300710542450349499a0b42d0300c680b400d00222200440050b0064401400740c1d50b08216403907005800d910007004001c80580c08240c0e140d140c000c1e00410603802c3d030002503d014042011030b80c8607400e40b4840c80c2100b0b00c410054040d401442040b800b50044007000d00c8081a4001035400301c03500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 501744955 1250 501743705 501743707
    0x1050a0c0c0c1203030e0d1101050717040222020f04091104060f11030702151c0204050a030b060402070f1202070506070c0b030a09020603010f05010908030c0a120e030a0309051311 79
    0x281007160300744480c003c5411030a250b100d490060290405206504901c0300710b48454400c0402c0c42c008900316000102504140305a003000f00320003627200c000070b0382d1055059581c03001c031100c00b0b00c00010701d03440c1360a42c2d01c2c658000503400c40c0c241c00c2800541300321400740070203100340104043c0d052102d0146006100c001462014003c1955201c1e4107960140901d06055038548096600401c4001e00300d01c041c0650458000755001e09140710064134404440780748400c60030719050000052004449101c0508920022001300d24a9501c641c102c0d26541c1c0d001c220129400031510300340d003110720b0410414001d405a003800180508000e821a804554802c0ca00e1900c0c5081440e420301a800142494004543c4e5824820040e103d45e40214040d200381c0303000c3d0140f0391401c4001466040d0326081140310f50014011502c02d500005242d0741111390061200c400407a40e1102220384960b5003014075032602c20360030144241a0064440c0c0182c034010f6038803504400c0c1950f2810301751020000199001c0344 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 501746205 1250 501744955 501744959
    0x60b0304151404030507120c020f0f010302040b03091c02010c020a24060806090d11150601140a03050f15011d031002033108030105130b04050901050a0c0c0c 69
    0x182441109010500008002500d110b180d20405201c0304121400c0300403442c005144e500388080b07400b02d083e80100d50701c0c288c0306da11596030124050791100d0407001c0c06000e90400d80c46017680260152070203801c0300d082054989c9081c0c0011680c546640512101d040070000e0404401441030043c000d00c01c4140d00103155030769080d990715181004442074400c8680415400c440852600d00412006280301c1c1d0091031103080508505041071000c0050b101032001150765a50728000100c4c0d007059600402c9500b1040f0340e03460b0010b0fa11040f001c00780c81940d01d40010380034a8242c055201c05d0040c86102c440350940c0d40c4801d01c01c01c032555000922404500000101c60b54aa184501413161000150a0f900145a0781c15002c01360b81050311800c5615540c2d410414a25010b0290850f84418400c545103401c50140c403203494610060281c40d020305002e18551030f03088060b8001103418980900200454602100010700801701600c0c109440350600c81d802604600c20400801c83c25044120300e18824 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 501747455 1250 501746205 501746213
    0x5091b090105070515010e0601020d120c02010b10110706111c0216030b010806070801060f050306030a0f050618061905060a050a0308040305060c1204031d0307060c15060b0304 77
    0x40c1044003294108076040002600045061000845a1a0a40c0f42103002d506180031500100e00c0107101034110340c820102c04080b164000042a1605040e290016410203030700c0049025005101869820100180c2d82171140c650000d9990090424203050381e103105e858400456154155125001c02580410203d410b008602108400e10191500403901c600089800d400004031b520f03842039401d0072480b00100b000010601140b40d00c10b0451500602d40e60601201400083c3c0109420040150201c00504d10740c80820501e004a5000071104803058417524101b0754403482111141c51608030b000b250394143c1c0000a0007409000409042c20b036090f99140718800401c0d0080106a00c0002e1034070004113504c8a95100001d18080c4044960311800c1d030500514080024180317140c04107081200120202c40c441c0100e42156145c5412400d4a400b1044404076407506242103905009040d0f00085140d00901003000302031161303d001c907100f1043d600100441e55148900e284400302000010005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 501748705 1250 501747455 501747457
    0xf01090507090e1e0a0e1027030203070f0809040b0a0612150513020a1403010302011b0602130816050307120308130b07020c09010503061306020f040515120105091b 72
    0x108820038840b00900000510300c040c080c4e4240c41c040d10f050f41c1c4e138042c10b00340402070009031460300312080c0501c00048058071a0342c0811a592050440b4408c01002604152080c000ca6041607044482c0c800a0142030030010080c0e880b442d01980f04a10b810500e080f0b900700f81003140c1c111041929242000101072460760050310702c070407140f96420024200070426545140b07540c65400c1c1109401078486494150207010214400c1040c2d2116105100410050780c1c8000004400e00400d00d8210030100d00303191000181c0100076814802014a00000c80d06040028411440c15402410912842d80d204189611912203001e01403107019001100d070082405400e034290040310030304604030881d081c0e4540100c0c0140958825005030440f03504032001e40b83c0341d407005015120071005044c8600340b10704044000260b4100041c03441c0d03000700360000c48110300310070358000701406418061205c502912004080c1d00101c28011009503800c00840d80d82080c40b00c25103c0c02d0705510f81300300c0e80c4281d810b010301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 501749955 1250 501748705 501748711
    0x80f07081f120b010302040b09040b1b0f0c0d140a02071517040c0513050606160503040f0f030203010f061802070804230916021906090503040803030f01090507090e 72
    0x10506211000040e0302d102000c40140e06030080b030345440d032541940b04010541d031012003428030409c03010741400003080b030110301290400200750746050070b1002141c1032a1680291101000500d82c0455010000c44001c600304640c08190342d2202100c2a041e5000145e40c0183d001c0040140d102e803070184034200303c10485000c0840c00d130804840144e4900c600803a480812101203400d288010030420982c00e0890a42d05c0d0b80d481000700f40010301d04040801ca00c0d000b5010400b407064070242241040c02002d104803000707840b0003e00002d0305611038401009034141840200c0c007d610b480103152a0100500c5044150f034056008443c90702848042a4041c0d0084003040e6540c0c1410000040e04c800110300540e81343c0f2441580c94000306907242007002c0450700825200031100148842c1e00e5442c0e01182918000c0c0901c0d051894641003401c0410040200040081036403200003001301700041d000020394810003614503520300356030300ca000050640744140c501d071001c03800e0b16506101c000c020362803840d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 501751205 1250 501749955 501750001
    0x1b160b28180204020a09150f05180d08040807051c03140a030213060306060f0306060e190e0c070b070c0f0b0a1812091d16020703051606080f0708 64
    0x1100040030b40028089034040d50751a000300e0125241045604160b0800c1d4400b590181030000700071851040182c214890303c260107030f220400004c059243d95072031081039404c7c0c0d0070000d42920b0703607260303384940d459401d405a980700b84410300881e500044018010540740e641592103800110820b01d00407407039041a008142170580070301c9003a04210440001c1002003140303540200c1c645141c124040c02030744500d60b41104044c2040000d0121b250050307080940c451042d1100d00110381005410500c500181c0c00c00e440f24803200c428040310146103c090003900e0300810254050381c03100c2800384e890303807850320008040d8121b0740503c07070204031140f9070a9030044e1404804144442202c1d804800306814110480781541800c00d648807095200a61030302519081189588500e81ca0b03205030498100100114015292000080400352090017200000c42e800001c5030205030842200500c101c495016842c0028803000016480179601112903000b24860740700e50025844003411500a1110f09012078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 501752455 1250 501751205 501751241
    0x1101110c16150f0239010c0c1404020405040509010c09050a030c050607060b21070807080a020d031103030a0204030209161b061b050d050a0209030709051b160b28 71
    0x5104122158178400d071410020380d04004601c1c966810640f00080c1030001e0704000f0002500c000103082a0b501409840860341c14180654aa030f00040c0070b480f440c1c108503086400e00382401036180c015044003171000043d483e15216aa102c1c801c1c880340c00c8152001510600f64120200f0090034140020490540070f03a00c041401425080455042e4021407021540750340c880b585200c4907403050000e01d015088010107806107070329101c40d03e5511060760b000070b881001660611000c140c0038903800d11412082c0d200342d80c0c03285042900040290460303c01a805084103a0000305005003104000511f22403c0e11b660340a00d6440041030fa07800301981040704d2a6640e14100021014500c0580e102804583c0e5040da69070010601c400907254050178151040d070042c0a040c0e003d940210303030a410390300b01c440c0c002020f50364a1400d944035464a20030310405480098464080742100c07101709010360003241c201d00c40c0c0d202d0504200c5c4c0002000803031844070205d001d01d020b24112039080f641758081880c0b508 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 501753705 1250 501752455 501752473
    0xf03040e10210b1009020403080306030c0a291908070e030102120106180b1605010b040c0f11031204080702100e06030604090f08030708040b0f0106080103121101110c16150f02 77
    0x24101b00e03071050700141d488010220401131146000c001d4821100c0c0240d404000a518010f400c3c41c4500c1904201d10b55001000c1c01c8001c100402e100b0380e9031403945107100d144a40d18114015245480c20380f041d0300010007207241943c0300c1c1814000c48260b40c0a450002c2c0040c0e103400d908880700c00c000200ca9415542d02d0000061500c0e40c0b00107029813142c10b404030003d0b80542d1403d2421181e02e89013581c00b40f814001d40714405031b0030103150070403800242441c4450101050410741588502c06010002c0701d2107405000610010a014000c968400c1d5001140f1000c010000d481240c010240c040e407007141000000d5940c103050700702d00f07129403145d8500342d40c1400710b0b075505a441d00200d03800c60000307903400100410320103d810082e400c2451400300c04001d505000c2c0c01884642c05000240402d08604480c0e031095108071401d00da80341000000700304244100034088076950082d14070b108107104910410700700080c00d0041e041103c4240b0b08100140500020036aa0008130903448010350040346a2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 501754955 1250 501753705 501753719
    0x122202040c120b0f0d060b0102031201032102010e060103060b0a0819050d080f060103020307111006080c0319060c02070b120106020d1d0d050f03040e10210b10 70
    0x280c407a441c109441d100241d030201d00108003180c5003004650300c20b11138100b02040315100c41c07441142e00d0b500300c1404030b40b0490140c0141e19520a0380c90b0003c1d000c004000000c240075540000e02e035110101c0d074401e000c1c1d40b058101203090b22041162030320103400c02e900420003e00d440c0d100c0103900c1e034080c0c407402d002c55982044a0820104401d1003660204800c0701c0c0040000500c14403002d140c690618900034100041d951036503080c0200707401c4c145035000000c100858046d418004a008020003212414165440347c03d01502c8a403040c01d0f5244602101c40c2002e03d004510954102120111220741c9105030b280c0802500c000e0a03000254003c0740b0700810180032100081a245c440e540700c1e07030f10b03652400034004d14204140d500d55041050040f0f0212115100d1103949074103072402c8079400d071020400c0c01c0450500d086140007030a14400010001030f040c94402d61540b00c1da0041141c5452150754404105c1c0b03405864030244c4803401104034040014004210072500a40341c911466001511210703 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 501756205 1250 501754955 501754961
    0xf06090b030d020102070b13060f0219021005060f1e0a030f11060301030b010509151c200612130503130509060103060e070c0503130905071412220204 66
    0x908011600c0d000948003a09080048403020b5a40d031000b1403424003070780c0700e54500d203401138201e501401ca0851a9824040f454203c0b501100f807543e800c40d51203002401a031005941805108058050840305005854a0f0f1180c5482400702404c00c0c444078010ba010818806000b1564114550a8a00111890311108a44000f840c4501c2c103103044c010007418419840c803804002d441c442c100400042c00003c4608180d141141c0781941c52440035114000c109001e0110010240d4104156a51031440f802c0700c442200495801815040c9288402d0035001417460031008040d038011004000704200400035104c001c1d80040c0e00a501d800042040c0e41c3e460550b4070000c0000002141080e0a1160746011900503410403400d08040003040c1c40e10143e854801802042003092021100d401c405226092003140e40d001090030300103c02c152101a0314000300030070b640f4240021411000500c000c0d0130304007100d0700e41040c1c40341d031461507450200c100110804d452108903040311000044005881c1c0340 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 501757455 1250 501756205 501756209
    0x6010f032a0c1a161d040c030506040b031506010e01021e03030414030717030c0d0f02190c0c03230a0b0105030c010f1706040e0f0a1b0608070f030f06 66
    0x90b41d40142d002c03050510f502e240b03a00e80c43d1500c001071068240040d030745003040b100d18000c1d13681c10920f00c0e102010b02c003070040400c245000c2c2e4025042001d078004003030303040e406284607140459040000000500a16a031031410720410702c21002044082117580d8000c50940200b9003052040b507980550ba03152816842e401c01608008603070011040c082040001c0c521000410200c1e17000f142000c01984840c04203085070980c048098000102042d0348150318002c03552841019601840000b0041c05084d00a510032117980b001510400320843d5058820f0000240d0700340c0040329002c01e1821622180c00460015444040b0310700482906005071000b44046000e40d8002c00b4200017a43c035100c14182051402c40c41d9a0402200050451905d90050381004e500034046040c00050340c0d070b507408600108860301a4200600c00c41c01c2d45140c0c9440040c100c10081c0c410003900d901000901c88031480225903005103c041110440012002441000b03526407010b200d10b80807803410101207046045850513 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 501758705 1250 501757455 501757457
    0x3140c030f160302150c0712030b040e0a0605060a0b18040603060e0c0a05031609050603070b1204151a01030509101d060603030705120a0e060f0307110606010f032a 72
    0x10741220003c0c03513014009000400e110341c0d00110107103800c864144103403140074801010080c020340c0303884219210368003014403d44090020425403c18007a40780d907131841100112003080c00c240000300e5500300020308000b00c880385402c250038404800f444003614005100381c1d50f04203903a0100003000c28100c5c0500c012410700b0310007403e961504001030021043d500d42049000e94000c01d0200b0400342061300100480c1c004c030100180b591034060000341002e2144d44507143c0300380046000242540d51000780ea008502c1181c10b4502602581d04c48000d40741d020041d60100309828050407890350181c0c1056500504400c180d0380840c0f07625078480201c1c0e80030303001d0395020440d00500050301c5004208568104408030002c1d401d004aa50b109603440130500c5030035a04000c0451302844842c01a0f2000016003070041075991180c1007201d080d6401c3d001110b0b128000780e00d201082070341800218107903000300c0040e90303000704c8a11030f5442030380030b0b003491f10110741c072190050320b01448048140c00301c0d0791441207 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 501759955 1250 501758705 501758737
    0x10c1b060e1f0806130b09010f0e10050f0909010915020c0d020f0c0409021302030a0c030617250306020c0f120c060411121006031b0303140c030f 64
    0x40710050012101c6a0452180060404141014015004051a0351240e4100c508040c42c00690040b000608052500103800c5100c4000105044094100848c00d80d800c001c102046d680e10b06880c0c0704c00c0c1e4483c4c859140c00113003003585d0340071078109030402c0c0d43d008000c4000803d29051940d40c0c508080303142035003c0107040c0d02240d07a440f00341d410b0082030055807280c4010201c9002c00a201600e885070030540754400c91703461180808641354050042904000204210340700c2c0380410320400604001030403100003924104010441036280714088200103280740080413003010000c0e0041801c24900c0011803000c01c20400040003a02d680028800745c414640681100018808080d180080c0500b00c20050242070100301d0702c1002c0011116401034008155440b040e400e2404070b040401000340c2034001d4000c40413698410481a08403200300c80c03041040038821a066901000d0030150f5000050005502094010840040304042c00c40180c200050702e00c2c210003501c0400b80c0c0da000c907520740d4205803 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 501761205 1250 501759955 501759977
    0x50405091503011b0e121f09020117040f0b070504080d0918060b030c0913091208100f0b031012230c0109030212010e070803091f05030402010c1b06 65
    0xa0a01900303401611802c190a021341c8080000f030f1108a29130140c1d4016816400d0b42004141e080092410349140041e001e5010302d0210b21101c0640340b000000da0102d10403000028014040500b1603100c1c03034000240c0311f000d00c4c040d40e801c0c02580d800341a034401c020040c0400301e00008144100c00380c030b00c119116941194a48042680e59450301401d20200502d00481005003031009822207600408030303c5001e940715070840025040c111203120841c0c42c1483c080306002003000703141e5442204e5196031200c5049507216011a01840018064402c160102e08420800701440d03c02554100726000d404141c402e4507546022414155060103a17803001800c1301440741f102a400b81c0ca4050f504071400351001120003800603114100724030000740100ca0584900f01d88000a501c0110150741e07030401d8441403980e81030369a40e80d412559042e80b0400110003060300102030b1f140000741c0b800803622040d040d0b50f1036030019207421704c204000741c5008101e41103800036242001012005405540c0311004a44 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 501762455 1250 501761205 501761209
    0x140309031209070501020a080c0a0b0109020d2405041d060a020a090b160807021207180c02061b0a02120409050114040902030a08030a02070b0c0306040b03060403050f0a0504050915 79
    0x1c024200001540008005010503603000c2508440b054221104503612400b41090354a003a1070780902030020100d040020628010980081c1210441c0d80c5042c00450740358805444400460488100c0503010808100940e04054020042c0f00d28800c450907422030032201c515003000310031140360030030950016841e4001600002210007400d0f10175000b60818111145100100340a800050410440801c9005c210360b05e8028500700715001c60306139007206030b035103c210794040242c00c11184503e00302501c0003010784c40010101d10803d0380107100c25440d0741d404405c022581c08a10003004500620b2090a4420200ca009100424090100003200d40c540351220044a48208240744198180780d02200503a400080c1c0710602604052031944d40e4030340c411800b00074890140000c0000d242c1e002081081d500b040040e601c140003d03070b42484a15000420903845040888004011038424400700221070038034000b030a580b101d10b04000b490306031540c001505080303040b289201c200c00c002c40040c14078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 501763705 1250 501762455 501762487
    0xb0d080c06010e131502030a092004060b07080409020a02030705061e0a1a10020c040c0c0213020c150402060d0e031c05010b0d0f02090405072601030f1214030903 71
    0x107900c3d1308000c090396125a9501c00c3e03240f61071181c405095000300c085241200303241d04c146038583c1d000d048440085201c03004560381c1e9000039007181c0718524000000908403405802c9942c02c2d540705013160700c0c09050a100000170b41004000b00e0462100303108604c00941e081024134020740c684070f00f452a02e0744804001d140108004d000000042c2071019000c1003c0c00503509440d1701070704071040350a4903807a00049103030003140446103038440d04040c10b00d00d41580008a0349060350080d15141ba0282c103071180c440507882601203071070140e03102c20440721000a508030842c0d0424030050050b407511044072098001e6492602a50105400000754141e4000a40304c448100c10385044c411f01c03071503241003039061850003031756040c6013215112030702500d105000754115615908020700402290a0628005004120303e440c001d400804851401d0819001c09490504895010107400c000c00c100350355a6074082440e020a0301409550030102c0b41c1d0240c0f9502075441185603000031910f035085500601d40c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 501764955 1250 501763705 501763711
    0x6030c0403060507020109080a031a060301140307080307031704031403010f0501030b040c090510020109060f1b02070f0b090d0204060b03070f0c0203030301091e15030b0c0a0c02040b0d080c06010e 86
    0x251b80c50485810005181081582c09001890400048010303856481e0b954008620300540d610407000000854003c500303800e503001001c1c00f50b0860351003070b8458480ea5924820354401501041c503200f0344440001c0c00030500d90b4058884c1c41c00801e004c0300c03015003240b40e80003a0000502c056a0201c14003140d40d1610508403112402c44090100da40702c0107018101c21920b01443d401070b2084c00c000d002c103078000d4211080003940040e00f002654a240d0341d01c0c004014051000040420324007003d505281b0016071344040c0d5091500b00c0f0b00991414610926580c0b0045459800c02c00c040b80e900050b940790300c03c1c6001000310315880c95491512040052088091300500c00c2804940f01004000d40c03070010580b4191241400c00042940f0000c4c080441c0341d41540300340c0442c50034101d500c40301203045500c2004680c4101540071454460461940007402020030342d00010f03030303a421000c01601d042d40114030100300c00391184111818680b24480243e01841040580350b0204d0010040380c5025040541c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 501766205 1250 501764955 501764957
    0x1507021c020a02270c0c0a0f050c010e010903050316020a0e0708070e040903050306040c110d02070603060611060402010e01050f0a170105040204080607030b03070b160308060609210c06030c0403060507 88
    0x620075642294141004c00180030904050400b0a064100400c00c01020380425005510800105018030307196a4409442d00105e00150441c254a1300c1da50050000343d0549501502035800c250b102801c0292060006034180d07440000d00000003180314081e44403d0040d455943c654105241c2000060581c00c000c000ca503004601d0a2030560110b54481c2c1501e4200d94102d0300803599000000003100d054241018600c40c60142c400543d030119000941c84044881c2e6803418043c403540c644041e0755060070181000003a4001100050066111b038150142007501410420b0801000c0801c200841d0010400840444e035140b4010740020903c40b10240180301c100c4044d840e180c14100c5031512498054400303401d0545541c1040080e40e42480340b0000351404070074a5465522000080c4440c1440c5142a008a40c03140081401424000c080305c80c0c0c0c10029110340b2080070441d0b51000a90144413044000e4041d032070084845503100700c0254000d500e030f029a60340740c9007103040401c200c0b240504844 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 501767455 1250 501766205 501766249
    0x130515010905060108100f0302040203180607050304111020210d14010b0f03040c03020405270a0c0b0a02100203090a034802030f030d0b0109081507021c020a02 70
    0x10752002c4801015227034156005078076502d6104181111003c0c140e002d48045c003d01003080040f50f402809144510702510340081c1c10200502880304030350181c8030300c070700084101580040b00030003a1000d4100300c02000440790700d00700c2981e030003143c80300c4082e00d41c50813000042c0f5110f03050114061080740213406401c1c00550352400100b40c2040c403518070b00e076401c0d440c08000103040c001c0740751201000b590060001d0190f4940300c04c01c00c000c3c103040f003841c4000d040c0c520300200010000040030f50748607500c1600425090b0901030030424a4100e00849421437150084212200d80c1c0d5002035802042e9400c0100702c0031840b0310b0081e001d9201d1483c000c100320400040030000c058150421800f02c40e075405c011895a0b1002c1100c07240c1101c083c400380d0540306200e141c56a00c1400002002c00100740303181000745e601602c00454501d8002d01ca860b99130360184080da940403207031070390882d0010990300440e101c0301c142e00614441c100c01400c0000140c0c21907000c41040d130401d4031840c40c0041c024881a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 501768705 1250 501767455 501767459
    0xc011202030f0619030501020f03040606090b0a0902033303010e060f130204090b040b010314190b0a091209080d09031a040816050c1302070203030313051501090506010810 75
    0x1070416190b0003403034584104900f4210f004480741d1014040c005c0c5410100035503442c00d08000418065209a8044400914210000510040901c100b0f65400801420b0001d101d14008680703010390006040c2400b0581c1818600d040a038800e5008100c00c07074140c400c49441c54024040608480782511810141c2d0402c004101c10003100d4101c8591041d0403075140c0704200741a0000c9801002011001131048100320144800c0c04903030302e0040c0c1240c1c03141030700c0000c03000d0280312203446428150310341c0c20740540000b00100080e0004401540f291650344001004c2c1079940718040e0f00c1b410000c02034045074941c0010b01440c6c82c1032004008510700c41c00d20071182440d564600a80084500d18621203d11080c007140401411130700710384d0304400c0380401e407460b65490700f403a0381caa03a1503c1c00c0380e2041840340c9849107813903000c1c001d03102040e0700200070b1401d5513a8059200400c0a540104031058010b00e0540d990b90010004141d002c8c2c802c0300d1001410f0324150001600018010b403d40c07070040b1500c401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 501769955 1250 501768705 501768721
    0x50402041a031e030d060e0604060602011a1c050304030b0a06050904020a03060e0c1302041706010303051909091103070809071a2208010c08180a0303180b01080c01120203 75
    0x8102249007004000903d00701c907034074459086008152080d030010f03080000000700b0181a07614540038000455040103d66030350801a4201c03a0144804140b080d51030590700b02030315154081c03002e840c42c0300074012015116950348608540c8103410480780341c00290306118071000d043c42698081c2100f0307078030704909042c150000380e51005103100c028911900e90421900717000701032094810f40712001e018090001c8030700e07500101940040c00340c008801d03100c0d06e0242402d00c00007002c0341269010340394a85070030081000d0319101c80c0c1c5004500f00b800071031500011051407500c01e00381ca40248020054072030401110081802d500a0300e1a00d03507500c12a0180007060312040014111080f100c01075075128044050310029440c80c4e00403071341043d01e07008002491071041d0024110801c851791803040c0340e51000000000b00105050200440c1d21410b10301780003d0080d403100c50f01c004034860b00b200f404115a41c003580030f04c1c01d81000c1000e40001c004011156004070018081240d13140083d81107190280c0c1c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 501771205 1250 501769955 501769963
    0x91f090201080a02160c031401150b030408090316030303060f1202031b01090302180a050c0a0c11060919080708030a0c11010e06030c0310060912020f01030e010f050402041a03 77
    0x41003c0496a0000c0c40861542e2120200402c1d01da0003011014196508d09042c0c1c0d4810541d8140f40071942008031481c2c80c207400002c5041a2010710510f5415921507440e8210513400101c0e0f115090722600c88500c5451840b03042000082d4403998002c46c540741010801c4051032410383c8030103003000484201d4401641d011402c8008245544502c1c1e009201d8000101e410105030b6201030b400150840001a40e1596030b1841840703026000e5052045844e45050194180310325800034002179030700c0c06a04001070603062408061480142103034104001d2500140101c0c10460303000c00c403442d502c130301002480c0781400b11100520b80700c805581080d0403040003400980c2002d100821000021590900c0f50780250703454903080d4406005141c4030700d04040608070171750080d151150040014007002403424812441442518059072003135080c01581d0382449032017202c0c095560705042d10754422450544c024450b02c110130701160000b0500d41000d00602c82220302c203044807140d03c411042c1603545a03d00003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 501772455 1250 501771205 501771211
    0x15020c0d1215030b06030f0a0209010902181e01080c0a05070b040507080102030c04060e06030403122f04031703060f1c0519150522020a0e091f09020108 67
    0x4104040880c41c0c9032480402030412614189002c000420080f0a02562141481c4120801d03000c0300c0440344030104613652000c8103400254030180704001440190b0447c2c000d00004d0606082400135121604006010340ca280064404250350414400d515580c0c031802d41c58101349040c03003c0389400642d0344020410b20400d03d010382206060000304042207000c00001c0020320100000315203038140071501c0e60482e070107441843c001580c007000c9410185084002c690040354540c4600da0032070501c00521019000c0240c2d4040b00c403030f000b00440001007004151902c0300304001d8520350307614203601d1302070440300282da50045121414400c01900d034a5010302031141513030071504103111401400c0c50000012038194000c00600403a0b100d181c4041000209421251080b040e104884840641070b01c12102c04071828040ba070894040007105140c041c03142c08244e40003a000400d807948070352182c1c0070102c0582e03228000764400c984180c4c166a04410700d003500c0b2500c201c04d00c00d80c559074000030300e50031000e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 501773705 1250 501772455 501772457
    0x3171306230c0f04050402070309050312040e06010c1a07110706091203031104090e010c0306090504020f0f0f031c110d0e130905010f0608060c090a0b0f040b040b0715020c0d 76
    0x29100f0b0490321410280c2d07000b068010002c1d0b41d9507503240f4005100003120700c280e034000d00c03e540d44180d010041e042580c1c141c8000301c01c900c50b69510440111451044640140c41d4840e00180c04549070001070344007407081c411034450b03264000d8a01c5200e45000020b520400800c80ca40100307100300c0c1c1100c0c6a51100c0740c5c05140108400001c2e44488000e8070580d4403140c0c40301c2c80d0921000c082c1006400160080145480810560799119004000e490080303030000e62100318055802458540b401ca81ca01d1150068000d2081400c184046850a0302c0c038030400d502d0700c078500883ca0f06158003080c02482646000090f0007070003100800541400b005015042c0b042c00219480510301f4241d07800352101039000340080c0a0384007540711400082105e0300500200d030150390001600c003200402103d817a40001b40c0552005843c102e00720001c1c5d00f00082000c0300700020040003500c201c440d0040c0001d44410146181e4803916840c014800220719018403456a0061210560080c0041400d4803481c0279 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 501774955 1250 501773705 501773707
    0xe18061005040806092107080d050a0b101d0a0f0603050c0721081b0a030b0f0d0b090c040606050301061101090b161205040503070f03171306230c 64
    0xc030090700c0301d020b15000318116105a8040007030074140011010010a40c82040e5041c151310300c59207405501c00c61343d001d802d0324010040403050035020f6006503440b1010000c0061860b00610002c0e90640b0151942400584042c0d00d0003109030a42aa0402d5004111350110315203181507030310407081d04179204000900d070f540c5001034500300c034220403a204943e0207201c198074211200c02441c505181e1508001c0002c1c804c42c0004d1800704d0081c000040d40e84c140d02140d0800d00c50200450260640c41c001c2038000c082d001800e090f40e00d03030720445c44210b4880d00211009150405900e07107001c00c2d00750311501c03403030904200300302e0303250402c0c1242d05590191500d00440383c114032580d40034002d013000003800d881401e810031221481030401c61150f980381da030703d84003186c0e107202850090b074000b5540039106400810108000411004103028028802d0805140044441d203007401100004c840c15661881c000000c0d200b0000c1130710a407100c28102101c410840c141000340001403400c010814068140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 501776205 1250 501774955 501774979
    0x804030908030d09050607020c06041809023001110304020103052815050109080c06032206060311120703030e0103021b0106030203010b180402040b040b1c030e1806 72
    0x481148803402030100502120381e42c9000d0342411000f000c00301401e079401d000e5503010031121880450b54a07481280105454102420302c1e5600c2050003081f8014400300d03640e42030140c01603e808008080c0c51b0205204640c42e0005c003010040c80b0244070401f0141d41c0d24092011040313041e04421303203400980a00e030004003642e81c00100007040c0084507891000303004251400224606079013007085210b81e40358081d01015a28801076810651901071220990800d550003910350411340b0146a00070400804110740001c1d15a0b1100548403140c0160352143d1074034014028030482402a0a0302507007030390b40902902c100c2c680662640000d00000301003000c000c400010304da101e03405030b8001000a601c06c1401c4005030344214003e000303521040740030394204000c0e900c0501d80894803480c4606c0ca001c1c681c1c01603640f582004014180c050702582d05c103688092941c010785550b800b10103c6043e480280304004442d003005001d0b4040e104440b440b80c08100c80c80d10303045802c614825040f1000780c0303804071411 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 501777455 1250 501776205 501776207
    0x10308030402180f0919150b0d0f080703090e041110120c090e011521020d050901090615051011030706050c04030b070906090513060515091c0210080403 67
    0x7410040340c0c4142030b0040340611400354000900b46001d600340170115600d0307101a28054203c41710000000d05984c3e0055044d000701d20141d00940328440c801814800201d84030f0742c0342582c1401c50030059071103180100c0d21104054110440340301414a240c000b02c0a07241035940c142911988000c40ca00400c0c01000840025006500c10160303540e003c0d000f40308042c0101c10003401080c1c68400c500c07000d03a44000005199070103000c50708040305e0640c0d03204aa00d20f082e0403041400506c41c0ca4001003982001001843e0f1440c0c0700c0c03513000d5070542001042d41d5403507050030400c1d5454100300e140d04005c03030310080000d650707040d8103c44c00d58401e06003484c0d1542c0078081c060840c0a8240090001800e1908002d0f100c3c00741401001501d1150f1910481500ca0503400c844000032405585c021a2034035409015501d0f000da1303804240414101b01181080d2500003051000d030201049c103010301000324070b070089464100501809090030840380c0220f07101a800107680158a00425806d00141c0c801107810303d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 501778705 1250 501777455 501777469
    0x501050d03111e0a0204050f220c0e0c0a0e0a0b0a0c0f08040605091521090109060e030a020717072c0106021014060f060d021b0c01080c070b010308030402 68
    0x251540380f0404141c1c0c2c818401952254100c6000724032880c44c10b000130f01d0384401908a80d0145103032159501d14140700c40003040502ca119a4159243c2c084080c0000f4801003180485100c1c1508442caa030304c50b1000803000d0460003542070034900c21440540c061140240c03c2d81514074103105407900350101c24190a284c2000900080301a111940000d00030a01c00c3e003080003007242c0e982c1659026060822007071000da050080c0f5090031140000b088040201000765400c0d2a008800300000007551081c90351107000300c480350820f0f1480c50300003140d0095940c0d01844060024620607165200b02d0404111858031903c15000d03018004665a0f05500310b81403840c2c0610091420481500ba2540c441402035500ca801c0d40c4000d0b102c508204110b03108a0321400907501540e00030b050415085011402c0018507003080c114030b18242c1c0d007030044540c4440d14100c0d0241000900d00602050b40c0d100000401d86c0d80001c00e41e01010f901044500001001100e64174110b94000981c1502c81c1c6480c4000364036 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 501779955 1250 501778705 501778723
    0x130b060f06130609051210110c160f06020d0210020705010b09090c040b04021c0b0316121a070f05070819080603060105011b020607140a030804050105010503010501050d0311 76
    0x800d101042c072800503032000184100f42c4009469030702c106550307441080154555940b000003990008200c1111036010b542180442c040f90b51406030030b100366501510715015103400820003080c4115800c0050040c000802c0c3d015004038800741403084102d0402a503218600316881c40c450b80e00040c100240f120039030110802c04401000b410303541c1400b00030a542c07100380310141845945062100c41151405100b122039610492491401e480e91000710480200403000380c0c10f415007d01c525441e040103141090b8030140011524806200060b07003401080c0380150344070182400508c0040c4401103402144d240392900d200d20b0901c0d510030861600149034000c0c08003544a0040b07003041130713248079040501a4403549060381100d10981c0d8075801104c1c48408101248507501d1407004410150500c20010240c240c02510143c0c00c80c0102400245040c0f60350b94190002000e40003030004002c1e00703002e42401001e04a009104075410200014014529500c0c02030034030584e41030351f510541e418040c4080c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 501781205 1250 501779955 501779959
    0x160e060f0304030203040806011e03080a09050a0b07030809060f0606030a0e0712060e16090e07080a240b060901030c0e040e030a030b0612010314030c01020a0f08010e130b060f 77
    0x78503424580b034003030368030342290143c6e03109401801c001244402c2c4800550003116806050011143c0c9140c442d0141d0b0f92058103200204041c0e008007280c1d6131594482d040091035680d0328107540d5091400c004090120140c00c0098640040c130170310614404241403682c00081c11030b504c070f5072611030440b04001001c2c412904e000074026141d000461061000031065554020710301030200246c0310082e6901ca0880107809080900e00705414058904a94010702c005000c1d5011030700510f4840c5045031030b0260a80080b40e00e51030820b45005143c2e0024000305801c0f44403032050003804003200c0050501e01800300c80c2c3c0d0405030303125000b42c030151240c1c2c50103a40e03070741c090b10811040b40d641e445580c0b3303a44042c0554020a0401c0f003404030780d0400700200c030018204200c03198601e90950f036645032802e040c886032000300c1c4401e00203080051020b100602a0441c44d44802034020385048018041c0b000580c003108200d0200300c10407060307840c5141c6903081180d00c000c641d00543d030f889000071080303008081280d03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 501782455 1250 501781205 501781207
    0x240105103009031e08010605030a180b01050a0e01080c01081012050c0102010c0e01090b13030b0f0a050106111f061208030f1617040203070506160b01050603160e060f 73
    0x407401c410ba07100c0c412490182e40c49451140140c00380380d101080c0c80b5152000101c2000040003c0c9106034061600541188408280361b19110800c40e49070404680960744140c021004000703900d8192922002003004111100042d8545040144c46540c4600100d06215080b40001e522050440007540a0066460040c2540c155800c0499440c1855111640950319242409140b03500424a08140040503074400301c1440c01c02010358091303040a1083c400380100c4100220000d8040000980f01c0c01500c0c4404c41c5614000540d001030343c0040e80950706100c1c3c61103041154200c0810009500e402c1529011118200c071140040241103075440301100b07103060451305042254080085000d4024003064048580f115403180c1850815801c0301000308107440c0d20046401042c040352503116000500b52242d02c0ea40f80c1c003141c00c6a010125140b07103440d812101404000f040002139003d4038054a1303da0442c50003503044040410701c01d004c5000e10101e8410302c6025907420301200c0058103401c00b11 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 501783705 1250 501782455 501782537
    0x60b06092d011b030c050106080d0c1101050702150c0f0106092c15070302040b04030f03030507080f130c080a1110020a0c03060f0b030d0224010510 65
    0x101d0240244400881071004241c03448110700e62240c9003940141d050704810350f415002e507a9050f1985040030300115615500d03004005a43d95080c840d00070703402090f44443c14540801d190001c46080d40d86009030500c013080c80150090f8681e500c500d0141c0040003003d580d84c1910708440f61078401210102481982000004200e141c8190080d0401494500034401c86201c050340d540001031070880540260750182260700e101049020f01e16030088a241001850f00c0d40301c000200e420343c010340041d114206d09103045e0041591610031540d000410380303040303619030a00a14010741c28401401402210340c10809040502c080c100c0003000070032012040301d03656802450700c400f01c41c001415040c420b02c010004681c1c000d002007100c0110365071046000c10f165040d45d0f15040100300f003030041c00c081642c07644152050349040001c00a000c10540041c007503190070111002c001d443e48607030802e000c080c01c1d004205545603003150440c1002c440c245040c07842d1201c0d40364003054044003e8074401da41d4100c01c1c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 501784955 1250 501783705 501783739
    0x1e02010e100605130203090c010528080615030709170f0303010e06040605030d1715300d051b0307020901030b06090a020a081314010f1e0b010507060b0609 68
    0x40301e8122481a50700c1d101151210405a017240012203010a194000d2002020950704c035400404005c410960400907070040385110801c46d03041c07440b001d004580f2002c04e0100030b242840c4d25001c0501f08081301407a52524034801000020f15104941801406907180941800103009184c0c2c100043c404403512036035201941503070084252a00c034092460581c003c02e0a080201c0d650030001000e49910051400099100440520040400c000c0c81c0940b11002130a0b650300e034800b0081e2501071103024410f940c0f000b03003410807050100c00807007d602c2040ea0610071500300007a90201c81d05120302c00044150354116900354815041c009510440020000c0300300a80000700b00d0040c3d0080d5400c030000d03076684450a04a00c200c5500ca0049184c04d4005401d011218034583c403a644035502ca40607503c00055001c0c00d41e204880c40720012519041c0900e21410210041c02e0300c0c0540901c14010f826142e00080c04521900c0c2000d41010780b104071582094076020105c504d000710103825110a2a01081 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 501786205 1250 501784955 501784961
    0x718150e06310e0f04080c120d020307021b0a050603040602040801060807080708010504030504120f02100f020c0d0b0403080a09020604060e01030f0b0a06030b030a0b0f01031506061e02010e10 84
    0x7200c0340b9450b00740c600460314004020f02680700d4295054140501c0c0c4550300d88140320f0300041a0074503a48510740c080080d240d40d40000c1e1003200c10b4260056100e040202d400703403c20b983d481400e41c664500c00010304d12952004a110211101619040d507251114201800030384a15080781a5a40c01c2000c00038501d640028040e040398102000c0d03904107072b2034404403400e031181030300c001d00020018407040c400a0b840608000110388034000c00913220f4055404503403521003001030b4002158950700c01340c1110303805100c61681050121625641e5070140d40c1d8110300541c1c054009810803884400080c0da20541390320088000d03400902c0a6211a0b480200505c000010728a060000341403c2c1c0369020006a0f00a0382c1d11035000410800c8040d040c000c00701c0c0108200401260b1610519200201281410182c10300908107260b20400c2036040d81414054800c2000d46c10f20914640310040102c5a44101c00e98802181041d502200c0b0103440d4040b4098285091410018080c0280b584101041a4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 501787455 1250 501786205 501786277
    0x3090302090c03070809030c030a1110060f17010905030a0c24050a112b0908030c2a1c090b0d060503210d09020105160303050718150e06 60
    0x107517510303419036642c1040329201d000d054002400c40e8024803031401e01c0390058110403800030b001c6086414404141c0308080030340703026a100d09a1000c545500b40881000071030520701030008500240304204881e41d809541c0e2041440a0040061030041c0d00704200261f05801d007901c00c82c5140d91511121400c40c40020182034407456040c40c50400c02c40248558281950f821850b110318003d01001070140700d51442c0400511880f040d5a11a1844000f403c1000614000c100e1411003d40300d1102c24420945565507244001c0054003403007480c648940001840b42c9020300028041d0300c03c103500c50381070722408038a800075441a40c000c503550089400b40d50107176080303a4045084400c100641900002800c54000600740850020420006a1120307a040701d01030a00c10700d030661414000c40c84408954545250803000252560280540c030f0b0740c0100462440880304c1a924200d038a000035018800c00080c0c0c01130f06010360005c440d6000d946490588203850080300c2c600f40c640346c013694140111a090 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 501788705 1250 501787455 501787457
    0x3170c07031209090c0c060c02030c1b1e0604092a02030a181208130b040b070b0a1406090a0b0a080a0218070e0d0f0f2004050411010c03090302090c0307 67
    0x3e50b00080304026401440c14252180d241c001c848061074903041c01a01e4041d05250561004002110305200c041041c108003c58809220380002031540c1046002941c00e5442d04040f42c42c20520035240c0d41d108119822904d5020000400f05440c1d01041c4200c00c44074030b00c010315000f085a40f84201e0300400100402c1000743c0c1c41d490384a006501d503001c090720710b00503260301900414804000a80f208010b0510030022840d41003603958421901e100d50f480fa410502103400041030890400a203494034031b401601c1c0e02c0c82800b00601c0c0d00c0c50b910044034000e02c80d6108492040100f00600643d600c03e41072146c0182c1282402ea0706d440c030b030aa0b12110414224041c10b04114101071034030202407194080c0c0807680e91080308207803403070801c82400440075041e01c0038403840080e08000b800c140301e40441c07684140c00c52940c5030f00300300c0c60031030055880c02e000d40118240b108220000b40d100803100b414100900707101e201185542400c40d07503282d807a04000d400801c2d450a01c20115405006140303c2c2c541c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 501789955 1250 501788705 501788717
    0xc0503010b0d1101030f1d0703031407020114090123130e1e040c0902040f0626040303180b150913050a0f21120b0f030703170c070312 59
    0x1404040c003003840403100024201c81c0c000140b9a074258443d41001d00c0051846d1000320b0580181e090f02e03030820505075003490959000040c1082010f03006001d2046084a120040d41003418940010340510103c1d006a461604001001c407900c0e80241910901d05003501011344c0f1111800d070400206a01051040304a82240b403000603c135a003184c1001e2003080000c00c840c0100b0304a0000c030400f140060421503584210712804038843c1018030240000380340c60392074050140d24014016003402c18015801c030a000c62921201c214040301110f0a80059051038000750f280c02d600d500c01000030250f070006258259444c14014001304a1640c2e10701818200d50005207500c541d00402c0c60440038070001095a00240c001401082007002c141400c54052411100e060180d1100301d80e03a248545001c0010075504400c05601d10040c0c4a00500c4090656110707d0510300d06c0002562402548402840c110190340b8505101e25110141c5800345288011210401d45a02c0c100b9034145c1d0110b1500c0003d26 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 501791205 1250 501789955 501789971
    0x31005030106120218060d1401050114060c031b07091503050c0108100306050c0d02030f0412020610050906040213030302150f0c0706020d060807060c0501060915060c0c050301090c050301 82
    0x10340f02e1a24003600c4c0d030003000d0701d070043c000350641007020000070003c5034080c044100c00d0010481e48151304504607040b0300002515070510f0207010042e84880950b40c0180810f11000c1803035140082241c03500c820340c014441c50155411221883d1002075080520103a080011078010346021a2801003940d12400540d010380ba4410b004481082e0304076205220000071550401c04144940d0000c0c1e08181145052450700c03100041280917a8400d13681d15054440c103004200c1440401c6100030f01c1d030a014805000c042c10b10640c0d122b00d080705070042030321030b0f0350601c00324050359034582c1202c041281c40d1041013819540c900300a529881403d140c1c803c80340e61040080e1b0340c82d0340310507030364460301c15204202d05042241c1c9885000350800306900c1c0031503554900c040303800307041000028002c101c0c0342d0303e01282118900e0107034207550480e40980100d60515a80e00c0f44031042602e000c1c155000c43c640380000c20752500713003403000074601c0d48001c0e050751810310200188151604940b05440d42a402405544 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 501792455 1250 501791205 501791219
    0x5130c02010f020f0a08070201291c11010e0607060608010b09010b04080307080d0b0d0819080103020306010501210c050306010e01050703020619020903060a0b24040524031005030106 80
    0x1208003401811340ca40e0400540000e1809980d201d504444988000a01c2a148400d400c0c25610b004440d542200c145031040700a6243c625268035842c21084442012203c00d03982d404405540729200d5410f02c0a83c4650002a89540c801d070313414590842000c0c440c0503510301c0d980b402000803505080c01502e0316400410129041030886045a8000b0700031f51804850b42c44914298100d425541d0900b0741315401034002c0d44e6130310b482c401160b0007084c500340e4a850021804c200d654030164100d00b44507006004001694000c01d180d81100c0003070a250340705219440080b042e100060000d8600c4610707120300604056441400b0398881d1400380c1f92120200341003001134a5901514000900581c81440001c189010060500c00b4800400c031002d0b00b8422480002400c016044030101009980c070001c10400b0301d48445803190031405440340750440c120031a91f111540c4184c0c0206401001050031015041451400300c1c001c14110441140e16400c0035000220382d88003070301c03d080c401c0d8201140800c1c04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 501793705 1250 501792455 501792457
    0xe151302150a0c060b0f03031c0c0905030a08180303040603090b52020102030406060f0308161b0305030a0207150903030c080c0a0c080f030a171005130c02010f02 71
    0x750b41580c4501c9410a0140d84080151456594140d0454900132051456407420409401da01c0520f45805a0018480c0324290407545a031904000f000704880c0108400d0701c0110314502c003117402006107130751654001040d082000c8152090380d05484005400201d45615a02540b290f42c0f1941005110352203d0b4800541105046440d148148800e0400250208030441c07007001d00c1241344400c0702d48850f0202c40491011080502d90250b50000200000c21046125440180000c402a0b607a00d5003107443c0c00c0000d0064810541030a5201c58590084c02000341c080b01840111240200310b040d00c0745051501d80e0846500c1304050311035104003060345141950006120000c42c1c0d04c0c9559030f455034404403001d000082c000d0ba2010740c10040c1d050413003070922494030b03481d000e10201d5007a540341c205030602d00f802002940002d90014010507401641c84001c4046864800841544544030b41004811164a40d413005034080000041e41040203202e4020100030b200d075070000c00088007010468000d03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 501794955 1250 501793705 501793717
    0x80403050405010f020c0a0b0903061015050a0c0c030c0302100c03023c010c17010b1606021c0f0b030601050604030b0414160510051c0e15130215 64
    0x30400a000c24003030b552080d4020041c20f1164030454011008000100d200d40d141c0c1d03040800c0d802800608807034582001c1003200e1700018003001303400d103261520700305103145107445070600104400050342a240d681306d0650340038240c0d00b202c000c18240c0d030b40b8540320001982c03901c8200c2c010b203c04000e001c0c84030b00440e9104e8026805801500400345410203143d2225200d00e0009401c009070303032004544080f400210800031051030000542e199214401411840440300340ba555403012a0061280c0614001a01c440e00c0d16881030340510031091800502038018a440002550b40e44503082581c40020341121400d1450a0000c20082c00050189610381a090203241d411107401c01c0100300280c50040c5040d8854001c4107610341003040342c246942060b0702c28501e0400d0042c0031006204620340902090300740c42403410040d02d401d0700c03130481c40080280080c0d14858143d503003822411340e004c248a907504510820303020450310701d016040407103800038880b4142d0044e410300b801d14004c14600300481d10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 501796205 1250 501794955 501794957
    0x302030f06040e0307080c0706021207150b0a090203090d1b0218070203070c0329060102061603110d050a0f06031a070905060a0503090c04050106170c0f0f03090c01080403 75
    0xc2036614031081c00050201c0e0320140c03195210070801200400e41410251a2450845c0c018201143c90010002d26121054090500d11070041140b800062803207103e2004201c3c14820210701c6c015010b0004000c110315502180350640000208240c411340494107544c0c240303441d22000003400c0701100c24012200344110007500001074030007003c42c10407144980356000d40c451040324034002d295a204010004d2550080f241c400400003441d80d15100900409a003180d0141210f9a40c030f84600002e503a900080d01c00014650b2000985650f94800d400030b601943c18044120f41d584d520142c0c0b1001007a02300ea4030992103107000c084410b6500f250007104203d036040700d000c00d084803400b12503100c68107010780110b0601c058508001066191440500886000344d100c06449161042c2c40f14140003944004922a030700d08030042c0714003600400d604204070400403c060081e038840254131402c3c03160b420703100026038005c03540701515036500c001940305003010002d5405964140005540110060364014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 501797455 1250 501796205 501796231
    0xb0a020703080304110d150b01050a0801030f02011206060c020301060803090a05061c06030605090105092107031202030412261501020c220b03031306031812050a0f030203 75
    0x2081080c0c024641280c000e80041d80205100c0c40000d44041b200079007101c0c03804602000001013076040c856032010036003e0030507524100d10102d00a010910501005040d03200d07901060041d6442031001c00705000b01040704000460312180d000e4210410f003a01240f00b07608040012491080110030780381c480102030141c03003c5034200010003500350407006000c0f030080400c49862060340c030310f1301400d401903016001c0000d0a00f03103800140c1c00c4d10001003141c0c0440d030040c450188110004c02c40b0072a0502035060791510781c60185021900b140036068414130f01e41c0040140001c0c055181614000b40c0300d903403155592103480c01d143e0b9600c000713a80314140d000e001c14000940601360b00132800d8140c1c4014410303182030b40c079103200141401980108103082050f00f00049045503030180f00713105107004218029420500c3c000d18246890b5601d00a440070951628401042002412034141c081644404507850441c208072000303200d504942680000680d0141e11221042c4c000d100b01e070300070300b4140016 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 501798561 1106 501797455 501797459
    0x3030b011103090102070603021c090c06170c180d0b0a090c0f0b16050f060c13050108041101030509070b070803090c150301140a2303070b0a0207 64
    0x44006a104002060343d0707a80002d40c08045800c00d24001d41c0c0c414a103400d5100b454202d080c5200000e00b0a4136050411125200e08070030b4403243c1d80c1d1900180c0c2240f001d0f40030150140d03200c0e0706203001080101e1596403e81d520b58440d0b035001c2c04e0480312418550f109207102c08103c0c1c0000c50156180e520800f08580001070341c00500381c1ca9249880346062504100451103507001e00070007556014800720030800e003800400e010b90720403020f440f80e0780b03001040311070319030700c0340c0440d0030164503405011074150302810145001c0c60704900800c018410f40c100544c000c001c080c16030001d51080040c0015a1206000200f000501c05c039121512400c201c0d403001e161020b581c8695100d0140e034128a044050440c0036641181c045801c009400c0d20b00303002241e501a1207802051001045981007031440c464032080600c007190540417140441d542e0f07603601d105405501c03801c1005800907802 = true := by decide +kernel

theorem cover : BRFrame.Cov 501618705 501798561 := by
  have h0 := BRFrame.cov_init 501618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 501618705 ≤ n) (h2 : n < 501798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
