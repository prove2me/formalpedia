-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3207
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:58:50.721136+00:00
-- url     : https://prove2.me/submissions/b64e11a9-cc4b-46fa-826f-b820247933ac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 576618705 ≤ n < 576798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 576619955 1250 576618705 576618719
    0x9010c03210b21030901030f2d06090b030c120709390206010b09030c0307090203010302030d050307120b010e06030703060905090a170313080705060a1a09130309 71
    0xc0740c103180c146424041510500c60041c05034030031104404001e030565a1110415603030300801200c40d00e40c000c0c0784c0403440300403003c000000381500150100181100c000e0240d0200c04140300c0c942600040c80082c40465514503440341910300c0c50f020740d541504003500c0240a440c105000c030b05040d88203800da0b1310b0b60ba81c0b020140211031461aa2203a030401b01540d145034240c10b582c000795110031481c1c1c000f4003e41c4800d0020b40c3e0341c005002e0b0321140600082d6000c4030365401c010143da101c03802411110b4007900c805142e0041d4100380309c102c0c080d200310911150303140e0065041e2485000340ea5102c030050061140c400c0e018050901c5028103114010500490580b10200190321811031514003080841c580b00c060f1088030300040114540e504154400c0001466031003007040100408000c958498a40f110380d4100700124481c002e04030381300082da1000b08100803502901c07900400c1e41c1007004801c08030441d12010050013480c0e0344115000e0008105084100006902601910b015451181c5580b5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 576621205 1250 576619955 576619997
    0x1003140403050c060a0219180f0f0f05030f03031f050d1406060307061403090115060f09050f0901030204050411040513020a0f0f061101151d1b09010c03 67
    0x40c0a0300014000640b030701481200f009003a4122040d180210320700150441c2081c0816046d41c240c008002030100000c2c0c8000365107004034081c03d10020320743c10171666410f003c50545180c0c40b0383e0088a14040c0e0008031031130301003511540c210040014618581c0e8615031580c1071710300c85c0c2401040461000d00814282c0f516040e0840036480382c1c01902c1c1c0d151030014000d00d0482d0040c88544654441001488410b900c41d000b005940645843c103500d80e210282c1e05805400301c650000c4030f0125094000070b900382d0110410400e920320f622104036007520b0b1407c2c0318202100786030840d001640c2c84010001410540d1019a01500a0741860780301400c000000d015107500ba5040d01103203007060520f50543c90001300c914001c260091820007018039150760209044260302c030791410b1085c030108103031881c0000c4d0040074450603084900c003502c64580d4003544144888224241410400c08001401001030500c0401d43c900e0f05110f060806a440f001162800d50050b022400c220b0b640c0c1c03ca0240000c502 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 576622455 1250 576621205 576621211
    0x180908070b0a1404020609152712010b030c12190b0105030708010207050a020d020d052505010203090a170c12010608190305030112021f030606020d02010902060306100314 75
    0x1d01d0741c1c0840c140000c1c0041600c601c4904042c840d02031200340801642d440c07088510755501a505580d458001e010059400c0c05405014060042d010b40e207104d080f68040141b1400d4007088510701400d107070304241c1c1383c00c80320b0341d0a0702134041d840403504140c5803038051040c49420080c01c007100c40c03034020540c5030320b404078a44000300e0344103402c040184114a0b06105950250500d00300841c2810000c0e02c5040e43e17540722460103400740c8050400c100030b64403142135803104550840c00312004401520300c45d81010501080c0c4d1034041101140100e415071001c4212658000c000f448840b24504001a6421040c60800d51000360301c00c8910700b03e866164020040314400c6800c000042842c40c2c0008181032070344081001000701031034007031040000d0304402920705403405100d020204c101c643c0b001c5241c44001940000c1c007030300c0301100a41500d80c141c002031306072040c96090368000c0c00782aa003a42610b6072000e0007544403800740002040d0b410040e65548207030b07990745408241c10500030300400344500c080e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 576623705 1250 576622455 576622463
    0xe030a0c030306060c0308060d260702031c0c0212011506090e0702210a03271209080a03081b0403030801081207020f0112141f0e0106050418090807 65
    0x100e41030074590140300c0d0100a10311401c00084d802c003199001800d001d130051416210300c80036040c0106002c40e6012010300e11084410703503001604943c22000460b00103050407442445958580000000325a460b40403160340380d162804214031550030820100306e95100c002c442e65031104a40b400d09400385501e00200b84580769500c0c060f007000300100322040002c0a000c10756024860102040b2500e5a415080c81d641b4860580c4481018404401904581c2c40071080000d01440611507048d074000381d074031690f100d400e010032046007400059440c00c8561141d00c40755017095a91b040824000c00c4241d81c018500c2c0300e800030300c0c1c43d522144000d50b00b0640081c0c0010b00d030705005100019080082d082211908204641032000301d0380015400119010010304100964400120100050300521403c8c143c0c00002e1484d4136048e00c2c0c140c122034080c08c1c1e00c2101040ea500000b22a6084510541078510513542c29282504090714585440c001c603601c048203555500d400404140498041c0224500c6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 576624955 1250 576623705 576623717
    0x904150920040609022505100911181b130e0106081905040f08090d020901032009040f020409022e0801051e1003150b37120e030a 57
    0x11002840100c850075040103525034070400804607440400d109154208503a0010340c1b02c800010700d40749007031200103066a4007203402c03c07184c0410000b03003100c8400075040a445d120720181d008201e4000e001d50070f1b90782001d05041402100d4040a82d0401050b049221050700345505646800ca07443c00c900c01d9001d103001440d020140602c844001100c0c1410201c2003406100904103525070104110980f04014212a40010400400d803640d0411601042c0c00801c4030070300d1340c0d4034108908840c3d00b50b100e1b41c0060110b042445142d01d000c410702c1d0300039a042050f0010302540399080c4001025022001d03079205a401000c013014005c6032400c005d511045003c0c5d101002c0c00514041c12040c010b800941c0b188114511030302c031525880e094105106801c94a60707141d5241000300360b000b814901c1c2059142d184a440c0490030300b600b013000389042030241c5509030103920010340302411034000f030565180308115402c004c00322500c5030802d5460107034402d00004070400240790007443c55003c00101c10101e84 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 576626205 1250 576624955 576625013
    0xb0a2a0201060e0405030301051e0619110102070b04060c11060c0421082a150603060a0204030f06020a1202160308070f02071e0f0b0319090209041509 66
    0xa4207004a42c0188100c40b610400340c14503075501510783c001401558041c030141c451241c900716000c8540d406070310020b8102a503451850b40d250001c0024160200d0128482031624410004141b003215541038202d840c51a007500c4c1d581d5000c01a00109030a2030400103031111038030f00b48405000c09401202e11000c07a03179599180c4180c400a21040f40d1604060b058035440c5100410b01010880c1c6080000702070010110140000030140109490301c20b409500c90701d0f801004200c0c024030440d000d0f04048007210f0850b0b84410b88034040c1d215500005111401c24100840001c4458003c1d20900c030079809c0c80c1100140d11640101283c20000c2c00350003203d4060b541d107041c1034120007100d0700403207140303054580c5004240b4040c0d41c4e400d06100b00c070302c091503c101c00e00381d040001b134040c0050004118141d81c82541e464860406801c181c03003a60100f00d81001c0f203403c00007244035108269501a010200340da0b01d6480300c1010012a181e4240400e4079510440000f03140d100a054054a84606041000d0317 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 576627455 1250 576626205 576626207
    0x40e011a0307082205030c0a060f020406090e0712050f010303080603011415061204030f080c070203150c070b04031d1206060603061f0507120f0801030b0a2a 69
    0x3514840c00c0e160040820014820000e900c0416507038402e401003611290f12a5031030901c0c408004107080603201d8000403c40c001e0180001c2015800e1602900c0207006400700c55006400300e105030300c01c01c408a000d10a042106000e20040543d2241c1c80d0f040c202c0c0b03407041d0725080c842596000c9865188001900006104158010043c80d8011800394000c01220031222801e82d03080300040c0c020844081841d036189001da90300401c40e8030703010344540c690200d8101860041c0808255900e0340001c41d81c01000130303e450201d08181e4017120380040003080b001000345100828001e01900354503d5030703020404000842c440140c90f40c0210700c40c0d90b03107580610f64a8507c800c406226504544120b1114000e66040714000504a400c07510440c1e207255a5150b150010b40940c260010381a19800f4070f084105c82960040003038541d803806810702800c00c00400c0400ca1311030111000700c002007180342e0014004a048902c4a5a2081f40c207240015900c6031103e00c00b400074003049485002c6060004040e6142e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 576628705 1250 576627455 576627479
    0xd0f0c0906020303040c0e090717030a020d0206040503030114041b0e0f0105090a090515100c11010302030903031f1208030604110c100b0a0f080322062001090602040e01 74
    0x141070901c043c40c2141070030764800b940342e00340744110290103a012001c201c0b0b0850a000c801c008006184680100c42900c2240580340d81040601d1405400780b5403e0401c114004902d0324841d5a100010750728503800d002da803100c0000050507803500507544141060b44505007514a40c01003540307403102e024001e102c504100f1458581210b250401030203201e00025515200003100c10380e0310005000c1950764403180a81841071404403050703404440e4204107a0403d8001c501c80032a1800742524400c4150700300300640a900c4152960b4889520404c0090344030f0802e1207076000352466400047c920240d0300c800350b060401d0103242c140d801d48400018810545001d1180c0600c07408040f154504026800510588135003d4181d10740e000381e11841411241e6070385400da00060500840060600c03038440345142e5030380e0050001b103490094440400c4010307200e003406e001d00712002136545038074030078040b0400040c804008050b00380e00d40d22800701d5000996903001400250444400041031585419080018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 576629955 1250 576628705 576628709
    0xb0f22030c020a030812062d040f0207080a0206070804030c030c02030705030f0c03060105040606080c0a0504120c0305010c08280207050d020307210c0f08070218060f01020f210d0f0c09 81
    0x810a08084038040701e074001d814123041016281e40003410705540c600424040d00c4280c030b95559251002030403004012040001d46000f002583c00c444443d5540c00080e50005001da83c081d0106e0b250352082000284a00325102e8607910242c1038031146995070000c68602044100c08040e40d0700b00301c4100c0441e040030840c0c1c60050804442c148803032450007d0141c21814051322a4183d03480c0020b03401041390181081310020124200007690440050420340b003e500c80c1d00088805500b8034183c086002c1c401d04a55002d0402d407002001c40c081061001c01001d0204098085060340901010340400c1c1c00780440748001d001600070315542c034010302e04002041c09040c1e81d03c00c401c7d9451800b2100c1a48650344803041503014003003d17401c0005081c1001640288000207510180107070140260121040420f801020203549514200c1c0340d901c01a62034030107142c00800c0641c4007480c0e40680200e60a140380d20301400701007107490503401014040a945040a90140b840c0e02c90b1031150886605c01c0340100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 576631205 1250 576629955 576629959
    0x303061703090d060e03070f061e05060901170a060e0601031106032406090d03120b040c0219060605120a0b22020121060608040b0f22030c020a03081206 67
    0x460b0451401c00034400c1084514043c04080c0d43d00544032030b03c4000c00441d80010b0b040b04c036125291a10f49052405020840440707209410701041e00d20b01c00215011780340c020880100003642070f80c00c004040c0300e82c9001c0c103002c45052046e0034109020401c02d1094220f03803d000300161a0705d60460500e0501885514801401400104100141d14442e07007500c00755883d050030380540c240d03400c00018016028055400c0d40c08451114040c0070103400001052079065411010700132038508004120803035035140c04080268110605002e41d01d584003503842185440b03035100042503a103490202e2002c45000355040019332000640c0f205200e1100e52295011820701c1407111400c4805002001700d010341080207060059000e0b401541c00360040c1d9002e0551001d00307040048a03a11000200011000e440907a505001c1c038012a50142514100310b100340b5080a0003250301c40c002d6900030b0607041041c01a000c102d00518038400503501d1880c0d100085011700841a120089050b19070b000c810007911044c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 576632455 1250 576631205 576631207
    0xa0503060601020a030e060702060d0e060c0c03040e0a0212040506150604050f06071a100501030e12040e0a0207050601182a210606030903080108030a0c02061b06040303061703 77
    0x41c980c0c1d0000d03162010a0307240c505041185850004224640a0104c00950111001c10392107002c12880e402003440c030b035070403007100c1c0c0c00e0301c030010800791900c00c44c40801400d8100700030500c540420342c1e42098002c50146001490110701030415001c2c2c0c8401c1c0d03030480b0281c2002040c00b400c44400420841c00e120110354052509241c00c0c0003032900c0d00c19095017409840c0100303114090125029a00d45210560454445503142c018034a10064500d03000d118042450f010318588030b100002019190380b0080300b600ca1405080403400d443c0500020007509000d0703000c004020000e80280080e60007842440e01888081e0b15a012072025108150503050450002d0304007a010903400030341c494072050071410003040040120003d201861400a4032680b414180303140091115030682c0013400003800f81d03640001030b0b602c0e491815140d101c0e10203220001680d5101c03000c00761030180300400d00c0e091000603041c0c021281e444000d04009048500740c0c00b01e070b0b490300c0c2003206452041c2e84881c003550f40c0d4061 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 576633705 1250 576632455 576632461
    0x1030209070329120f1f02040311060903100903030204050a0e090d0f09050406030b10171c050d14040606051005030f041406160210060501050a0c03050d02070b060a050306 75
    0x1d6440c0500c000c0d001d2400340d244801c0700240c0c481400d000300141d25401500c84100171011450f07900c2d614540000405881a000c8488035080c074801e68060f01d50000d412812992813108000840e00034040c03560f414003810b80ca00104040705c2c40342d40c02003031113514050380b07030343c074040800c06080300c5a480380c510b1201850811046020100341c44d00d0600b0710f03042040003c10245012074004050b5080150000d140507004030601800c03501c400c6c07103003c401c8200704180e5141e41c2074000718207000b4002c44079940300c80c881c07585000e44442d00310503440e42850020301784145420f04009070382d041c81600c00c415240b40d050209004607800303200040c1500741c1b410725501900100040140c40014101300302811000b0115040108400349003031804045800c4071007504000e01c02c466040410f04040c4058420b228546980c400540a00c50071100161501420010f41c0c0009907140b4000742c000b201007003010410151400e0301c034800381250901038440311846140c83c106228a0340c141d034100c41c0c484c0c0c0c001e00030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 576634955 1250 576633705 576633731
    0x50f071b0204091401020705460201170a150b0306010f030f0e0102070503180a06120c1e020c03100209330f030906150901140613060305010302090703 66
    0x805a54a80c103550004007070b4404c1c1070000c18000009100100f0f54000180e46040c0040008e11a50119080451519500745440e114200d808820018417040c0711000e00300d048440e10000c20300c2423a006061403112014410030101010600701e0b50455480d0742c5121440740740700800440000340909400c01880d5050000000e001c1c14000710780f0404042e15005088001001a0041d402043c034480c000d40d2900f03440c1c60800e4581e00402c1002583e000980600310365450103101e40400c4805a880303500c03201c044492141c028204090414046c8501104160010020350728059a000b41c1a4058442c01e02200c007014100b01e103403580486001d0040c0300300c1130f20741d44d040b904812500d020400c102c2d407009041507200c42c0c8030b0003288108252401064601c44d0407408002180f0070a03802007555402d54800814602081002c065150816407500051254100c02c6022100c142d000511213400c0410303102480a01076903035004040000d40b220010002c50518485103030300400e4a090a0201ca090042 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 576636205 1250 576634955 576634997
    0xd020f03090d03110709020a1b0b0106030e0a05060f09120301140f0a09140a0c11060a0f1508030a0201060e091f11070b060f04020f0717090a0306050f07 67
    0x10854407a0b6103081d0039408142c06120401058503d0200380c80046554107981700094114402da030001c24400003205030b11034010340b000041e45072b1080351410143d080020441c01008a032182c11014031078a068140420410400e0714840c02200035080c11a140007081d041c00d0601004517140009030900062055065a407941c4103100b1040d54040c040c4051400003800c5c801c10b5501c50344031503180401c0c4622800da2201554810146034005220008a100c0100c8051032854051040f641086001c42c19a0455421140c0d4511049101240504c01c1400d100a40714040d030048c0c80c5588005422584a5020301680707006040c0c0300c00200c0749190031904e454031384c070740d107200e04650041c0044954101ea18607400104003241101240e0307151050342c070f0030007098403003a51441c1c0300e01c070314030340c821310514140c0215814410701094460404185507109e20040c412000840e00c404030521400c0d0050300ca2016810065000381e00100703080c100881e13001c4000384054808002c002c07540e5079804100c84c5c441 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 576637455 1250 576636205 576636217
    0x70812041403161b0f09060602150402030c1311160b07110303010308070c17010b090912040b0903011808070308013c08030f07020a050f1503040807080a0c03020d020f03 74
    0x13200030711440c6080c803103070309615a01d90844001980d4080c008240282c05a00c4001078510f26005c80392a212480c044207101c08040310f0003903142c5d1100c005948a810010401030008181e440080340c0c4102d04880d240c2160441d901e00721050340003200725020312000f4000103400070182c1c01c00848090002070003c0d2684030500004d8119000007450703204004a44001308014651451610000d41240e40c803240603009150302c2c64482d4464402140601e000031415100c030425214040c1c1c5080e10f0682141041d41011038400d5140d5a035a1958110b08000d0000e408810301c0744202d1542c0300c25510700030b844110b06800055100b4000700082c603114403401c007002d08240d5200492030b0701030110034124005081a8116030301034080814223071007034803514005e842d2083c8211b4555189645800501800da1740300d08610b0350000084a2401840380d002008540160113020f005140070215180d451041c1d120b0465280040c0324260904141541400b0f400454201480a030003941c03040b07030160b59240200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 576638705 1250 576637455 576637463
    0x2090106180b03061c030507020d03080106030c0212090f1503040c050a1205060f040203160608071b020f1203070c080d080c0a020a060b0303040f09020903010b0d0b04110607081204140316 82
    0xa4175601c8103250052050740d0041d075000780034880d625200c1c0780060280100b03200c0d28000c681822145c0748010f002080d0005022140c0c0902030401da811420040300b880d4066000c0d0f0403201070740344c03105129030b41c0004603c514020346d2442c3ca52464070b000e20440059960214050024000503600001d1003c564a40c01000d1041501d80603152400000d0074a5112401c4c110389121040c40068141d0b00451b00341c5c41074180780c454011111000c894840105a413141c000d40c4507151a4050750540b400c5d101d20702c040d00740482180d080007401e13030f40c0311480011604000c0541d032000110713904203548500d5184c5cac84204802014203014800c0d001942e81c004a550040401c0c0e12220300d812613840800c00e0360014485030f0440c007032a60352120410b00070360104003114007950a0482e174004900341814240620b0b0303441340700d1146a569640f00d01a01c501c00c0300f03036254840420000c0c1400700340540d010307010202c200c080c02c5180e400c0c1850b044910b58586d50141549030010700c405030550403807044201440d604 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 576639955 1250 576638705 576638749
    0x6150c0c090a0e061521060f040303060b030901140703090803061302091009030501060f060804030f020304050414060315061302091305040f03080f1017070302090106180b0306 77
    0x984410b030b40600340d040d036814007511441c0304011182c91199404120b400d4256080d81b40050b80c10001d400c0c1c0b644134a206c000c01e600c014049004800500c60190b8414007a150009080b0f48501c100b52203603006449801240c3c1d1505a203e003551108520340360801e100d070a0411041c15240d40b510301c00d010003429244101c699104c9000008280d804954007074200070030703248044030744135406802052907000607501c640c80c0c010042910051117880e0313011344241d515052070740d60783d540c0c0845125200d42c0c052001c60105101c0000c294032107010301c48552404101c450b05916142040c10705e811010702d030f0805045001018060b01c0c0d00c0d65454006c5002840a01581d21006075000c0750041a001008240c0035103810100000c2c000240c06003d6914402e648403c0300e070711140b0303460105610940780942c05182c101402c101d445c2e58405a00c600e031384000c0507160201d0f603e0700042c4c5400000d078860f101003804048101c6000c4500c1c41c0318405401c8070348025042d41840e8000c584045240c281001608032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 576641205 1250 576639955 576639961
    0xf03031a0919150f0306060b0c15071103040906080f01110a0f17040614070c02010906030c021510051005042d0305030a050d0f02030402180a2306150c0c09 68
    0x28168200c0c070700e00121600d5075490140c4c0c420002c00c0c0601ea512090320040d00d4030f900454007036400381c00c50701c52004120003000080b180350020b40b4150700141004007400b184600340da0004800b88050801020000b00c00500f040c0b610b08520b050007506a075407801649883c51070031020450f041903866404551502c1910b90300101000d036607024114540c03022603107100040004010058000010032003102030340465984481005483c88882864002c1c04280d05400c03d200b41ca1180e88410b198410610480b210148982c0343c0c9c1c464640142c4540340e0280348460148410f0500d0400c401040c11240f0b0a0f030700d4240341c007420166960740a0808010b141300003d0041c20000168a982c026542140540e40c0d141c040d0700025145a008054154805081c280c1d000002e008501c01c0c5c0303100b5a00604101c9a000441050b845881401060a40c0003655900d00b0340a02020081c0a041c2d000e04d0b031002811400c0c007d0410141150205006003100410080c00d0038601c00456030701003012060b21840602c1d2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 576642455 1250 576641205 576641251
    0xb010906050d1815060501080f0a05040206070602120703112b0b06130519031203050402060c01091b0e0106140921060a050903040b040317040e01030f03031a09 70
    0x4683c2c0c00b59100b080103007098541c00c1c446000116452401c90500802c41140e448006440c3d42000b1600d88035400d43e9040003e009200907040194014401007810f441d169080c0d545004036004800041850700c409010404219010301c5030801701e81c2114003060404843c80414803e00268180e080d0b41c002119842409241280e0000a0140030007811a9190001d51403c50a03074541840b40502c10b003450b04441d5020b041c20030b61141500c0d0001c82c0c42d8129081541c090b0003400c005003040b030b00010108401c3c800500c1c01c0c86161070b4944244031200b01148181155070104903160080308802e040b03c001004451380240780099a0b1864502050300c0e103032241e00007007650015100f0202003c07813040031401116808140d50744100314882c410030064403a656426564052400740b40325442d4200001d00100b0840302c10200c0500311a0304003440e01e520341e50f80c895240020fa0080701d038041405038110405415000700044056420225240000d125000804200b400340024a000346078260200c000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 576643705 1250 576642455 576642461
    0x11090402090a052d1527090c040306050606032e030f06020919061d04020903011b08090c010c021309060e160501020c13020306061608090a0503010b010906050d 70
    0x2810b000700100d8100c554409203c11100034540c511300ca0a454104040140c82d14100703220440644000590825803100c00040903444800500c0078408440c0c4500b400640c0c80c0d01c81c4600c13820f500c00c0815100d03803440c60040103481022f00070a00c01c40091081092604840110800450343c0300d254a00d1074900d00886040702e82d20382c01c00b40c0919941031103481403004540050840c0301003510000b0208004888115085c180b0b40286c1c000280140580302200000c0001001c9004c8020300c01481e050001c0006800c42c0c1141e0712250000d40344441d01501d06800190b01a4403030541c2c40640000c1150351300088c2070010081e0003c1c8103115080144c1186040c40e4411061550b201c0300421215500f44440c40da1108000c00722606032200400c0030609520108252020070b202030f00c0e01c0c0245014075080d2000c0d4100400e02d68100c0c0c42400000000c003407032068440d01601604109560350b0983e000d02070205815004280240e052100f030a8543e40d0180031941142e002d45092901c0b964101c21010103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 576644955 1250 576643705 576643709
    0xb0705040e0903250312050c160615051c020108070302070602072a0e1812040902040e0c0408030307032711100f0c0f060b060d0209030d0311090402090a 67
    0x7826040e002000b220242c00801440c4050034031a8000d01c0641441c00750215290000c0300134002034000c800c10400d1042030b00aa500070500c04405410308810050b00710b40503403444000c4c3d0f00980c4410800c0a00031091503420301414096801c80040c400300030008400c0740b400c4e2802410090520300040c40988640e050340c4100741c0c80b090035580e03080c45d07040a05000004001101d910000c95440c204201540c80250b0300300c0b44883c0320714104da900d0030007041265407058a204018040d81920391603517003000c0001c0001d08102000181c50764145904440c0c00040208104524001000144000d1800100f90382c0d100c503213464040b48000380d0390a00085c2c440b4201110b1410b1522074030101c2040514400104090002e545a02801c0050082110000032200010020841200d8120049610501074035500c5020b45808074400b0303041800f05026074042c0035002240c035804141c0009528084c0b0484000256034901030050307101018100ca0700d84114407000d48100c0c1d0000b24034100380c0b0b681c000940 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 576646205 1250 576644955 576644969
    0x50304020109030f150606021f1107020316093801031b0507050105060423090f0d030f0e070e0112140709020901020601090c080708041110020c1801030f0b070504 71
    0x11403001c4c1c1c5404e50282c5040c400715000c4034201980840c0c401c0c80042c0202a19980700c90312080c00c1120f81c44000200070000101c00e65041c101f08020150b01c0c100002e400081c01d46440090079450104540203e411101d82850032003490b00c940100ba21100c2d00e802030b0281961450601c3d8944500140c0c024070f28243c0380d0f0195a011030b1801650345d00b090213028140c0c010002404540d9540c03040008403203d10720f100c0f00d4020801c40b80d031003c00e01105800d5000e0500300480d41e500c1a0303841c1c65031818005160b102d00003501c525555500202a0291400c0c426a150040c104582004481c07180040140a90701d8420007010b05a001d11609800c0d9034900c510342c8060711400754403003000c1c202a60000c039016000d80b01c2c060001603c0f550700d214040e60007440ba80e440d036a0351141740701192144806042551114103040c603007031b100d64034038110b5a82d094007500200100400c20040c080c6003281d032000c5c401100c01d158010000314008541c18001c144d40500b5107880359803100001d840900458100748 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 576647455 1250 576646205 576646223
    0x70f0e130f051b16113706020a0507051909020414240a05130503190606060e030604080d02040b030a09050c0a080309010e0102070b0c01090b06091605030402010903 72
    0x72218003269004a00540810307030070b2039442c00912000071031403048800b01400030b1a00c040340c00201e01c5507503501c0c0d0000d030028243c01e1342803400d040980c100411542c000383d03001100d8205c469505600d000201c02030003580068141c580032521000e898600c03d11a1b207005224407102e8120000e0001d8a40c03000d4600c0c81d00840d02c90307445000401c5004043d01e4030502a005207103490201800c0d4403000e08c0040310342203941d450450741850454150308110b10388200d9413140a40496569001d004181d03c000900d03152010903181411310f60161100d507801817083c4801034441ca107682d1008103800e54050341260700c1903940d51010003c40300900c11544018000000802800040790f01a000086003d000304121003401c428074041061500140c8564450f0b58010098440c09502406190428000500694024a0f5546440314407580306112039940c50755101da000080040701c0c40e4254100300305070382c404003d103030030301d000d00384c22000595107030510038007000040c11a0f1195008078040c0d0342c080908 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 576648705 1250 576647455 576647471
    0x41b0b0d51080313060203070b010614090406060f0f09060f0e060f03010609030302010f1803111006080a03080f0f0f0c132709080f0c1002130f0e070f0e13 68
    0x341c3d140e402007000e103009200352807000a4114400410741c1d40d5142c024141c0c844503481e00c42d0560700034901000c0000b007035a0a1107109a581d8440c456100141015140d8040c00201094000c0c01e07191080d015000303100d0501000d00c05258051080c404a0031242001d598483d100300020b0141d014103007403000e00000010012880a9002454100300d034401d1700240040c49181021a0aa030312240c1e01c10380818203140341c600424030458992a61b070749940c0c1992070310018519228260f68581c1c0003200707240d020040f04000c15620104040d40b01c0803410600004d0708114440500f44100a003655100300b00c0709002c01c1201084804641c3c2400c0071a9001030700350341d5800c0e1402c9142400310945e04088034081da5a000701d07854094004050f5003d4461464004c0300c2a0403203694000d03a9000006100341e10003249a12a41d10003411031468211000d03030810700e40f98179015050144e800806100341040706100020740c008020f4148030030389091500c100602180881d0741e55540303079144001c4a0400000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 576649955 1250 576648705 576648719
    0xf09030f020708010905060a020d020c0706030b0112051e060604150c060f0507140d1404080403060b0619080414100e01051f0b03041b0b0d51 62
    0x218040340d295029a40510342d1080352034201c0e50070120262540c1c2040f000184121016801041c03003101102c0010704050842d5201e83c90f003d165000f43e80401c0ea03038010a1415a0004018030714120342000a01480c945510a0000400031301448140203040c403000c901d4659908041e20090400710251521041c20024010100c1c8a1181c0c1929842c1c5000007607204148903018041c4208035039101e610307000784a1100d0040a51214800d0141c4950740c2c0301180700c100180420a006601070b05040d92101c4c154203205044918030160144901802c1042045c04e1b00c00d86181000841d01781082c8420b0340c2c0d503051045450500451111250203a0140007000c00324075840802d0000303118000304801d50f5181040c0d4100f1480c0403450480c580043d504001400422005590242c03040310788dd00300140c01c1301c0c1d450560103560844600c00e1070102e01074049800c4ca118180d4200c501104019840e80312000c41c03c1d05449000c102e2030030a441040c2d510f1402141d020200d10f90030078110340d20105031b0320300c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 576651205 1250 576649955 576649967
    0x9130c1203030b100207180b1e041508010b040e0f0a0b06040f0507020105150312041a0f0c1b010206062803140c0f0f0307061b080a0f0e120c10030f0903 67
    0x2c4c051100b0f11f10320240c5503c903051085042e00c91025200030040540f900800440303031840b01d10258046e40781c01c8441c04180820540030b009114020000c5214420001004142e82055101000359031085241a2040078000f440074410b41c1c0250060101d82c8034003000c07802810054141c2c4850720b051000b4020030320782c150320107485070180c2003040c10001062405c00d40c036001720350240c800500040c03100b84002140d0090000b00b241551900a01d0521211220f40050301700d10171582c41900103101d0b41001c1c824402d01c02921030401d2010300342919103840000c05025886000c000441070030080d000303506118030708020280d5080510003d8030350440c03007e6547c1d943c9031225240034480144607000da13400c000c01c02c0b440e40c840040c0a00381c081c1c20a20301300c031034a1001c2c090800040d807414059011807240d10050000c138a03184e40300c05245810700d01c0030381a62141c180d01d5001d030802e21000c140307560b4003041c000b1480303c00302c0f88512a6441c031035080b0050b00c1c0480c0007061951501c2c1c039400c20543c000c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 576652455 1250 576651205 576651209
    0x5070812010311100e04020c07030609120f0203040b07110303070605040602210f040b1b0309010c0809030c1507121109030705010f0c030f0504030609030e09130c1203030b100207 78
    0x203482090b00d24903c0709210301a010f40a8440c04904a800d900d14586811380280001c000540101c138065556030f11103205544181c40d05039a03100c140240d0b000044c1c3c0c80b071107100c403441450006619040c540007a03901140301d848000f81002c2c0002c11000c0046da814021500e42030f800010901c03035800d050400400a40c0f000b0900903040030240c03900751415181c5525140b280c07545e00160050b80ea5141c581e107220400c0204103030350710141a000030b1081011080034600a1501c14000601101c008801510b88071000d01207007801c2d441403100141c440c0c00020003684400311040b01c4040c035241c1810036100068001510f220031780c1080942c001c20303a0b1400151000b140110b0441c0e00880e0f07504015290314101240d01c80020708111850300101e40601c242158209551400314034181d680c1c0c0f2510200c5050103c11800500c500c00b040d82030740340281d481c80c0c00c108040800e0400c00407642c0c03801100d558610924080c0d51281e8031010505000ba4401c000b12100900801090501260300940742c000078 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 576653705 1250 576652455 576652463
    0x31008010b030a0206070b0c04031e020415031104111b0327013e0604020907020313030311030702040908030a0614151b010f0e060108210703050708120103 68
    0x11101142952a000030f150540039005040b42d4035201140c0c6620540d440010025558541d04204c0000090b0891307000c28010f458500c22403003da04203104000c241c0700d0b130035004d60207041e5400d401c3c0041010100b000c0c50081c4201c90004a00c9042041d4411501a001300320000c4503042464140c6490084010314041c204c0a130480c4581ea2485000c2c800f600e0100c00060020300c0300c1030003041c1c100408500020490030154241d01d00403011144181400d0013000300c1c042c7c0c1d00880284402c40c2000301c1c020b90815001e0028608003017007900000a0001684005010004c843d801042013420078400c0704c03800ca030080d2062007044103c1c103002d1410380c01950004251807812070000b0309503045500c0e0700ca64050080c4914542c06424a0194a030b030010b0014109081280c01072192040e02481903c50700e0304812404105038110710794060a002d0141e005094a400000c09080070400480b036100b882044046525254401400e00700d41901032a00020041c1c60002040c400010741c1c244e0240c100c03440307 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 576654955 1250 576653705 576653711
    0x90e0a15060e1f020c1203070821070c0b150409020d0b100614040b18041506090902070804270e1506060901080f06061608030a051e070c020a0b03100801 67
    0x10f001403044406481c000d03071801130b040380300100030900d0026080c011280042d0110390600c2020f8441011030b41c040090108041d541c00020504003500b012010381c042010308011401c0c00c0301e80c581401440c00140880d254202161582d51180e5071a444001e400790054010640c0c0c0f01c191801c3d503c850020740d11600f0310084203000003040c41c0305007030fa2101d1030b40642c00b150805103400c050042d103401c440b01c51050714442c100704280503100c0b4071a501111040405414800e45080740151802007290020810389004121903800b1910100442d002ca07108508030610014003500640a030300c42d80341010140f241090b8410b02e407501c000400241d64034030048502e44139111842000007901c01d101c14603010a481d140080c81c01c11100c0c030341582c44580a071460f80342c40441013001a40003000d0074103d48000020013800356031802880f0f515400801d01c402021201c040c139014410f0a500240345000b04003e03000c5d000b046440f044030290041180c069125140d003450080f0391007044003400f0728122580303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 576656205 1250 576654955 576654979
    0x2030112020117040c12060b03012306040b01082a27011b030806190b0304050c01031e05040510090b0f0709060e01121503031709070501090e0a15060e 66
    0xe40409140c019984050300b039171041d26200b901ea851030090b59003698542e80d600710103d250f072003e00809403015000c101d8062020304220454001d0040900040e00640c030b0800140b03001d0740c010b8052034208455840c075140d4038a0385190614405113a0406500d480c0c408181c00407030800036500c0885840c440d0b15100e0b10662004011554500390110340b04120079055200340c08a801000e60903000540902200c1c284206069802c1e105481c0398040d207070707100000040000744041401804807461007460140000c25002040d40c0891240e0485240e0550b95035000c03030100f10b0108071100c88094440400d01603c0e10320704003040c2d454012143d05c0780c04048600040c038064441c1070111300381e405988901c1e54120000c0b004440c100c00354200c81030110303900c484203421402c18055000045229a2b0703107144220694034001010900034042101c47d07881880288030f00da0b08618000705031902c2060900301984c800c0c06040c041c046c00351045841205140020420f6a401904031507444010754003001400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 576657455 1250 576656205 576656237
    0x30605010b121311100203070309050f0315070302121512010902090a0c090e0c0405030706090b16030c021e0117060d02010503100b2a1f0f020409020301120201 70
    0x1100d2441c51950042e5020005942081c1c4510028456030040760052401c0e5036101c041091101d20080c088050f07031000c5102004c155003e28210301801d82074403141444c5a42c8404030f03071781c0d001c0305009190328802c070000200040c0c880d6040c0c0d1210540b60030b0382d04540c00e042d910540c03094160310aa501904c15141c1021103000140203002500d07501410906042da144181c41c8005c03e0307110301c50742c10018015000201c035000011264020714180c0c88080d9142d20700030400d0f290138000e80c840070900c48114800c0103c1c0c2500d030142c804544200d9036807901c0000c0740c50211003803040781074000e40c0200400c9000c1c070407402c42980d1250080081c0c036a00080c0080c2118840b00c143c1c11540950b002120741c40310700065114a0181d6004000b40d01c040c108980c07948050282600050415814610400f0f4142810b0083c28807410f443c00c81c1c0c40143c100c0005030f00c038145c48a0844a03030750445a4a800f0704009408080d412903005054240003191a940c40e21001c080685a040050340040c10883e0707154054 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 576658705 1250 576657455 576657457
    0x9090b0f13121b05100c090605030c030601030603050f0105010515040b0304150e150603060a0522020f040c080a0e010e1f02070606180e03040b22120c030605010b 71
    0x80d1546203540c80c60309a0079038910340320b01c00c1ca090300000c101808045404504012040001162280740a04a00300d00d5000c140104c03900d060040b800c210602000f0003100f90010308581c1c024502081160b0380c0d554100059000c2c0c5000d074070042680c42003101307149807200194081030607540c01301c3d202115540103d06002c940e000d140242500d1400030404140000c2022900601c440708800000c507043c2c104038034642c201402a00010744043c00b01c01040204c0c901406203a500c070400b01e4080255040c90110b02142c82428002c1103009007104d1030040c203543d688490104010070040050041841461004011280980f4244807090400c0b00300c50341c1001c1030180640384071100009041030403110f0386188000c0b580303951001e4169820400b54000c20002e010b1400640300c0104e00315100034103c9500b20840d0111039030507103641c0007030000384203090304e40c4111004820410180325014070001c98034924141640c2c841c1106095028138042006454021442280c1c023800c0100242e1307903a400600c0c22 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 576659955 1250 576658705 576658711
    0x71b11060f120c09030c040906060b21130b0402011d030303010807060206010f120318050d030302030f0601080f060f1f030516030908070305030901090209010e06100905030c2809090b0f 81
    0x810742001b0f0001810b070030aa0703c038042c45409040e0100b016076850060303070342581c400d043d400000e81e180541c83c800603030034194035904419800310151404840380c4613601300d60b50140c80241005421890788510b005140e2801c1c0040d0f00083c25280d0700c1d655221407958501c401d100e100054041c10b000001c4145561602000b200c0c0c40744440a0000b80f070381e40440315031411030142c400c1140d03502170114071134441c040c1d1713030101901c08e032001662406c05c517000342030426008110310304000d061020402c8401100b020a03400c00340a49200003450981c40024200b44000c00390641603021400c01c0004840c3e0541205000d10030040f84504010305e4402c00314280c0d00c209101403c0c280041164400003489800110f1384800744c8000002c0c2080203038001120b04c07001b82d0100c1d6004082d501031202c08d01c1d28034421440340000d070038045d20760f916100219442d09904e0801d01e1080a00100c014020300c0c0c076900c41a00500c0c4604c09101079520b0b020701ca0300400c0c164070b00380d0340708012a0001d58900c00c08203007140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 576661205 1250 576659955 576659959
    0x15070807021e12130803120601030f090c030204020f1b01140106020312130f020904060522021503090102091507051b010c3314060108071b11060f120c09 67
    0xc02488003440d14440d9400301c14910007200e02c440c0300140c1c840d0140094940b51b810815031144a04023600014180c4038007500c0388030001e2604507003100086ca50b4581408a0b6815a0050385034180307180d802c503160049040950b280d02c0e51107215205a181035101d4902d00e900d000c0340242030707602d41d4001c036902c1c0a45080c00c40340030010400705501c01c464515021405115100e0582c000c01994086406003800381c2d000c48030181c4400500c602d40018244c0d9407809a00109412504e0f07020b40c00107034a40000c05202c1c01034410000205d040036000703404550070400040c1412101c14100842c2907216400b48034140c809000700203003c503404412680f400e03444941650350042d03a40c040e0700c07a00300c0740d40e01c0445480c520081c0500500a400d0440819550010b03071000002d50140501c0907401e01d0300300601d038504003c17840303040002131ba0300450792030f09590240104010341303050741c80c0a41203a02e5605116501c0700c030101700395003589a80f1b40240741c0b87c8001d445210541e00c07403a400b403400d40030300e1600356 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 576662455 1250 576661205 576661213
    0xb0702042d051b0703030e07090e0703170c123609060a090c091805160c1104050f15030a020109151202030a150b0f0f0a0215070807021e 60
    0x40c014140c1d03a00800c0d040b452000140c0a802007410328205650b000c0c80c01200803e03100d051545503180c061049500410030450b091003002e1100d24615110307400c07400300405800d0080d00710380340218071800783d9003051070080c2203605012450003801d07246e410901040c44021601c00300c00442c950a1b074280c000c0c10b101d0380d003102840c01880003080b00903440141115045000c044c0001105000b6028020305d911403a1104101e0504200890f18031080d080e408140701030400050147c00408804074108a070300d14030b00b0300c0580e58241f905100c0c8a6507500340550082c1080d081c0318202e003c050105003c1c041104d80c00481c48210340c1415101c4911220190120310324072420850216041900420080c51b8980b42484844103040c0d402240c006a42c1c000886681d247c1c407408509040a03107502902c0c002d10080c2c00c080c190100c0c00258440c1c0740c0c42d5903041102142e0100454020041004c05a030254a601c541e450203440040820808442620040c4950520543d040e805000c3c900420a5008040c4c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 576663705 1250 576662455 576662531
    0x31002070f060209010c0209010f0609060c1e23030306090108060907031401020702030a11090c03100521030a080610030e03090913150501140a080c1311040b070204 72
    0x4800035084602010305000c801c00c40000141d55100e6414003034180803601400990411100a10cc00c0d2150004418082140b0b02500407400800307a03d034030741c0310100900d007d0701554940300ca403040400d4100910021182d4001d20061000300103188118020f45886889a80c0d0701250347c0c0e207130400d841d03007085034010840a2020030901c00303d1800010061002600d020166404a464010049001d07145400032078002032312494500e0905401c80380e43c40d41241507060951420b0340c114074a2203424400c43c5218103c0780464440745041041c41d400c0001d481c1c54900c5010064592881110f115110b5540082c01c5501c05010344149260b0000b440000c42c14140d91900380440c552018095402d0a414201c60310001541c00007004641c01101501082a525140068804101011940c4c0c0b041702410b00074001d00b10001007504140c40110303448030b0102c0440c0660030051000801d44140384200003070118540d8590002012510310030b88003040485241d0700c0c1441510400341c09580f1030207100c016 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 576664955 1250 576663705 576663713
    0xb0904050705131805060102031207110a141c030501180b030a05010e1506030c0f010c06110d0207142407030f0507030c0e0f09011502030c0d0905031002070f 69
    0x2581d4003400c5400c105103442d01400042c8900b411540c008400d103c0000d201c110000c0c01030003000c0d0884030a00085041204200482110b1500108810104000180c110b1101c00041000c01c5443c2e81203800d204059841900c00750301e6082d42034803d56244464200402c99134860720070b2904840303082034204000c0359606400c0c005022039056459142c840c00d910100412002e104052140812400038016245030444040c44000c0050525200f50401c40c061500ba880f9106c40c50000c0400b440c1105908409140c200c0c0101100c190700d0b80044008104a0201003495000344005406600ca00e40b503501d4108110740d461401324101103040b0301901c10220320fa007010419a40105490078007141c100c5030380c4416000c54034102c8101e000a502c4140e442041500031036041d0f40504107680d221a10a2048080349590394180700d01301d034200a4840780507100e0320a00542d442e06600c0c0d410740e0140d5a400e2801410a1094005c40c2d10902904582c44050005482101d40d0389038030201d9007a0101c81521 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 576666205 1250 576664955 576664961
    0x1090e010b0903030f03092d060604270327050f10021002030a0f1812080603070302191a250317160801060c080304200607080913060b0904 61
    0x90b0150903110900030101d0012404000e1880f4031407080040c4119009010786049681a401d522016444c80c8031010b20351800115101d41d2068043e14040b4040d41040000b0f00b07400c0d940c9150000e545074108900042549c420102c1c0e41c04d4074201d4680850054038000c0440c46916842001c0d0300101201c0c64201508019070408076131000c2d030068078141503828032400280d03801140c070034256035615008034059440910400241c0308580c040c03152110a96074a840d00300c05c0742602c10051040344400945150303010030070b00c006584d001d0800f00480d40e48031402c0900032001d000e007204025902c5801c00c0b049240c942076903282d4000c0810080440f1910040e234009000c1c4280c00e80400200c0081c3c01918064205c4685c02155152402c0c10160103e00340188444010f8100604000d0714a04904c0418203c40580c1c0d001600300401c0c008030803441c241d20402c183c1c0e883c4040d42082002ca4907500b03002c004000750111a00c281e13120500d005480d0308440460381d03903020b001046201407203800c20a0078258 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 576667455 1250 576666205 576666217
    0x8090f1903050f040e011d0702030702090405010f090605060a150210050901060b070f12080601171905040b0714070305030c0c100f060302010905041406102c0f01090e010b 75
    0x420000e14020500f00304800f00e520a400416480006800421408420b106044000c0038401070b640840d0512440c020349a01c50698041d1241c070001c2c0c04a01444800c1d480341d50112186c0c902001090190318014024100071210b5621692503208001101714152074100303404a5554040c0039191441c1072601c001f050054940d400d6503513074040c003007225601c1e034000b07006050003102602e0100d40c0c4e520703141c0388103901d501300d1004200c00c03402030202c240d03000072000422004603e603510140e41d840c01401c0c41d60410140340b00c011030405003403006003e1446481401f42801d0350301d03061925002c072180b50b403512070342c0300060001d041000045c203511540700c0a0010600008140e406030381d4410315010654040d000e226440c1a9605c0c0c0400842d03800c106204014901590300340900424901c1100b008a070040c440340c06030041000b4000021b11802403040c0f08030390a01d00a5031016819a065014800c9142d80380c081e481101c1d04407010b60007410654100c841e00c6000c440142c0c00c1c0400a40c16030820 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 576668705 1250 576667455 576667457
    0x60a0e06070602210603010e1612030201020c0102040b0301030b0703020703080f060f2805030a0206071106070c080304170c0d0210110307110102010b12100c0c150c08090f1903 77
    0x2400500c848a00100844210a0713843c1a03444050502c20201802c495988484800b26407202c0c445607480d503130058001040703030010100c00c60049a107080580c003900c0f0380012520039500c00180425100701580155040c1c0340a01e640110541d07518105500328441d01201401250403140010048810003004503800318000d800d144c9060000d501080c8007240500d4094445c201050080a003942d2400b2404001c14003100180362425503900410340c030703224034000034101c81c0c440e81d980030841c2c50304400c595226074044030b92100c1c1c55886c2415070b125041402112420460000440c240002c006452441c0010051030400c0e0081150b01300110b03a000180c42c0c100303100071560504100402840541002c5000303801e948418a0444002403c5560484080d48282c0d1102201d007070901001490549200032407500154108050708140c0ba2100c003001c00804150080403c100c3c44c0b003894200c1c05148519480303034400740e1140c02c501a2503c0c0c0b40031381048103070b06c2080030541c0d014030a00080c40803030003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 576669955 1250 576668705 576668707
    0x60d02120109050c010e010e0d142b020706050a05030f270a05150106080117100204080f060c1801050d090b250f08070f030605130b01080105060a0e06070602 69
    0x40880c040c02d54a801005071030300e400085100001d03580103072107621040b40920f442c02203201150002004480c2c001030180c1100000d0f440742c00fa0368020001c1d00034108069561458440301d40c0d801d48134509040350301e100113004400c80081c490340100251180212582c0301d0904541d14165983c40c0c3c031f00700a0400141609440100945990589017001542d00c980c004e0001c51515060003407608110a000c5001680c4c3c000c0104040e03a407101c001070641c0e803002c010b244100d180720340780b80c5004001d5444064007440007800095407000051200703a005a03010070349003117942e03030582c4020074000c1500002e20040f801c1c02305411588038500806044185000004041c00640c031003950719201200c07a164051030061449005d032035801044889001c452401c0006a4519580207020740800341402c820301070a03100e0300c40c0301d134065040040070701405400191820b410940c1c140207040c202d81c0b440e004c0780202c0c0c004070311400c00c0000c54070b51143c29207910903d825480305002065210030410340d04158 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 576671205 1250 576669955 576669979
    0x14070e0a030c1d01080c0d080c0708030a08090c01020a02010909020c1f0630020904050c15090f0102070f0509060111030a080411180f0a061d01080d0215060d02 70
    0x70b00400074502401c1407210340300c1d4140c600c040e12810030a0603008011280e00100c5103031410b9a4400e010510703941d21080050f200c1d40003003401403074000c403500281c1980c040410100c001e02c0d800310710541708002413400c880c80c040d0356400690316a441c01c44081d0005a00139818042518160010a41c4118401c11590443d5008100e651401c80319241c0910503500d9040c100101c046000040d0501c00032814109000d109c0600f40702c050200071840280500e010000007414400140700d080800c4a028291081040259440003580d0380580b07a12449440804124150713944000b0715481500c1050045141e01c5c0e0400d0104040741074002c000c14100201500416080b070020300c09003e41c00c926455083c0941451320307107543c0c0580d05000007401401119602a000e60f00840c88139080810a0028950f42d140c00c0150805001c0e00d800240a1400e84641d20800c1242402405d0496000000b43c45031183c1500080740c99414a1100c50580e0000c2d002040f120b00d80700024002c034520041520704195 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 576672455 1250 576671205 576671213
    0x1401090b0d080c15090309010206060303030106121a04090f030201201c090f03050a030c0c0b04060e01180f1703010b181f12050114100e040906050903030403090914070e0a03 76
    0x13010032038018801e500080340f10f10311540c0400c120b40c1c202c042100a1811503040190080c28007520000003600741c0d40301d41c81c810307549141048400083c42c003d4010722152400d41400d0301d4208040100b00c00642c613180307404809240801100301400030305d24600d0f1030b10000c0d5a03600d02c500c13110300c1d070a00d80903a6480b007c0300049a160342504c030b82c0e100792207540d01c0c0d4081d550041c0407200640a52410f00ca90300c3e803d40d00050050080c90b60290340a600020b1955080c490103004101072242c89004010164026003800100350990080c43e104680d94003118132030f0340d03e9a00502083c1b062103503c81c414441d0102c032010400d0b0a0b900554080c0480c1c0d8009410b0864484c0d003d410f0558401240c5140030350210102d4600035507001d003194070b002381400344c840d6000ca07090320a03080c1500200828941c0d800070a0f80d680d0450904690040c80610850400d049001e40ba688195011030105003050000a08200a03004000301410440e45900b400d64031690b058500e495042c080682c841d410200100000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 576673705 1250 576672455 576672493
    0x160303120605060a09031e060e01060905061f0c08091003020901021902010921050601030c0611060103020a06120e101a012c030f010e011401090b0d080c 67
    0x450180d039425061210030320203a000c4400c56082140514401c010300c60886030001888411294005540580c1c0e41c80c2e480541181001c5840041a03641000e0303403104503140541040c800c2c0c450340b40c0104816147c0030200400c6444804c1c003107103c0c0380c9400400000790f0041c0750b54050180038076000c0e89440d2101c070000d2030b048004a014400f1a030701180000c640d5070304110724600c00c2030701c03866100d1428460b0006850440c41d0b1060f030380e01c65030101c40b00c9500080d0480001896078040c0403100c4950712883c2051407038455001310000118541e09585419000143c00380c101ca4002d0f1518030200d04040301180c07840703004222040e62603140c881c1d07103d100340c080104800c0d80340e6100d4002031010000c0207401e0080e181d109000e0401c84a80c29488214900c010b109140c40d4140d15590707250102d40010900f809010049006207500c1c1c031100c1064080c064000c13000000f041040d415481c1c5e01c4510100c2120403800d9090341050071750440d0400102908020041490002c0c100c0b549007102920410007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 576674955 1250 576673705 576673709
    0x111603020d12120f1b11120d0f0905072904061d060c010603020f031f020a020f1002070b01092307031512020a06051204060b011803061a0306011802090316 68
    0x10260b0b6268070058541ca042c910007045d80f000e2620050a800d8001410f0740c6100c400e2485200800c002180c0e80f0625055010300400e04016606128200369400c02e00d071964424031920600102d003940001c145400c1268005001e0b010001f65800e0501744182215040450351744020b40c41c01902c8180c41d00d948007406412000041000415004e0541c4140051a81c111420034001e91240947d00000c1581d104800703560b42100d200161038415244080380780c03051001c0e0301c094500030800f41c504a102c0b142c0042450780e00400707014213240d80e03030408501283c0c06241c490b44018422035070760000481a5220355000803062802148208002c60719001805040e03000140045101750f48808604010394020700824690415508001100004811280d0010401001c3d43c1d5a48600c0c1c0081c1e0042400500782d0180c40c071f220300030326140d140c2000100850f0382407151310345128000028510340029241e050700c2c0450100d0b1ba00d40390302c140d000301940100411940c54000d03814461003540e229886000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 576676205 1250 576674955 576674981
    0x4030605090c0103141509040215040602030a090b07030905060d060e07030b0f04060f06050a03020d0c0f020f011e09020303120a020a0909050f1b1207111603020d1212 73
    0x1503402c801c0016045031004141144d080d00c1c440100081c01e0441000603030058025541c2c820103649520001d2015200c0d020307109228030b00401c02065460b800005011804110741341e01c0b03801510358140108500030210020b000920101051249040c0702c0040c01960195801c0480e50544501b400910002e0032680100007039a260301402ca90b141414505403071020135201000801d0400f020050000d919000741c1050200003c0d001c08070a03c0fa034102c49071403402c0401080b0140381c2000041250907140b844000502c60444031000001062043e00840c0070a980704014001c001e40010f4042c0105100903685070000380b00c6403d00c010004845803050b55400d20050352034000e020b010307003141c0c0b49030041e002151070442002000a102510340f9041100c01429004a01207031001c1c9501c0d01c107003216030100744c41c0d010074404401d811a000140c2e1103c0340c802c0e10f004215102e48500741003d64480651b10900040c86000401c1e00880b00754540d81082c90260a918144000e8409a8001d292149 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 576677455 1250 576676205 576676213
    0x30610030b061905031909020d02041d01090609021521060a08060405100e031204020603060d14060105090c0a090b0c151e130308190b030d1d04150303140403060509 72
    0x1e11090000021060301b098450070001510b054010030380704100780f08003d000d240c1c0c689070840c580c9100003824054150721310080c00403d08034600040940341298049000340708504c8441d03004207549082e5016102c560f0000101c0b80e01d05400508800e02c0501242e4000c0d042100c04180208140301e1607104030300403001080c4416203000202e046800a0992000c5a0000d01041350050351100d0815002501114025201d0300c4510001d43c0e4070009410003020740c4182070701e0340c0c1007d0010849034120707141240d02c0941c41e9241d5845200300d00c81c900800b000112010030030b11202c40c07444c010304038000c1d03031004407600c01001f40e60b04030640d0000ea0300c103c10000c004280422164a0b92025070f03000020405403220b039141680d0140040c580544000000300c4240da010f4054030841d4480344407603030010b0454a04040035180545014501c2040303203061400a10302c81c81038201801412100242108010f483c2d5156407001ca40ca1200f4420342e08246404203c00404501d00340150340c02004104064 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 576678705 1250 576677455 576677461
    0x20102031b1303030c080d0c0804031106100308130306110403170901090902091207120303050603160e0a0e1b040b0906011e050d051614030610030b06190503 69
    0x7000880c0c0300d280039290190030400d1001c0c940500516070100c070360505108411440d146400c54481c0640901003001c00e1605003d8440b065210820301c0c0500c2c001d40394008034022030140207484035822100200c0b0000108410000240d140d802401100c0030408400c0c103442d03d03581c0d03140507180540d0070349800c1e02c0041024028004801e452400b00a09030940074070341083d850018142c1e001611603503800c030354040b50300c1c061038039012a0707096510b01204c1910421030b01c2c0d6030103142c82c0703103c01c0043e0006031420000540a007800590010117000d00010a0103451400b403080450403401808141e00f40c1e00c40704400700c0081c0801c0b500e0200d408101690040d00324450034441214072107040c0030f200300c1010301402042c0c2d0300205a0120914030030f84008440007175640584a500c101c072803161801f0b1410041168030b400c002d00c00c2090130042c2d910043c40c0d49182030070501c0d5000654800da801a20a6003122205000354401040c044002c0c4c1f20a041499115084503600e40441045010038400010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 576679955 1250 576678705 576678721
    0x2010e1801030b160207090207030c140102031008070503192d0201030507210b060702180105100c1109070c02030610090c0507030c08130513090204050a02070503090f01051902010203 80
    0x10041d4050310000c59041c0c2030184410007552206c0c06d21410029a5000641400b4144656a00c84085410500401e80c2d040303204101c42c005d50003190310030b16000a20790702098042c40803a8450441d10003d0003400103058010704480b50b002c00407002c40f00b003800e40031242c0c8050000c04845046400b00b04d41c0e80e140844900024041c2e4100411620800c0101c03030485c10403540650180303000d24150b660004012641102045003442001000303076001303a40320030304145200d4422170281a60001c0e504250680c18202043e40c00d408800c4000b8030218182408402a04145184640c000c4092410451648075900460305040b01540c0c844c1d000b041400050000b10303500e00401c01503003143e00c0d10758940b50036901c0060000d403081500a20425000482c83d2029040c1d128030409860000d10010002c80324401f06001008004000c901039402d01002900c400000d00c01c0d180c095030084081c1d46880780c20010481ea42950306100c03414070005000c0d91510095010b0030a0110019800041c0d8906210403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 576681205 1250 576679955 576679973
    0x9030a08190f080f1b040f0513020313080d1503060c090f0f0614043b07053921041203050c030403060c0e2d0d02010e180103 55
    0x703191001c0c40000b50b1811416a480fa6115a101320900500440c0ba03d4041030296401400414400030601c08540464103c0c2d804550f042120421550307204450f0200b11034a090b8041250240d80d00480242d0700404211448001c0061080c814000a850722034502d03403400280c21500b05961140e03641c00c015045580040401024160102d8140c0700c081c508540d0018601c0b40d030040000300182004051031100409042c1c4004c0d000c0c0c030710503072984d00103070aa8441280300d0307026007140040d501e6490150019852501401181e041e529140b404000c40c1c138001c281c070b10300c0e41c0040241040a005245030b1021040d01c0070911008009401f0b00c06030102e403010810306075600030780144001c00040200311002c100807540281d050500989954814451034150f00860344043e0010741001c0d40c005580754000700b40c0544103400c55004900c0f03a2203120075040d40b152522007200b4580f4040f0700c0e945500e0082500e581040c4140343c0140b0f0070810801080c9220300030000a861400d0601c010300400c28800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 576682455 1250 576681205 576681247
    0x70e041104140105060723030703020d0f050702010f020a0609080408010e010605030c0409030219030215010e090a06270b010501140f030406150e07080a050907050609040b010509030a08 81
    0x441c02d00a5220703109450b1078510040c0f05503031090000040f803204002441c00c000192561490500034004100300c20795031640e1160000310014051229070000079401a545010070b0000c65a0b440e09003c182d50054440c0c2c038003200d191044d4404c42c560207000400034010010501d22a014241d11117285c0407038607003501c50b47c0c1210201a4140141801242c030f0019213100b4244084402081104050034141d06124003401003020307011b06c250040702403640018420b480000700314440c28143e030340c3d0110309110400a58007640d91750091112000801d200350048401203402c4011100b8601c42840c121040304566401107440445e0340004200c0c0d9a0030030b100005600351300b03882d6032070000c0724403020000d4800248010111503840e8071110302111200801005001c0d41e0303480700c0c200d0816100180213044111141c10032581030200240140c0070224041c0c0441c2d0015181a0034000c1501c200b00c0500410006541000400d201c13104090f0342c200504d4904600409205540c0c0c42c0800200d13400c80110 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 576683705 1250 576682455 576682459
    0x90a0c170303041b080303010e04290a05040501111c051609180b090a0902030f2116350414100c080a110601050d080a080702010b03070e0411 62
    0x1100d10111403030200403030f035010340d1084540720146460111104200d1094212203110710011001180c0c3e61040d2030180d0140e401103030001d0103010030032803500c0720721498252050b04000709008100c070350354941c01c002c2c3c00c98031800011441844040c50918150000705000e50b00310114070b0030010410f0f441c0301c0c580e000204174424400d007a410a0b0040c240e64914405e6001d00c03800f86020712040a1582d011241d01c001c000d01a000c02d0501038a6070b0040c00c107100381a4401c1c0204008964603510000344480310070311801d004a100c1000e0b110411460f08000c0c02c640e00004141c0c045800500501c402419080c004c1c900099040000340c01c034101c200d42122041c1d8000c1c820801130040c54071181031801218802c40740740c4030031280071404a800282401c00288038450100d0f230f0022803a003148507404540c00c10011512103030b0380e036030411644402d00c0d1005850f0f024100300c0305606070f200d54002507014202c1c2c00080b8240d844880030030b181141d0b5030701801c09072105006100c10000414000c0c10b0032501 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 576684955 1250 576683705 576683729
    0xc0e0a0e01140d1b0b1b210a0201140403050703020709020a0903060209040902041103070f03020708040608060a15030c030f020a0906031808030406020a030b030a03020606060a1106090a0c 82
    0x109850b061a000301d00b01c02c1845400c070302481204200b0015980c501140c5a000007070307421541c41014191503042100301c00d1580002c5070038181080c10018443d1000c0182c1c0f030364031481c02802000036815078007200b862401c40d52a05002c910300302c0800c004134040c5100395981c0b9501e0189040090a04500f42c00000e107450041004581e0b02c1d50103818081600d0300000c0041c0d480c080d020002d030080503a035000070341045c03c001c215850448400040d40c81204140c80f50103102c401004c00700d040784240500108510782c2400f050244034410b60000d6842100030300000c0e5980d407a0425540700504640580380001c0c2c44210811a4039403501078038000d074030700c00c01c1581841030007040179041c0311490080c401010f03030340c4034130800040420301c040c1c8185810410b0103a40742000c1c1041070203548650240400f00c4c1c1850381204603810001503455145406901404603601c4010402580b540104050010011680b85510050030107110090103005200000c1c02d2003030944c648111007107100d0f8421200c10803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 576686205 1250 576684955 576684959
    0x80a0e370f0206030709080109110a0630110c010c14090d03120204051005030a050c0702030d0c02060702060d0b0307090e1009020a0f080a110603150402090d060c0e0a0e01 75
    0x807114011260040e4111422901ca81d2941710844140301a6840b01d00303150f0078004460144401000202d40c008802d894640c611602c50b4000d41e40c03000c1c1042c1001452150f000c48501c02d280111400103044070b1250080340c03102290320440e6054001103145203241c0d65036000001c54130703000140451094060041c160812503580c1c00120441e0301e60b14041e0a20441d01690600194190704860140000404545070400c11750030040035a0000c0395600d48103032402d4089016280400290b840043d4020000e21801c4052001140e402100c400126000032040c017140005a0780c280c080d06c49080340b070300005521000f03941014a081507650002c400346103030800f0b4806004000c10680c000d18282400030403480184d07c0812103911f09984100341000070580f000c5008100412070210700c9000c1e601c074070456000102007240303d1105991001c040c4010100450040c200368000e0580743c54002c2080400c43c410327480b041c0035900d030391500c0c070300003070004001c104146800341e5900003810b110591504998 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 576687455 1250 576686205 576686213
    0xb07110d02120a1b151a0a081f09020406140306070c0302031e090915100e0d1211070312020f070302090105090c0408030408010902270106080a0e37 65
    0x71040c46043c0e4104a20740c02019240501c1400d240341c40b40c2e100c60003078590410110144002c2000f40c28282d088010024214018a40108004185d8002102030880141c06e6801e000c01c0407054004003045a4542034600d015a030340d0320441c0001c1c01a40321b104c42c0b845000c0c0c10035080c50310041c108018007202c5a0240b012940c0081500c040056a885441c0318042000c0001d405d0b01540100c554481c0030f800030808030b022201d490f00304c0d002080d02d040d0101d0b1006d10050328a203c4500b402500011901042030101703400c2d44209003400303ea410428045c10403800e40b24109506038006482c6039110380414500154100000b810810305d90300900700c05425603000607100f210620500c0d1145000c203020039114404002203c1c000c003c0c00003200d46d0b813642d0f0449103010706040a810707849950007080c1c0e6203a03401c0e02c0d090624804c00002c05c0003042d80c200001541c00900c080d0a0318401030340e954071110314000401c4000400a0340f02c80742d205042c0040c60b601e00035141241e0840507000d00b80383c014001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 576688705 1250 576687455 576687457
    0x9302601050909010603050a1103070b0406050f03070e040c090311011106010b090616030f0e040908120403050c0d0201060306050a090c03290106050309061f140303070b07110d0212 79
    0x340c0c0d070455500da516198411110702601560700060194042c81c004134080020880004419000035001d49120355a640006003050150388107010100700101320501100f48090000c65200c102e42c00d0207001e440c91800401d0458070b090403c6400f240190900b4000e1101a4040d40c50000091805485039001500140c3d02c441042c031400b840c884010aa5288540d100000c1d5860460441b410780009041418000d00741030701c15400e8004140e1802003002d281c1841d0041816803900540030a1400e003440282001c0c00d04005c0c0f09600b01b05062011002c0d5003018490f9803010316003580041051070850038402e04480d0040c0005400c01c2c42c140f582000034151145d8401100e0b00716001240700e01d5509000c001c01421014917400c92070042c40041441604540039500811448044840c0c1d0360314180c4503030081d00c400040500d0300d03c01c00010003165400390150007080c00090142ca04020040d030381c14032224402d682070300101d021010703d101509402c02c0705d85c2654036a4030040c6050381140c5106611 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 576689955 1250 576688705 576688709
    0xb1509040207050120030f0a1b0e010e041a1c0c030f03090504140a050a0b01021e01061a030117060c040e0a1d010f06090e060a09302601 60
    0x210307004181e42040c46400c0d802a40d06019407841c420703803040204494000740d4070032181c820075030120001061146e0b00c180308415810001c40386005290380c080009441419030900028100002c0110710211901e0358014400210383c845000c0781403003401c404200085c041d240d4107008a103540146107021800080380c00c402c5035002504015407000c1410100c4000206802131600301d4100b9441c000c1910341034010910038503001004004903100d03111510b05580708000428010392180c0107006c0d075030300c05503041c0c05900610000019116a80d18400b1072121811103040c0120307601000411401003540e00e42040d030661900605110700d072612200d011070269000d1200307080c0c1e400c0001b03204400c0c5503200d5011114136000741c01408684000e01d50107040c440d40c4241206007404000038092640e809091222540c04010b07150958640c0450b00080800300b40584078000206840f950711442c01310083e00141c0c8004074411000c0c0360200240c040200d4205403442c05070000140480c1d4251701c00c0080c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 576691205 1250 576689955 576689959
    0x150603090307080310032a3602280f02060c0301090f06030203030705010504060b0a030b060d0f020d0302070501090e01061d0102010b031203090c010903020102100b0a0b07030507060b1509 82
    0x504d03901c928400480d0840c0c240c00051442420b00d202d40d05031301e4070b0900515602c80300c1000950080c1c40380b40c11080584031290201e8100d400062200823144060600b0107400c0000780300500f8030340b00711040d010b407842c0c02d1100d21411b281310b034820f0010b41c0e11020802103100700740020041800d01644d440365034403051054601c0107550707020403d150740b0f258101600840d0000c0441c0c0c0c961150f030400174001c4c03100756412a2040d103491900a00750038060004400c898021109554590b00c240c01e005000724401801c44600814280300ca006030f030380c1c407030201d5001d01039401040c071141418005007a440f1207820440c0004107900040089640c0107240c1e07a440c80442c841000c85561800c010707405400aa03000b00c3c0d1501891a10b06a4140f09030080d5201d107480e5401c82c0c0081c540d03400103440011080c040a030042e040100484a800119000800904009805048400d039103004106240d04540000c0340000e40000380031041c0b10301030180a9072131200b00e07201540100c01c1c0b14401c4080c070440c15418 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 576692455 1250 576691205 576691207
    0xb060403030c080f0307030b0109060f020d18080d05120c0711220c121d0c12031303033c0c060608031315081e0411100815060309030708 60
    0x20b041003200c0064034402000f942c0303a0303a2603080080d4060041c09140800324001001d1060000d0042c2c415080040e808146070080d014100011004840c811030b14001005104100c1d00300084009003002403103e608000c0e51215290806c084c3e4078149142d01801c0c0d49400e280034804c01000c10044200c0302d00d214403c5071281c503000a042c522060030f4400c1140765810520746070781c080c40d00d504084200500c1880d6102001004a1181108580c061f002c42d01c801543c41000301c8141400e00b02d843c003507865040341c12070b82000d5420400049121070f0703400403000503031036094400410389610031050440101d00035403185040183d02c02c070440f08404401c0e108109009154506118207507010101805000301901d0b82e17404d6000854014050700c0c403480c0b1a5004007894425003e200e030000e6405030446400d0301c1180700c060400d4003100c62000d88141c59101010411100a41c0c0d0f090031035020140903140c825440c81c00848840345050308407240d80c00380300d08104001cad40d0b1401204031015954020303489 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 576693705 1250 576692455 576692477
    0xb090108280c030b0d060c18030803010b0c0a05011505041406030c13021303290f010302010e010e060d0501030623130c0b1c0f1b032d0b03010b01030b06040303 70
    0x48003e070051300c6255130844101c0e02c101d030502801e038004c0d440e004c540352600d90002c0003801040300802c0303c51201501e0721409000500c06408503000500c000b107429000c845060210344c41c0c0d242151585004404500e01801080103542001d000322280901000f5404600e8604540420303220404500c0c0c084c070031050300103c49049041030b410340740210940566040c526840e4580380100c0802d4609807600030b0020480005000000d0008e2441100345441c0f80c03030f89910750380c010b45051000624031814040c140c021111140c41c1e6038003601d0a940f809401092951650034010201c4410040a90703620412240e010641004800c3c2590400e0380c0404609101041e070620b0452007042d600800a0100d001584280f04103002500f8000b491b2100390411484182c540d14500f2140c0c5080e441b4aa80c5507150200c055a00947c401d0410b6618001090b58101140c0b40101c0c00c01c95a80404040c19a02c1d144131515040910640c40802c900b030074104410311030300000900d1030240e403000a0401c8161000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 576694955 1250 576693705 576693707
    0x50a050910090807060309060b2403040203070e07230a0522030b070c110306011809140303090f10090305120405010608010c08091603030504210203070b090108280c 72
    0x2c001c01440c0309419a1015921040020040e2082400c180c460504140714403040385890130440c103090300701c06000402620904814200303504000e1050fa498041d00c000083d2882d40390515600c41c5410395030744690f0020350642c02c070805503e400e994220030418081503c2868120044911000400720300c820390b1303200c00700c0c0c12200116907003009040c82040420f0204035034101d83c0e10300056109540000f12110003205050307481c1800d00c04c5600c0040e02064035038075515140c0c801080180610561004a89141070b01451a84203881d8001c0941c01103215040010003802000030310201110f080c030004000703840050183c00760032001c940c04501c00b4003290812070300354030020050900c0e170000c2c080441d074201c02401d020401c40d500301d5a4003580c00716010803019000d00304183c87e0300d40c0b0b501d802c0c14108000308800c0000880c980700054000c1c0040380240e5420441e0754000d1544000042c1e50754940000141003401c050602e41255000c80883c11801c12156040034880c0c10340c0d44005070416240d40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 576696205 1250 576694955 576694967
    0x17070e0c0c0304050607032c06190e031516110322120b01033305180f01020406030c0c030f0e13090606060e060a08040f02010e150301080607050a050910 67
    0x130002e83d1044000400008042d00884040314902021848001003103100800080141d0b006180c00e41c440f90404c5549055031a0002c54032a0300a0b0780340c07040895603040d0100b032400303004817010903240904c002000344c594004141c05c1c2002c0d1641c50032024681c00049502e60340e02440e40303062149020301000c12116a222014803008151143c822404010b05040c00e149240c428041513459114007030060440135a440900101c5600307201c03c100d00a13180c688440002c2030041c0030388070520410413114a000780304002220100340710b000010b81d901c0c035200014007103903100203006042c0440c0000680c0030a8224000000040f03040c28609a003010b4080007440e807244100900700c1181c40e0903007150501c003041d84020f06817801502c034001401d000d001041824080e960610001500b01000940000c60080c8024403840c0306050488881d4040701c00690700008549802c402e03d00c002c001005450420000590003081508125103000f848000c010322a02c10540f441d405517a202c00c6e0301c04078501c900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 576697455 1250 576696205 576696209
    0x8180c010816110601060503070e0f030613110a080f07060e2d061b071a07060b04090206030903070c240e0109050307120327050d08070f0c17070e0c0c0304 68
    0x90f007503503090b41c0c458038060010742080e00d0500016640440e18001820f002c0c01e601d002e0840240102001e03550208800300302d058404007241c00b143d036000240ca081c2c80f0a20030301e01800c4620050f20481850010300c42c5404650b51242c010071509645582c489c0d202da1850901440c014103042181c140c5240e41c48104014104110340c0003031000508248815407900b186203d08100000d03184040d64404001520112070f15426070104000c04c403850001e0341c1607212064001d0301800114889543d500054042c0d0001c503038024543d000045d0f140108410411084050a03201c240318003440c10a22100c000c5032828200002480700c540d84081d21a80112070306e800526001341100c03407076a200c00301804140509a001c0340807a03000d462052a006201007491581d030385080c83c521070503140208010000300c0151051310165020003519000c01e0381c1d29284e0100714043c0800000542c60100d072103100d07031028541c2012640003154180100d880300c1c58207035000780071068229150b1130041c200302d00718820381d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 576698705 1250 576697455 576697487
    0x10203131e0507030f05011b0f0302070c0305010906050610050c030a050c3a090b0f09060d0908180f0f04050601020c0a030b0619080703170702030a0308180c010816 72
    0x1038001300f0070010a140d540001c0c4110024800800e80002d014150b904460282c0080b43c00300c0300c2181c00c64426405425164040c5002c242c120b035a988441e800c6407018142995459203e208110351420154208102c4204c1440c208ac03411108400d01740d02ca0041076451800c00c034000074220340c814030803c03404100700d0029801c05405e042d228800b914400c00741c01c4260b15103042001c1c0100c441e0080c560003040743c04241d0b0340e901c2d00884282007141030388060703ca03507448403084c060104102060b100396025148100341070355aa046000b0400351030302c10f29145a1107441c404020704402c5d22254183c54950343d007998049465140c500060341850300c080301581d0408601031000040c40510110140074000c165900410b074580e03600340c610312207418010318101d54407104040000440103464403005100c0c9004007030a00003607a000a00b0004585025400a07000406001c00548110406000000c07640001c0c0040c94034840060420b1800400040c00c02c00ca0280da060041d001c0c040b04e1003005a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 576699955 1250 576698705 576698713
    0xf1602061c1409070f031401021b1f180b0406020f0a0207091802032a042a030e070302090a1409070e0903031e090a05060901090311010203131e05 64
    0x2440c1540141440c150460180d218180820803d48001c0b42840903038540300b1405030f00c1402c649407011440e07200c260f000540c0d035081000c5042c7c04a14481c1a440e1143d00c406080c1e00352018174001459159038021000091500e400c100c00c61070813442d0040c0d504d80c0214010010355450a0110090240c0241455000e100281441d141036000c00c01c80c0a8a05e8028108590141c1038030361310f000ca40c070180094059100c070406141901d071881084501400304d5000d50184c04246011030195081041104424a01c51505001c0e1700c19551044080300250700d41080400b0544001075541d440510010340203c041e83c01040c481f00c0550000302001041c2213001030769003804201d8550f01d0449200b04840f09001c0008240c4804001c0100e0b0301030321600c1d50791102d075840711000081c421005441d0590b44c0c4561114030001500a0084500c22000340000103201c4102e401e000c2c10001103145030340101e034410001c000003540140c0342826103e4000501e888032403280341e010748141140380000380162003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 576701205 1250 576699955 576699997
    0x906061503060503010608010902030d0c06091e05010c0e0a090c0311041e08030a02060f07050d05070206090c0604051503270a02121b0111030d06091506050f160206 72
    0x60142c00c000100c071403d82c02004820f0369481050b08a50880c623009505070090b0b02c031210b40740c1c4180aa014283c0c01000c00040840c2d0359906c5010003111080034095401da40448101802000e1040c24982100c03410824502000b000c002100c291440c00745170081030303941c050508402e00c40d0f840b00d604410b03a59400384e5101d858622840c0568001007440c009000010380100f020702000c010b03902d1b4a245078001302800d45500e003243c141e0034002000041000000e01c0114201c2c846809000d0203460b094001e0001810300c40142400c100080110303034000d020412081040d5102d07100624440c10052141549079100e0203510000009184001008103010315400810b0400202c1c80440341c0f4803c640d8608203590141c4010340b00c1e115000307045ca001c4032801c070320780742c0c0e50190b503501c01d90050090a40f49801f01016440040b1459a00120341503a40c507800d12090007141000140601190304109080c0412031500b4400343c407640041c54454005124a1421074039602c0030780312905000010085651 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 576702455 1250 576701205 576701207
    0x109090c0e09131b180c120f090309210602030718030507080618032d04140306060d12050c1f090c1505040b0304080d0c02030c0721030309060615 64
    0x110820f40076a50445032080d011400045001540308845210300c0c3d8012004078000c0940041c11041c10410a00004802031810640d681c4540c50180401d5140010310400380e040090500200303070042e8018451000c452004000c2c0814600d181c60350140015030f89558040049503100c0012081501d68040d254021080200c089161b0382902d05200491318280e641ca40000788401c646203018020381c00400c03040e42420001d0420500811041014010407000e5014003016540250b2103400c8940300416111328a10f01445003d0308007104492110341c00c551a01c59541c18043d0164040600c01c0c005040040e102040c4602c00b04d4a605500914001c03041c500c0e218040c28801204070ba85940b00d5201180d543d100541085000340030342da4641c201804d0410240b49a030010b030056951150a2010f017880601501038002c0d104c4c1c0725400b40d07898070240b11141d4075206045c1c002c980c0b06a0b81c81e421620703200c0b8641c41803601a8252401188081507400c1803401400d03e60498829071134400041c540b11 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 576703705 1250 576702455 576702481
    0x20d0212130f060503070f090b040e1302060d1406182d010311030c010f0f050a0302091002073012031401060e13050907050f18070c0b070e0109090c0e09 67
    0x14094a80387d003000100301460846682c40c83d030094070300c000300c207010030f1240303883c00c801300750307011035010003841c150100e13a000034200350000396400030a103440c0c81d00c003d0078030340030b0b0009078000c0c4041e140e140040c255020b621400302c80040c108158400c520100c040c00403016150b684444016a59005072941c4905101c40c4a2500440180c003922503640e000700c00707510808445413920040d13038a08520014244003216a03038840b9001c101019001e1204000f6075031039400c14614000c007070300240320720340c644010000010b40b04001400f09800e06181c05244911211340031070425440b00d04a40c0d0414003020a4004010005160b03980d4900d0400204409030842c401411484c1d04840320484200c00382e0b1050b0a94400f1030380745c0d2413a0043c0d0810441030502602600916200802000d0800e83d006014902002d048402c940000c0007404100c1c1400300c52100950003040a250820610401100103400d40c41284a4101d005a0704c42d0f038214600e00c145d14203040389a00074202030341414a00070003546 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 576704955 1250 576703705 576703711
    0x921030603120f140306040f060806090d11030a0c14060a090b0c1c020f04081506150307020c090c1b030702030105010e0601120c02030708030a050412020d0212130f060503 75
    0x1c2c800310403060425000d1074a242000880d41c1e120300400c01c03548080c800c50741002d443c6507082030329481103914890f154050300b009040001c00804061030f220440364900892111a8014880031202e0003403281000b100700c031070f02e401c5414460884441d47c80c1c1030b560441c1c4c41c004c10380079000e00d84c1803181d10400b80d0070440b80c5a0048841c0d040da9250703044002424450200c0603004000a04011030030314003150041c184c120b202ca9101402d1956854045003010400400240001e003200b040101601d401c0d0b0040450320301400301c0b24214070b00814043d6850240310030044c41095200002001180b0b0784044030341090000c00b1a102002d82c034010250340f50015403040744a542440000710300480c580c0c20b80c030b10680b016541c8a4460381c0103004c0c18000c0c01801030381e0046003c10404880407440070b9005600480c060480055103213000c2c10501d228003004c42446085400001c0620340e06603000076081d0741231085205096644600c9486540001c8295010040000d10a100000c0c0150440040c500c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 576706205 1250 576704955 576704963
    0xc170a030201060509060d0201270617130b04060203060406080d020c031009050601050d0c1e1d0103030801141908010c020712021f03140405010204050109091802040921030603 77
    0x19443d04c41d0200001741c00101c508540040c104006100550f01c9200c500044488003054050070b03495000c4810790300780c0650080c00c0030130710740f01c40c01940701c1d40080720a5004116880801e52074900d6a00c46034600300c00b51014050310340120202c1c40541d20356104100601340401180d904480a04c0060f484507207804403107120780603034030410f170749094503020303510301c542c0e0010241030103a00385000c00510368183c9400303440300c0185000c085440540f401ca90030240289884607a086840c0203996400482c154a01900710704c41000100002030300502064195800142c0c16036281d21000041114242d00302000010940404800a003418040d4004070240740c0356800c0d10702643d00d801c019006014001e01c0250080004001c212903101c40300a07140d0001111318010916801006061612800c165402e6610b654000760400066810030a6031008000b508418800e000001042044d05403d4440107070145495421300c0c010007071220340d0391207580e028012684035402c606000034010140360000301c1d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 576707455 1250 576706205 576706211
    0x712120e271e392b0c08060f01020f190b06090408070b15091e070906120209060408060a0608120c1b040b0a0b210705040306090c170a030201 62
    0x5608408040000341c40f0300c0c0380c60451606250100c201c07201a55500b50070110300c00f0384407110940025460000c004a0040110003204000d01940c508803071010720b500c0540c60792a0038810450190840ba1590f170105044403d031200c15089401030b4104100040061041d02174103aa5419082e00121140c026034051032400130241d84000c103100c0540c50540e00600009014060f074000102045401c90740010703030030010410102401c01140700d1810646003000c046155130b000d10b9958000c0c0c0007817940100c0030320704126010320b07001000d801d1251400700c5510940d00011490255102e05003228000c1144500329540f5103005038510307000709101d00540c1000d019601c862400e5565070001e550a00a80c2000341c41300203160500c2c0c1c904040315040361500541c403504121219a00c10041000401d08c1003031841d0744030302616111242e500d0841c040d000080c40710090289044d8840161001d032680080e000440c0303006820000213008166000307a861014252181071400e0010400b0b0610307a120390024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 576708705 1250 576707455 576707491
    0xf030c11250f0e1b090a060c060c1b15110307020f1207020616051002030108031309060b030103020d14060c0a0f030b060919030813080712120e27 64
    0x90312801442d485400c1d04002e0220100305418883c8164222400c001e1078105d241ca1007483c042030310a2165842600440c0080102c481031021501030340c5002c1c0410f02c0c01441c15030300055002000c4004040140c031a1507075004083c4011006c0e07012006194088640035268940358000a550f40724101190001e4043c860388102e08002c002c080d598035582c000d21b1300c0d040c40c00d00442410040d4810405403090710400c036403524614664401035000c2d01c41c010103143d50b00c0303e482c4213451150303050b4040f420340fa00e421341c00c11010b108441a241520340c11030300509111460b0030400c00d40000315400005034010303042405070036010711004103442c00460310303040c41c1c085600d0720960442d04403600c02c030340100041243e00e0316407829140c0162180400010405299202d8455004a402c02c00200094041c4504180550b020400644008200d940c0c401400750605a486600c2107454020040031702590948502d415519001845003139444800443c514011021038600c10000a548052798207041d15a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 576709955 1250 576708705 576708719
    0xd061a03160b09040b011b08211306020c03070512030601031103131103250314030708160c0e07021e0c030c1306051305010f060f0f030c1125 62
    0x28200840d210240300383c0c01d108081052001505500c000981000b8000003807a040c54048a038500c18140501c03100341c2c8402803100c05480d40c0c44209a40540c010107a070420070741d084d2a10b0340c4140203a00c03600160700d445d80c2c8480c0c0341c554094440020040d0090100d414000d05605000c0c503c07800c0240c1e0f00f80034251600c0c80082c0c2e248030a4452000001002100c00041040c81c0b10501e08140080d045580300009404d8140d581d806500300c100c43c212144c0780c2007003070055500546104d40700307020140d0314000b296031f5010721a20a03101811105080e5206010138003204004000090904680c11a210300d801c80000391512000d401491004800d6444003400d2507000544034600c110140082950102c80030400231180c0c4a180e04890b110b45074400892151900400c614004100510120b41941800d0801685a01a4024404000aa20010030300503400034a91101107058180001c12490b40381040300d80b0049081c0c0c401a134420364100d81c51015625004001d000b8480749100d80d82600c503c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 576711205 1250 576709955 576709993
    0x3120e040516080712020409020d060e070c15021908070f0e0d030c051002190e060918060a0302060307110111040e04080a0903050a0f0317060a090b0d061a03 69
    0x1540510b1051074107540ca060342c0030381c0e5025003207016401c0502500043c400070005a9105070004805d240d00458240a01c1109005e200080c1584042c1d0b855503151000008100d43c0ca1120080c2010b40e0b498144e9a2028003941110566002030360010b440e000192009404c03404180c404000292880c1900c1505c0d034030940e410004094010135985060300b040c0c904661124100710182c1d801d02460207a5041c6452a00c01001d0f042c2003803181040501404201611141103151054080c1d4010066010031360780f17003080e81e11081800042c4000315100c0e54007103034801603503400080d08507800100f441145070700301010030240780500b00203101118030300c1600040c5010f1841800107043c407e50219000440c0c5038043d20600d0010714108550907a01c2d11030b240360607250780e404e540043d28070222205240d401800320b41014916007a0040c181444000720300c0c80c0c24140700f2141c0e1a0f075162801d504607983c298000e0807a58100c2700c1800880312104901e282d000300406c0d190300c688100b404200741c40321240 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 576712455 1250 576711205 576711211
    0x210f14060d0b010501140c0f0d1d01050d110c07181a09040b04031106250503070c021e060d050a0e191101050f0309010b0109050a030203280c03120e0405 67
    0x954000030a03480c003001940c0008000046d516a030f1400d015110f0412800c000c2403a0031400d01006088030b50b10964003900c094072a400641003415190880c03103243c1d8010301200e042100740b10001540c0d0790106241e00c0e540c02031441c3c4410500a0400014503100c2000700780400030b0040358200704030381109000750842070001c4407098101c3d1925000a001c114032948050b03000c0d00905000e0164040000f82d01e0602c601290000902d0103081d5080071003034000b0385145100302441c14100d185041084000d0300554110750700a00c03d021060945018011103154900040b902810300341d2510030340c3c90038801900c41240d0750b121262409908014403a0005410195500324a2070000d00002070f80750120040f501855060621008100c6000b40301d401c0f40080d485125120f000243c6002c02c4030004090203555842944940300000303050001d40c0d000b11703541d0505603010380c0d4184038503000c1c240611054011007014044194891001051110b99a280b1041d1140d03640e544030018803240420040b03c0040d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 576713705 1250 576712455 576712463
    0x30c0e010801120804080709140708010303120c1803060e0c060304030914011b0503130b090a0902030a0b12060406060902030c07110111010e0705030c03030406050307210f14060d 78
    0x1075004103c0e40b800c0035400c0e0141c0c1c0c0902126403402c1d880340d00302ca20780b80b07d660240030f4165407800c1d800c00c40c084290702580c0214440ca025412940f454400500d80c050070540c9421446d90340c10740c0ca200c00c1c0102d184032090076414215030f03000799503400c1201c001d19044a55510a006500422401d45003c0084910840e81038880c0940d06080c120408210029015540d041c041e82102d04040d0030802c03c1148011482400110356031204c80c07170000012403082c0cac04104900e10510400506a0b10314408400341d51303160038010384036034a0880034409840303644803040c0c10008030100400c050748045688d6100701d014035414046103a6900c4103504070701c001c42d15140c040a040c420300c0d00240d03040b03180c505124030525103e01603407012010b017800c43c7c0d680d8986060715402460300304100e0909100310080c0311000c80196003803030318202c1c0c007074007501c001410842000a94041c15864210b481a0a4228068000c0400011410f406818001c1c042207000c1c210205000380007030341031702d403070062450300c40d80c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 576714955 1250 576713705 576713717
    0x6010602121e040e04060b01030e030a0e0d0c08030301060906020c0a092d020c0111120601030b0d06020d0212061207031b0e1302090906071b02210d030c0e01 69
    0x391401c0126140c000c8100490224001c040036042401c200c0040d2028000d4002d80582da81850703e4003030100c8130b400038014141420194480d10320303031012064982c65081c81c18030100144108000411841c043c0c40300804210340418049003009000000c0d506944070380d12059066926502e0681c1e441c400d0007485548480904014000080c068000f202000c0c030005044510b90300184450076a0002200452010341d40400c10094100c001d01070405541c51004032245004411f118404801c940105918141916121004c1c41500e41d14002440e803908200115119401c0200940182d4000f806002c901d006480100d0a030f4038200c9441e0758204100e00050000a14603501c40401013550402e054100b0700c8403c00103100201d60043c0e6111b41000aa03610312010284100013000b140a07007400382681c840800c00501c50f411004804441001c0d4080c683c0d070720042d00c009060b4003441c000c1079040c1e00c4490044544003c000070704203c1821941c90921150809020498605082c00e07400340c0000c0b1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 576716205 1250 576714955 576714973
    0x1b030304110a15120b10030902031002090f09060d08030901140f0603030307110106120308042006040902030910020408011515051c1b081801050403210e1b030f06010602 74
    0x1010311070503251080794404c08900c9042940004000034864003125000c251030b20391200852605000034608041228811030030100ca00740440d40041850081c14094810070700800e034a50b540f100070209095024581c40c1e601c0c81c1521003280680601e00d01029000c14210220f45040200403043d84540c1c4c014000f94113643d40c50004540c504400180b82405544e41d0102003608524201550110b500948401079142418501003104040144012061a000e010605c00c160b541004807401c0700c04002c005031f140d444420b00c0c10f041c42e042c144107108040c4001170008103004190400d914405285440d03031086030b912000c81c00d00e2080540c0c100c000810420600c00080030a140f030017102c2c4003c800024003807816480c0342010001041c8204046802801000030314a0781c10f407003600c2c0caa007101c000d00c81c500f003d81e000f4045c407070103140300304214031000f8001c411813041f41c2c00122440d400a088031100d5042484030900c2e0b083d02420b00c2d0207401020811540003c001951504a410650040a07594 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 576717455 1250 576716205 576716207
    0x2100c050f0606060f072a030b010503010b0d0f08040f140102010506010f020304092c1507020313030b06040e1b030c030c09060913150f060603140402060306061b030304110a15 77
    0x2c6e0049008481051340c1080c80402c06000000080100c5c40b101d03d101c05441c2582000075180c0300c164001446681405003041c52611180d80810306540d002d00c0c02003040e0854684030605000c6e42c0c02091201000301d500294500d5640c184840340b103402c0e0020801ea4503040c1c01110740d02264440070016a000b08030420040b1602d40c0908040c1403210400045007140550200030301e0b03852501c20845501c00c91b0440c0c0c190702404c12031038004815000842c034010420700c01c100090000e10010b44500141c40001e4210f0301c84d9004003844140c50816900d800388200240c580b2809640b01080c0284901c0c080d542c001c3c2000640f00c6642d1000400009031075a0305e4080190200c4020180941c01d618400740c840080c1300001900000801c3c240041007441d4400740d984100e41e1258422010541013112184400c604060800d40003034041d24010395036603404001c54654810707410501c000e001540e80701d0103002f001002079800b4511408003100921400030070070040e5020b5008a82d0f0840e40a60004005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 576718705 1250 576717455 576717457
    0xc0f1c080906040c2903040501020c0f03121b0c0d08040302280f1a0a0c0e04020721140a0207090605040603051009020f12160602070f05061602100c050f0606060f 71
    0x19801000314645d001c0301150140c01c0c00d130810307070302200c582c0c0d00424800c010780c501f407284503040c0600400443c18001d818020201c04140501030841c2682d410b6500642c04402604480c406861401260740024503104000c2c08032604517000d40050280b9008402e0105914201660b0901841c00303402c0b0307502442e200c0c21110740d8584002c17280e070a40000500071721142e540c078030303403080034413440001c2d44401c1d100003d4030042803103421a20640c410400000020001c0400e5250f45024a0442040210054050b2180440442c060004550100f10711005940c0001c850040d81c00240d81405001c3d5140148010745115010041094010041a4420450301e6115400650000f000c10700d1210000c0c0100d019029001042c110131b41192030b414102036104083c11004003020301c0108042889c0c09418040403900307004082c407070a8005608016260602c040b8011940c004020980b01540b204002d0042d07455140100c0d600c0c080c24003503400d29030b00031501521403c0064402860722004000410340c07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 576719955 1250 576718705 576718739
    0x10524031612060c0305060a1e17160b040803040e0703060b0f0301140901150e03010f0f0605030d1b02060702030f0109081c0912050c0f1c080906040c 66
    0x2612948403030035101251000c0381d10040c102e00c004031003040c4050a0038003d4036201d080100a050503c5c080c0079081d1039110a14044607224480d000022505c2c084580d03d204040d4403484860300300c00c4158000d01380104000301c0c06030b40841492185582c6000c4d16078a4002c600c03a000980e0810300007000f400320140d15051b4881464900040c0307507074079011a24032031340100044001c01580400188180d00700001013891a036000c41c2c0c40c048661600440e8180c181229039007c08200c40000812013540b02504000c0c9040801801481030542006003c0018045885030321b2180c46090b6413030b1030060042c4a201c0f84a83c10110201030354480740c081c028540d0100304100d0700b41c03049035500c0603429800c0c03080d84405485006182e540300181300c0700c0d00409501c1d20100714190b1502e4420700014000c010f02c44048000c5003485501c0b1040a5025414824903d00100c40c901031981c10b00308110444414031004911905c034003c054a540c01c030245c2d10f1000302c4004049201004090180040f8007962450f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 576721205 1250 576719955 576719959
    0x40501150e1015120608070303030b061245070b0a0801060f050f030a0903030b030c0307090e0f0601030b06030d08060913020f060406050306031b0907030e210a11010524 74
    0x4940c103440e00c5113100716000c0390311010389a00415028000c041e414029001000c0d400c90f20346080038640190200300102c0030b008000e0501d041440c83e502c41840b48501032403410031403180c8000d05250001c15200481c2e43d4000350b01030180b0703400400d231940e40300140c030ba910403103981e040100e030300303240c0261500c198004440e07085c05418098200043e8080e4001c51103a100c0d1079000c07900406602d0007030199060046020300c80d4102d10010b040e243c800049450446201b2000031600c00501c5101a042c03150b60a0800c1881c01041c1c004010702140c00e80383d0303001c1c0800f0342c101e614102c1c011f50100c0c2da14806584103a4003003408008543d40f52004110f03584501d000030001d200940b0700400061456106900c84804141c0100801a1038a801d204046204c0024000c490301c1e00103030b10025010f607130020601020301d981c0f00315404400004003d0308001010380b50b802c841813845c5040400f580e0700304d01c10710340006685c80a00d2b401603206010300e42c0244042c04007106441d550081070b500303c01159000350707 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 576722455 1250 576721205 576721217
    0x1c14150c12040c0b03190f0e030f07060b100503070f03200d15080d17070e1201020f0d02030a05070306060207060507110406061115010612050915040501150e1015 71
    0xc1801d01c4e607100158007410100740f02c09011341d12020f02e1420b03101910009448546801c2d0031010102011045a448204016480d0307910356880c5004001000450358941c1c012080805458905821100440c041d0381251150520042d00c03140440c01d60301d022401402107034000ca07051868841e44009092030342c0041002285900780742c5034655a8201740d920079403240c1c0c420355a441c0380e00c1c1c0003881c04e2600c40140c00891218648001c0c06003e000b882c3c07013441e0203035980c500c060766100c800b135060b1002080c80c0c00b0a9950b4507400c2071034001a40040e00c00300c42503840c0c18041940580684a11000c6500e00c0e0040c1500500e0309600341c0e02038000c0c07842500d890440d6500480a030391584259009032405880e02d040b8020071021036031400141c80b03c2201204503c400500c81f0795003100348945c200100780804a40790781e5800c29113040000d080444080f40d500d10041c0b10401c101904030303420001c200031024a1280d900e002c081c1c0e58450580d0030391800b04402006100f140c000fa8115081104141401c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 576723705 1250 576722455 576722459
    0x30309021807090503060108070e04020a1503020304060506120d0809071707030302010c02030a1d13020307080f091b04050702010603021206090c0607030e010309021c14150c12040c 79
    0x110300003032108070608400340c58500c208280c0a4002d294503000e08001e0b00100031660519084e196102c100303001c0c5140f070b0590200000c003103585000d0303030324040c010f0820384c00e608210702c0700094040d41064400311105400d000c00100340341801243c00304101d40d420001c0000070700114054450704400f40910413a0301070788501064200c801c6824003440040c940082180c1d03451820005d0844d201d4410394411074000b002003030051030307201461042c000d86289211300c40500d07000c00280349140e140c604040150011040001154010805520544031318600e06199500d240100f612040700c00d08000b10345481100154050516500041d8032550034000010b07e60303202e800141880c01c0c240e00000403603211000b00a060302003070100358842101070340d581c1c0c2012450741d00a0b224401c128032807410959205403080c00c1d035a030420407403c2080030044086180e10503040c907820002c07200c0f8102086e84500302d841006941200b0742c4da0300c100003513108035041a014000140803444050b20681d5002100080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 576724955 1250 576723705 576723709
    0x30207080a201b120303010e18010f0f0902010f020706020312060402090a26061e040c05090703020406080c03041a0c1e040e130507090e011806020a090b0301140d03030902 75
    0xd60043c0ea0041d0500e034080305411810010707204466001c60002d03400c14401045903003901c0c034095800c000070038a0b54072282e000e150b0180c010701c500e1880000442c103210003906509080d07845000158000c0e07a4110b4800d108480507642c0301050303c00d403001a481002180c5090342800004c0c0c0e00518020b0001d8600740300d80000540e00c00c9542c200070489285180f21a4642c036060000c2c1c140e2440c1d1802501c86807801101c0a4024400004065440240d401c0000c0030003602c4480b050240034010000e110900b0403900080c000e4226028610102c2da400340840c450114104c1928461988030704440d03901000100e000303070502d038003800403e54200e09205003d44c2c0c021003150f116480924003040c0d030321350385090b554401d01d050180024215004060111000c11004214035045d82c2241d40e01140032418120f000c1d0041503c08520800441c241d4000c904000207500180b01599050f078492086649400b1100c1151000307114284000601900701806030900340b081c4210603019050001d000030003500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 576726205 1250 576724955 576724963
    0xe010e0d02071e05011b1a011401030f020408031602190303120b010302091302131d0405060c0316030911040906050105041b02071a0408030d020316030207080a20 71
    0x2000260704481c1c41070010f90b20208095904960308420b5105091800380084e209003001941413610140d240040418416200400703103040200003c040425a928410103562803e00e84480c1e0020b41405403050302c05006000b95800d40e00b101024601d80755641800c40f10510140304100c0c1c000b00c40e0503442c0c628003481001c05c00218081c2e121400c01810780d009050444060030700e001e052500c140301071046511840c040004480041c0f4005954498444900482d40c0450344140300307030ba861440c00c12a55a0781400300d40030b0b61044080381d100c0d0b19011040e0826000442c3c0551404603522035920b40c0b60f03ca034000d4441a070003588013422030380200c4085010380d1306112050f51301685500041005041620940d402e4198040d03c2501850300c0316402521100c031391141151000303803000d21684854142080368000c01069084a40e5050802c0070391000c1d4104580300c1c0c20102c90302c01e20b071205600034002c4801203a80f00e40d0103494800d8080341541c1c1c02a44042c00d0518001c0c084c091500844c0c100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 576727455 1250 576726205 576726223
    0x10905030a0323040f0201030905071a0d060603050103030c080f2505060708060d0b0c090402131e0308040e090f100225020303120411030d09080d110706030e010e 71
    0x103a80401c2d00602c40f000d84410360400280c191080c0e0b208010800030410388803040515a0782440c0204a1902c9804c0c00c80c9402450740101d00fa119500380070390340600c03059008204100c4a01c0d4184040d555a2800743c3c1151402d11001c0d01040400402000094509006203ca1080d02407458140780c00510303910451107100303c140804285040221040c00020480694001c01c80d2402102038030300702001c82e0b14440041d40007841403540c20089024440070409a98240300090003c40d102c0000c85142494040c45114840d141c0118070340480410000103c3c00e0190b0790050422071909240c511525452000240158014020001600c041140c24440b0318a04501850301507100c00242500350f56070000e244901c04122105405080142c8020043d16500250300a1030311181d6241d0800702013000701046100d0b4140600304810003400e4010600d0702c10380350800300315003c00061080a44180c000c00740c64007080c4d40b00342d004000c0544280c010302c00baa602000045164480500c2c1d042c5041014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 576728705 1250 576727455 576727457
    0x1050f0d0c0915061d031c110105070305100602010203060603071b0209070207060f090f0b07051920040509060402040506030f0307080306090c0a0c1b12050601030201020f0a020a1205010905030a 85
    0x41804016a540c0310100f490a0020245d00c004841100400a0b6a51204500544454850040c80c0003801e00410050044901ca11700030322051502ca070000300105402c03548000070082c0d806022441c5031051090f21311441d40903002c03500e152910041950f0b0700c00790041c200c001c011142e0b4081b0040e1604581140980965001050f205082c0b88010f0b000c0d00710612484100180c40004101c1c140000c00d00c3d40844250b1421140d4403611070900a0420040c07807540045100d0124108007040042d81c0200b480b5000d03039044a28210882040106071002607540710160703070005003c1005481c2640c003540d080903000301118000d8480e5140b4906542255600340e0341208080200440ca08201d101c80358052410a0f501e407034038801c0e10020703120400c0d0060103044110040300c0c1030384429090b00458081c0005441081e1825442e00d0050307607074142400224014043c401041c3e0b40c141c8005103205c9904d50050054000c641003018465110560300c401303a0f020744d00e9001c100b0102d481400101491002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 576729955 1250 576728705 576728741
    0x6010513060320030c15030406021b0322060801030f1b15050306090105090c0d02030709121b0b03010513020d0f0612050c1e010302220b0405041401050f0d0c09 70
    0x1050708050070b10300d40b8001c8070b001d00310006e1078003040d00c1280100e82d1700503070103140181c4a0400006a0b120000c814229803402e10000800c4194012410002080d4014450640a005445201c00c45500c1000c0c40000d000200c80c0d985400050314650004454004104510001e9641e0300c0502410102290182c004200004240080c80c10710030003a60240c0410b0b01e5945280c01e208121607424030886001b00b038401e41c08008a05032610468135007004003c0c00c3c20001007a030442c2000780001c0001d406c0700c031240ba00030400103030141240c410703a412680001d00342001d0b40d05000100c0c0213036100308900300a450750f178424045180d5140c0728603006032100d0007040c145501c4510b403503840c10040d0211a40b00c0c0036180614000c424040301e460340d40403000e02e405030b166500500804607411040b00304a2103210764407004590b8006420141080380c038111401c0c40615000c441020000d44c0a0007100c0d0080d030401c840d80183d003000111609010700c681031080346151354069000480c4c0044040b0849541 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 576731205 1250 576729955 576730013
    0x2c040f0e06010b0406020a1e0b01090f05130804090f020708040920120103030c030e030a03030f0b19030215120103050d030b040c09031b08060c09010917060105130603 73
    0x103410440d2a0240200d04480d40c94141424006540e8403040080146600d190380881c40b44e1040000110b9480c940c0b112070a40e8550b115403507240940000d20130414014a0480020340c07500a1010310a14250030400c00b42c0340500704840000540300c4040c0d04109150204401000510490000d00041c01e04402c00100040d14101c0c6002e1104d40d41c942500c111014000e6500c182c0c1910207050449034141814020070f0306074070742502e4005114403850341c5030182914031000e041e016004030b450f40082d070408101c018a080c0070803100c40b2a0f54629824220280c00500c014140000314900190b0103591050034015280e0700941802070907003040300e6940081c442001007580500614130040801c503014031100c40b500c0d40c01040109a844041c005503042011004105a0342c01c00c00301400700002a18268036003c40d0301d981a0380031403a160f00003030f0301103000148500c08a820448208542010300034a0740380c01e042152910342104004d10560b980c075000400203184840c0480005050000885002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 576732455 1250 576731205 576731231
    0x30e04020c030405092d041e0609020612040c0506130918080c01020706050703020304110103050601031104030614060301050f0c0703090b0711040e0105090d051305030d1107080c012c040f 82
    0x1c1002d0078000751900001b0034440011020142c0e80d00001c2c0c2114020b0030700100f414188043c210581019400440c0080c140c07107810000030715980700d0750141000d01101030342c641c20720885108130080600640f0705001d061006424a4000b00c441c03503190000c5065a0482c1d444240003540569111050340c0c0d80000c003031003009464002d2a030b00400340d080450441c82e00b51070712103c413034104240604155441d000120a0b03800380c0d100301c80e15000c41c5045c3d43c403562030b031801c1c60007450300008940340014400300180d118036050148900c1061110b1604400c0d40710b03c011507070b581d04035500880c01d21141c8040890461210806400510b00506918002e6200c00c0306000c00c40c1c140550b014600d034100b07001c10214101c0041c40303083c4110245466a502c03051583e1a403900250b0b600955414010b8426406005520030b0000f07001544200a4a4201d503407a808030b544c07141d01404050214180444098520b81c0c2d900d0000880d071054a4481001105d140000d801c4418600115041641d1280c007034900e4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 576733705 1250 576732455 576732511
    0xb03010f050f0a06080405100203010b1c05040f030f14030708061e010801060f091502280f12170906090f0a0b06120a062a020a030e04020c03040509 65
    0x30003040e280303000c0d200c2d403440c049000e51589005038003d00841c8404101084420012a0715044c03d108007191296110150074942c2ea00c0300d80c1d240f40743c030081c1054003a101850f01c6402e001d10303844201c4094401c4140e030243c40080c9452810300500251038011821030030b01d00010340c0f05000540d6880c443e4075000d01044005082c4000c00341400c90741100701915641c20541d218150360080c100a030f084540c0786011950003101e90071a01380c5174402d8081c50292600001c0903003040b1941c0100005207100f440760801d4520b951440541001074000c1114041100300c040c500441d1000c6c94440b40580d51500c0780d107241e54050382c001415a0101d8200004070409002103d0301c0790400c800b400d95088603859884441070060040740c4102000400360784c035044100522294903622039418460340040e000302c0400c029480c41d60800c030901c3c1201c00950b0340d10124444620075455210f01a46000c07110501c00203411080400c14540300400001c2216900c002d509881741304402841403510104121601d02 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 576734955 1250 576733705 576733709
    0x6220b0414070903060b131a010806061201050603070512070c0308060a0f0b160c0b030703110406021e072105011406030a1401060f14150a050909090111040b03010f 72
    0x18407261001030002c0320307500c91400d0003200e40004000c0340080e4070800081c1a00540040703400d81c0742c60302c658441000504400040341040903245c4000e250b681d6018030046104440d03201c003050304c070880144050702e49607002e190004994a045400c0900003404688411002c2c3e8043d804a0b4034042c4c66030406070701600d000d5103e503041d580031a80c1d602e0306949002c440c065008511500c14086007408100c0c40c0213501c15042900030660481c02a86d40d445440158000e48000340040c1c02c002107402c41d00500000c50301110f0081d401052503a10000c007201a0a0b440883c0880c035010b102000201d03a01da500580a54461001d40498400307441c1c034009085500840700c141009441c3c03010050b560b5004268044200d8000b52446002c60004c00420b00401c0306411103204071b5460360011230301000000c201015600c060b11a20102c0c0302c01351a601c21401000c0007500012002c100a10090901141042d0484601d07000460307105440c4ca49035480d82c00640042140c500048010001180103041c4280 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 576736205 1250 576734955 576734981
    0x3010311090a0c0512041401022701030b0a03032d0201061701050702060f0a060b03070e01030e011a010507050a020405161d1c231f111206220b04 64
    0x18003e44001500c2400703181441451040c00c1070000b0184074260411034110724007140210360710103880400035500c1d503000200880c200040195030355194000e100c0c0c0d0441481c010000881186107a40403a0303401c00d003040107440781045d028a45d45508410202d10340c2102c0940001c41c41d1740c240010f42041022003104907903260704120078003418580200b882034014800485000741d694800048102070161030b03205003400c0c4800001c10100755801412901c81000990b4140003105120790307814207880c4041ca02828000600c220200f0325070044000b021003a2051007911b0543c8010b8000a007100d000303d035a20f00c11403040e5080307001c09a0203000c1403520103b1448802140503213030702068910160060b0500390001c13561030702c014070800e10740703100d601034901c80c0c10940c000e11000001e0300c0b4ac800e414989203061141c0e100144500c03040c05007120481c0d48004a5003840e4000880c4080f036a4060040d68024449212904207201e030080d1202d0856480c000100d01c00c00604144802c48401e641440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 576737455 1250 576736205 576736211
    0x110c010c0c0b2a0a0201060e01050306090601060e15040b09040b12030a080c0702120c130c020a0206131809020306161b030315060809010b09060a060c08090603010311090a 75
    0x81c0091034803254a500040364601031250070041510300b14408080c446488420740c00803035094003e07541500144140d400d50b4107042c00c542da0380c0040c181d8683c401c0d10780c0c1c0c03401d0304020700500c103d5104500002c0c40e0701c00100035500f0511500402049503000f50040280c101c030020750301d0741c41d0a060260080c0d000c400e0b90386c221502e5511001a4a9004403094a0700304110340d4007080c44200c05000351029035400074007071040c941e0404e5100c0d9903030050554490280c480d02e0701910301c10100b03124010300d0540070307009002100203503800c01909034064840040e02100030680424811201008920708034804400041c9209040c0105440d041c0010403500400200540c0a490790386e101d40d03290458800d143d100d4036076000700d14041d00a040200490144440a040d0001d601d0b507004008a025994110081103000e8050080c003622032021100d090300301000000410506116944c211a200d004048850900c006040040d170298400e90050380e500403a4604141c59182c541e6003e030700044607400c10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 576738705 1250 576737455 576737477
    0xc020309090411150a080f06030d1d0612010b1809060d02041d06090c01030501120f020108071803030f0f0801030b0615070204090b070f0903020904081c110c010c 71
    0x14901a2004100800c0c004843d0b5014209440d8802c10048010076481110f0310740c41c0c1072100030714200702101c0c2040704c3d007a00800726015007404200c0c80300c42405559211500c040b034a581250a00f103555000e90040750400c40030032161071020041d8064800900d00940d2080ca811343e0000c0080c4158410384106d8140052207000c0c1c1c0d9000c541e090b1164107541c081050300200201c541060f090b0007200300c5600403c03081020300740700890025410607003601c0800c01e03662a1a031a0009090107400104100441d03049000550b00980c841c80e80a0070900c0d00400300c0500201034025044503a00c01c0f0041200c684491003c150049208078031039085181160f000e61568031004041c0030054402c900503001180c0b110320b207aa00c08201d46107c0c1c0c0240c4103001007003680c900000c035402c04a0701d0f100003600250301c400350039110700080022a42c004143c8c035100c3e12592140020b6500c003440c3c200c0703074140117064413a80f039646001d4881c0b1001c0d42d80720035480d044480c01150a56144003040c1c81040840445 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 576739955 1250 576738705 576738709
    0xc14010c0219080705011104180603050606041d070e042a090c020a020402040e090606090f0a05060109050d0c0303020d050f18010e150414060f0a110304050a06020606040c020309 78
    0x2010201a0380340d0510390120307203d0030703c0091841000c20103130541d4245582c2c240345010890060040740c04500000c1255800342c44601c1c121a214040280250001000324400b4a400d030004120080158480340c001408003501d24a01192540b0402c00b00032000104401c0c003003045141e06d0401d000b250340c1343d400542d520110b40003588601403810745c603503605160314a0304c1c802c103d40c5d2000c2d94003400455490b0340725840c0d1a0120422204004288100300016159040020318280540c008090400454171041084c801810004290904021460000103446d54440380c400d203e542c002e60241c079096065043c000d0070020307000b00303007000d22808001e620a0f4218910031200b800b00342c0d69030960710816100040b149a0f22450100e41e0000341302d607e03400c02c01c000c100188100c454030b08544500000350801e1000303500035080e010800306014000a4452130142d6881036030400900e095a2915803554005051400c058103d031005a119030100708207820944102d0440d0304650005504180e01840 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 576741205 1250 576739955 576739963
    0xe04051f020909060d0804090f020711010519080c0d020f0c0736061205100c03060e0c03060409020301050a0f0e0c061b0f010207060b190503060a0b1903030c14010c02 73
    0x40285e004109078221a4103100381c210a903806071001c608140305050b00303c0d1320361000e5000080c00382c82d50f1425002e10b26681d8020000c0303540042c0c480342d6000e0056406007064550160003401c2000c3d5031410030a40c2d4038814103100804e40381c1403c03e2915142c040301c80b10705103020f81c0b58114400d44584040744c2e0a00100e9440d401004001c0c21480c8889a440e0b049024060300035a80301100c0002c030323008550100305011138a18000791008604100820450030214181c404520444001940c072001040d40d03c6150b400669004501402c0801e00040f298003207030844d00100e4100700203a6403909028401840344c098040311420501c010005006580300090380c5100b003041c1000d02c1c2816818219450100784070101c1e084450400840d16680d090400c100070382010603915100d80c44c0d0888000c2c0034144030405005640707014001300440d55134140710b00010516010041e034000d1407902010010008003810030040c5100f90780b07074400c0312040d01d410141c020b00d0424100f45641822422143c0542c001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 576742455 1250 576741205 576741211
    0x6020d0e16090b0604050a080f0d050a081801180308100b0c031206030708070e040b090f0a0b0c07061a0a23010c140d08014b0e04051f020909 62
    0x10400209403a102002030305600c210f1b405982c000751014400141000081368040c0d1191901054800e02c0c56401e038116001d1080c41107440c00710f180ca00110b48103e003001c42405480c05144000220301036218210241c204400074124005500300301080403c02002e403100b8014042e5445007030030800c90340c3d1010344038004c0306202110b203800000000d00d69130f400c0000070010710707200064132842c5071501c4070010794400845d4180c030000c1c1c2e000301007401e26100060007100c0e200103c002d0611103865640d0a0b0203000003a0202092a0040c011200490514440c007a11440502d400001c0c5840300c0c4107000a185d910f5001a02140705010ba0078107030070344600600080542447c28806149140c42d066010340d40710721010143c1d1103007000c800c0300d441e00440810b06841d5003203406100d50402444641da480501503102c000c4c5400189800c08814410880d03c0b0b00541c07103000b0381c0c0301c15103400700b400b518141110b095030a5400745034115070b80800b01d5881c41f03403003600c0c0101b940b07003c020901240b0140409 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 576743705 1250 576742455 576742469
    0x6050a05040f0915051509040218190608071d040305030f04030302040315090c0b040605040308090d060e0312070801121509020316060206090105250504050d06020d0e16 74
    0x30250090742d03041c281d0040035083c1d400700c04148840101c4041100414003214854106e1011858000541c600280c150f03108070350082000c900717000300c42013007000c114001e01600013602d006580502c080d5054021403001c2e10101000340704c2940343c404084503a01201440780c0c4103c14010038400031075406000c4951004c448036040c2c2e91030b120303854102d00034819940040c002000440d000810b5005d03070b4110011090266801c2d401c1c0c562200c0c1c0c0c3c0b42261050b4443e140216000300000c00000d001d0a02810103680024120340000d20309403100c40603264650643c884079003001910852143c0708517841d030303000011894000ca0541c1012083e587c0341c010540041c02c2e4284013414100200c149411401030700342c0c0542920341c103070198171503503404503003502801001d0300a140004e8800c590520034a4840d505c03002440e40054000d8020710348000c036041c2003e04010003044041190b03203981040c01040c0d4030540c0010781ea4207041007000101c42c0c0d0302807040c04070341000780142d102078012503803070055401d9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 576744955 1250 576743705 576743711
    0xc070302010521011d0a0605010e0d05010b060723010204030809011202130e061305041a0403050d060308090a1409010302210609070806090703050d0c170d0c110106050a0504 76
    0x103c08031000c2241d40300a01200380030f5034030001ca00c200a03040c0b0014200283d8582c0001c5880340d4504c80143c640d1400342c00d001548000c008180362030108940d0321114003950001840d0304120b00401e5030f0380d200d06002e4602e80c00000001c80300c015031400c00c00f6541c480c403008609082c01c69032411a00d00c44c3d480c0c040d04000d031500304410003081c5d550481313034114618100c3c0d0340304913681d0202d4101001c080328803903c00e4413041481045000300d8003400e80315035404003100c0c1612a1200141c0c26590010b403095080207024055001104060700ca600080e600515819850f28031940802004030240d0f0003120300a0180c45204801d902c45c8080c42d81925412501c9044015586103140c030501811000e20000e445a4802e00001010204c1d00805035000041600d00030351724482e01e00d5a407007140c130005155501042c40c585415101c0c20135000c0503407250003903030000c200755824036400303030891748104044903030f40c040740d01c122500003d400128003086402400707014a8030001034141ca046119950089803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 576746205 1250 576744955 576744967
    0xb0d09060b101205061909110c06090a020f010f0816030209030703080309010f050402030703110f09072006070f1103070602030f010e011a030103020d030e041d120c0703020105 77
    0x480ea410a041114015001814011801d0001040b00c40482000d081051400020451a0800c030510f070380100c0101c81902400d6140035400740040051182c5007801071814418100380381014407006014000c02402010a136085004101c1c0c400140205641400000445034200d40d0300460341c0340e80a0350400201a024180031010740280c818801d00c280e140c0201a40407042040c040051401528110003c004040c824007100b4111041500c01a515a109000400006001002d00038500c03002804517000d28440c4400710384411400d0b164071000c94807039a02d00551508441141e0080d500c8000140410b0034500301c06400741825940d01da0411003d1450260710210410440300c00c00c4e4018000c566900e01f92803a0200307008280200e000b80c401400000035130080c2612140941d10035109243e185034a59820445213508a203400ca040c0986840541c03542c1c0d46500c01c0a62035048200d00d00f2210998042c0c09003450442000404c500b030040c066103440940c00102c800c00d580e03082c00c18941d554 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 576747455 1250 576746205 576746213
    0x51308061315090b07020109060f0c020319090308030c04060f020d051b03130f080d020a020102121614061618060e0a091118011b150b04090b060117010b0d09 69
    0x50f2000c406405581e0340c505010382990305503c15404ca5000f404100441804643c4503400d031076244c2603c6005034000d010002e804a403103005c51004d51020305044825903641d03516010642c0040302c522405040101d41000229000814821448010310190085000010024080780584d00300c0a0784048902c0344a240702108000302c413400c80740c51a400e841d050790313503842200c40e610381e003d8804c1030300031103482e441101c1c00040d10742141907050300600005003c64034213641c03580281010742c074042c550a030240041803210308a80515051440a032109117810341c6000306ca52141e060031020040800310082000101503000c5003030356a0f0346030028400c614140050103244844d04212980c0b86400c82c078445001940700103140004030007154149403d550303c01521401165020300000060b506c20110000d180e0559001ca040307025070700000c9051803140030800f00d440341c1c0b0003220464107903402d1013003560b0001032a401449030214164400e41c10f1085004090207001010070550b40c030340c0039040c100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 576748705 1250 576747455 576747461
    0x606011205070e030a0c2607061416261602040b1f020105040c090905030315041b030603020a150f0e0103200706050c1602010c1e03051308061315 64
    0xb443c001411125210200e08068540075403d1142e445400b1602c039104000c29104000514645615005052018940b20080c6c0c0c00c8043c207012061000020421030602c0750703109074288642c41c01001b14020301541c0e8140208414142c200d10341a440c6c0a001038080001c2404041d40e038940d058074003080304036600001ca0300c0c40e403203140ca003e245212a10220043c9038158030592040340039180707a00031190348001000454100c003201038102d420420000300f2141508503101208040a8000101032200c1d10340310755034507040f042080000391111010015442d04080340e0b0060007044400007444000b02c1000741615646105840078803e21520040040c0c2c000d5002c12048209448101d1a540b400400000180e0091a0855820f032600340400c86203101d22041c0da40d00603921175403c00525003600152141c03580280c08441c1c41d0700090500c1c1109002c4521490901d03c2900d40c640c40f04d060b140c0059030b50005800c00803150b4428010802c4901070203007001c20a40d00101c1e030b0b003196000d1008813806 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 576749955 1250 576748705 576748727
    0x1011010f0e0f06240409020109050310022a0d0c1106040f08010c02060403200f03040f210201050a0537021510062f031b060601120507 59
    0x1460300d0900304149040c004255042c609086109440721503481142841d0142122485500780103001540740c4018103084c0d0012220500504100003096560300000346416000c0007070112003900801c5240072101c0240c441d9000d2400c80d040c4001c0c02140c5410555110000e850f9803042151141c1c203407003030041600c40744c183c40c1000350100780c1e106c0c0c4079401d2080c5001140704449140d841c0076280141d0900c08140035000d1945682d070212400743c45001d41d4880238110f500200d8a004030b141c50000c0c00300030001400103048181c10000d0b820b103405d0710100c9030000501030039034060301481c3c03040041c0c0e4400119440404117040042c1c0381c840362400c1d4141445902003210150700903032007222030000703116030202c00722847d50f0031500304a083d486107611208040c0c0d110038401c00c26540034008030307001d21030100818458130a10b200040c00b26814411030280703041080e141d60000103040a151420500c4010b4640c0050000c090f81d00380100000d15440b811070020411540d140d0124481038454928424 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 576751205 1250 576749955 576749981
    0xf0408031f090204150305040b0c22080a12051815070b0702010b15040e0109050903070c031406070906120f15030b0118060b030703021818070201060b0306101101 71
    0x4281902d07561004003e41c01401026065070b0781070301c461741c05413180c02024480c540c040b414a1407900c446450500c560059a40305d400c2d0718450903041c1c4800070395042e030380040408200801c444c5070301d420002e1001082c0041c0004200b8104821000d1182003403210003d044241d82c01500b025022201c12103600904100401084200080c4060320794150041c0d4102c00c2d007290005050200c504c150001407155120300c0d0000307403010f401040841042d60040764800c10302d0041c2da02e23018407650340441003182074100b03c800828208005201b000100034043d4840c145081002c80a41028409011030a103058000001030315440003407250400342e000010100350582c081c40015880346003400c0610002d0041c640034030035403c605418040c960148400725607188000a03d50388801008501940c40b0059003800c1c2e051800c0618000d480c0d102c1450030220000c1011149410b264030000e00b52807880d80103041e4090184140041a0350300785007030700042d80d5401d0540c060740c80d4401490140131803a103404 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 576752455 1250 576751205 576751261
    0x7020a060201020306132d0209100c1209030b0609040f060e0a200108010509090313060c02040509010b0a05040e070b0a020a02131503060c052a0d080f040803 69
    0x18a4076015009103000d45c50840342c00403d5682c422407101161b00110240301101c00c0114140e40344414480130103194408180050300e4121404041040c811064203800b00107100e03440c024052100c10321004c104190280391180341035142d51521b03a050400a0540341c4142030407030220b4100000f20312202e020390351241c030034403c800051428a44071807550409a41841518440c0441c503801e1000101c51804140c694520b240d080609000306510001c0040040c5d11007005480540a40341207014010300c82036a40c02d0f6020002d01c10703c401c2d200d001d05080c08603810030708040640d940301d8082d0420b650003603400207600c1c0450400c86103803003c3c65000c0201c403134001032520070701a40462412a002c2c0240c82402c0d417041c002d5614400c40389004180704898801a1051000581c5500060a04000d0f45801420141030100c07605029071040450043e01c50726031030002c515203080c410492500c442d8105039a5a10300004a00400b0400520040c52524000700269004100804115500030030030740b00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 576753705 1250 576752455 576752459
    0x8150a15051c051806040c0e0612030304060f06090221130b09030903071d0109151e03050106080f03070b071403010303090e01090e030702130b060f090f010c030f0e0607020a 76
    0x8540108400d88010141c02c4164403a4a203000000400ba4040c9501c00c100c7c0505a260480c1e604402c1e5001e00010780c0b0507412800c2d49000c04080001c2d5001e1401040300081c24054140c120084903000d0380111035050040c0051500c10080c583d020048108004041d107840d685e03010b1341c2401e06000b400040c03030000e20000f0300c83c03000e03c0080a440c050303005500f10341c52070762540701020101e9030080705911400300724001445001002d4100010084580c00107490007030f160450400040b110703581c24007a000c0305000420034000c0c2409801300900e2442d010b40303070111360900102c3c0c030f07032160840280c4950180c00201d07021501c140410300c880d00b40e104507192030b56101d01d4002e04001c854404c40c01624561701c000300300501148031300c000d2a82034500841c601446503092107002d010170810342511f6561a034504070305488800040c03888102d002c1e4100c1d961200e0404008107001c01c0000e15041140c0e83d024103000a4000c12610011700150401c4594860021700040e198032238803a000790820720420300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 576754955 1250 576753705 576753757
    0xc0d032a110706090e0f040c06051c14071d0a0b2d130f0501050910030f020c03040623030f040606050315040303050f0702120c0a080c0601030308150a1505 68
    0x160b10305441e617075014284242c5620500b40c400000c10307200030b44030744410941041950f0080006050b0280c901c245120040640503040084814a5440c503a0f03800c0ca240404c40040e61140c043c2e480303a660410843c03400d0903800e0118180403c54002c4140c40c1e6000a01e01780114008076195207032100160800a5000c0307125160b0742c00740c000341800411013099a0004c11410b09039008603042e00c006942c2c850405124204022100c4040c40f00b14051542ea160036042c0b1340d819000516407143c203a00155503e62030184010b041d51144070170702e81101214901c02d8021000348046a0b000400c0801d419900d8440d400c00e40b00a250907404154140b242010780203220b05074001d40c0d84668029202004103070344903d400042d0b48402c58090340107800950303e43c07400d8440c18000d8494001036504407081d00706142d5860b1a82c0d44840c1c4c040f40507500c2800100105988044880d60098032000c0a02d489aa0b600124950000502030503d20058652660300002e00c03840550315058a2400700071000803600c50 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 576756205 1250 576754955 576754967
    0x4060b0a030b04260d150e2d0f0a1107141e1204030f021f030603060501050102030304230f060c04080c1903031b020415090606030b09061005071203020c0d032a110706 73
    0x568031050003031801c0441e00300c8c006100010311452040c840001c00b5034900c01c2204c0242100220702d06816001e22885010810280070994181c1400c0018180307040800a01c800b65a85400e52032400d034080346101e45025458000c5e242120b902080a4200103000d10000d91401030300c040503140a030920001c1b20030030b07a145e0484400c59000e881d041149988035401241c507403000301c0e0007074007000003d10890b00d0070f220306075a804c1c4900d000341560b8262201c10100c504140d02644d09003a40b07800450280001c000510011402460450705040d4000e0100210a9499502c0c80041c09021000094111300110207002a184a80c010020050400a80440038900f0a140145019940b501c0004034010b03010344030300c10301040300034060324441c1e0350401080700c1089224180410050284851000214146450aa8440151400b43c0c849035040c81e40d604d001d5169007448105410008214040303410391000c5281c0e40c0018200e00c044c60354040b000c0d9100030011101460500c1611000181943d100c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 576757455 1250 576756205 576756241
    0xc0f0a0815071205060108070c0804050312070c05030705010f1817100507020303191a090c0d0c020610031209051c020108150906010804060b0a030b04260d150e 70
    0x18807445000c40d8a81c14401c100c404c12035900340403801e40c8000c40d40f0280541c40b0f20140070300c601d10540c5090345801c0803e0901c00d441551145282001c10010b04004840380080040c05050b4010030041d460301d00002c08030a18907280d80180205109009a01c109454000300a058a14496100d070300380a144582da81a6000815900c0740c030742000f0031381a52010084a02410812200706507484181c024140104480700e03004543c003854440c03005150b111540f001d032003101d9040d030700c035100e10383d130001d080a5a01c40540002150801c8080180c02a0001a000162038120400800c822004003050f5500c80d650f070490f5030300c50815074820207030b00704121754a80228802ea0303074030300d80d6150008048651100124030303070b600241c107500143c0c15520924031160701c176020303510101e00a8015000300300032503819001502c6030020b010400041c4501071704034a0301a200700f4200c185071100c41071445d00c64051608181c08464550001c0b1002c030032612544409000382030400c1c001c90034104100760183c0070302 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 576758705 1250 576757455 576757457
    0x60303090302130605014823060403050702030f06040c060f031503020108100314030304020108330a08010e060703060506070b0c0a03020d090b0f0a0e0c0f0a081507 72
    0x200d03000c0310f05140b10340246822a50103841c0ca60700130f80500c524440d02001d40074051100821441c1032510004200401c0da1021640c2001a01d0000c1c9030905194801811840320000c070804803201c0d1006200240283e40301d605440d0643e01d401e01440003e06103c03e000641a0300d101340d409003c140840c0d0300c48201240d00c03c0c1c840c90f00d500401202601a1000340e10210b201070000c1a00f04003550040074025404140c0d0307d24949010380380d68034010852650441c0b94450390010007040f0455070807083c516042880010302e24100d41000803402c45064034044100c0d0004482c00d400042911038549000c06007120364000c3c0100c4460400465030380c40116002c80c0040c0c00c0800025850030498100c0c1c010035005503080100703654100741017400381c0c80042c0d074404040e820010800d4100b100d1241020f00c1e442160b0301c5103681022000b0302244100588501c06203881c00e051404400300014444d03c4500040c0c4001203140c1c020800510440108d45c4130500382d0140c181c2015095060060b1640304042c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 576759955 1250 576758705 576758719
    0x80c09090a0e010b010c05030409111c090606120209060d031b060f05060f0a15120e0607121e2304030915090f12061508100b0f0105091210060303090302 67
    0x4c0001100d410200940180c800d8208010500c41500d01f9049600010110040079280c441d2461000320f81550b2202c502c0747c06a81c9078408020030982d4050035000305209a01c0080c0984290002072928401418142c4148194221241007500803c0d0401c8403940c1080d0581d00b140d060306040c1c0140c220044162041da141600251003803a01000700c1852007400750000b141e241c00e1210100f4030000c00000302083c4070710b9140741c81260051f8051020015072603c05041e16081907000a880b505c0e108180c0c0303580c2e03401d10b62512608000f01c031500e0400c2070240320210320f603800041b90004d410f030304510304010085c50500704818960800c604a084440810300300c0c2c00f00340315403012075a0301040d004090026000c00420810701c407040351145201030040c100081e10720f2150302501c80d407018652042c402c0d41c02c5a12450b07445401842002460401500c1804108c4110b00000b40740303104901285110310300c20850b5400f402400c00444002c1583c0040401c0580d48a00340608208002c1c40201c1c81982 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 576761205 1250 576759955 576759971
    0xc0314030c12010504020301080c010f0908060c0a08070c020f0d0305040b03130b01080606030613110916020f03040b090603040f0b0a020d0b0f01091a0708030f06030c06070503040303080c09090a0e01 87
    0x1801e03c21241227030549000b8000100401c80111012404084e21004001f088080402d03401002d001c0c480c02000c0c50450301e40d60b40c00c0c036a005444030b80010468000e000394402e43e034000d6181c4512884160908680900c04211245810b07151030103250000e13010441c003c0b04100342d0b00500c00b98050204d0080803000d801d685d0750506c480c0d0b24041102c2c4260150800320108000c1c4c00033f45071000c0b1140c4a80600007130421a0008221071000883d0703240e0020704400701c1d504010380c0510603c50702000180c0614602800d01d0301503500e0388646071505008103400800103060100505191105c140c2c0410b11219500b40541d0000c06034002114412005190007401002d52410003652242c01d101a11600012032500c00000e1540310303410b01c1d045041c1020400180040c0e000401144113101483d42000035041140034540790802e0000140c2c002e940c2000074401043c000000d603400c0303d070300d8500920a6a181c90b121100d50080c0001d0503045034410090001908980e0401e40019082c00001c22580d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 576762455 1250 576761205 576761209
    0xf03160206131a0a060b18101b08090a1809021306140409480e0c07031b03050904110412060203100806010b1c0212070c0314030c120105 60
    0x60341809000740b51140200c000d01c41e40c510f80b200c995001150000000e0712942e511030035401a4440c0e101180c00f424000300503001403404003410600c090941c60320a081e400e060300d007220b406e880b4410150054901007164441640d90003040c00c050300c030803400c1401500280080d44041d02d131621080b8411140300129012a940030322444d000ca0342d080200b001c48a1003a001e100007000290381c00d90b02d019540d0150011501071419980321511600c00501030840c501e007820581c50307103040075900c4d0f5815402080241e0204204803603080204503207080c0d0f44803050300e800d449184a282c0321900080e071108200043c140c006014184d90310055038207000b81c030131a020340000c0d4030590080307801101d030144812002c1031499002c1e6034807401d840a080c4820381c41d8074101d454088260300c490b11203540040c0d407200c940c90000c03010242c0c00c1c07846030660030030032210404101c0d01c0c40100044208120318480505041c4a400d00352100d11150807001c3d66800c1c511000380440c1d1107451005950102e10000040358 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 576763705 1250 576762455 576762481
    0xd051501060f0c030f090e13060501050904080a11030c070e010e06030a150c0c0f0c0302010216120201080c0706060602061005030303040c0302090606040801050708040b07020a020a0612020f03160206 87
    0x51103d581d804100400c0e0b41d01039801c552104445420012405408617282641c044039501890250301200600844c6140030001da44050700800e000700144802e000026402500b9551941e2a03070404846801140070028558000c4011010041c841e9041c0000d00b00380e03960555050b51140c03840400c1c0380d43c464051641d106980c200062118009400c0c107140c0d0320301644402d500241c1c030300e0140810031440d103c0c24402500070000391032100301c03080c0802c21581c040100b0030707915041450280c00145401d10034004803c4512029050001650014505558030021100c2c0517511110400c425074558200a40d1082c0840d488106c88582d0500410725140002c15284102c1d802200080ba0394119400e0100c2108007500e504c0d00880e05200200300d80000b80600c030300c114281c4d0389020007854582082881000080c2c00f0005542040e0309107005078840782007400a660560510100071180600c1c0440240b2031f8030040503d41c0004414080120742d112031300c0b03d84005d1542190110740700e444400b101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 576764955 1250 576763705 576763727
    0x902100e030d080c0903010e070602060f16030b120102270102070807050409030e0a08030a0801050418020d26031009060803030703090804030c0b07051b030a0f0609020d05150106 78
    0x4154403401001141910500c91150301003081c000c000e085c00701d620046800d64511040208040c0c000c0c82c401c1c45015410032055521022000541800e0b041c2400600e4111904011a00c00c268842c2c1c408000740c2c0362007200da08181a000021543d400e0003620108106051a607496030500d448041c1114640c80020719400f96203045001c0c201c40340c41d0508010080c036810700200c05000521307000f80c80a542d6201380310010314081014541e00d40c95044010303d80c400580006200c0d40c41c05140c0000c00d1901c03100341100d1176040d980145120042d0070402c0c81c210140b40341d0340401025404041d40d554140024500825400f5000911039403214003580c01d0320068010481181d0050000404061082d00311280b180d008400c594586038480d118805d082c01540c01010590500141c1c034010003404010100c1e102644940880c1d40c0344440d4000380d2643c80142002d400f44821220078024001c030350380301c03480c55a070042c440002c1c48068580720b40c850100c107900c91090000c081c00020310b11700403080c07911 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 576766205 1250 576764955 576764959
    0x1905101109061b07030602031009060f0b030a15240e0406031e0f12030203090c0a0303121109061902070801060302010c031110050114240d020912030a030902100e 71
    0x401c0c2505140808280000d4440b907407421322500380c00201050f040d01c011805502c4450b0f105001c581495008000d42b285079014000d28807004808000050740c0d80103894001d0a1810041081c410790048034030075100ca071708003454000074040d0b2020305200078803401082d059a82c680000540303030613007048100e410320302c405400c0c421400c1c1e818040b0950600d0041d01030744560381c800205000d5031140f8824520801d076101c00b10f87d000013130240c0204200200d4021110031074884071580d003182e60051080d110030181a070006d40b1020540070b44111401503a410a03c09003441c0c0c0c50340c4a6520710540d20002000e03076009400f4801d004200000180201400d83e071301038584101440ba43d42d011609881c11b18000030b031600940c00c0c940d0f034050700c81c05094002d103004000500c1100d50072041058452101004c05003980d040742240202c0204001916078440c5003502c0142c540707103103402250741800c090f2070300107041c0000140c40000342d03010350041f14114002d5442d1444407a1504080e581e0130000d0502035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 576767455 1250 576766205 576766207
    0x10c02070f05131112070207050913150c1205150405012c0c04080f0601050901171b0612071713030804020f1c03020a140a0305040b0c190510110906 65
    0x800f030f118003034211402c1c1034800e1500c1407070440344007903080f11090155070700801030700020402c2000740b2300100260b4000d8840c018030900c03000b003580c0d034041141503d00d400b01c40e80d031508080c852150107803400c03480c844404071041c4094a0801e003030303810102021612504c1180b50000220b60100009130241030b42c8202103102e100000003400342c0480c4d8100400034900c0e803808010201e007a000078080d403120240d0403001040c2c1941400304103c414070050700002a001801c2c40541c2984c0c4000810291881003c813416551819020205245100c3d1003190b90390702006100f40f2100a921030f40461000c0070030030700d0300e01030b4855020009903030502c014003400141c509404200946400d4240030401100203249402042000c80c52000505000c4400e80c01758000c4c880040c180300001d40115000f102440c0540109005641c02800500841c040e0501295000c40d401c110840c1c2002418503503807a800407069403104614105942d00000300f0b9018946080a14140828100e40d041e60b1240300d009201b2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 576768705 1250 576767455 576767479
    0xa12030e0a0b480d02010f0c1b0501020d141b040605070b091e010c08180d12060b03010b0406020c030601051c08070204020a021509060103050723030d02010c02070f05 73
    0x604600580c05429000c3c2e941060940e030351500c05000b40841e46495a0060718500c1c0b40075a000c0c1c2114800b00100d146241003403091003045500511900508550540312806c000450404a009000e400a822683c6260001c01c0040e01400702e0001c0c818158210b4030300107503048002d00f07449400f8902c200401b20340140300b80e500107500010925840118141162140342000030505402200725070310036040e954906001548a0344403c4544d8007400c000c420300404800460030030742e1000d09244500420072403001d100c00311300481e0001c27070080c5032034403d0545950b11340745a062154414460540584644074140340e0504000c104141243e04c010700814068400000244210301900400c481c01d010400400c00103036034a10207001403004c0755000340f003203007200c0c080302010380e001801d5640b643d07005400400004100190110a82c0c0605981d03801040c0406001c0d00d004041140b03256250103080d0342c81c0c588a505500504110400b9800c8420655940d950603103403201034005c207500800e8044038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 576769955 1250 576768705 576768757
    0x180e030f07020d0f120e0a050d0f050a0c06050306270105040e01021c02040e0919120e09040506040605160e062101080c04050708070813020a12030e0a0b 67
    0x140c07800034006000c90400c3c0300325035280007a07140c1c0c1c1c0104031000344900e04210010303a44001403113621281034030040840e41c10000020a200c680080080c07200c12400f80d0441004000c3c04505c1c005603210185036119916940c0240c5590000c0314081d000301241c44119006820001040c1d00801000400407880d90914090101800302c00700f00e55201d640030000006217941005822010300000c0300010384603420070b04000010040a42010096170080445139910310b0a010200c0d00b142d8055512001c00710b0a80044c0c4800450b1501141c0c03129002007040144100400d4031842507100b001c0801c4250b50b0b2600c0d001e00030100041c8040040c441000e0800241001c20041900100600d07500800c0c040d404001d000d6018241c112812a400080702c030000c40c2401e00515030031003d2402d081150349031042004050080041c80c040b02d004620b448581952a1906100043c100149541b0440c80c2e25050203004c031104c040b071241c00b03010041c01c001103040341d490035103c28030040706052500160844c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 576771205 1250 576769955 576769957
    0xd090504051e1306110a03091203050c220e070e0f011d040f0f061203020105060f0d1b08030c010212010509040b370501050102012009010f020118030306180e030f 71
    0x3c81110b406903504803640149601074054201c1044540e00401e03036200a01d0451144a0305c00100018107082006014501101c541603446811a4600150139038000320010300b4004450f9100610002040b414001807951082106049000a6030b4030800101a80011118603840900016980e070301010b04400c2490a50003480e1682911440803641000030454542100d00c1c2d0380c8a003090b02d084a11810405070280180c65001c0412141c00040280440110341a0760741480020010082e0340d070b542d130411103448203450103440c840e4100d81c1c441681120341c034001d600c41c11541c044034101100004482c60000c4041d072003541d001140d002240ca0700d03181c401503140c90989516001500440d4982da104c02c0080100300148004008036080d450a4006400c441110a00031020340300c010f904650b112001003119491442807820014200003108203d0040210b00d48860754000c000102100b0316906070896000c2d10b5881580ca01c102d610500c620040b0340050481c544540c000303008111411103ca0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 576772455 1250 576771205 576771241
    0x91d0d050a1106090d02060106031401030f020d0f081b0303041203020c0a050f03070606090216170d060801021306020a0c05270f010e0601180504110c0d090504051e 72
    0x10821490b09440072968504007241140c4080e400d1707101c450003030b40da01d40c10001c0d6801001141030410204103440d9440c07894641c1400701515554100d1170007021916841c203140722143c6c2000304200c3c4200769281c100c8103540515030340d900743c414883d000c18228070041b04590003582d02403070200c1160110749090b8065005500280342a01424050801040b4240943c031111000c0a000d540c2c2c600361464410100c0301240c1103550014414080310700701145035010607500caa00021a0992200e80c50503400103803040c1910041010701b0301030001030b14441500640041c00ba07050299103500d4640d0012680c43c1c0c0340d000c0183c9085200301041203075061412580e0b12042042400c10210b840403030840309010780c10307543c500c040f03d81200100b00b400703900c5426680095091810200c90751426444074811003c0d400380600ca580d8888860025540c407000b1260f000b1140001c0d03030000030f00c094019001c58003d10696014904040006103562040e00c010714076480d4070103001410703464500307180b440b80c0611 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 576773705 1250 576772455 576772457
    0x40501200318160b0c06070309050d1103091507050c090c0f0906070f08070201030b0a050d060225080a090518010b070212070801150f15080a140c0301091d0d050a 71
    0x150710f007a03191000320303824001402d07501130341590700c410000b20b1030310342907000b4040c01c1054588528800001c00100d40c10428044515003004041000407031142548102605142d01c05e415401d288201d4030500d01a0a48500490549401c09043c40910100210494000501000400c403c540803c0d10001420030140040d1405042118036565880f042808280c00d44040c440400e0520441da0325002c5d0b4a8424015100d281d122490b042c040743d240d03151034000400c40780c0c000c1450714401c015911a081ca10718941c00100c8940d0b401c0c2000c1c3c94591080c0f40c0d0360300150302160042014108408100c001a1818099008903032034041489000c1e002103a049034803900c80045141140001c00c10f040103091800c0002a400ea00001c82c2c07030095400780d000e014421810f0004115008460020b403035030380f00d242041403482c2c1d104143d0b41c0c018089002c6a4000c01c0c03100d0b00313102410300c1e080051410313126204c0301000404042c0310401d0074400b21000c1d68945a000d1582141094411000b4280400c51 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 576774955 1250 576773705 576773713
    0x3020d0809090a091101020c0f0f0414130b0901150612021b072912090a0804030309050f01050c0a062003090a0302150103030c030f050705030a08040501200318 70
    0x101c00052078000003500c2002000b40c039204d4040900060228405921009000030880c100f104004211000285160389104661b07000d00d000107912160403070174101c0c0c9007440322046898403072060001d04100710026104500e40c0d10008a03041814441c1d0724005210f042c23105052803400e181191b079001840f41c0c2062030364007400071201608000b203108403900082000391029904000d0840001c85809091480d080000c0e80894640204401100c069450380d4142e000c1c10b6450b0803e081c90300020510050800000240010a1550140c15441039840441d14891070158003c01158107000318040c1c1b00c8950020000d9500140305072340700c0041c0c0821010460701c4070f200ca03072810b03045400032110601c03913401214903c801c041c0c2c10b000c00c880c40001c4011f5071000d541151401440300308000001814443d0448001242501441c1500c903401c0e40700c0f080300c1d915102c1c000001c00c00a81640c08440c0e070360905c0b00c503408546004120058006c42240180d0441d5200b03820002a08180c4c1003660390750003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 576776205 1250 576774955 576774967
    0xc0d0804210905040c030b01021209010c1e2003010b010c0302060a05061201020f090f0607080d050703090209160e091603021605070f06110706080408091807020f16060903020d08 78
    0x48170b0060741410070b2282c41c00070f5034950400019007005040480030010910410003080282c0c4c100003002e5400f5007040700c48030380e00150041070300c1041d1421400b81145440381030101c1c3d10041000014500341c8290000d11034903401174010342d01c040e6100310003400f50704040002058440c641d0b111941c40907004100c40c5002810403540c40c2282c0c0000c0f8001c0495100140841540c00d040d18440c10641c02038990928141303030358541c4606800303101454001c0c01d4441001c201414801e40008400c107400400c45002c80c2820800b020b21a0304110a2038003103184180d00c1001d91510028640c8540018051002c1ca03080150003103000f580b01070302c401c0030403031382d45400c00c045002000701002038500c94842c400aa402d051000c3e000c0c074120400d00380250f120751414071a00b42e100071920382081c3d00c9420341c0e48521582000039240740c1e0301c4034165002000a8100f103803160740000da108098002d40260b422000f98071100d014144002e00035207000c102d100004100500f080d5540300c6c80c40b4003403504241009 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 576777455 1250 576776205 576776209
    0x1030504050c060d15121a0c0d0212040b06030d08010501030b0303041d1909030f03091e060506131a10110f1b040902030706030b0f0a0b0c0d0804210905 67
    0x90130040350709800139600c100c1000038200d64024003000d40748500581110300c2e66961013162404415122000d107a0059001c15000ba0380c06007550190100c0d10020f5480c0d89010040c840150b00440303007500c0c100301080c042100c90401040d041c0b00f10102d692281016800c0c6001500544000c2d155250103110400c80041c020110002e002c01d0f00c1e0300003030040c040b41449124407108075081e4000c040c510307203440708610000b90490070001c1da542c400e040109000c0700354240381e4507041002c0b1b000c2d04450461a40c06042204580c007040c400c0000304c44921038005990098401c0301e0301c5800100101c800d041c141d40d824600105081100025031400258078550609d41500b00141242101c1d011352040c06403d8080c201c400100c40070301c4041e00c082050b001d032a00007070395480c90f5126110901d5035683c0800a9615801c55806c0d0910025150014159490700b00851582c8030707032004607840c021070114600c0b030381c80303110b04034012a0020000c3c1d02040300d007801a12a28071241a603020702404000c00a026 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 576778705 1250 576777455 576777457
    0x131805010b03060132030a0c020c010504080d1b0206070302010f0501060926010b1207030c270509010e0d0206341815080403020d0905060d090c050607140c0105071101030504050c06 79
    0x13007d100a010826800c225406407401100d210000d050080074803003488888400180780840c0055450041d40e1140d1038517061980070700c44000a5080000080e001c01410f0b015004860498401c0608100903a030f28041191032052a00803085425000a01120980207201c40e00c2c5078481400d000092400145c00081e43c0881805000034103900301c084200140503441d000d00d4020320316140c034268411111485603092085442109643d43e65400c0800d0f4605025070107020010020001ca918074141c20f04041e550f404200c0342c0e00f00407030b0101480300c28a245000d00d00c180d24a451b5084a0003185d81d47d080e87c5500b0844840d518602020600042c1c1c048100015455559140c076106000d04181c2030090426440c170b044d28060224200c2c040140ea2900310031034000c03800340b000008070144140380040c01c985182e4440b41d4400d070f01123183d40030b0003034480482d50745d241c0d03900464034844035041c0191142e0064590140584425071600280d550082e04003545c0039104409492070340e4201000900d403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 576779955 1250 576778705 576778711
    0x4020d11071b090207080a0804050a080f25020306010e0a090f1104050601030b0a0b07020604081e07140f09041a0103080c0f060103050307080f131805010b0306013203 73
    0x844200041004111502d03010040c000d000c01c1c01c0c0c15458880d0b43d0325004058401d6401c100b04201d000300009051050074410041025403110003240d07a10480007807c20140c03c07034042c10540c2520100301e202402101ca01c000384040e400380207080141e10340310401540210043c024032855860b00c800c00006005180c8102c076080c410611000112048010300c8210380000305440d0515107040d102424643c4e071098403104886680c40b140d6034490251001ca4040d00a0380c0c0a1140351240080050f2404410340701c035004002c107982203500d00356039001c109080120b070000c0c6517004030200d94001410b04203000e60700d604c10302a6183e500036500c6280350000c1801c0903070054940c1d031404a040c0245110a0240c60f0745900500002c0c80c0550540d240c05440b0f2048502c002c064000010320b140c1d0b81103042c0283d55103950300084049081c0d540d07081d80000000e8040c01020203510706030011a4068401047d64090001a969640c526580d440b00d08880203208070180384003000d54004100400b411001144 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 576781205 1250 576779955 576779963
    0x2011802031b0121050a050c03280213031101081f050d0804031b030c08030703120b01020c09040f0b1b03060f0307210209010f0e1504060b03040b100501020706050904020d1107 77
    0x3c072494240c0e046c41c200d41002d0540d80101000f00248440030303150080c01c0344042d1914017408034515220b41200000d21515a0079194520340d032100205021055483d0910300c0801c0c0ca95280075a01e1040041c0c03a44a02c1300040c51400da010410311140c20600314034103005220b44c00c141c0c905626901c4d501c82d803034480d080941c0c403122040c10900c00c0146176010140102104401542009003503a006003100303c0a1aa05082650f1100740c001c66a10030070140002400c083c00d082a541014241450780c9552070400f030310005100b0020506014241c1c0c00c0c40b00c1181140d00b484d0550303ca41d020418000c91034128507a26116000700490954210740c4490501000d4581605144030203105000c41500142e00c203a001740f0a00e1740410070ba00070050303441c0d4846141146640c621a4000014009200641203c014840040100030400c58100c0c80c09014a400001549605654600482e51084207000b1400000d00038002c1c1035031420f0680161240228450700071403041c440000c0580c0903004800c09075 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 576782455 1250 576781205 576781211
    0x24040210050313060e16030b0a240603090602040f0e0a0c1d010c0302120d0c090e0603070e04080c0a080c2e02070c12030207150305130b0717040602030702011802031b0121 75
    0x94101400e200312190100c0b01d00c180740070b81400c054240e406980c14400c500502d51537050b1001048000d0341200c014042c141170300e000341c81d15101c0102c2d94840407154484c0091502c451014250700a0301010005800c181400340b0700304540c001111040240181181948a64130301661005055000b400c40f00514400026030400b002d04010303d01c4251b030f80300b483c0ca8940c071002d10501d500e01140c80d9040d5030000c0e00000c0b59840d01e181071744c194462032030072000c1d0340030780110303a01082419002021204100030485100701c4000180300382c80d208880f10444801c3c105583c01c0c58202c4a5000b901c14103014003100f0002c144d82d0661a4035480c03a80c4411801a04035902c10300c940500303950540700da000b06240070081440e00d8850000b1121510310050500d0203401c0024060358803468030310081c1500004459802c0c1800d10340b030000307500145e59800140d400c003c810346140154540c0c100e401500103004040740380d22205a980c403503d0b40c0141c0c904004c1c042214443c00003c101d9034500d5030295141c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 576783705 1250 576782455 576782461
    0x306030c15021e1c0c15052805010518090c13090605090f06090d1b0f020d0f14010c14070c0b04030302031c09021f0224040210050313060e16030b 64
    0x82c0b075030184500d4540248400250030801098a4100702406d40030a2100025162139030300c0d00b004140e141e20b458211170842d8200c0c4607124900b581189040f15001e0b04d03800c80390010507412105445046441c0e40b003075404001c1001d81880c000c1602141e8080311400043d01031125140c240581c1e0003202c04401310740c054202029013220411031150320025040c0a01000a07079040001e00031006014100049043e0600c104180700c064a11505242da00030007545448180e46403c01a03400350b1101504c0503000c6e0404441d210310180580000800c143d5209000c4000210b40020150030015040d540c55a00c2500030038485070150060020354080e4008640310307822a072040800c092800c1d0300d81644c03070030107003c80d005032998102000c4501d0003450b1b0440c03195920100324641550405604600c60078041080d400040c03440300769028500030b440714012001000300070390707241c401503440004820010860350701059881d40300c81e10050000c03064400a80d07000b9070404090b085600162000c1d800c0d0b0040c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 576784955 1250 576783705 576783733
    0x60f0228030203040c0b031b0a080a060b18120a050601031506150806100e1e010e04060e011a0423030f0706020303070302220b13060306030c15021e 65
    0x204a0303808030586001d41c610725095580c820040290320900c0000100440441c143c0c0f1001192610441100c01c0b01e182c0300c02c59580001d18200017039a8000e81c175840c001010a45162882c11a1400d5510949101e07041c9104420b002a298110b10041c0650041c03060740400170384140301c44d0307000318010b02806a200c2071640514048500d564062401000307404010703001142c0001c02180c0c084000c03550350840c040c2080d03041c1c42d0342000c045ca00e54032050b960b91a859001e102d4a01941a440031f907509035000140100303000840312540501c05280b568800100038261407103001c400348640d095812400e103503441d90b2501060001ca4820441c0d041104c0031110682010403070221506403101c000e0880a00d00301d0b001c0d440740b00140c0303090304058002684074519609585a050f5200720824010040c55485a1981503900701101060300ca41079884000f4000d0310034059541540c0d080440d010f4411705d41550440c08c45508103041c0c082d80282c0c001c0003103c01240e5012191411800003a0000415080c0307 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 576786205 1250 576784955 576785017
    0x3080304170901020c010c0303090212100f0203091b010207080114010314060609060f041d070f060c0c0b090d060914070b1201030605100f0305010b0306011719060f02 73
    0x1414250800c02e0140748056039002800c0c034049070382800e00b000400980d01341100a090500c4000e504952004d5130500d4008002941e4013016680030001c120342d201d802250000d0b844291074880c0c0d2075010704e10014102d00b0070303240c07201c10680c140100c4001e26038811015080d242002c1000b10101080b00041044c00284206400b44420350809043d00f480d0000010700300d0200a00407034002c680307071094644152915804405855092801500c00c200500c1e071099484a950103038282c1421070b41000907616000b140c903604d5440c0d03c040014489820801503603001d401c0701d540d0941c0182034245480200702030f88111404c89024044081c0241d21a0780d06c54038091082d40860b02c011020046a603800440310451819aa4801000300d119152100c0303000300d40819410030164015032140000820005520841c80c0ea0b8050b8203940b016030340d850380c41070141d40910000009400202070389802000180c0c0b0f007071103244142d6000543e80014001ca03002c0b41c1016944421880c0c500b01c59802c1039482032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 576787455 1250 576786205 576786233
    0x32106062106030b01060509150702090714040f1e09050105030a03080403030b0d1a060a060507080904020706050c190207030c0e060102010e0d0c05251a0f0703033806070c0503060103080304 83
    0x14114ac0f410105a01107030007c003004040c0d004120450080740352012a00007258000c0200c0782e009940705844190901001d048101200c4624a04403000520100103009142c1210b600030b019106030322041d01c003560501c038010811010180c2c1d890421b6010b5680180c10981c6c14040c1d1102e406001411003009501440540454424040001d04001007544501240c5180d41c4c488a0180c4441504011402a000f212001450340b41040c0400204000080207032000d00341000e08040b600880c980c050b41c8500460001404000d107a8006108203208242031580120061000007090f0100840041c10885145100400514211100d60030302c2010428414400d6680004011101c803014104030389503000e00c5101d244503001c06114808000e40320503110790540803105175607a1440c03031500400400c42206014424468582403480800c8021018403103142e0002c017265000303c0180400030281c2040700203e400d0720031000007007626103003449024000c0d4898400340d80c8900302403600e10301d40c903045 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 576788705 1250 576787455 576787489
    0x50c1e070f0312050a0e190515010902030f01090e0d050a0e0d030809010e0616030b220203061201090c2603070c050a2c0c16032106062106030b01060509 67
    0x10819000b0f02c81000314442d009110f401c8541c0f0782c901c61f0b070f1828904125620800d10540e86058000192464068000f948103080ca005100d22983c2c8514004044070f114070044400d980c8040c0c140c0e000c550050000b00b5066020381847e1840a51040000e07030145000740c1c0880019107802d083c455140b4003405400d00e0500c040000e0309880c5441480442100d81e807484190805841d550b107021140c40b0f80440589403020300c2c1c41e82401840740c48400740650b0003176403140d009a031441440c2500300810302c44c480c0e00540c0603007544112440e0120500c401d00d00d481018010003d101d211791814202080100440380c0b02c0d400000000b0318040402a144401d940224031480c0d03060640d11500d00080e0110580c00e2017882c40050782e4980300760075041802a09a81801c2d040641651018150819201c440d03a054500400320041402c2040c4801d44603284200740100d00881c18074540308a0b078402405443e1007100002a905035240c40f40c1780525020703131000001c81e07400100c0c00864206940191148164 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 576789955 1250 576788705 576788711
    0xb0a15060f020c060307110a0818010c0308040b04050f1b04060b0913110d020412060621170c060f0103030206060603190902011106010f1404050c1e070f0312050a 71
    0x9818002e501e4014071403100d8030900d00000003694003801115400d401300055411144101c2c4249050203040e40584400c0c08403d146204d0124036621880ca00c8210542c146d0302c2030149d4959a807041d100c048041d104440da8003032032583d005030600c10802800b4403185011450880540107060008481c442d40104022000401020440d500c03012400800d0b01d102e40400210104900f8429542d0302504040c0303c00d131400042c00144a8113814180b918050042c9002c03c50303140d50320048400400c504d05080e80c0300742502203030f00220706010740810303050303078450003040c80d00140d0500c00d400c18800b00d4244d91341d00710724401030050580c1000340716446903041d10014513600f0070311551500054204100c0070701540307c54240e0116403003000e48004c42e01e00001180c80075611500810a166a680103c0103155140c1c0c2189550746024003400d4024405801041d140074044542e8140ca03010400ba955500c1d0400c000d448000783c4103c0c181c5078524044e640388042d403070005d2090740a80384058855008141 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 576791205 1250 576789955 576789977
    0x9110702100c021905180112080c07030803040614071805010e04020403080d0617010c02100522050105010503010b0604050603010303050304030c0c060f0f020303091203100f0e040c21020d020d0b0a1506 88
    0x5012410f501d20320b42000f41035403542b81f4000020b20300f208980004052020100a100812006400c070204405103141440100d90303444004450407a50440c08034003030303070b113038402084107500480f110320007500c0242c80589401c3d100d482e030b000d26901c0f8000710320445944400821019040c0343e01502401204402807140c1540550000d5807001050320f1007403540d5480300824000c4003215140002408010518800c0c5c0c0b0352420100d00819092042d2030003942000c4a220b524944030040b00c003914030040600b421033342903880484a642004100302c0602c0700d200c8201340401c820b01d213240020030503540c44444074074408500802002d01512441d0075135100348144004104007007482e0a40d0190b0281e00c40e16551042c0d41220030b240d5070b920045010800101c08902e004829061030720642c043c82d01018441d45e210030144046126124083c841c04000b0120801840d0030244d219000340020880100042161181d900707014040c3d8000c8235941d5a81c50100701c50689520200c000e01c81e506140102c02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 576792455 1250 576791205 576791219
    0x606061216090302030a1209060203070308041502071709030d1b0f111c020f010c050717010914100605060307050d020714071e09110702100c0219051801 67
    0x94409007403900500e4095990701449445010241c00440d00241100e811034100d080c13103401c12200342c0305140001d100036001300b4141c0c000000c448485074550784607011a0303030701c1c1c8039409a0691561002e0390300e5020424140898284030591080903a00d5103003582e514000e6041524000d40d1175030303503428000303410030540784240c440b445183c02940020090003465001e10b41048802c0b00034011940c000000443c0343d104091a042c0850218400e550071004500d0110040d41c00b0940da00d0024004d501110003809207624040103003c2d815a10000030900300400c1c2e951642203025145482d80da60b00511307110100340120f0065000a11040c1c500a2640c1080c0400030b1040c07264000310812190002030b9082007060f10b011003498040c6040658480030384843e11240000241341c40070424419016000c00e1f00c031014403800724040e40d8024140e01d4607103103a09100c01000d0740c14066060008080b03102001d41c90780760007503142d0800c07611401000c80c189070400c00482c2c500301c01e10703891652a400601840d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 576793705 1250 576792455 576792487
    0x40815011e090f0b0a140a050303121f0503030a050c1b101d030106030503030103150c0903150f0e0304060f1b260c0604030f030506090a0e010b06070c0305060606 71
    0xe661004004941d0211445031840900381c142912038215260b140002500306640105100c40301b01250b07034807072403940c1e403041541d01d000d00fa04880050382102d002c201c890402e003030700024001c01482040070441d0b44000283c115000b49442030041140050112060b0034244140f061030351100603030071480f00c00c41001ca611203140d641a5414400360407421100c406805c0055918008010002e2041c2d5459140c01a01c80d0002c0c40101d03410103649286c0c14070780d03110b4001d40a600a0b10b0307840651881c9940c848a030001e2890145110b12035640d11600d131100c0d40c074042c0110400c40e4a000b036131307682d1030100e00520b00c140c1000c481c1c00b0010041102099040002c1824074000d40000c1c42d05031001030050081490814880130669800b03000920700003220001c03d4185c4118020b499070b00c2d04541e0414164240c0d01d0464205a1000d07140c07000509041d40303076108032441c050a030b0000854043d07000102d511640301a4056480003a40c0000300108141000065480707403080c1c0300c0f82e003051141d000a00380c1c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 576794955 1250 576793705 576793709
    0x4030c080a050403020d061a0a1202040b0d0f0317100303120b01180e10170604060c030b100c062703030c030b090c0c011104080c0105031b040815011e 66
    0xa046000140301103002c0c850025180075540050103441c50440601d448001005038401620f07080318544c44040051415080010444602c01c2507251030020590800c0700030200d020900d03601040c41d4200070007180c400b0b00304042c054440d4882da2001454180d080c0000b2030b00400d9600c000600304020304c0007950025001c205290705040215903601d0350310040c1e50b046100702c200e85c1c4400c107030350700051114894280c2c02c0c0039008403444141340c0354075090070252512a4a6040c0700310b40c4030794003040008500340c1c4800c0c0d080d00145000580c440207000015124410300b810440001c2c800e42100040c84442d1048881428014100c40d0324030208945541c3c15203020640a41850760354420880004c0c06a0415401090f004010040c81e290803084200c240d04142030f200f403250320380307000a428101c8001c00c031800c0e00c000d5401426080c9121004450f42e600c010411142e041032054000341408860000e0f101500310080642240e42d903001080006440503071041c00020300c483c020684502407003031101c003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 576796205 1250 576794955 576794963
    0x1090b060703181a0a0f03060501080718030203160603140402030a0b090f06070816020d020709021b1005040b071805130213080309030c040504081b12130501110604030c 74
    0x580f1290042c003480b07042c0640e61084d050036080d000841c58205841c0e0052a22181613280c007664031941110840890780c0c5809490301081440c3c0100d19a140511070313181c6800107021110b0a800c1d200d9000c682481140308119030ba4481c60300e0248030580e0103002c0c1031392441c1e101e810702c03446207081d07000207640e0617513480c0240880300001c0201d29062810300c03a072403400900404562060925401c01012400c0407620118a103040103070384a80b6901c045540341880d01d1540c000d2089601b0308000200030350090000a401c6100d4154a007080a424400e94107075524a00c0c2c002120304c0e19007040f000e501d800508500c10070a501030060104194000c80d201610310a480c510340034580c5a0b40d103c0244070354501306207010650040050032840000c0200f15200090f0240c1c2e0440802c0070501080c1c51081d5802804120203020000d0184140c0a40c800c007085c4000484040b0700e4454003594165120a25040000114020500055804c441c8034100341c81c6d0440144098130341501d00500030905640010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 576797455 1250 576796205 576796217
    0xb04020d141b15030907230301060806010617010308030c130905041b14011e0c0b1f0f061e26011404090c0603050a02040e0411010801090b060703 64
    0x10003800342054602440c500340384111414041c0514000c01090607801e8210300c50812204044480703080e51013528000c0c2146001806100c0c2030445984404400f007944144595548000000b16903090194070014010704000d00b40950416100501644501c5c03002c2c0c41c14185480100006030400040766445243c000140d41c9a070b0158240f04501d41e004d500248195060070103010900407040301100b0707060354401c540c0c7d110594a402c000305c05121402943d020031101000640f00705d800c00c502d0381d00e01505282505902889a0700c4103180c101c280c0d01060410035022a840d40c1c401000c0b40c1034061b10440000c44541d91400c00001c10862120f048035156410200103800030f54064101030705c80b84072003488801241343c100c0c001e90341ca0f003007442000ea02a0101c0c000440e282400c0c81148480f54102100da4405810288160040c1c00301600c0090026800c000019800060350007040c0600d1143c1501203039031040c0b40004103d2101030700642c915604e0588400055501c45045540c0107506003001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 576798561 1106 576797455 576797479
    0x90c0c0c030b15030607021b12060c0403060b1e0f0a150c020a09200307170703021c06060503060f01020a1b0f0f08060f0612070f090609090b0402 64
    0x10340588c015480111110201d2010158410809080c681c8071001d22a0f080c1d12b8448100d9014442c3d1001103000d10800c00a030182012043c422141e6560003500c140084000c50b03942650140301d0140c44130f0040c07042d100c01d81c41c00018510325050458064107600017504514002000328400e000360280819003442901c079492100e07461000b03c1d500c00034002590321032503101425910500c104040d10031443c840c504851842000655409a1599a46519602c80c129441d00c180101410864103000c42c1c1d520005a030760005c4200c500c2402c15400300e005070b044c1800d00f14003500410202c00100d0880c00d00088110444140c0b010b0340f961507603944001610200c440c050121355401c60004036800b6091080302542022005002180c045010b80d0410b252910550120001e03c080b9407081000288074031907003009001c0f101d000d1003800c8641d650305861160040009200710303841114 = true := by decide +kernel

theorem cover : BRFrame.Cov 576618705 576798561 := by
  have h0 := BRFrame.cov_init 576618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 576618705 ≤ n) (h2 : n < 576798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
