-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2660
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:22:10.652773+00:00
-- url     : https://prove2.me/submissions/594281fe-cda4-462e-8b4e-be7cb61c787f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 478237410 ≤ n < 478417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 478238660 1250 478237410 478237433
    0x20c090103060b0901120f020d1e050d09080f120904110313020a0e0f04150b100503100b0703020a080702030c0a0b0304021e0a0306050606070209090f010f0c0801060305070309050d050403 82
    0x150106ca1043c1c2d00740c0d51a44041da2030b0501000348180400c5224400700081d00892503448240a4044034105a40740740655650020f04502ca002c68445d20340003e031918001102c20701404000060a0000c03e12a2100041e8004920b00c9500c50789030b80b514400644c406018500c03034600451088000c40c41c0b401444025100b541220141442190800001c1d01d880c0b1801c0e0380280e80710b40b016111440d141d607580c2c028680d8281c80da0340501d03000407060f889641704010318060032003071011001c0c0e01d0351281280e05034800c81e00003d0158111680e80000300b403600001e01140360014060302c404002100006034114034542095901100110901007541071050300747d4054001400e10280c26414100000c01d4030791284001028a911200042c0003925410141d969007035000e8400c5400b8145010801e0316140001c410700072a42c41e24140c502000020b00910130f541403141c03075040036642000030880180c40000c00000c24982c86919030000a207040042c1340d4005d44c155555500c481c03c0d031600340c03203521 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 478239910 1250 478238660 478238669
    0x70c0309060503040809210111090918060103080f0c120a0315050f1c050d20060105100e28051509100305040519030201060608090a0b070f020c090103060b0901 70
    0x1018400c04c400940c0d14000c4400b440c02c00c85407000341d0303450f911145020f0603a80304691165400c0c0004030301d0f6055981c0c00381c2081c3d1011203090003d5500c2681d104840461900c42d0221030380403100420100e00d00000030010b40813507807a4a46042031200c2d42070720304161001c60f000d0006000402c900825414814900c0c02d451041c0300518651405c000501c000b0340010506201c0c128048660b210044c60071405c00003568400c1c00e03100b44410b2110050400d10740e40d51040b1110110401d1420440c03400320f1500d0580e0b074000c14107420801203d8044404010490000c1e0300b10000342c40b0f200a0324039009840300070101491a058001d401c00c0c0603c20926003140106001540600c40907109a17110071030034241c0368042c60006100e554034100907242c00180d01c000c0140112441080040c10342c10340120f03050f0360168451031551b40301c500c6e04a98031400a00701070444000c0c03101040302d02d44120003407480d2842034030441e54510445c400060072914280d0045441c030b6a103090085003810401249070040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 478241160 1250 478239910 478239917
    0x415080402120d02100b010c050a0b16080c030a02030a180b220201020a11030a0c08010204151704121e081605040609030b0c120c0703020c0402030601020d050c030c06070c030906 78
    0x158000d100185da030340c1e0030340703404204280c85648100041c1d10070b0b1030104507640c10070101c86038a900d03070501c003040407010390390b070410781a510152090381030241c140c0324090502041c0e1249941d4031030002200a410113842e20034040d40382c102203146040da020040740414041c401e9003006040c007a204440c2103c803524610000b0420b4803002001d40e801203580711150b0b811004400549499200090030030300c180074006c149520366503000c81c5904055003d4402e0303c01000d0101d20401c03481e0800d562100c6045590fa03021745403a4001800940c409007042030884450030f00500b2400214000c0d1030008003010b0307903000560450100404000310740300138a1000c096003001490075003805e42c024521915808058854001100800c0d8000c1e41c00702203c0d0201c00805884541741802400b0702c015a001c120217500511070b8040803070b2540b0380351080340e000f64416001807041c541488025903060f0000756002040e0300040c004103449800a1000c540324807002e0742c070400c40001d289400b8105030202c0e000030b002c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 478242410 1250 478241160 478241173
    0xd02190f0201202703031c0b091b07020102070512010f0522080307020f070e01321003020708340c060509031603050304170c0303090411041508040212 66
    0xc41880e4822607555030354201e01d0403580c4510b0204041202074520703050760540300000b600d04080d0103480104484019110042c040e02c02d08404111807040181c0384030b44440e00b423884ac0d0500424207401041418410700644243c40e5a03540083c041030031000203038115945844080f80005028420a5441401a0300b5462102e13002405988401c4040c00d00804100300007002c030f4180740c001c0151084161858080b110300340c4e02d03069a900424002c0c8a4082c0860707405800f140c07030030384615003292640c44075040840e010500e6800c018440c0300507100c000c24181d00304004804144214001d22650310094058080c042440b000f0a00301004580d01c041c0200440c3d03604c1002070306081c400b00441e040f52030420388034035440000a0900c80d1240c50765000640c00070001042080210107082101c40380480c01c064040e1488503541c03100c103000c01007941500704021140c460301d0254040d03011180104070315410143c4600750600681c0c42800513402144200080200b145080d81c4801018071281d006001c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 478243660 1250 478242410 478242461
    0xf01090510090314031017010c1d040f090609020a0b0a050702041109030d03060f060302070b0f0a06030803040609170c06130212250e010e07050d02190f0201 69
    0x1200c1085a064012642c0c850080400303143c4152003030010b00304c00c0d00101c0d41e2410020a1418203881901c1161841a010001d41c84550300604c5094402103c1e0349400c10f4007130955010201d10003222801a0340a640c0b060301c1c0300d500c280743c420702040e00d00c1030100041d00c3c1405c1c010015514090f03800014a410b080164507c5a64490150341d0643e80c10b0381c0204844070b274810740384254081d4668280c5c0511034038400c1c0703500d03d5150b00040d040361000b1000010b000e0301d07204128160b21503154003801000100c2e0104003003020004501e40c1c4800600c0000415585941c0c80000aa0060b20251401a115000c00061240032424035040d25182c50b5100c0c500000343c00c40c00d4841390014039103c40f00403804400c00c00c1d501c80220300c80948070400160343c600300004002e00c01c40d014054002031180e0300600d0124661a240c01414142d83d03104582548682d00c41e0801c4a032944400301440c4016020311100100c80d00014080098031030360b0f2107907010381c02886030023170840303030000681c042c0807484000240 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 478244910 1250 478243660 478243663
    0xa0203190c090e10180b100b120910110406020601090506090c03060121060e06270907120602041809110d0606080a0f0b0f09101e060f080f010905 64
    0x50840b508260040355103c0041c008a0800c2c1c0381c0b06103103203018100b002041100d10403001401e00c883c41030070942c4d1980c58801c0c0300c4030494850f000d60028141c1c04c004103108070f00482d40d01607200c51448210760714000220001804e035a40c3c12090740c444c1700c0100f000d00c201d94040c0561030140c40307440010080c40c600400001d01c82c00e006081040682d00000100b0601d9108104010402c0e10500100580e0007400c04108000d107142d110381c41c28440100003040030b038a0001b00341e42010401c10408203d0383c0d00140d448840600148c102c5503148103e403c0001d1030303800d12100b0b0390703683d00801c801038031945041c0c130a12a910a40d0001880d040ca8141d00030700140d14808245e811a40c01d4402c140c8400640c03400200a103105c0c0c01000242c171414000c0303410030580b00461448030f8440c0c0d2041007a5116240815145441503a50300c000780c102d03c80c0d1905206580c4e0001d860a41c403081000c40041c1d01000c500100c0303081307410401d60040c080200b0f00c0145020010041c40341d5041000300000c1a01e62101c6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 478246160 1250 478244910 478244933
    0x60117030d02210103050d020f030309030304021203040801090303060e07030b010c20061201050117011d070519031d070501080103111f11010f0e0307030309030207170a020319 77
    0x10840c1da001c01c400001142c00341183d80c50440c00380f0050740d1540c5034280700ba40c1f202a8604000148501050b0004001c1c011099a01508a40d4029801e5444580c00c02070400011402024144020321002420340804d0103011140d6010b504c0c0004c020341000300c0402000740c01031481d0245070820203da40b082e41d0128041d03c10940004560b64000b45503240040c02d94030305998187d001c2000304280c01e05075107209083e4100d903070903229010048941401e207017240c0024032546c2315845002c02c0404004c05801441c0da800707981d51420352b180c510011341d0803611340c01141ea00d00019541e01d030080380c0f440c40030415040c0c0496134002020054a408002000b0760014000100051025404405182c84260030424000c0c805450740e018043c03003840080002d03141a801da4440d41c2800c11001c80018240f051515040c00e400c0614940b00c01c50310700380e0103001400703411001c5110b10300f40011003815a401015400c8040c0b400b40481c04014010107241440080c3c410044c0c944513621900051115044d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 478247410 1250 478246160 478246177
    0xd0503071203060b09181513020d0b090606040e041b0806070e01031a010c1403300c0901260108030d0e0105101206020405090408070b0f0f0606090f060a05070506011703 74
    0x15245140e40780e4005100640202600d142c0264403900c081612904270340241c03031302012000081005101190420407401c0c001d44500760001c03000c100601c048142d0304d40320381d4001d000381307182003040c202102ca03c40390350000d03401031500d900980300703000301640e104030049154030003481d0501c80d82d0b20307810780301c4084c0441080280c144514600c4003420449000405504000c119040d00e0725202a000e01107041420303910b44070144840f52040da005c0d05a580e039228007401d4020300395401d0510180054803041c2c2c0c0c06048408440210308014003040e4081601ca028104d280d02071030301d945c030f0f000300e013803d0340c50584d003801199041504003c0e50f8030b4101104030859410034940c8401c0d51940c1002c80c020702c5141c10441c0c0094580c1c00308824006048000c1440511070a07503425280c5d200280d003d4900401e03244804a0816200803c0052038403a01808028100401070f070f201c440c10340005502544844a26000314a000c40d204061140a101082c010000c2c0110344220224000c403103030b141d1040440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 478248660 1250 478247410 478247449
    0x40803061e0d0b090d0f08061c060614040b0a1212050f041412010b09041403040504050114090610020c0409060609020d0b030106120c12020d0503071203060b09 70
    0x100c0c024034500640d00c01071085070262010450b240e59060000c0d031110300710380c032403e588030380340110b01003d10440c50858101040e81e40d20005888040810400c1022058184d401141600554021480500c621802401d00c0c9100c540c500c5c1e4880140410384042e01030840c0302e41a01c4104010305646a41c0c140c1105901550114004200150035200b0b0b00844130003107510540400d010640f511181d003441180002220100710300402003841500744c4242d40852500200144007040c0040c4440c1c050001d600c020b40146c0303041c6a2228042411070f0000da024000c0848410000d01060800c41d00503900804142c910f0b5490b084a0000a580c4150403100a80116654406081440403542c880750291185100540d5100306010801d409444002035482c4217518144c400107610342508440b0403190391282110020740c0c588290105041005e00c41641c008400301c40400000d20140000e140c154890000309000c012000402030403104035400c03014000c1c80401201c540741d5191090b400d4000d4040e02d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 478249910 1250 478248660 478248679
    0x5010609030c05270a0608150c0d0c1e03091104090804031502070b0103031e0203040f090e03040e040c03060b2b170c0109050606060a140d0908040312030507030504080306 75
    0x1648254800d030708131984040e0214806103c52401d00c2d4221404441905046401d00301c2c1c128103500c0004000e481241c03512008015041c1907003490382141e4001001c509048054106070200854540c0304240c2500c006940c40c440d500c10444401c280d140c140e20240ea080084a600c5e54030103100b03108901010b000800002c241c101a14042e40484251582c0010840c52075607491401402d501c0c030200d140354440420a107103004c0c20348004141c0341290682e00d103484410b0b02d4055980020003038504046100c0c04100030115107154540e0b100d6014a1080364074000281c6541840c2d02100c05040b626407151241e80204140203292008401140e5411010010b449584c2d02c0c0c07100c108080b614011128003000304860040310b00640c003602c0300900034002e556040e52000100039451141001d000e000c206415400300b901c88951026002d0b543d5214000281510107450301c8019400c00d5000b100c100c0801c000e041ca24642c18001d154006105040921203402c00d642c480405001c01841140940201d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 478251160 1250 478249910 478249939
    0xe0304140d0c090204030f050c19120f0606080705130606080609090316050319030504020607060914162111041e020c01090c060801230d1b0302010305010609030c05 72
    0xa403050b030024488100f0456450f40c0c1c03031070030386883c01d12920b0554540c081c42c41904d440d800c0c0400000955005000300014507820020010b0030709011001c161100c50800080b00c000814504c940d1000e0300f44d580041c0052450402000111200300740074446a074100320f420005103411014564010004813074071075084d962034229501d14010844101c04003280ca5201c030082c0840440201a0300c01d00d04081170038103824140a5042da44180d80094100700e0820405000c6401903103c02800d510841c0b085420450b8004400c0c80c200406800304400c0080722001c04c040742c0d00d0005040c04144450880a80444646510070810450072803e07004e180c40ba04401d0f00101d01024116071544440c40464413100003030078490007048840000c17603e9181c100ca000c6200e5001d0701c1c00034100e030071321148c00c55031103c1c10200708170f4260502003050700f14110000520018100c01d90190108905600c02ca9101c1c0c0341d80001019941c06a002a09000a1440901c0400c240c160302105441e0285c0303100e604030301c05 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 478252410 1250 478251160 478251173
    0xe01081803220b0a091202010504050a080309090f0c030403030b0a0f090605120a0b191b020a0506100b040b09060702040509030c0606101e0e0406080d02010e0304140d 73
    0xc5030300322149400002000344440c2000c202c030018202c41100180350071030b11000e440b442403041d07058401c0804d00300c400800880c07032100c121601e002d10600d00107042c5903032030000c00c01c00761040c3c01002290300003083c46038950500d103041c41d1b405095112359111301d0811038055421488040c001a0816031605115100c5450341c280f9a001014010944026156101000c000810090284502c100000b40845030006000903411046039000207000d00750340c81e60035404400c0840d0079000e50f070072501c2d0700b0320f290b01403c145c004200c400036940107481740c52100e162490504000500003850440300303e070f0a0080c464a10181c3d419589540e244594407000040065180d000d20080250b0090601041284c02280840138255050240c1300b206c034551681400c0028007520700f42440001142803459010b00390800c140d040914025081090041009001150540300c0c150040829a40801246150280d09114800d42d43c000d0002660078103040000020b810800040f82078482e4100c14010000d1000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 478253660 1250 478252410 478252441
    0x1502010603050615190302090601080907050307030f121106010b0d021b010605100206070c060c0c0204290d02061b071707061d030604060c03230117030a0e0108 70
    0x2c104080310420700c1d00c039440b81c5120307590409040c0a240b208841041203400322904109903039005140c1500303030750760b04011101c01030020301c4080c15100c0c00d14002044d84040c040640614080e0b24070800c03441c414207100840d40040e0041d4030400030304202035084801c010032001d041d203118040c242da403241110070b0030f0302034013580d40300c080b0410034126814008141540400c0c215202a164102c91654141d8240d8540c1400c0b514000854485440300c030000b000c0341e00046070001f040c18144103900581d004641140e0b80f0900d82e011005000c00e651000c2c4e4440851401000d00442e1462404040395020035442d00403101d00ea2090288030031010544402846103101070400c0c90090200140840c0c412940d503403481c4140d2020929030705d10303041400340c214440e8800c080701600803e03554075280d0ba240014041c41d0741d08010965105814422401601601050700107500d200c040d955041080c9071076131a000a403082001e82c801c104075514250844a4911440f06c2407c1022041e175402c15020809030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 478254910 1250 478253660 478253663
    0x15030613051503160e0106080c0403110d08030403081009021809130803070f0306090b030c300f0606270c0906030c0a030f02181c05011e0c02070f1502010603 69
    0x11302080c1c40c4101d4520061035045400b4143c40c0300c82666a603009503484802510306600c4200c0420080c030103ea020081e1142c40e1402038000d840d07200e00c949031804141c0056804400041007070003404190540c00400501800e00390500714036150b00811240c3c6181c890007072884c0640b10340303000036135100f808085d4101000c2c5c00c1010f450f0f80b4900048020300e80d8150f542d62402080c03a01c0004204c0c00c5035881a4102010050014407181028000300602d1034000c1c01c4d1a855490203041108200d00321050784031038100c0c018020140400c40141a90615400030400c0d4042e0b010080f000c42e40d103030400740640044600101c055041c2d240c00c1c1c440c031300364450604201d80181001050003a03034003210b001440008443d5804110761085051404182d02c0340c284100c228400c074000101440c40d04503000c5009800e41d89401070815046c0c2c2d40c0300d095414600d90030318440350a14480b82d92031080e01483d001e10540d071001d80f0202d400c1640e1170290107440c2c02003010b4000e1108514444078000d600420146 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 478256160 1250 478254910 478254913
    0xc0301020a020303180a02010e01050c0f01020406050409180b0f040f02030d09051009060203040611010f0f0e1b030d0807020f1c02190812040c120303060515030613051503 75
    0x450303080c103020356079030701c243c4141761060000a030307129824038041543c15080758143e503013030000280340b001100c6c260000784007200300c0d01800f840103a644c0001d100900081402e921096181c500c0e00da00f0004031042614040c10703035481e210110000400310f050840d4003402980d1038190949071400c01c1541c0d0740390204002d40521410f0007640300c95401422801c1200c104680c107441c0c1c1200c3d008d048905500744d00c5000301690051005010440c0103000d4403002e01205400011101910041c101c150b400303140c0c0f180c049075941d00721400641c2c000c6c0111518501c10040c48000c0003c84004203540d061000b000d882005200408111440e10902c9070511624800381101c1c80ca0407030300007034887e4000c261408800340c4200049980308614840080c40c046801c0130311241011149038407030f00c8000004100320b403041881c007000f107104011241844095030181e500021500e08041c2400100e20f9024074003d49003000340704024455490280350b551150f4120400f054540314104484c0300c004000c4c1c1d08903810f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 478257410 1250 478256160 478256167
    0xa0c081005060c1c0341060d0f0606060e030f0712030c1b050901051503150d0506150301050a140a0b01050c01110c061f031b0f090207050d020f070e090c030102 70
    0x40c3c17507258000c40a494138203201a409120b03c10000b0f1503c481c8050900d422691580300d80c501550488404c0d50f20900280000a41004035178239004041105401110f2041d541d9405008540d40444810040801507004000301e02c005070440da9174494911445034070003450b40a4a00f0940f003a00350702c00f06d503403060b20480c102418002c003018121181c02039600413034024000041078a407043e4150040e030f0203112a945151540c00c403403810301007203040d865003201000203290001403040143d14814400002d8481c20510702204040c05c0d00c5000c3d0a1003804c07420105504408400341c0031142d00100c1210000030440f56000041c3d0b0940640d0405501c06d500c0c141040002d660b03040e009061072071808003591016681c1c040c502e081e601d00300980810050107103009100150b01c251050b207058003d04441c5901c9a0313508000d0045500e503820001146070080b41d84070800500b08005912000680003800c0c0e0301400d4402c0b070fa41c41d0401d11030901d18216040100b01031010a101015100e203000c3d0003951b5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 478258660 1250 478257410 478257463
    0xb070f0812070509040506100c0204110702090c1308031218010609110c190819050f0304030903050c0301051522020403030509090c0c0a03031d01050f0a0c081005060c 73
    0x103d44c0003691118061400d2100107240c0b8505441401c610191540364a09081c1c079130b4003031100516a41d400c0005a030010400c00002d0303903036032090034410707444c03e418603954200781007d09d020b410842c1c1c0030708456401805070f0743c000c0448503009276204450394511201000d1025005000d090a0350211408500d440701c141c2030f08081c20f00805071100030004a50503000707510304c0f18040701507a45000d480e1000030300200c19081941ca42d185c42c40b074500c4c6000ca0030031a149901440e203a000340d07030031000300e414454100100032081c460600459400c030002c11070b174640b070140003441840048510344501d005400e40100b2103c5017a40440c03110003200110349079503c81c640504254008103085114004040004802e80c441c8000ca40030900940040e000030191564140c0140900d10741500c110050050340300003000c82480b4051040302a860842c1040c1041002001145c2074562070078108809003081000b0b1844018070a011503d003a41d0343c51782da1720125403150030601c000500e0500030001c0440c155 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 478259910 1250 478258660 478258667
    0x607061506180605090307030303050402130204080a03110a0b04171309020406020c06040f0905180109030e040b01020120030916060309120509011709031c0207110108010b070f081207 80
    0x404001020b0071220407549078101a51140035043e65281d044d4401d450500020744a0f400550308548060002c00030f031820411306005a0300280c01030844c0d540800032050078990302c2003007081c0014800300a80030542e5151036030f06009000800c050f12202d10118104003a043c190100d03945412011030021b41a6103824000010b5403151041900511858401d512589072240403102180c42503203045407031500d00b52003007018000041ca0003100048000a0562480b02030103941c220714801c0d0b980208203c2010100030417100ea480c5030b141103a15000941d08500390300700c005841c44035403549041d180d98841442c1884c10b05036415080360114441d100190550301500314420442c4120749040c000881d10600301c9140c00b80581090005e1817604204000c00032002c41c003900001048140c0e0315011501601080211200d0100c088856000402c007007030002006106060b64000d1824507220b5140c50801c581d103001c0c8881c060002003040c0d106000b00881c0000b2200e140300e00e02c0800700c0c1c40c9403c41c00074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 478261160 1250 478259910 478259927
    0x8030708030429041104201201090e07030b090a081204050709021c0f0902041b030e1507080a0603020d030c200303030a0c0908010f0e1603020f0607061506 68
    0x100e5541100f001500d001c64201a22680900450b503108012566152140304804440c5283c4503000f40d52800710310300d00740141c91310080340300640c10b03001c2d524810110401d001480c16071101600b2407900300c444403c90000324440003200d400000480341515000700d01800c08c00c0c111002404070b50300141c10200074003243c0d00c1c4c512a80c041e8054504490303440301d400081c0d202daa41802400c82108041540840c02a8072414a01414040025000e40c0c198042021203242055020f000002d21140030a4240d06025464004a10704041d00d0105680602c240c100780d80903054030180600580042c1030100705038862002940c00420900c6290f0060070f0103880c00c81c0c1c09800b5554a100140412003ca913042203155080e80040e000b1803460303130345200001c01007000407035220400411000019084100740200ca0b1111a003603400190008401e64052070401e007080c100b07401d00484001000561b543e40c1c0f5041c000801079078101e55802d07641c54140020103102074408040d0700c0e0400040784496225000c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 478262410 1250 478261160 478261163
    0x40b070c050901170606121e25030f080f0d02030708010e0a090b0106211a240909060d0204020a021024050d03030b0307031b0605030105010804060504020a080307080304 74
    0xc040590b2510426109001160119155980124046900c0e401c04804032868240c0707c506031940c6050500065440c14074140703204409030f1006046400849814250440190103100a0076000345540d80b240c407030160204018000e00c1e0042440d034031240c0c000b000c5504010030014115030b00e2810800c05011904280603400524000b1070000d003140004d4421001480c0d000301d0210100d07882c00f00c0843d005c50740d2000e160707121681d030004010646698000d5050f2210710b020158000c08410042c40081500e485141541c0400d03c61080c40341c1d1907084c216501401c0a4605100742d50f46c0c8070114001c2400083d000f50881d20002e80d0b8000c0e19030100d62400c030030182c007801703002440c11101800304501600c404422006100035082140303145c95081e04004d42d100341030124510310484000390400400b80c2c02642d42402134070105800b9040f007410070024215034100349086505001c0003d1030f0000040c001000c0d2542e600104080d59181d120310001000c54a0807030395550300900d0700100541040c1d90 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 478263660 1250 478262410 478262419
    0x70b040603110304050c12190f021f0f050f1902010b040b0a050609090a0906062c071b0f0b01091d0309060a0828090b070906020d03020f040b070c05 65
    0x11909495040c41c0200d82c0500d40080040460320000c0d07007000516000c0142a480030711a54480d1440e44005800d2300c0180c03400748042c00f001c01c8041c010301800e0f1440305007003e01c0c10301d0b81c4181c3c51155000820000d4004240c40d1a50300c46442086c9682c19100c1c14100c02111030403a81c610745884e03415001508640c0d0161014410000600140414807580d03001d80b5a01080034007880c10103050206c0a01e50203645070b400402c07100d0951310384408450a50f0400c1d80f400007500340b140070003644008110303940b0184084038041803030400c1c001810740a43d41221104002c402d00030209204004621100c000e13040500c417905941c0d81d0382160020104d04052040c1404108020f00020901100341d031110719002c0c1c662498040c592200703d0b20b480000f0414104c407000304148030035655031600c50080e030022000001071580d02070300b02120610701c020100780c2000b00500007481342d1640441c0070440136086080141e00c44510080340881030085400c08001945e000c00c1081c14031481d00c2482d000c5502c1078a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 478264910 1250 478263660 478263671
    0x1021e12030c25170706060b030408190c0203070311061b0607030b010903020906090405070e28092f03030304080a0801050a0e1311060c1b0105090102100c11070b040603 74
    0x18400d1440b40802c00900032001d00000d511301400c181000380703921031140703100003240e81c7c0301d0003c0101604103841c1036640c00e0010400e10401410603240c5294000a0b040098004860750300203940d988050000400c0d9003024010404951500c0c001d48560018003070b640181040200251581c480044500c01d001a080903039004d1554000d0b0b010748280c0e50081c10551965942c1018412000005401290284600c520000300c4500e43c094450098111107480000e050702007615181d40e00883c182d910400c0c2c07038400d4010002d40c924940705000c0007004a400300348030011894004080401400706c9d0580000000c000400803001c0c010007403011903480c0c98005980b04c0090040f85038003400f80c2c441d5408460007180b0500c900303410303c0914910429030800c3c07e14010f80480d625802030300d070303640c1280d101612008903c08642580c1031100801c2c82c10608100e660300000f955108000f802c1401d85a4507440884480d106400001e1485441002c860403141c0d01e40162041c1e900c03a20410300042c1c68503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 478266160 1250 478264910 478264957
    0x2060d05101502151f0806040326160203042d0609150e0a150e150a0c0b1f15030509030918060d2103140601021e12030c 53
    0x150345040000c500e43e8014110112074071007012803400c01a0205a842c1000c0e01c01110030440381c0080006040c2020240825080034034020700002c2000c10841d001e0002c0d80086106901020205681304940310700501e50200c100d03d041e802d501c500d0300840700202c6500301c2c15000c1403808420b0780051188205c603401181c1c1e1080111040c090310f0183e440c60800a2070149034551140c01c0b03a9001c180020200c0d20300541e22007018661180001c0c5040c089038481ca2001620b00d000800e54940d1220941451b00e09010340fa001001840001c1c4000c0400300d0002c0812103610041800c440301d5000c0c0701070040101d48440300070300c01d020544803020002c1c3c141030000320408408010382e02c0c4028060407090850007a0400f54503449001060150000344500c0c0720130104074420707142c0e00d0034500f0501c60391036001a20030080c00d54602200111070044900144090380c0d0f40019100c3c000d0032901070320216041d03112001030420810380c0d01090810800700c184450010020002d010013940005014007004a4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 478267410 1250 478266160 478266179
    0xf1406070308010e2d060414280209060703020618070f05060705030c0d0f0e1c02040902060d0905010b040c020a0f1407051203030f0f01080c0103020f0702060d0510 72
    0x31200014000354070080100481134000e80529084003605081d1481d10900070150200c540b071000c01080042c00001c140404c9003820311400301c450b204100b60300904c1c94582c44003550742c001d502c0c1d03035071060511030f8004000c2c1d200d6606840360814002c046942e1230f605810001e540c0d04050b0365001841c200a002144425000140042141c000045140328241b400c01007008030340000c0701c251403600040042c451000814091690440c40b01d80714030071110345088005242c035501400356402026484406c440400c4051403c4101ca541110040340854291000c20603500445aaa1001c10b00f0b050b01202003000c10341200503d040300b0340f0b00704100d2044003030484e60380a0011010f0640c224690121000c00c02c216a0500c04000b000d0440d5281980d9801051400410001e842c040e500701005000040040100c0c568228802d02004a203d5040101d420348500c0742000705e6051503800160000c03c2e40c81d1a00780d9031020307001015145c903140f400f8058006400100c1e100c04401c04410400b00b00d031000d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 478268660 1250 478267410 478267417
    0x201030e060709090504082a010e010606020a080a0e031603020f0105030f070c140f0f0f0a050d030f0b04050c0c01050601031112041109101a04061409040b0a0f1406 72
    0x482c0c2d43c50180d458038090702d40d0000c18028005030f592103020003840c00741c041c0400041d15019000880d003403c03505211007050842c0c001c441c0d00c80080c0d06005040004544c00912041d403185c0050f0f00950b03940f02c0000580c0d0960b210f44819425005070590300e002e03001031328140c000310b82c0240d4204507002d801d2801181c4038401202d540d03000d5003605c0d0100e000240328488820b80c0d54487c02158160182c1d4620061600b15400d0006106078003000055007441c406000c0d8014004039200180441c95081d51159156000010808200750341d54540003c02c881917000070718501000340003046a4241111000385607480050784500395030900012841551080c403e120300c05030903a203100c0c1028481280c3e41380603c0054020384880303040302006c098650303880011381d00414005101902c42c07071a000106503502041100b2200076401440100040c60300703d43d4280180303408000c9a0f82e105901c000240003070000c8281242c1000d4100c401082016200c1c064109403462080e07a54685054030b82001071510 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 478269910 1250 478268660 478268671
    0xa031403010303050412020a0b0301120c0f050a0b0d020d060f06080601020a020603150d0209070215070903051b060c100b0a091a0111150f0f0129031e040507030201030e06 75
    0x450405c01040041c20400a07505003902c01081010a2540d5814a144d560001e0b00031055440d19000201c04024500502e24000d04480154048503498440050f10b11a650f102d481d4907070100252400c0641d18a40c125221044a01383c2045295250f8400c505240d01d18055003020070380d04030100780d0560001400042803a4000c2c40c4514555034444900201b40c040d508031504007480980c0307400103a07500d4180500c80e54555000b8074003800c0300d9400c01d141643c06884031b405d001000c20b0500101c0c1c0040b42c500e09503440f440a410300da0000c000400d9142c85201450301d8035018281d00c030b17416041181c1021a81d00e600300c5803c20500c0d1590701620441d62001c2401140c00b0403441402903e50050100303001400c0007100352100810104040c90400d00300f191030101c0b20381010200248604901d4a65016102c9c08040c046000c0c281c1102c06504800d40718502400c0a0110025090400c511a81480d140c50075800020303905080c5407083e65070030305000482c0801d0400003c0c0c110207500150700d51240c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 478271160 1250 478269910 478269917
    0x30e03090a03030e010c0519020a210201030b0f0306041a0c0a020703170f040906050108150907140910031a040b0d060c09030c080a1a1b0f12090a031403010303 70
    0x1450b540e4182d4414180c0c0003140d060040780c111000120b00c2c1803003034801811030072260361092211403040002c45200760f0800c10190a480d81c0181c0d14002c1964038281c40c0d42d0a00340024440324050010300056104d0312803551501c0b0700d00c1000200201683d01c1e10340700800040b10005034456900d079410700d0049048280050b4041c0d081000802c0f5040f01c11410064503044041c58618001d01060081e44a40c0100402685403e4100081e580c403044c9607074812002064200503c14410000e158000040d02e00d20400c400384001e00110041e101c112000e150006218030308003495500c002d0064105481c030300c2218665400050381d035080034003400d0f001e890010011070b50154680e0382e605c01050750414080c00c0000460010000450300e460f070384040c0a40900034400d0303c05030310300704444403840840c5c001002e141405000c081e202882072000d001d074108803203d40368a200c020440d00350055116200203001c40d1824000303c941c000c2030040300180240d80c0c0351020700154405e50964802880001c000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 478272410 1250 478271160 478271179
    0x60c09092f0d0c05250201080109051503030a0e01020106050604050607080a230304060b1203090103090201050f0307030e071505090409150509161d06010813060e0c01030e0309 77
    0x4008030188044158022000e06040046040000d011902e1110f01980403410001d40c514070048200d001c802c800f607001c603171440c0700ea45a500082c08144180300b0b0209554132030f000300b20f20800c00d050b84450100040c04a80d04e03100340e036a0003048592603000050240d403811101184e641005011181a1a800340c0a28a800c4459542c40c06a0780400701450030031500316106010340c18a000d002d006022703448903890702c0e0304250828004071031111000038480e40961100b120507150200644180e90710034200052010303420300059034544a900703002d501804000041048032901940041c100100503012655125100c0c0d10b80012a0107524030540891018413140c003013464260041d59050b40301d07101d00c002d4524000c00c650284c0d442600d41c0481a041b002003c00480c80481211000300003000c80c42c034003544060030041c00300101400301410031a504001a0f0b07511421070b4101c1040c0d512403010040b0741c3c442210b6a499420f480c40840c0040d003030080720b805500c1d001040d03820501004201070035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 478273660 1250 478272410 478272461
    0x50c0a0f0207030506040c03060e160e060a0b031806010510090e0c04030b070e0f040b090408071103030a020309040b040203011409070306090c0e18220204090f060c0909 74
    0x8480206405020861092802c0480020002d01c8118000d0b440f601d45960414251f10742982601d400c0d840c03c042580c00284001203101d00d00340002d0880707441503007070b012540302c0c0f10104000340d030300d0342166011400020600c01d12100c07241d90018441e01040503946140d072600c0810080c0c0c094000008000340382c001c0c3c00c2c04074401c0c84401980040d603c3d0b5240707207056a01c0d42c40150a9000b02c1c1d0220100c2d003d44c075903800c0d909140c0350040011000310703010407001c800e0400207640594082c0020300401008100130081166081200b080e066000302280d8031041c012100039a00d51110710f41d03d0044d41030510222090916009417411b07a4208003d030b101c90070000c01403100c2110700800480405450b00300c002103043c00d03449225680980307030380c3d01080c0c1c030028424000110002c20944d5203d40c1040e0030845c401c92100000403140941490050b80600c440c000540648020800039103000e485134010740410000751700c00d044081583d04c5890304136503181201c0040320704902030041d4010141d0000f10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 478274910 1250 478273660 478273667
    0x9010b0423042705061005130b0607020d1b0914040602072d03090f08030406231201031b08100902190e040c0f0f12020d02030d050d0c03050c0a 63
    0x91241c4400342000071489418080c1030415188110f03222800d0044810401c1485401d101042c1c0c044640068402d8140c608001f00c1c9181c2ca05d81610414a42d407130580c0300882c0d41c0c0c0307002c452010340c0003440c1c0f03e8180c3c21410110382449010940340110b0a07216400214904d140c040d41e10074403140142042d07250380d9a119038004c1c1d4800b0340b0480340208100716000048218480c6206001140640141c60140030b02e409400c141da1900904102c1910000403c0034880c000125000d407021494400c1c0348844d600c0320791400d08030003285010000404181c4000d0201030b000c80a0403a40960a0303c010759a24039003564002c2e407140500c4036a42c1011120f0643d4800380c0e000b07440c02601c05408103100c004141002003141c0403030342084a03140300c171005200c10b00602c48114805408c503a0864000a450309440d004101824492000001000c03030020080d0f40d01d050600202d0342d006001c1d504941901c10b0700619075402804101c0f00d061138407445040584c030a00c9424450208200fa00c4d18003407110b003043c1c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 478276160 1250 478274910 478274969
    0x1106040303063f031803110a05060f0301121b06021f1b030c0e0603010e0915090d0e0105120a09120203090a1a070210170a0c05030a05070e04021809010b04 68
    0x10b40602c00400c004204110308402524006e5000b103000c030700083d021008204203494190f00c480c0c452981032045401c6003d04004a1381180c0c0000a1041816402d00e0141d11156016524160042444e02c001602c1a004504504420052400204500202c840c818200c81c0700c0001c0c5020100d07440b0000072038074080e80c054461041c4906010400e42d100d0710010780d075a44241c1051100200b9a41400140002000040805541d07984585aa8034020315042c0c0d69520494802041000f0801800c3d00359004504172219405d14880102c110310300018030310302a01095101706c4114070808000700c0700382d1010058038102c8000403c0c0390a500d00d401c0e1007034501d0407606484400d015007000b8920040e0b6400c52900d0b8040c00540712694a940300c14117081100c0c1004050070106400e1071144080c5035803000c102d9030300c40080b0b40700142a80b12580111a80040c4c26030413a0030a20020308a015542e00c003103200301c000d408903081203c40c4e0300d46889070324500845c41454070340d0f0170f0080317064999440034180 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 478277410 1250 478276160 478276163
    0xb030703110c010f0603052e02090d06050403020c180714091507030804110402072406090510030c080f190609051506040b012307031106040303063f 65
    0x2030b003030411082485084402607412241100d0b502c0c10100108941800b004045041c0454400b0305002c4040b5186a0030407000e5450240c541c2c00216800c41d96501c2c0d11020036241c22060421442c0b07414540a0340d0b4810300b80d0f20758407a40081c1030044400b040c05411600c101c1003030b503808031050342d259503866141e00500f07101c81d807010648501160041c0da90004d0f14205001c0ea454104600302420010035000106541c60b0040d0300420580010555540300c0300d901e080840d035004d42d81d403001e01c5202e004141582007419854200070510500c49558070100c0280c9015131818442681c0c0ca900c85a82e03480d65540305001600302c800a41d0580035031103160170311580148004a490403141c1e079240d08008800350046502c010b810305115050906108a9901403003e007440640425401c201c5a00c060030302100c107801c58400100c006c2098440c080302518108208125034290600c3d28000c3c0142c1554022840a44144098004011852019102200c0855018002100381c810510070340c41e108400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 478278660 1250 478277410 478277441
    0xc0510020d0c170606161a0703050709140f06070303093e09011403070308030106020d09080f2505060d0203041406040305161a040f0203010606020307201807020a0201020c0603010b030703 82
    0x1a41040c07107c404c1105803150055660015052a044001030b041c8146c40c1c01c50540c007210444206205d4544c00c5006420a900b100c603151550030524044001d0800800000e2100c1d0241a4412000c0380c2214032180300c0507601d0307103000700603004050702807101051101142e1120402d0010071a10301d034030030766030554200581039403d081d45a80b61081c05600c00c1e440400140e000b280b8081581e540909500c0c0a04002c8000e080ca0150790901a6034444410741030754500d81c0d0031400340c0714101400d8201001020064a0240c480280030394131002504100c4041c0c8420800010247e0800804a8424800c640c941c03241814000011514080359054890071034210204665458800141000039885280b054454002841c680e00c181825510325500c030b9070642d4005c0c007000780010315005114400e07400203d804070b007809042000460314081d6500910303a0a04450502003c603902040403005a4000e808036007411a0840610849100901c201c0441310000c2c03001c1510603100303800410b18203400c601d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 478279910 1250 478278660 478278683
    0x7060f0b09011509150503060f0a0504091104110a080c0304150e0303100b090a090f2003090c03030403030f0804020d0219030309090605010903030c0510020d0c17060616 74
    0x1404a00144800c0e044550707456140c0c3c5440d01500c0e400702c048800b600321038468089450341c0c594041c081c1d010242075244202c80004445540c2c0c0c80c1e400c9408000c16000b042880000aa801d0828055030004c41950051b810000c0d078000e000d110328211540072130650b4a01020381c1d038154061030070b070700080c00480c4c840c3ca028440041c6200e8902079000741c80c424601841e07032800c0000c80e00011003803c0d072215001840c14410403003103680346800601290410003002c00c3c0300132030101c2c2c18005e00d2400300802c4513035010102c0580c1d110000300174500c0b55500008443c11030b04032108150b901c1c01140300050001c0e02840d10444003e10030440160020300c05407101203081d20b1a0300051060403000307010704140059100070824540e0000047e03009101d414001c111140c20715000a105008500028050040d081c040c001000800c20004001d1480744004644480382003204402a2004407000340014000200f480440740d5a40c08603800f801c0014411840e1441d140c0200302c510103e000d0036210811030381c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 478281160 1250 478279910 478279931
    0x3080a0906050c0a11060601090b0703020708030c03090a120b0703022206110c01030e0c06070c09020c0705090106050a081504060b030f0414070305030a0e150d0f0605040e0307060f 79
    0x280100c40c060403c03100460b88840320280010300d00344804615500a602200a100050341c11868060540c1d030802161036650006013000da190160a41c4460410301c80018140e51b44140880585a100403c41c0c000c2411580c4e2000c07981082e1403070380003030b008600c44404500040d00139070081c01800b48402c1c10000303000600000f1a88500305500c0741c80850026554011402002d000c02015003100b401d04002600911103900c1e40c800d1005c0c00c590041d04001000d00031b03c01020400e20042c401158255aa00700103202d51362150180c0c414640100c15120011034102e000e14203a4604a105903030b6144640d80c0d880c50701900d036039941c6034150060764681021070b81848000055201d907802d100000300a003000c3c43c1607007610009440d103036140d421208050002480100449500c503c6600e0f1940341d9810b0100007900e04400c1c1851020012400a6489401002c58120140034220920208021503441e030074001034900f9001c4500450b0810800500024182d50150042200c03000000409040780c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 478282410 1250 478281160 478281173
    0x3030310060c0c080f01092a03140307121106011a0703030b060904020703031d0706080c090114160c0603020307020c0402180405131202010b01051204020112021b06130b0403080a09 79
    0x405d048940d46030b1304194180003081548103508070340340040745000000301107065000029400700804900503045030000700841003050b140d0150308560258185440ca08000e0098099010b00800c18041c00c0000514103008401c00e0710f0055241ca4460f2510b440e81e60124010212181039550001c0140f00c1d580d460b440d0351018205191080d14001000c10308a82184151007100101c9209030344516410301c81103500c038002907002a034645445840300e180d40016580e843d00274000c1001120045441c0305001e00048040c8895402900c0c04810700c0d0b15141c0c100c0c2a84012203540015900c40a000002d9041a1b0b0050440500b442c000300180440d40300020241e0300300780c1c3d03c003403115040c0b42c48409001d081403c00f501440e00740001c101c03070012480003800900800d40104401700701c480c0080c0540e4041c000b400780c0e00d110a00c2c210760b2217210f16590f003401c84d600f0b84020414860702c1c000035013aa41d003103400030800360000301c0400980d44565080780e00100041c01444103584401c41100003d62 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 478283660 1250 478282410 478282423
    0x120c0801050702072d0e04050a170a03051003320a0609030206010e060109230d03031b0203040b0f0f0403080c070306230703050a02070c0311010e03030310060c0c08 72
    0xb60707010341a4180381800d0051082000c1d000507001381110741115041d0903460144400b164a0528401141e90315401c1c030340e01303050000d0310181420340c0017150440718110303ca008204601c01918100f00c240c4801c0c3d85c804070f203c154000180b072a0090b0300090341001034040801445a40d003109060300e200000300b090305003e1080340448131592140e089000b00358040c04814003603c13001d80780030902d00d02071000801c0000144501501c098007602c2c0800340c1e4407041c032240d01010000d0803004002c0350900e4010003c100401000507004030748100520224400700480f0200d8903041d035081e04280d80c0c030a0903942648049000034210004210000000e82514040e000e00d0400c18040c249061543c14510262620b04d1091514958504a100c550300358500d03406420140528000626035114003061009107d01007016000c0f441102c03000042000741000301440c10400c1c1c2e11170500c407031404241a542d01050b90710324151004000107014007442180d104220324001c2d07080308000b41d50750642d1801e100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 478284910 1250 478283660 478283671
    0x15211503011a150309061513020a12050a020426010b0a092412060911130509100c020601060c0c050d061a1f0e06121e070315120c080105 60
    0x1e040b03200c03a980c14034160588001800e074842c4024036510380100702d180c869800820752240044408210041910b230700080010a201d02042195541d10107071b80503140c0c04403032403128041c505010000352040c8980c020340e001c8602400c251040749800106520300e1040115026040c0d43d6a501c03c0b840c15030340d404550009201e16540041d52002e200714040f03801c401980c0d48143d00181103000c000d100e440e524000d41d0160080000a1440640e1411605c03a20103401141d0740401d4841c1000380700031155100501270400041129a9020403500d100240c075058165200960000300041200601030780030025210701c54420505210317250f1000030103245005409a580b00d603034000395400c09031600460b15006404840b80c840c082c3d00307084221106d190704481001000507644403a9000c1d280d030000e85002c03124445030040030385410099220008156050410014a00c5004c107405c18024815441028a40c030421400035080c514403400149103940100ea9540c5007442c0011002007c0c407825010302e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 478286160 1250 478284910 478284941
    0x309040e03090418060f060e0703020a0315080102180409030e0d03020703050114060306090606030d0e0f0406030f02092a030c0705070305011b080903030105010c050307060f09021521150301 83
    0x415908103841180c01d0003200c1c4202914005d410b100c0300d080c08c200294041c1c12842c0c056910b42c0317144400c034090b2001401c002a034045002c00412011419005091040003540c1007001e415511340400065a184420280114645200400103400c3c40031600801c90b0080c01140c51715a13503a0303101d60840351fa030a102c075005498102801418601484403076040002d8400414031805c0840c0000d480c0c400b507150070802e000c501d03541040c65454440075018503500c020f00801100340d40f424203020060441c0030880c03007850000c0004035070b00c611018150a040c44410209ca4410410981e03100f13552001d002c0e4103008c80180310b00d200151381004010060f40c860800400d503a40080300c0340340c0c540d10f5203416505001704041000130070000002903d044030b40929050030960801d082c114254810485c0c05001981460005c82e505103094000718211442514800403025010801d48954055001e00501001f0440100c1c15581c0c00d8805140d0484408180c45204034030f17180002e401c6603020100100309 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 478287410 1250 478286160 478286201
    0x40b0d0515030a020f0618090a090c0f0303090504020f042409090c0518120717100903051207030f0c0206011e0e010b07211d01110309040e030904 64
    0x2038121601a01035600750941c010401d01150354005500b500e04170028600800300428020b15803c6840b51200c0001400f6100e02d401e030402041800203400440740549042c1410a00040c110541078042000c880c0c241d51100c550702d0500c420480a944407d0f0383c038580c19018003000c26030b0044050018003003600130074400307007030442880d01030a01d00d0707190b128003d45403420384079510050b0024203c0b003041c04000c0b007031800c034401c4e0303000034515201e5080f45120500c20354401113000e2030001d52854140410b0400c407122082c1b040c103604266818080018001a014002c0c155407141d890a4150000c40c2030501280d10410007070381b0000c560300344543c4801a441200100325500c00302d02100b0381d00e20707280c4d0b483d0891400c00782041c0c40b072401031141c10803050000501005100646805000d0801c62801180b5110501c901c0140217403200c0d407103500807001c00108080503600a4031600f080d00d1404001e5810403000780c0400c401080360581c1c1c0a041d000230040e401c00c50343c40b440359804408440b000c010f072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 478288660 1250 478287410 478287421
    0x2030f1b06160507080903010e01020a181e0e0a0e1b04060e0408040e090c03030703200d0207090c02030912060f090102030402060706090204090c03050c01031116030311040b0d05 78
    0x40c0030406000c0c2d220b03503900040c803221410350002c1210340945c0c009801580d078211103c0070078010401d4012400040d440403038134803500e545c0181c441108003201364424031495260000c0c103500840d40040451820903070310080100070f2403030300c6072548840d40c003000258800d80030700500d0038000c082d051000390802040d030614483c40c01c0d02c00d00024000c1c804014900e4039040c0d680202902c114000c500c40f9803000000240c81078010051031400400180c02d03a5101c2407645809064132012560200c610085911610340711100019000c04030318440d8000c0c001d0f1450024208010140c6818050450104014104042c0c548010042040a00d10014241da00d03000d850b42060f410040c1c61010264010014000513075128000c2c1d0724100c3d0444400940b0758860304c00a40113000441001f0243d4400c00000410b020700820003044420081c1c03000c0c00000c08072560400a0302c1244a2681c181000c0002400401e03c241c0c410307007224640014251a00703483e410550b80320380103128014000d42d01c8008024 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 478289910 1250 478288660 478288663
    0x15040c08070603050c090906150705150c03090a030e0604030803010e151e0418061401090507180311010c1e030e09090a030822061a010f0f080702030f1b 67
    0x40090000c0c0c41c0421135800c3c8024414400e1280103030b25845007070424045066a950313001800540440c01c1c5450340d95410360b02c1c1040c0c0322007400080d01c01c40b03030758240041d010140035400c607446152100064215486140c0d0142d0340b0030950020960040ca041c0b00100c009064a0010741c0602049107140798649000d44940e42485d090300c028900444041050000300c181c0090820600001240c000c503407241624022180c0309121030001d05481d09203a800c00f01d40c004c1d04070040c180e80c20068184115603880c2e40659825000b000c090400d228040800c01c049840c00c0340e0151603220503d0a0202040c40341c55441030034091020301607414180b48201400c050b00006016519201a5100400303898403840d82d503100d0858042c05030a1202c00000208088001c00c590400c41d07018003103c0e002c01c08070303040c82c00061182c0600d11703030040b100c07000701402c56001d0004140c2094082c0da411081500c0314a0440d90700b4400340142003544820f2081c800c110b900c00002c2e00c9031a54441008200918080196 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 478291160 1250 478289910 478289923
    0xd15110c01060b0415080a180b0f071803110f0406030c0e06041a0d11042309060603060103020d110d0f1203140a1505061819060f1115040c08 62
    0xb198051002c210800681720003d0042022444070b0400143d180d541d03100074409000d4040700a051043c84034020303410401d001c004180a50350b0403e65001c0c594484105075160400c10460815004100c076041002900c802e100c90464180500007011140800b03011800b95003040e0003ca0740c101d5540c4052120180e03600c030f0070764003610888060100ca010700740c4820901a0301c2c030500740200b9a502c80d64091045400000c146c090740500308210b50340c0c0c1007041c503020a040400321041000503e010841e080c40004403c0c2c0a080010050130303082c1d285a0801860b601201c02c221a400d40c500030340d480e59039a007412800004e00a40c031007011907010345008009071000c081200107041c502400c80402100c175656440d4081815480000c005c100741c11451141341c0300fa03102e41c3d4414800200c5c41e0088403401070703500300740000352804002a040c3c409011720a10441c06010009a0701c194070785141d034030844a01c1841781180042c4c41c40c040d2540415840130300c0c03c0390290303401180fa0500b000000b2041151 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 478292410 1250 478291160 478291169
    0x60320030d0c030e0d050f070906050f030127021216170307110f030312180708120306040207080f07140708151803040806010906230f0d15110c0106 65
    0x10300c0d03903402d6940c018000e19803134041a4021082e4040c4502044010800032000f405030350100d0b94100d95420400001d000c490107103501541045816143c0c5003014001c41c80550461610b1004103c09080d00042c0c0458072803069034004105e2401351010384c006d0240c546109404d203490030015003400718010107042984109400d651003088030002203060180301503284002240d014001601c4140040c0c6103000780d80c00790750640070801c240501300c880d12054104292401c2e0603a41c1d010b07170752280f9036116200345c2c4010100d50001c02c00182280340641c0107102c003c1c4288281810b1002180e0104415004a201280d180364411007991034444208162002460303420000c3c196000e00703c0206040e0000642a00c08040203400000d10509044c001c0d01c2c085c00d0301c903049412039a910721030040074040d20300c20403802201011402460400204c0000c0c801a809800c002c10b4500d000c5c14001481902002961026194030940d0100c0000380181504044140001611604808586421200e15a00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 478293660 1250 478292410 478292417
    0x103230411210f0c0f03100c1202040f05090907030b0a0903021221010b032205030910080103030327030f0c02060a030b1c050606271003030215070909090303060320030d 74
    0x4002d0400c6d9000241d4285070b03422000c01140101540f5000c0d103100d03801941c1080b11078000302d008514094158690303004c44800300d41c501801c0e1225031980e0f80390003150001034801801040042c10130325a54010754440b0f44a0300c116403a20403a054045ca46403c02c010789000844ca1140d046480c070a0029070601400150824030320b14180040c019807071847c3c441000080810030341c4c0d600c0911070701b40305446aa0308041c04181c80c9d0820004001d000550900040340440e1821808102007070260141140c841103010080100400a890541d550304030300203d001001100f030450760058030303103c001e80040f5400c0e803408515201c0202c100041e106c4452a40c1880201c0c03911640040b0b0030000354a90840c1c020740c0d0030402e11401643d0010000358081c8006183d43e244800e2060421460120301c040303a00030390903261201c1900041140100c019100c100014510310002c2c002407130300d030344007208440c420b060005000d81e481d070721072000d041103030000c0b00082c0d181410070402d400c00b400960116062881c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 478294910 1250 478293660 478293679
    0x20106050303180d0b0103030302070308130f480e0f06060c03041205030d14040b01050103020c010b090c04080601060f080f1302060d09020103230411210f0c 69
    0xd010a80d203008030200c14070070100003160b86010303446952410203982d030050b42d1010b19684a040184c003a510000085001404130000100c4491040c900c482e8869030200710b070004030b62a610341c0d000c0b9000f01c04101c003180c41c221000c40c07041c40d40540303071091011881c4003149007054002c0300100120080e910146214006008000c4214140845030760b02c400200c4589481c0c00100b52918a103004940080d143ca0350249d0314113040c480008041d0a24030f404840c28042130580340002802c0320310540300281503800c444010302041d800b80d00a05184c000080000450015110019803800350aa405591928001401303000c009030620510303002d0f04681c00e06034041e084618005282e9900241a40e00844000d070101d603020202c0742c03100c0c0d242c0342c0003001241c4075900008008010b08501001300c2c0403c1c50100002c0c2d49400504038041c1002c0c0d03858501c0310f40c0c2e4460722444034826013a403045604c0500e00000d10800900b6803054250254a0002070486c070380e200705054509200c41016030b01c01c4009a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 478296160 1250 478294910 478294919
    0xb1e01080106030e070b0711180105040605040216060b03030c0114010302040c02010b010c060c030b0a1805070905010e0d051204030506040302061317071112012003161803060f0e0d020106 82
    0x103031740d90440e07400d400c0302983c40405080c402c3d52064858030860b44000240884d003619407000650381e040c1c94040b61300308180760342c940c104802c0344180c07400c141601c80d418086501080030f6500072604880060141da180445400013103084407d86030070703404442e01840041c029800d141c8a41c03064000c482c00200501c48425002030001c545142c4002c181030b80300c881e0f003014903201e80c00903030840c6c0000d40034100c555211408100503803041040c810003d4075140c0043c16443c13094440e40d007110b4041e101c02548070f03001c000380500e81806a03000e4505118482e1403580c80030110004000850080000e0701c264281482c0080c10044042d2039021a80d82080e0400040340f0074160284442a84072041d40d41ca940754907240d0829024602c0d425440034180f68442c142a0341900703d06001c0100795032144034210406103041c1940030954100c0340f0300300900122a000e0f4011140d49c142c01c1044010640001d0b40d0b9502c01080e030b03901c0c0c404824255101c41e4003010340c00007005445448915030000f44006402d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 478297410 1250 478296160 478296163
    0x304030f0b041a0c0315030706200304030b0f1f0608060904051509160f18020f0c010e030409060b070302282a0506190507060b1e01080106030e 63
    0x8624080c10200440d00410b04200103008590802442c40d00c0c010703003a2901148010080e0012545424406104500d8040b280b0b0040ba82005980c0c85440d540c1400603d011641c0005209034090715080c40104408000f180f0b0281e00305100302008186a03006103020006020781c200e03a80c128009108160400380130050704181c2e0070340d001c1426030320f000c80341c0c1c2d80d8241545444c01000c20248030005c21001e20030004000304c0c0c4a001c0424162045441690710134800e1a010200c1c030510180e900160340e00703c0d0b1020990014840341c4a5070f51401c0c03c140c8500d481c0ca084942c52001c0042036800000d0400c00f5159034041d103801030402c1601d42c0e042120030f072800780d110505204c40740108900c0394000703500d10f100d0311034008040e5040050f04104041a954100d00c094075483c1a070600440003400080c185000011a0311225072300c061110001007140040c0c40c150025041202c24a0b29101c000c0016203c250807403550840c00d0134444442045000050140c02040e0041d4042500f02455102e80c02c2c2c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 478298660 1250 478297410 478297433
    0xf030304030c1202060d0e0a061526070f06050c0c0a05060a030525031d060408191b05150c03070c0b1003060203040302030c010e07050a060f0e060301091d030403 71
    0x4103c032a0954610364800a0310603c920400000010701d010094481356400181d03440c81d0a208040402c8904400a5506c089001c80d02c100d0442091000c0444012104240f2107021060b0820844007021307103c588102e04403034207400c4000005c00200758002059010001004920425501040744a0030b040c080742c02031182e843c402e418141c03140c011440049a091070201e00c10083d0303825075001480400014050505880e00340000020f0000c40703101c80c500400d41c24001c66010003600e24040c0e0051400e454400003c03071401c00e10140c650400189203a9100c2510401d20410160103008000f0000c81c0464030003070688460407000784108884540c0081701b445e2529000000a503450f03482030b00c0841052100c1d0002044a4004401d0004141d00000541060000d07103000788038443c03111460b503a80e64610b00c916540050f0124040050b14080ca0f40c0007035142051804c0f00644094802080d050740c4281d1204104696450004060281c104c03c0111081a402c001d107151034510b0310b40036054003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 478299910 1250 478298660 478298669
    0xc04110703030b0f0a15030506032b09120c080607080c030a021b150402100c020a060f030f140615070b150d0c09051e0403090b0d06080115050f030304030c 68
    0x16901c0003184150341e1544c04030051030800030074920945880da000c10f034880421701d402c00003280c01c040118000d0319001c91104800b0304440d5030100342010b43c0b40c80725203075001c0011000a000c20507001003008416071602d0300c01c503400ac9229101d1300c0d15005000d45070502c01490794040040f58000d10622100e0041101e8110440c560b003d070f140c03100c00e03020392800d0810b010460401c3c4141541d0310300d00340703030300703a080d445a8003c80320460140c515101c103075801242180000c1d4405060002400036034012056005841e41a00c0c0000d0a00d5141d4902411036801e0b40c0307200e001043c842e04201861070800301d0602c10340300c5404007a061040c0c0e40d80704920440d001e48921401281d4840c001407940350007080c0f102050300f08410784800d9564a101e00000e00042d00e124000b607014001c20744401e200179020f1805294195600481d20785000352099451304000314401c101741e03c44d0800520301409003d082c02c0380001400390f40d48246007400b00500d000e01007018500030340040c00100007046000a05101702c5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 478301160 1250 478299910 478299917
    0x60806010914031f050406110301080c10030b060d0f1a0303190309081803010609090f062414040c0c0c0b18060409020309010b010503060a0314030f12090c04110703 72
    0x6980ca00000f909000615003805106580e041d07800d013100352180c0180303000e5401040700b000742e03006091120255120034002d030250f6520841c9050100e007002401400644082c2c41c0004141080c2c400041c9140d20030040e04201075100d10003258142c500d48201c20034280030582132158a210b40f80400c0d240e0150300e4924408200107804a03001600942084c07805030b510444003641c0d8418038908140c4003000712052030181d0310309603001c200551540300750650117400154000400d4241d9490030050062850880d619040d10505007804089115840d0040c1004c0320034804039144003410321003214201c800079410055414143c03004110303040801415181032450a07550780104407070310f106890130400420b410642c0000c00144c56244e50340914001d09146c4001d01441c00d10a004440c10300058810703551044518000b000010400c020b01f0030003000c02c000f5a410084030031250009134000080c4518802e80210400c401c04c8000d00980c202c00000726020000c07d06c20003030820f0a40690071000701807 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 478302410 1250 478301160 478301189
    0x10f030203040804170a050105011d01050603060a03050118060e0c090f0a1b030203010503010b12030a0509120304080708160305030d020f090334030b0604150806040515010608060109 80
    0x1d0001a034125005803400107802c05051700c00904079659802140e40694440d480e1100104100342e01244c0201c11040d02160003005900340800c000c480c2e440a000700d07901900c40140040041c00a00131800b030b500c0b40c1c00e41c0f24140081401c004050351500070002c6c10035040401407000955404000c40d400c0003400303901c24102c0c3d448400c81401000d4a500241d01e4800d0b40c1e89440d03079140c4c15001503058400c2900203000721030b041c00c02d10880b080c9001c00402150004d019045080c0d104a01070192950000e11480898144e14480b0b4119030246d0070040294002d00c0c418050b250303040149411840707990b600c0f80300840c03558640b80c0e100d020304002900700700c4c1c00190032140c03400f400043d20045400202a1042c800014411850785103c001500d84100e40e5a842c800456040c01c4840341101c1e003040652055035900d40c1084010100d1110381500403441520105a01c8020031809204500c548010305076040c9081981960300740c16440601009002c104020f00c0c1e90b840713407800c4211f41e0660440d450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 478303660 1250 478302410 478302413
    0x21090a03030c090b07080316110a0201030b01050409110d0b011e0315030506090f0c01030207110d0305040b040902071a2205120a021c0203070b04110d0b270705010f03020304 76
    0x104580e1a80c41340403d5400820203506002d030320b20003140a03c081c071f260404681e80b1201c003601c66165408407102c51383c102e031082e81e000d940a0b400076030100405242091419459210b24021a400700113144034039480400c2c2041109464410399540c00400d081048d004291700800c0000c080300f203080c1804040d11050700c00644540646031001956104054031032901d000b00d50300390b803044000c0703403105144601c55030440f55502900c00c44017442d07085200e017000410380e82c0901814100c3c9100403000c102041000281250344000648042c00d40c000c00942d48017254117107041100423110075410000546001c1c0312802410904076052120002551041320303500f07060590a2a03412408140e1646001500c80d20003a8080340659555904c6907031061034061540080b0b07a2400b81120050101c00c400c40402c000c02c032001101884010014080c1d19032140302c1e5510008514244d810304a0500c0300c0c040c0164002c400c7d2a044101d06016000f041d450f45800300080204008403441d005240d4000003250 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 478304910 1250 478303660 478303667
    0xf180902030c0402030c0306090117031b0a080a020a060c080f040204050601030f0c0e0102150f061c020303191d01050f0c03070c030c170105010510030b01180b21090a03030c 76
    0x7041e04010f000719280c0c500820003000c168400c0325828401c2d00900000706000386e140705c0745414008410000d5040c03503034000d07181b0a02c6104e1201c1c4541481054440b000041c41c03500140000d00d4258003512542c5118a01001901c42d03001100b41840307040340c200601c0011103040a940280c045501045648074800146c004007031110440c0074840c109042c4220b42c1e60440200d800784d82084c0d084812020603100311420f0794034261800040140c0380c00c04185145802d401a56004034010240d404030001540000c2c6903521000d0000940e80c00e9200580c0c0da190030142e2010f030135000d2504046640b1413040002e00c2c6103d224060341509902091142d20800700304103031085158850491280941c0303e050164a0602601c2020030240c207826002021070720600403d812140e001c2d03c2d6224506401ca4140c0142007110304240c10001c800e80400b1000c500030380041c0091011100031036070340c954070ba8030503c1c01424480041c114071000703050207441d80000804108458140c500041c56a10700c0100702c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 478306160 1250 478304910 478304923
    0x1b0715050a0c0606090608151312050f12150d0c270608010603050c011b081e1b010c020a02130e1606020102280c0f060204080102070302030c070f18090203 68
    0x1070601e134030f0001c0105c2c080ca0b803035015030252031044049901c00c0c0c200c0c10302403101800449a40501a51a400101c001040d0b000400d03404030300c40c18100d0404800c0312001c0803d070424404039000145810520041c042c51080310521040140e400e590b140806441daa030508d2114403503421202e003d00744c104c01142c48862003d0b00c2e4041d03480c0901c281c0365600c01490280c00783e40003c0e50240141c43d0701d040c043d0701801e08540c4024202e0341c5a0800c3c1000e4984c03900a80001e00c0304036110601320800319039050031000901446c3e1f142c600400b038160042400740e08688000e001c0030b00f994000714081d070150b82d8480706004416103240000c5425140c94000c80c0c2042e416880d4100c6d0345280510100e003194064010703100008101c00e00720518071800891000c00e041e0b141d101c9022072001c2541c035010800e1460b0300e0090070300808015150554507034905007242d0000380207400603000410401a0044103010a000800101008071820783c10212085400242e0391a0456400c0c0c0d607900305001c5480c1030051 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 478307410 1250 478306160 478306163
    0x140304050303120f0601030902090106030e0109020d051501050108010b0927040503180402090a060c02120615040e010506010206180f0105101509061b05011b051b0715050a0c 76
    0x1540c2d180e070b06030601d1016a4105130b4101d0121180800040c0c01e40d40b1911034080d80315001890054180d1900c2401d8009103e0029108815500c62201c00003513211010451425441400204900548c0707a07a0390070b0500c0c040c2c100c0342c104600400100702c01080581074541400049405202071316403031400809520990012903940a8148208818408048060003a951a02c4501c54040c4a0242004200c2c070030a1000b40d4800034004003400707828450325500d12170078405042c45201e01b0049151500d025400c42d080c501d010305c071403a5038000e0b04150003545030b5500c13000001c0c8400e0030848000313529007200400a4806110901202980b1001040000700415507030f0000c1045007000030001c0c0c01d200c3c0078010075046500046000d003031280b0440a03041211110b40c1d680c1c0180c2e500340d0402866400851003a41c80c0c0d902d0703841840d8110b02078200041c4203076003602e407595101881200441081c40c28101200e25800800d8100a0b0342841c8075600c0d4404514071303015540317142c07104060ba50300804a60 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 478308660 1250 478307410 478307413
    0x320061e040f1d070912060f020d060e091009050703020913060615300b15031302040e071a1b03070c060809010902010c08070809030a0b060406211403040503 69
    0x1400a002c03c00e12240340c1c3c6802d614880300400f951081c0c0141c90904030b911070381745446d07102c0c01001e000c40d501d541724a2581d10795031405841c0c804826102c0003070f41d0064009154641d513040034001004410400d0034000600c030001441100b5580e200c0ca5145c14003448064010170422000441410071500d5030504607a0020007081403e840c6c040741c4180c004150861004103201c0d803c0b0042d04d14000f114152001d50108030510300401103210302d0301130b2000c00302441e040b80c10890714500024403500070350311070070107500340070103441d180e004000907155078400303407000358100e0350301030062144031141605044d01c0230204d180d881c060414201d08510040f40510803a0001040b40402c0204420003c42110420307910300c10f007911620303440d83c03c90300c2c051030080c0840d550410090010310268060800c4030b001d0007645092550752400301b82403008566003112540481c10420406251a21400340070380501e503510200b880b012104980e9000c0e007000060300c1a00c440408911245040044401500e000780 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 478309910 1250 478308660 478308689
    0x141507110901030b0609010e04123b1507020a150c12200303010807051c0b072307110904020a0302120102070c050f0609190306020f040320061e04 64
    0x1c04c5618004240c03045031003180c000d400050110b124910141c00303907030020140300981071240410380e021b921032004000b500c007408022451100314000001e800112207124940c08464540400241820341d4502c0100c82005005c49005a121003a8440c10740b119008098108076001c4000e95460000520083c982410007108089403a485040c07100143e41110f60b80319146084000390307440740401d0141c00800d601c0b06d1070030409171030104184c02090140403007045404482c1e440348503100808807015008151b1039088600500003050513060300c40c9400543c5810b1000325620029150803640c9101d1103030f070840c400b080a540c1c8041d1000001d5900038203140b00c036401c11507018080c0d00a404255135441e045d0704001180c5c1000d002900c0600c0004041c43e00e01401901000f03016103031100c0104801e11481f00100024003107200070b1408001c01c807400c2ea12545140340030341c5da012080c6040b030800504080700314400c0d16000b00f50b90b00c4191490400c80e026400c810070341198011a40401040030554 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 478311160 1250 478309910 478309913
    0x403020a090219021b061b070e070908062202120a03110c090408030703050403200a020a05180c03090a05031605010b0303030405120901030b03150108010614150711090103 75
    0x15402060482c1103040d1103100c0380c00d83c1000380d8450800d113a01d007580e8008081e1880603807030300100920f40d21a013034220400d01ca10390310180d4907045103a000301e007070420150140448035401c541c1c481e005004460080885203004000480034941c00c403510a0302c09100889a0115a504482e8290300d000501c12542c01e5402402c00a05103400b107640d544890084249840c500e0500c1014640f245402c074001c18a0b54450803011070040c5002041541040300050200e24800b415034203000300c0300c01650050215280900401000780316541c0040d22078484440000758501c1d00405a5511410308542a522907840703207486402c3c0040054002c3c060701001509030701076901c0007010703010607001e08002c200b6481c0307100c241540d0b84021354020f03141d544403420940441c07e5290040141600600d0f0104401d0384410110f440c22400255229401161000601140600348a4075008020040205419200e01c5000c62070700c00c4440c00d407080d55000058131500303000a403c2c842c0f4501c5000b804070026903940e0f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 478312410 1250 478311160 478311179
    0x7030e010f1a0d03080c0d02160c030506010b04080604031d030a150e07060503041412030901020a020c03011e11070215030403120209010923041104060201050603010606081b0403020a 80
    0x2900c5000059415107602402800c002803e014169415182e02085031a44c8280b034079142c04c000900303000c0c1d517000c0290703c0c0f01c0f031801500549140d10518400803142c1c00c40c0b500300c1c00d21005070400d9002480c244002c10060a001880c04c0d0400e80505220000320f0754260603802c0c10b280f180090b80c140c80381610000c1040440b515011894600030010400c8408082580e0703120341140c41020000355050012401245003101c908110148880c100c0d200301c0481502c45100741c00840d20080340c0d1b50701041140910750140001c01c001c40f000c03402001310380c0b80f2180d00001460145134081b0025076811804018046446c1220003064004005e0008840d52180d2400d843e401201c084001070980300d030781c0b0302c015850300a0f1291904142c603031101d034508020254001c1c0241101032000354025202c1402c04d61128070030b0038841400304150661f03c600f0302c04041e00f50f40340a454103010b40c1c900076080007021760004107913400513080c0c80b031b020244000141c0c0c2109401541c2011f075100501d1030000400102 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 478313660 1250 478312410 478312421
    0x1103030114040f1107380a05165c0303010302090606030603031603020c120f0a060b1216090c0c02031506040207060216170f0f0307030e010f 62
    0x30120b41c24003082680c02d1240f020740e100512400d0706510180003200000301e00c1c0001142c2015800d0001040c9004c1c0d0590b8450a420078a01c183c003040d0450500c8046002030080716445031290320b405c54003887c0003c005040160707910b4207150088240c16140c01407120b0000041d88604506040c0e100200440101c00e04849100300100c60781007a06c00700070441c40d0110070349040780d4008241440300c0d6190000c0c00000c0e88002d1081d541030004100c5480900318a0425080c0340b0300990051600e04c6020f418002c0741c0300d00103441005a80525034038421508005844206c1540c807280208850941501040c4908500c01c204400d50050401c0301c54028501e0003280b00300c1e002101c09202c1d91401e80340641b0b0400900c000650160040c28010701c41d000301c00c2c11a5000f40c40544014901a19902c41408980007003511099017a2003482903020b000001c9da50b021046601e00c08203280041c040300c0440c1d144500c95100300c00c900c003c400601e843c0c0c060b6009000100010000307011014240c02034a00a24 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 478314910 1250 478313660 478313699
    0x70e011e170a061a091311010207030f02042a050a030f0902011e210203040b0601030b03030d0c051306030e010c020d1209111914091e0711030301 64
    0x2160844001844020341110506079451a00600200d00d8161140005081c4640403081d51481200310707650681c868213078540c07003000801d15a003110f100620b450a12659078405081c115802184284041110345125004d12035040310300003002940140e08100354486804010242080303c1c0340c2ca601c89800c54010a0b807001c95640c201700e400b095005070821101025400381c0012040b81c840160b40d42321154036002110603050002003510300341026a108940c400c10012400e4020084c801042000e41c1c43c140c00038400d08061091308403650100769603004400c2c0004c40fa640f16506c90342d00318002c00449030044030040d17514800545440003d0003504092038110b5956181021915026102140303419414140343e55001f910034140c0c0c1c5400140501034030a03507201d503805194404950780c0c400c070665010504038429240d40c2c0381035404400d20706000c1c8028045d40181040004d85d85921600c858501401d020091380e940302d103031040740c2e0251582c05c01445807000000210b250418a086421000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 478316160 1250 478314910 478314959
    0x507020a1d090601090c050a051b120a0905030601060507080a121a030d18090b0402090402070b100902070f080c2a030c030304030c05060702180708040317040c05040e070e01 76
    0x4d0340d80e02c406004035028980c1550009009020762030744079200c2d80003865240840b400d90075607914010b05035801e14812040440c042000041c0003440c080e0441240c00c0240700860103020a0741c03415002800502c1600d00040040000081002c00303a4058413490304021480c5500300312904483c0c123007105203400c140c440ca1080c407079181000b00c0c140c4290f50301d0f031810b0800050182200d207000700c10780c0a4807219450503486502402070045586035803020b080268011601a01e040c10603002c01d4240700d50541121074218010010200415078241c00e44207460341c001c0c00940d035800c08402840c1070141001c0d03620380e031801025400c04511390440c18501d5001c0224142c508400015080568074400c510004011800b451801c20492605001500312140054030961800d410350301422b200a80454006000c034080e41c0130712080c9948031407001c01711600b1103100540d5003400c0d2100580c0d0072161069a2069031210040c1494030010301c5a28020002c00940b0001c0303503111841c0e4825410084c11035110f0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 478317410 1250 478316160 478316173
    0x1109031b19092c100b0d051903140c0c010530040507080c0f0f0d02090420060403030e04090303060b0a05040e1e011202210c0102010b0405160507020a1d09 68
    0x4041d8020501c403a403c10a000900440141421400c00b030b06852050b00d42c0081082c450f140403400c180607040d01c814186000c0303480c0b0718081c43c020744086655804a42c00610900c2140c41d00350707002504000d41034003424420740b1880550555411244a114060842100c1034606a4a107502042a0380158451401d81e0342c2c0d251a09844d6030385000520120358000482c803401360b424105a01c0510203500083d0006444018640115010150035a4100c4060410702107008a141c69843c818040c081d04503442c0e0300d05895510010032440c81c104080703100303559481500c0200b41c01781d0f0001000f401400c148648800e40088040c20a4100e031080180000c1c020000030300020419290860b9401900b01d2801c1c03d90800d000700d84030480c3e1010417a0851100c10403103004152014142c00d000341c489000f05880b0201d5400242902c60860380c3ca8041e90819060240c9000038021204540c40c8a1a000b40c4491b01400060a90301c1c0540c171075801c85174006003625180da0211420381c42465440201d400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 478318660 1250 478317410 478317461
    0x13110a140112020a1b06020708160c06090302100305150a0b120f0103080a11031c0606020d02011109010309050307060f05060111070e060d03050903061503011109031b1909 75
    0x43c1d01c21112054005283c200e400e103140200f40c1c2d0a11502c40c0142c0005080c011941e80326492a80006544610750031003140c05000c0100c056110800b80c01c40346081d00e81e540c50765000c43e10b00c10205091000b410b0f00c0d003001680100c0700c0d01041d03030760010003409401010b03594034000b0b005034400d0201103001460a40015031a0405040d8075040b01d80c00031900c0d02e44078607a501140e41e228408400c1c402c03804104100d2010340c4035801c0400c2240b03010000010010318000700a0703e4203049483c480e09590408012414000300c0b0303800d41e40010020700300442c1602d5186402429071003401c0340204403070315101005a40404990003184120b0003030b2076604079201c00c500d0080c3c0e00c50451241582c90003100c030001c6c1d0541000c003140d10720039201c1e040040c20000044e0019080200445091203505240d40420400c1e00d002d003c0c8003108440f01c4507640c6070149520100380c9078403607422091300c01540b000030308074503032900f1003a102844d152501c0785941d19240c1e038400015100402040001e102030a80104d03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 478319910 1250 478318660 478318697
    0xb0c0d0e060c0405040905030f0d050106030c0c0c03030e012303060901170304060e040f0504060e010c0c020102070e0402031c110114150d0501150b031e07020613110a1401 75
    0x40c0105800e400c0b59080c00d28080800000c0d01c3e82c50400c9034035000a0000851490700c68014010301c1302000008941d640c180340c00101100c040c00f0084040102e1103a01e03c021034034181c00a41541e40600e07003805180b142e100182c62841d1180380078502c9034a00700686c40702c500203401550203080110f13100542d076603854450f0742440010354904107481c0c04c204010811140110903211840c03801a2001c50402151000c03042180c074101c0d0161040d070b85503840003c42090a00c640304140d911030174241420400c0c2d0700001e5441c40da5011341811031101c0000b043c2955800c000100d1009081100c0605402110354000d150004200540341c2c0340d801c0c612120400746208046a1050304102c010001106003c020000e54561249041d04c495507154038526010401c035428a015000c1560303031540d00d02f4541178a550103480a080303042c85c03180701d0701406946a07000ca0120340100114803805191005070410f001c40c8004810020303803140c00c1c2000050280c0707000740901d040303001c243c0b5440c0c24681d200c180340 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 478321160 1250 478319910 478319923
    0x151e0103022a070e0c040b0a0207030804090e1203090318040e010c0c0c05010c1e02040608010612030e0d02010801033f02010e0706140c0106030507030303060e1b071e0b0c0d0e 77
    0x20a96170500081c041c14446101030315900481c0e01c12992000d60301c0c1c43d042c0c074070340c001d41251270150b84400c400c0d42c5d0101c4c00c1090052083d040840c00c0d180d89080720040352a40100c1c1803101c9800d040a05103101507071503422803880310103804002c200c3c2c20385113900548030304090b03d000c8801304030440000a103507006014000d1104e402c140d25103601c43c1040c0381d00180d0401c20754101c7e1300a645550126041c0c00c24404d50010300341e464082d4090401504010300805003900d1128032032203ca011050050341e01c40385090460360b2140010b4040b0201c0e10f031036000080c030f1b8407201c0400205d4150030303001c0761100a003070680e101480c3c008000d0f0080814034641c9440d0700740500b0340807800c0910020f40d04084480203007020f008000000503103d450780d4859040032404ea00690000e078960310306100b46c03940d500170709400c50707200d11200c800039a07401c0c1900a00c0c00303400f1019010038a00031090059401c10980d10710610f501c01400d401c1880c0030300c807600c215040081030300720661400010a03190107001400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 478322410 1250 478321160 478321171
    0x120209010b0906090d031b0503040501120b03030a141b0703030806040b010f05031e0f01051906020604081b01020a08090c03070303020a020907020c1c0308151e0103022a070e 76
    0x80c0d4500440304007408405c3c00074401c210100b11420000740d24003109950070110031031249000d0340d46c0728a048001011913101c45c840c101120716080c1101030507600003003100c0f20710029043c0752084e01885141c0c10168061504d6008a51010800c07000c00040e01007083c2d410749109440703102207922102c060008a41600b01c0c55070100c1d40340200f080e060340c0031f0005541c2c410b00c0c088000f0001800b81c4082c0e02c8080c0c09903041103e62200c40b0040c4218a004c3d02005405044000d21200203882c11000030355445000e40050105400040c5003c00c419940c1243c1e4544202130000351358130090010010100c04c01240e511240317000340d941c3e0015903c0c01182c85400c4075050340c0103002b450a25001c008498002401600c154031420350440c625803120464100c202a9006003d100d018460034081e09051006140c0c0541c5e00d0811048082d5540d0918404284400802060828292440140c00070b00c509200c4200032482e8a08800301030b02c0800c42c2c000d403104a0000e60300700d2a61007000003daa002130b41c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 478323660 1250 478322410 478322419
    0x2150f0a2703020f0607020a0c09090c120b07030f060501020330090f0d02060606030403050a091a1315080402060d090206030109020d0c080103050c0111010b0901120209010b09 77
    0x11500308003054101810440070380c00903544000c1105440009519001c0c8100d0168012207030740154030b001440f52030f0307105940d0300150000e60640d6580714454400c5004295803a5642d071000b4050001074000a0003070511300008040210b0303241403001c03012204894420029003003c40010402020380a8402282c606800a44c1884000d600203c90b03c0518210740c50b5608940e02d2080f66040111038040c052400c14000d40409a581c41d16981811075003102c0d0803d540c030000900001e0346a20f07080b294041c0d050f1034419242e0082c06411203402a05610907509500550085400c02c0306240c014160100184915080d60f81c1e0f800030045940b0440701c01c10301107407030600040e0241c2441801071058001c04080000e00c00090b40c0042c0060f0001e13081110f00c2d41c0d01140d180c00b948024414014200d2190900c4480d641c590b650b10340d52200c01e55206410804080302c5104100b1003500030179150040203180340320641e1038408203903d6001c003400aa200c0e4800c90000a503520b180320455000000150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 478324910 1250 478323660 478323691
    0x1d0106050a0b090f0319050d18030f140609102f0c030c010f140105030604020f010f09050306010b0a09060503011d060f090703141f180204050d0f02010215 68
    0x32410303503041d008035100fa900440a4140180c042da000e10020040303003005007001071100514100b607498424084000c1051182200c444407c1e0207042801008403580040401c3d10f441c203e24021580f199260500b0105200c2c4409000c08020040366180158980c42002c1000040148600c0c40c41e40710048002d51a0587d2006495114803520040c0700741102041145c2ca8450804c919500716610700300048541c580c2c40b8201c1004080260300303c1e005002c1100100400d050940004944640715410a81400340440000100da40580d402100400d0010152038031036030740e080000700942c0001000740000780d41c054041032440c0903000b520b05036040b170080d41140d04030a0048541c81500900070703d0340302e42222842c0515580d00b890452003114203650200d1022052519101e83c02c40140c041e4000401c400c03030105003500c80c40080c1c0100d5845074901c00f9000c002d031541600030b05c600c0e0060364200700c980d1647d60600c070346140141d084903c01e900300c1c0c49145d20709a41d400710140540e48162081e0014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 478326160 1250 478324910 478324919
    0x50c010f0203121611070b03041506080c040507121503020301060603142e060c0c05060301080a0b0a06030c031a060102030f0a0c020424061403091c120207061d0106050a 74
    0x208090722030001305080c403141050082c400e0518240c2243e205580741c1e01d0000400c400c010002c022000b49a200b00c90a121f80c90170010000c0e241c0081c1001a405160b442c00043c05046c0715038002d02c2d907005244010820b94403240380340041d2039402d0005034044d40c20a00000703200361007407050f690100c21240b2003445580b9101200880e900301c080c000855038444021b41a07445a5501d007140c0204070944940884854078078146021484940c4200d101348428801044032100c0031402c1000c06620050000d403035500c0c100000b00519064202030281003003441c2c08010040e4143c01042c81c0c0d442c0d10310a903a9541c0c2d4100499507403051407810742103a241803000c035aa01d40111000341130907200a0021801482c030382da2441c4503050f24120f1424403200907004010081d040040c0d441364001c01e40c96146585083d60005545040940c00d006400c1c4c0200310340c0e4519482900191a035103086601596203903044d040407006000c000304480c00c0300c142c007182105030301014894075080315009070004074041d282 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 478327410 1250 478326160 478326181
    0x906090403020a0c0b03480c0d02010504020102100504020d030302030c09041a010f0e0915060d0c020d090e060102070e070c020301060e0a05010e0415090816050c010f020312 76
    0x1500840661003100b0350b41c400202e002c4005000740017961102d43e00c2e4030344240410036075044500354185d5611076400c03062421103400305242c00c80042c0108000380b107991801e0050644070b81c0f1040107840c020b40c0304034100d950741900b0240c041e600036402c0300e00206a1382e4a10007100d80548000f94440440d03030300c2c07500081c000e0700910344c0100f02102d00c604149800000c203064515851647c5825a00105400501d40c0c00c07007084040d20400d40350041240b40100041440d001000e444400c070003d140424686555a8104594900030368410078455840d80e01da01030340d2480e040d01040c0202e800c80e0404114038502143c00e5100342c1d0160700501045103802d6441c200740901400180030400003504030005602c090050700700409144018407094076161110008440d01a08940300d490416400d00c008940000e03410100214000000121514546400344891007100b004513401041205400e06000703012800140761300e420f07212204181e0703081e07800b240c0f284600c0740c02c01b4070f01c0d02150101e441c2180 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 478328660 1250 478327410 478327429
    0x30a030504060e0f07030201090b1c02091c03030f0c03051e180307030801030c090b0a0e1012060509010b030c0604091d0f0d020f030a1205130803130203060f060906 72
    0x9048001095000743d41840d00b0201c0312031100080da40050400c00031564415848001040d850301d040c0d0501c6141e40c2c0081f000304040924540e0103802140d990195610f1318a880c07100c0ca012a86104075546a29000d006000d0005451050500d03090701e94150034000d009051103040e4a0003940c04a03c00300d015001c0b81c2c9000303803011612402860140c210ad843c100014a0100d001e5140c46440d50b140d0310700800e40c42c015422200d0441e0914020451646504d02c0d420140c0c0c0341215030b51001da813182d82441e04001c2951044244c0400e47e91004140000350b800f00c0d0088083e0402444100102da092580c0c0e91225042560003400c2003000700142203a55210800c403c00000441081e4210010903a191004480e149042d42d00000340041c9030a4041140108024800c00914202180c1c44c00c081c18641d0306950540e0b50039250300015404026012903030324890361110700c841d00c0307040c0394200f24400b0030f50b010124000d200f2000802c14441200c0c801500c10680100450a280e503100d003808403402 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 478329910 1250 478328660 478328663
    0xc01030504330609021b0d05030403050c0c040c0e0f011404050f0a050d06050121030807051b010c02030406031103060f0f120712120f0e0118090f02040e010b030702030a030504 77
    0x285030791003014880c100383c003400006140c560005611000c4501200a20180449220b00140e10200c1030040880c1c12406480e0300c6a01b505200e51114012a21503040c010245282c6602034a003941221101c1e41128140c020020140c8044210003244401580e0b061000c28400c001104c041c0020401450148a0302c000d440c0050b00070f00340d445e590404030f609030395200400c031401c90b2540014040800c01004071400308d681c080220900380107645001c2e1406401500d54810000300140900a0440100b03980d081a00400d008021101c00300800946130340007402900c00181c00c01c40c3c1c804224103420184ca00480c0c004090200094440d810014580c0a060403150040c4462092403074040080c08108020320707080f060f5060345c011a15020240c40860031101d800d000301c0d000420260751b802008002c1317070003003801c040500003414103810040c580e0700d500000e600d81c200f1016035003002464019108503545600040d800340d80714440b80720240011143d200c010383c000d110104156200380c21035900a03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 478331160 1250 478329910 478329983
    0x102060115050d1e1503032a12110613080405091302090c0403120302070503030411150c01140105103509010203190513320f0c01030504 60
    0xf90345600e8501940c00c100c2110351041c00c043d6070b04224032418011503d0a5000351a442201030560390050a41c030a072203c420651910712030000041c200c402e03003a4451541000d1060401044080f0091448000c0c00c4c110006000344400700d00560000c032a11025942d0285807907040606003028040d00b0b04000f01000f80300c11540308100050784842c0e440502400480c1c8842d40c2d00c0c0d00318102000c0309071728080d4107401c16104100401c041540032060b2600f05610040740d1000305c11b1000064510b01070301c800f03000d4070f40340011106044c11056000003400300194100019981c1c2e150200308a0744085001400420140100500340e80354000c0383c294052002c0640b40d05914251140c40c82502c400c56444d1806e85d800400d00c5200320600c05121030a414480c002d02261811810be2141040b68250040006588038001039400c0e00071080440614803405000400310300b00e0240642d90512141082c0c0d41c0d024119801c0c003607520038000c4612032500199854800b0300141700c0c064400c00c00235124220b4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 478332410 1250 478331160 478331167
    0xc0906080316060f020c0d02010510060909090c030510060303031107020a03030503070504081009231b06160c062007540626030409050108060123010206011505 70
    0x580308601c0a04060a601b000805604c02c2c148800790071244046c0140b807110035458000c0029580c030004480543d0100480410f00d00c52a00e01400900c1e10703504020420300030031406801504c4a50720110440b17029640c1401000f040c2d1280c80d4079842040302c01707504032104001c2071003c03900490003140c0200f0549031044c0ba2655034041c0505100c055100d44814540702c0c0c51440601400740c091503111505000450a41c01c003160703031640d07540e076030110111200e58400d48101071559014140d51807090103100a41c0d00c2c0d6010f02d401c2007121038500418002c80d40d1043c04456620b000118146825071031001080c0c001e043c108460080001008501d01d03054210080c001c884942c19101c0745c07100c3d00c0d42011400c0d400142c8508030b80d4151003195014040ca491003c100c9180d11041100310004003058400500c618031400c1d5046d48140e40006541604040000030044800500541201d8480302010039042c00c8440c0c88000c60016402980107030300c5940180007581c0c81580c0e503001c070810f03800c04524 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 478333660 1250 478332410 478332431
    0x60a17010603090c0509090d081012050d02060c030c25020d060510080d02060408071106030c0903010b010e0f0108070207080d02030d1107150b060f04030f0c090608031606 75
    0x4405000d8000d20700280c1c4072040303141000100c6904801074001110340c1d009038640207014a41d1120300d10a540204803481010500b40f104003c900c80203410044c40741d2041c100d40e030801554414104040000510400000480407440c2500340d90140e0b0303510351151714100500701440b0708000d03111a0b180301d1400b02800c60b401a512241264130451145c0f001003101d240200d448200310019074854403141c1c0200408441d043d0307020030300c00e510541c407200b6107440d2482c2c0c0c10000c2c0001d4429112030703084000081480003003000c00029240c4954102d00900c8007003400d000441e1040000c00002e03070486003883ea5804151b015229960748000316204490446994455540ca0300c142030050034056040050018a14207581c051135400003c1140b80f549407601035551b00031809490807983c55810383c0c0d04e000210307a42e076100844015034400181182c80300d0b00ea00704140c40002c00c01c0200c828581044001518a00a010360401c40b4a88005513050410582e031402000c050003000700d8485580d00260741 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 478334910 1250 478333660 478333697
    0x5190e030423090f01290d020f070c090b06071103010e0115030b010504020406020c0108130b161101140a02090a0f0e0f1005130b010201180b060f09090a02060a 70
    0x1061072040410480007050342c0c203000081102900001030a00441c005101c0c80341d14041d000c05445541a11030f0900c054011030b83c01c3c9018044031440202e00004015203814410300c00780035500e001d091142100c2d503603a000f50342102c0804a0712a0407100900038400032454024120301c002c08003500114005200d501c03000e08651030320080303400020000105000b030001a0400f240900800d031001c510f483d08182010b9510703402440c0342c40c10412800001200000310b0b42c1c041240f60340c0b2007240c45242c144100c0302d1101c2003903d410400010040703060540102d83c14020324161000d900c0300c1381c4003601c82d90345080c0694485850290060900c0d41c2c00614042c02c08507240003030a00d18401044c90410741ea0b481100710700505800b0f22840c1c804e0060205940d02006180000c03d10708002580c0264800180d015000780d02c0040102d201d8080b01d102480024110540725071404c8418800710310030311301009694482540c0f1100c807640180c00c800c00500f00312000b003c202e282d0f802c005401e0301d66401d001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 478336160 1250 478334910 478334939
    0x110402091503070e0105030c070f0812090102120903070c0513020903101a09151309050115051311070609020f06030114010801050121110c0106060c110405190e0304 72
    0x104806001041060f0070741d110116030960082460900c4c55410f1400786140b42d4051081e000e01084440ca81400800401c0400c58604010303440c440d0085191034030b0294000d4000b41c0e01010000d8000340062003440c1d0200441d81c41035401032444017104d0910090003200e80010341e24a220960030800180e90780e50070030800742c1c091070401010441040c1402c8480c00304503002103031402040c064043c881030103540200040c1004043d01c0007019000c40c400316a024040d180da0107030071940390901c0251a1512006e112095410640303d00030013500c105001d0003128145800d0021b0350720280a04030000b980c0c1c0d001000b03000d00086c500e121034014180000d01c0c0d64000e030b100c0100481c1044004005581201c0030030700402d402d007021030443e00d2010104114031540d01b000d074030540c0d8840d21507840305c0d00c800c01d94801b1500c25008000f16a10f89101502c030f00703881c01c02510311000403120601d05e40350a00800e8070034812800790120507201102c200c0c024005404484d1070301d02051001241c1c05a040e0f155 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 478337410 1250 478336160 478336189
    0xc041505192106031110140301030303020c030d060e1f14010c020d0c08030a260402090402010c0b0717010b0a2a0b0705091f05160303150b0307140a0c11040209 70
    0x22600030003142020071052220125a400c07d20103500703080904000c191003683d04507a010300380540d5031480840307400c0c2503218040101c40106d203002c03000300350341040075802c0e8451070150b484550000c1d00f007200011180310a1103044144900181070180b603501c41d20b01440300610203014030710489826030b03070348510380c0e6030350002e80300c1381c2c00401c00c404072030b40c05103440d94803070042c0c110303024074a1a0704e29584070440001c3c0064040e1030444045011a40705801c800841c6130046260403890030301c800000c04440e254101c40440b0f56002d4004a1040280c804840da6000c544c0c07140070b0002070308083e0030215032034507607040460903002d240c00005c1600310480c5482f4400710344d10155104841c00800150307039294030101600e5140d4105141c4560f41150403a418004441b50003201000c0a14085000d000c401400348205039288400040704030161000d1030040040340ca03031120200410035181410b001340014400028120784c40500801d144408080e10350f040a0005443c0149a801240c45083c2d0f9041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 478338660 1250 478337410 478337423
    0x110c030307080a0207060c0f0b06060d09030504050111030c0d27090504031407022803050102120601030c11100504031e020705010f050a091406120c04150519210603 72
    0x3d54004581e418410310b0044c00d22410046400021900c514858003c03010000b000841074201140c96990781405487c003204003003c05000e162018640100310745c00c584291404a005401082895036020082c3e840350a0958001e2008050005044038060003110511540c08840e00754035901103900c2403140c0103051081c0c40480d00f81000d01c0d000b0844280140100040842406401c005955400c155002140e400c030080708403043d5640502e01d9610f00b9803006003c0d40c40090321030300c862050a80c0318410b1800340c804000310303441210301380c490010140c2240f690383c00039200c600e502e02d010340c8a03d4212380a4940138803203141c1a02c003c4000d4240032042c0c0b000d0fa010100802007036034843c2d410708071010181741c0706051100301a0702a11146041c0110310f2102078042d440c4215469000541e0301548000c2c0c080c06490800107001c0360164098021411480910342310001a0381c001d0003120010030007405003c059100d40101140d459545140e070090501101221f10001d06203401124040c0d4090358 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 478339910 1250 478338660 478338667
    0x611031927142b020a050310050a3603030617030304051e1f093239030607031a04150605072a031103011b110c03030708 53
    0x151401e180d0340c020800b05201d00c80c004419811400d4004800d444031034800c0c03c0303a8a00c016440011000c2c1700c51b42000d80c01d03102c1e50104501c181041e0304040d0007020000780403c0200d014040da10800c40c1502546420b10f03a109456031604500c1c102464251030082c5400101544c44a02c0c6111042c1c070302d240b590041e8008030030b10051140030300012440152150015030051082603a1545941848031060042c2d00d00411030200c10036150000c4407000c0e4841c04029032880603582c81c0810009440e44400c4804007500321050308200010b0000000b102803010343d11024003500c0c1312400070050310f928400781d0003408140419490402ca081d00512290b10049202d00e41c034a0458400d05500007043e1040781010b43e40c425400810b0b11303e6003594003a14040e5991101c605080315001907084c5c0c51701200215509880d80c0303c0c04024404c0659108600401040c4c542108060907141800c42e080b103501c18551154240700d001d10140c82c41c80a90905441604c07110384000703410f5030400c0509549054000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 478341160 1250 478339910 478339919
    0x406060801090b03072d030605010b040303110705030a0602031e0c0c0c0f0d06020a021515040e060411090a0906020c0105100f030302071e08011d070611031927 70
    0xd0041c100300800070f50040029500d415030b1841b0a000312080720b0100308010b41034102c9840b1010010000e1a0450700500281d40e680001c074980d58003a100580009100600c15101c0035004031b040004c4442c000c0c0100702d0100140c5841c0020351000e013201070104e4500b80c10f10441d0b004154854031482552580035102ca602410f880c0c20548400c0b22680300d85044403404007a541c40014a001d51f5404c9140103803940414007082e40341c4400565060004032006c0e00300702d03500440d14240896220140c605200442c0200e0310380f43ea40005031401003010506207903001840c1041a031103036228100100104001d45e0a49900c41260301c405544034403651983d040141e84019040410000c1102e10081d044207443c5442c004d440d084280a00b1011030078480204144d64035a80e041000307400d00d4070080065000c9240200c0201c01e00740d10700710b400e003d42080060f000d0b0055000200d50b14403c0081d5141071800c1134150842c4a00c1000c850501c024648000b040902607500e00c0c0c0842180e228001c2c64a040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 478342410 1250 478341160 478341179
    0x4030c0209011d0121051506010f141804060902040b0c15041505151314010e1005010e0a0902071a0105190e06120d0306090e070b090613050406060801 66
    0x1600030b43e0300d0b030540c100e2101c80c14100149070382c1180e01c00d611000c40d48050301c51000c415000000050314500c40c2d20804900c1040350008240618001d88515120b201111003d03141d5404a901d00180c40b00144032640000300c1c00006241203050080002803042c3d00c4407410022038200e0741281180000100b01e8540ca05070402c04803003030354000d02e0100702c2e41c1303000d5894044a96907002c031607952540320302c080340e41c000d01a50b031075881c0b801c002c102c9482800a035070902c00074442c0401415182410701d00000d450f420104a007030103200d40c1401e11522504004c01550700140b03682041d0b4011031680720001d200c00703040c8090b240e1580b183c2c050710300c2c0c2c0005041c044800340301a081548168864141200d50312419a803050840e1a110902c5006a507004005043c004c00403901520500440391113125150f4560320200030399100c0e0790200840f01c0d500707407001d80e00d8000d0300038001c01c1501085281c51500d018005007054012040b40c0c550034903110310104085e44c1c1036a0121011800e0880184440d41c0e1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 478343660 1250 478342410 478342429
    0xa060602011802030316060b0307030f0201031a03100e0c030111130807061b050a1703100e010e0117101b1202090d080d091e02030d080c18011704030c02 67
    0x2c60140d40841048903400080e164421404020b26214415601c14200682500943e80d82e041c003c083e540d0315652801c11441110010a080340003d140c200a502c540c0049000b03040722100c040d004100310030402d0091402420220000c485070f2040f2044048a65024000c04c030f066410941041d4980c05104c1c04a840f0103501d40028626070492001406455440f040c600c0006a81d040681c4a901040c10406d007011300c03540300a400044600c0110a11019010045d8000c034141d0081d0760702550b8030302c081c019440f403e0003071140a00588004118840300d1040d00303005c45000801b551f40d0b0305000b0010008231503030f03c032580e404404494600c8003c00c1e08958034500b0100c01d1802940f0b8000548001403600b440540010801c0d140491404111116640034400c00d40d407211400019150000c2881890103110390201d02c01e00c00d03202100c140b00c0c0302c0c0c1c0034640a46400c4203186d08258144440304000141c5404250420264620344110991405009405035010f6107441e010740400f401400141328 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 478344910 1250 478343660 478343681
    0xa061109120303011802071a040605100f0803030a021e070506040507090b010e0d03051b0f010507030209130b0105070804180509120a08150306040302032107090b070c0801050a06060201 81
    0x4106100410003009010017012001080721001699800e062424035841480e82880741508101e2804000800c98294010750086000903d0030300c030107a407030400254804550060542a400600200d080e245c43d64015140890512414800000001e0001d210390303000800107942c0c950100061009210052001202070300c0c0002c01032105015110020300034404040c1150700424500c2550000e00d4814015107140c1903e210880202031200001c03a90f40700c050140006d495440d110200c1c5d4503034060b100b00c60840700c02401000325078224256070350040007902066030600c1000c020100004d802d200082c4046c00c841d00f500c16412400344403107003c40b100100b0a00d0316030f22034001c1502c080194030a0b80d561400614185001e40da881d00000000c940d0510a40d030035204010a0008242c0c0100c0684038a00c003a60800401c14100d4044044000041e070303180000ca0000301c414000464042d0041c883c07503028450304500b881e03403014840d003114002c6900d41c050325668581400519030a000b06082e06 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 478346160 1250 478344910 478344913
    0x15180103050c0415030b12070303030b18041205160b0f0609010317180d0305040510050414060309030702030601030c05130212070503040f060f020a030e24090a06110912 74
    0xa20300786014800b00d11030f0340109030130b8240620861440e14441e400484280707501800c50f0540741991003d41daa20070943c0000c90110f800c00780910950305140b507104c091101485d0b089025038495459038480c1000000c142c10400101704034020f40100182d4141d4900f86c441d1020708851301d00002d014110000c0504100e110740c6a000040000c500305c05144110b240912103869541c0d542c0032909d50000000480c61a08a14901c161105250300100030f801201d400392044a041610307090211098841c84c00b5005110001d07030f280f01007605000b07002d190b00c000000100e81c90328806400184c5010826841103480101845007448641011784003690460400c580560a25110568121751008000c00102c08c07c00c01000003024008000d640c02181c61300441c04010303042e40d41c43c03508065071050a1040100342010400c402c0e03002c00254442510416041c40000071281520742c072000007018000c1e02e010f2240402e0203000c18118401c080004802446155807560510f007845071040b803040c05022203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 478347410 1250 478346160 478346171
    0x2010e0a12030534020f210105010906050102030f0a1404030209090a020a060c03083601060501080c09030604030c061b020f0c0d0f0b072a1515170304030215180103 72
    0x41c03c02d031140032644c640c1e0440312039040700d09001c0852a5050710000c072a601d0406006801a820019400f030b9050b104002c0c010702c2150349501c0113a03517a10034100c00313000c950002c025221490344610f038104065465a00420b10701503490300013884403007003541c90710745a4212002c2d100441c40c11503030a200030310283c20002ea80805903140500070010040503069a110760200d080c0d0310100c41c181d0b0510110403801034103604508281254000c040500401c1d010a2241002c5124801c00209441c0710480090042c581c1d1303541ea9404603644001104121412511103441d0005407083c031842ca0304011b0181c0c0188800004c5100443c9001c240040c6280561040c03100b600c042180c44e000802e4060b009616401c2d80c1c2c0b501075003290309c404884803c180d4007108041481804e01400b55520348203014800c0e259140c505961407408441c00707008460080045c01008000780c51076040c0100e602c035000c2d070a0343c0c14243e80c2d03000309410001031010001042e900103400c02585450880380001501e0a1070304028 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 478348660 1250 478347410 478347487
    0x90c1101060f142106270303240a0f090c020705270c07080301030c031a07050d0e071d041b03050c011d030a0302061603020c0a02010e0a120305 63
    0x1060035118168a005444405131054803d03840482c48440c410144111001c911340890411030500ca940884200050b591414481c04200002524080c0200c42c40310305c1c5101c1c80c2c90062440344070307203005240c1000305440e0001b0480101c03c6007a0003849a802c001c280c2014800d40242042c007640c01c03aa10a8001d160350000c19500e000e1130150003508050315070031a840c4c0e03c0c8011441c0c080d000005100003c004008010000e0110315482124481c2e00c0001c446403802c620112100310880b820000500305201098182d4880d8100b44030f40c21400e401e8136109500c51901c2c8415142c0300c20b00c581d564065a0501042204001185482039420b0441480450856845a1711440d0142105041203082d02c0800401c69031100705403012a401021035045080501d40a51101411240400464440d230f002d40782d41c034000d000f01d0700540716500152803155020341c0103541410300046c03102e0b0016480c0001092008840c240740d58100d0080d1186070310740da060200070740d2600c2903400442140c1440030007241c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 478349910 1250 478348660 478348679
    0x203100f1401030203060d06020c10050a020c06150f0d05010b1018030303020a090806040b06031002070314130b0a09090c05040302030c04110c0109030309051507050a1206090c1101060f 81
    0xc0c1c14520910b03026a42c0d0b210072000403041d210080010341503510001d03004900040000d445844080c100400b403101d99a41c03940c100c00c9001c4c1e20a40d4000d6008140000c890100300340c407a1191800003001094001103190129044841c60102201c09a5590710124002d18007241d080380c001c00a4540f101e030fa42c02d43c43c04080e958485200c01010304d0380108009030014080c0505202909070700040701c0d21860541898422244155a5a40a401282e16101502425000b1551801d40507100d10f0140050400e44000591041e040002e034a052540c001c00d034115290010b00601c5e00075506d0300d810a042c6040d9808031208460320b141841401c000810040e00c0c0442c01075409001164000740350811405140c019124015803031a072546007600820401d501540b220300e2150190048039001c4900c100081099001034841c000410428400440020300c1501c00a40141043d0000702c3c805d552104000c0a442d5100d01000c041100000c4c02034090f01300b4070400c1c005001c0100146441c0f03190840e01c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 478351160 1250 478349910 478349939
    0xf0703020a060513050d060203070e0603150d081207080114010c0c0b070f06020a0504140f01051608071707030f03110415020f19050d11030313050a02130203100f 71
    0x11018003e003c038005480c034141014010003000050f1140d548030869141401c001c2d8800c072909004640c80500c159024140002603a00c58202100802d00b2403a4200421104496900f07081b2454030b4100940c0c010b6100d1032050314050b130301c2600d5001495041c1120000c04800103070100e41040295001103000c03608500d5000100d407101d4102580c4c4c0c0f00340d41051101114400c001608060001903400c075400d510000900803071b04a046055180c00750306040007a200c9200c002d50f40010014424100b009403142030040105124a100516108840e40d03100550a0914103649441c4001b0510005054000050643e4200749250800030010614003180081c040d5024000c040c0d4503481086412030300130070444040c42c2801d0100da500c00d910010a42403800d2456081b500d40c01384086100199028560489604d11860080d40c03c41e5690392440703140030310b0103400342c416225680241c40540c44050745142c2c1c004c508000962340e4a0f1480060b0300c4a481c0d5804000310b000e045074204503028010030f0304c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 478352410 1250 478351160 478351169
    0x6020c03040512062202030319080108070501090e040b0709090f05010501260103030e13060f1e06052b050916120506010e070e031906110a080a0e0f010f0e0f0703020a 73
    0x75400143c0d45c0d002091560141c01904012004a00050058076410640041c12100c8150403120500d07241c0004441101c01f6215112901120a0120f00002e02e1145101d5100c800c624260b4400755445032007a00307541854440c600d003940e9034030052202d540d2000d12800d0000b03444180f5510080400c204801410701440b028080044040e016901544c45820b2404007401e2040180000c0c2d40720b91200403040864803c01801c080c1041c041102c446849501c2002c403141600d407035007014840c180c102c2c40e216100d10070307460a060b0720440b100c0340440b40c45940e01030300600e0000c1910030320030b245000d4443c1c40780d00942800d0485c1906040007400005041c0d0640b608841c11304501d4460110581c0c1c9141c485516517418052200951500c80c0100700400c142401030b007050100880a50781a00d4504c0750122040004802c00d001a0303000a40e50090340001d05000112280109140c5526084981000d00b0107480d94544c00d01003101d10081000052040340503000c0e1246078a103900280119480381704 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 478353660 1250 478352410 478352461
    0x60506041b0807140705010605120f030418060308210a020c1b030a1202150c0f0901031a0a12023a110d080a080f090712060906020c0304051206 63
    0xc07243c42c400c8100c03141c0409040c6846880c3c99007807078170a02a02c801d0003641c0c02042d190074406107400300059811a50302d54100030358507140c100314600c03e10784144028202001d0b00d41400000141c507034001080c5146c1c107650504041d2681c0c2c2000e09d0555400340c41341074240d00601c0259900140403c03c0d0b0140c04104801ca0b16403440140840e051a80c1d00a014100301103e501d6855410340201300a052041400010328140c0d444d8400c4c2c9800303001301160003490040030b2003201080d500a60040400c8a9001030000c0101000750000304403240c0c2da04000150a84180084118203024070801030800c00d107125180c0c0c003100b0001408072030602c1c2c4aa00105246051044140034040650341a0340301f01502c04401c828960034420000c0d40b001d0454400560468001509000319003d690702030203480b00600856403400c900150003100c005002c0e910031b0740d02d00a42000a007140f0041c0b2a0003500005541c40c5c605d408200444a01004c5c0c070246541c101100b044100c86520480304002c0d142c074071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 478354910 1250 478353660 478353677
    0x150f09121d12010b090a02190e040e0714040606031802040914030c03130501020d080109050a110c0c010f020303010b0909040606080f070510020a031e180909060506041b 74
    0x4501030703801c0024801d030b0741280e00300c2d840e4881d414041d088a050154156100f004603154050300300120310400c010b105d600e401c66440040c54501c0f4444003c12154018408a51240141030701402c208007503210b40340c40300903101e007215542000e004000c0284036a05081103107400c64080318030701c6020050024415030381c52155104111059501403600002001140c0d21120601c1c0e103e03682c1c0d03000b04800d4545c1c10312100c000415620000351785080d111250388a0790740d41d28040c1860094a80540a1800d0646890030a0402000710f0003a000043c1804008c00000d200d250000d00407181003e60f0380215002000103119010b1541c00322070386602c0940d0034a19031764490508500803da950403400c814000e03000c04445085001840400380e44040f24021b99a8000074000c0c1d03550700782c614000300494048006211008035800c03d410342c225050411b40c1e40c1c403454913840011321150307400039040c00d50398249407014031080d03116a56021005132020004d59510001040b07031040454004410403406d40e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 478356160 1250 478354910 478354937
    0x71d0a0b0103020f03041209051c0b1008150a060801020f040b0703020309090f041202030c10020706111303050706020304120b0a060b031302030615060307080709030c03150f0912 78
    0xf5070459a0509440c0d04c0c45489080030300d810b50002245504240c0040c03e18080811180f8100c502400d064060100c0c0c42c02404c0720703944010450748010f1032070a0482035400c00040d400c40600404100680b0200c3e01216850300496001c1243e00e43d0308005590781c414000e001c0000500804c46080e44c150b50b8081d51281c0036031408030700c1d5100b00000241c10180704003d001c4000c0c2401c0c880d60203540705440317241c5400c060704800c82c0d50307001d01601f081090b403090100f18843c1d0825070007042c027640903802c0411554001c00020b00254400d04140310320711110202003044c40380038040c082c040d160034406985040d162002e00310004104034406040d1444050100f02001c144d80d01150040c80ca0031070160b1a8501a21030320542518201300364000c1c0600000200c620488446402101713100601c07407411525101000c4600280080980c018081a00310110220719030400c042c004522950700c1481180d2607020440030359211038840c01c1d03124101a50840002e494216600c68180c50345001008101752 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 478357410 1250 478356160 478356167
    0x50303092b0c170d06090509010c141b0a1e050f06011404020322030e0f030c090109020c0a0f0605060f060903100f06090212060301050c0309100b12030d06050102071d0a0b01 76
    0x40904d00b1111a1501c000000c800100380c01451081001d84002c0068552514060302e940401540301e0a80300d00405c0b1100c07a52003ca0601502c181d4454204c500d600340984d601d0070324030101c200f0f1181c141800d00720b40b0b003000410040c4500e04051000a401c00303514000c0c541e540001b04110040c402c5401000069400f074284200e00c0c2d07404203035032034050080d503681009080401c1000c0c4480c041e041100f49880035050009213400e2100000d40904126072034154120300075080300041c0ca1040c081c15550001003041124840340e4a4003c010000303950402c0c0081002002082041a008074018002200160307004a0158500450100c0120300360311040009801000c064102000c0d8038408242c00140082c0030034401d108410a42c003c01103070b16814410710060008a6040c1c0e51580a10308698500f6125007040c50038000c050000348184c02940c01b03040c1542c01880f40c051040c0da40f910b04000c20340e41005110000c00381d000d0f241d48410103050b031020034240024190201140c0360102002503911 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 478358660 1250 478357410 478357417
    0x203220c032d14011b0903060902010509060f040f12050d08090c06161208010b1e040e010e10050145060504080609030f1213050303092b0c17 62
    0x20496101a02c007501490000b0400c21100b040040380e41c0307030569814480b81e00c0c84c140714460400e038541c810003601e5640d50384c02030102c010f802c13410040144401c0d078141c1c4401c1c024210080794141c0640d1070b02e050000c4122441000e138000c01c083c0b0b003006400d1002c10700100d0010070000b814940821150f60f59410f0a02d0b0102d001d10440e00b00f074000603034030111140d0701028040c80340b01d8200503001d00750741c3c14100c0d0000428010500c1d0300c60b08200c0c0010400004031420049403000f400c00303082664a0802e84010242640a660452951010400354900c0e144000c0080d003000d09121145013040e5291140903015050140310500040012480030744030783d0400c80c1d4040320002c0420f482072310b4a01c0104650071500c21120540b1440010886121010040e10651135594003850300301a80d07903120060420300900b801c4130551882500402140092000f03500c00c6180c1001428a80c105800000560b1100d058890b2a04990f2074108400350b4004041040c040e004403260000400109a040441c031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 478359910 1250 478358660 478358723
    0x1104051309050c120c01090806040210050a020c04090c03030305090604110f010504080109050705101b08091909050106120b060406030203041b080d080604140f07020f100203220c03 79
    0x201207814104e4040000388101c43c41c5003c1c0d0300d078290a81c3c0c0d90015503480c4810f5030b0003580b100e07a61421204081c4100058009003115204440d1034220043c00300781298502401a20980742011060050640600a064216049000500d006d00d81901d074400c1c90344d06241d03482d11901405140c0c2e4102c3c1e10440a80f4046e0000784000c010303240461070074566455840c46030600541660703958200c16801000700038883c4020320381c0ca07101c058103603485200a40c0100002c41c1e212440040c2031416603000c65201c0090140300000041e55410480083c2c080004a451000860b061440844941d1a12020307141140c10314140541c580d1a146014400040c0030301140801480c4083d000a103600e001952003401107054986140a032600c500b804103130303925144005141100c50005c40e00007604452070725401a294410b54a061801c0b041c410308109104e111a03100c42e4010081c003a1216412040c000d580021a45a00320000a9501e04140c120240b02c090101c2400c08155120001260701070030303150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 478361160 1250 478359910 478359919
    0x8060103180611030f070f1202090d080c06010f0f060e0d06060308070b072303060f03190c080609010605010909020d1104080f01050a0c0e0f03030d021c1104051309050c 74
    0x4881051074040744c10031607109900004003c0800c0440b4068000040411125652000440e0302d010600380079501c4004c2c1260400840e60415011902d0361000d0050040000040c103965403600c400d4480e1202503402205180c011a5070400416810080183c549241030707130000310b05c50050400744000d100903440031301020300000c1c01208010401d10f4441c03007201729840703101c044c00d2034019050605c401901200d031002c0342040401da0394076000e150b021080d8230050172107400b54030300348800002d0b441150044400022081c0c4c14001c000c828001c69a104504400030403a862421000800d90321041c40f07080115a130000f0b201e01000034035002910704040e901c01c0155a00c0e59000c580b0395647e1051150080c1e54601000b1501b40c45150064061020466507050340c952031101c02c0200d030324105280240d0521007042822040c04031030000c0c2840c0301d003d0690b0124060601285402d5403040c9036a4200c030351040006101135664013007060a02e00c564040000c034005940f03002d40c40c00c40e00c1e5260a42c070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 478362410 1250 478361160 478361171
    0x10e070f0609060810050607141009061413140c03030a1110061a0904090f061b030203220609050615120303041101140d15030b16080601031806 63
    0xc061644004000700d034480d0380c2e9140d00c956280400c0319410029500b0402c02c400c010b80400c618034120000d459018042c0d000d40c6c035841021103456140080035070311030440a45a01c802c00600c0300310711a0700e0846280b5034032485c00d881c000540d46048468050020080c1c088031844c121082e00410240006601c00b508582d0b507274030b4414002e00100150f01205801e44240d4000c0b96030600385000b810112000c1007291003150788852401070040c0c001c2e0b101305070050369030f005190115011481d00b130181800740f18005480d4450801070840c0303c802007a000d09050042040c0301101c9590089250502440c01e049800d40d41c151403c3c0f00900100321002e48140305800030b00c20200413030700c04003000c1003044a0b0050860301c0d0070f12080e117070b000440f030203040c0481e49600260304d9409500054400c1d04080002d1b0f00e061564401030084032070400503c1d0504040040500402200400231500b0800c40441144550746102d402812500300520390b50425803107215003034020300804400e40144c0e40c000b005014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 478363660 1250 478362410 478362419
    0x3040f0305070c080d0c06060603090309052701030809010807020a0b010501030902220b0a0510050f03040212120a080604050f13020102160b090f12031222081803010c050d0e010e07 79
    0x3140422450996a0524205000427480d009100d01d0140326410b4a64030b140520f8801001851415040c150840f945001e1194030800282c0f14050301075032141d07482036103ca01600006080720700003020300096500c80c0a0201c041034000011504450013440e01207580c100600c04203041602c944400030003030b00070306c0420040c0c0000d90056400e40780180c0b4900c96841e5504200000c00c0c8a800c03111001c00d100304200e8801200d840019503105001514804110751407071030082c68411021003a0070001070218980044603480300394543c00c9401224140001e081840030211541406080c1c4060801c510a0030701c21a4001e0082c00d208140071030000a6240c2d0350a800c090550040034024490807000784410b141d1725000c01c2e442c0c0700011342c200442c03c00e60410300400000002901104408000014003035200c0c0303040041181c520700c01c1c04001e8075030344500c1402d41c1312072001d0b158611990504505500095229095422619040402262548541802c02d0050080e40104900d0b805039840125 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 478364910 1250 478363660 478363667
    0x7030f0b04050f0706120b04060b0f130b07020a060c050f160f080303011d09030c0a03030617060622060e1509070503090a03050f090a0611010f0203040f0305070c080d 73
    0xd200d40c0c010300594401443c1100c1d61a00c0700e202d40688808601c1000541005050690142140290280001844a442c1c03003146d095074100340c00d600500d050006030080c418084601a03001028403450250800400b0f5000a843d1945030148004000c1c90803201c1d020b1000400032803820720080d4042c0e40c107124000d8160b41009845010b803450740e03c220400000c42d00800001c0b0380c121003603c160146103c01b40301c1d82120605024000349800c0c0b1090000d071f85280424813040e4510303442910b0000d21140f0b0a92011b07910000104030700f12a4100808000c00c40d26000d412201d0300b07046500c084001e19203200131a0082c11250001400700c1c0054040146088248030702028100c41150012455038a2603400c44643c40110340442c0b00740c0208040c400001d0140014001c400890342c1c7c464108800c500204002040640c00440040e40000b00e8044a000030b104007070042000b14400d514518050700c589840d59039103000182040400982d8000303012000c090000501207070415960105840c02009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 478366160 1250 478364910 478364933
    0xf120501021b1b010c11040e21091201090506070e0406090203010906140d12080429010504060b0703051b0109080a0f030506040b011e030b040207030c060608161707030f 74
    0x310403005090b4510711031344c0103c020880c01c0c0e0780080e400c519403198105120103000c0312940c040c801c0c0304043c0d01100b0110401901103a516081055907160301000d010840002d60030340c282c0380164902042c1c440464000f1a00c00d070f01000318109001c002441901180080405920012040341b02000100d2080301d960030000448001180c10000303540c404080140300c4da4181e4004004128505400d00c4143c003a56407107034818090504450001c0407a031b8140400600908011041c0c0c1ca0b013401848146000e1150320f01400300301c02c40c24200700e500d5a014080e8802c5c5a090508a694521b40c0000a84250458410140c1c003010954840b1903131a00074281c900c244040e8404642030100050310b600340391040c01040301d8160344814903040028024054072407160b084004040d112036070003483e502c840c00140401c0303110b6903a5004070400c1d41402c00469015420801d4142c12031451a44039003103100010b4103581440d59401c0c0c1070000c80300d0303581c54103629500080046500720401024072100300c218 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 478367410 1250 478366160 478366183
    0x1e1e0e090a0b09040b3d06090b041a090406060f09150e01050a030f061205060108070506070213090c060c0b0a090b1501170a0615020303010f120501021b 67
    0x9000c0306031201d01c40c0c442035400648074990043d0b209030001c0c02048141d00440d400045406110a81c1d0401141d100415100d840c04a11040e0002c1010500074134031402d81c00040584d8a4560707251820b201d01a41070784030300c0c424169840700f0401074040d0000f2010460300c540100800420003169141d00c050800801c102080d070200c0c40005000460901d00300084803004102c1c0c4d9403020800b140b4006540d10740042c8001410950354110642d50901148600c002900c40848000010b818900c0d116240800580014032160808001040070f52502c2c2c044c0d84a00c2d6044403100c9200010480307010042a1000029214022000c800580d098004201d94203041c0038480038a529900d04400c0300644003806002468050300c14005603191008000d9404981014980000410311305004841c03107902c00e40e50251083e64620040107003996801e801c0208100900241d8215890641681e0f40c21109125813055000d0848401003000001e43c1184c130211010203484020542000d000c0b07a59a40c481403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 478368660 1250 478367410 478367419
    0xa02210601051827250f0c080d050114040e0a1121030f0406121808130b0f2808270105130201110c0f0d0303060510020a060501050f011e1e0e 62
    0xb080040d0944c0d034200344584812074968100002ca984001c547c201d0795400251403408041c025640c5a0040340602c0c0c0c02042c03116a424050f004000c00c000403240d40034500200b41c3d20404424000404c00e818034000140c00b01c0d43c2207059901558611180307a185280c144840c04000340c4021000036000c00703001600c01d81c1e0780c1c0104400c2543c403a202116920380300b46486402087d0b00900003860034000780f419200c008208020349503101e0b2500d4040d08410b01182c050f100200e551840000d032550b841c2c001c1e40c01180785c20540e070302c110005403800b100a0156910303484c000010f42030718545000c036281295081c5c4020440c0b490030f001a901c881c6c031000d1003240010742c11501c6030b640d22070001e440242c00c038009088411200340b00c41003060f82d0030044802c509050b180ca03800604d0350f964201242003202c1d9a0050603110005142c403004507131050304210310903862001c9040090368000c81c001c00145024617401002c5480c1e220590762801c82448002e40c103410010301410030781d44509035200c941002d85 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 478369910 1250 478368660 478368691
    0x1f09051515030609040606050a0e06040e1504030503090715020303061207050a14040608030412060b090c07030302031005060d020c161a210a02210601051827 69
    0x20402584009a81d254401e00244081082d51a1514102d5000b40c8155000901c155448000c1800d140c90b540c425100a13400b070080240d2820140164403603180c0050107446010b000304401c02c1c6444028102070f04024010001481c2001b042042c1c1c0054030440030b80201c681e80d0400c009541e54800c0300d040d401803800007a03104400300002040c2c0140e55000b0001e0612030308066010342d00c600e05c0040e455005407690780010b900b0070b090005101401c060780c00301c1c442c1c51203401d0282c02e4540300900e0340d0003038a11000b044503039810f68050321030301c1768945800f681d240c90b510802024090a500041c0e405600007500c2c0404000681c010320a0a2100c003d440d00c000140352405400f80c0c01c2c0c861141c100c05646403260218400400500d0050160341414030a2815024010a0b4282c21200600010350000d154a00c48107240700b01100840c02c0050001140750990000b011805981806000e131041260400502c0e62220b40303c107104605282520303d07070300403070008008540b01901c001c086400d101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 478371160 1250 478369910 478369951
    0x31308130906090b0f030601060e0a03152f04061d0a091e0b03070902071401020c010f05060d0f140a0b0c0409060f030c030305310e010518040206031f0905 68
    0x83c0081045c4040090180c60103a03e894415149016451455540300944040c040000355602001e8201e10f0706500d0f0010301e1008881000200303514900c950340150460805003000002000c040703170140c0f05149001d01c490440340d00503c00c4150030201d000c3e800f82141c3c4004c900e801150380080c47ca120b0340925a00080e044544540c1110403524669400d5005200280240584c0342c00600b49644210144000c980c0c0030a02203007240c010845602499440d4003001092000328040c81c0d401c0385080743c610700581c20998410300e000d00c004030000d140990078058046400014000c59903510b412010500c0a441d281d2040d401d1a440760188041a0b450700340c01044828241070130341c060b039a0045c070029001d421620280c074990040e08038100d60107890914a201b02c0d030410000101c08604c01038101d000c0d424441c110080c0d450507040302c0c1c014030700c0c03810603205200481226504190107a800307559944070307450180500a466110321030040500760000a144845511961160701140c05650300c400c0d04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 478372410 1250 478371160 478371169
    0x606011b0203060408030414070605130b0301050f210a0c0f060206010b03040b0615122e06030207150e03180433080d0f091a031308130906090b 63
    0x810034040d401d0751100d40042c0c0010a01c0004503000b0307000300307425401812020036803071815007503801000000b00d001c02c0e0031523480c0c2c03030041000203400d601c3e120604542c10134001c00d400301440c50410340f1507113101c0418401d8440c034840300c50403030441301c040c1e0b100c241160400c1c100071540362240c801c03020715415000840c01c1c4080746160684103115202855038841d03403a0104614406410940d100640b0706881c0264103400004202010700032518241926012500d40c00c01d810240600350101001b005038001200748560120540b8018100141c0318401403c00200346174032003250303141d103c1c600740848402c910000050b0001441000d01d410b43e80203147d00b80400c0e902e01141810b20700801448194140d441158644210100f0354001181299130f134030264941420003407204041403904d012180166400721403030002d06200021520303160002c4080400b540300c01022424440d406000080800007403030200d891a044282c1c404104ea629104034000a040a114000300780303240c201d200866040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 478373660 1250 478372410 478372457
    0xe010905030d020a0b1f0303080f0601080c0904111201170d03090f02040b030102070501140907080a0206030a0506010c0602070809130b0952170105061303050a05060601 74
    0x181640034041c02805503036000a0f02e000a080540d8010306e2008450b580381d188404100194060350b02d00c101c5040031210b000711014054074141c100035000081140d1701c4240c3c82101e2400d501903400046140e40744a4903181c6024012980101119940c00020002c40d081016511400802c060790111195080c054044520031000205000310405084c80035182603070110041c0c03100980094030f04a15566503d00312941d41603407500210043d801c2c440203070402c02400f00580480c1c40100600c2506400150084c00014030f5041c0640c0c4400000300603034490b903802000e2652122066407100740c00c0c50070000c0c81d001140164001d5440c180400d4010888e40101c00d0000c1002c0c00c1000c06881d103035424000c098417207498040b203460450420a10001c50101c00c07486035801c040c0c0d004412102613440344081c4503124000b04001903401c4070b500041d01c42c1d010504407442111410354600d003400d400c1030399075203d40c805806030055006903030074848041541c0384074000990300e800564900c081300451841 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 478374910 1250 478373660 478373683
    0xf050708150402040209120105180d050c030f1608040603090302060a0c0e090a150b0d1109031522030201021210150320040f1403060412050904090606060e01090503 72
    0x807001c4041805030030140e0081240e00d6003d000800072a00c10384040742502c4054030f0403443e608140c000581c400c40144810380c14421a45001440d00c82c8920002e5600c1c02080d500028664001480ca4243c44050945081451384004401e454555500c0064000c050b110340c190054010800000d03e648260320944088241588809a81d40910802c1c80782d840002004001e10176034030109060700320b01c6c1c203650200030325090700c1d000d80c5c4901d8041e485095401d00c00005c0a846400d0010600c9581c1c04103034242607149002d0f600e4440e07910b004a5807052620340c240452003614940c01c9006040d03040d0002e24420b90380c2180203109481e418580d412800852040711400c404030140c5440051180d040002001a035448900141070740a611406a9200d0751061850095410f820840d22410020040001c0002c070003411052802d0345910140d10000028401080720009848045030346a1740b041110b150880000c010b165142d29016080c25150080c0030b0200f81110320000e0607103400100d444420b07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 478376160 1250 478374910 478374943
    0x3120f09020d14010b060d0e010e01110403080f070b0a0605041805030a140d020a0e012a0b0618010e10090e0705010f021f0606030e0f150a0f090f050708 67
    0x2030b02c0c5600ca8600c032102c103203001d4080b075490303101d1003000340e03a8000685601040e45000055202c070035500c1508660502d22503100d43c0e4104401c80c10701e45c52090959003142d41001140f6560525515922076034400d0260041c1101d400300140010800e00c1e50040c003d842d03058504120407081e0b4010180001502c030300c0240164810010815401d1191600540481e80021018142441224880240c0c1c120501c0440021040c1784061259a44149840c0c09241c420003404400c40c2c07240710181100b80349103009400146502e002c10150340740d99541310f4004804e00807010055845602811880300181e50742060b800a0300e40100c1d01c00303264400d0010024086c0010004280b5080040d2598500d244440f402d40c00341021000e03407000605401488c1240e16500010b08a060540140032580104e03000e4038240d014000c0300240034800a2030100d01940c440200c00c29540b0340d0f051001900d12012100580e03420103005004000805080045184c03088060310085626a156541c0d103405e91344070080030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 478377410 1250 478376160 478376179
    0xf03021e0d11040e0f0a060b0a1a07020105160b04050c03030f040504110403231006050303032701020a030e0d1e08060102030f0a051306030b030705150d0903120f0902 73
    0xd100c2c1400c19980500c054800718070302c5030f41c81225061000304010580345030008034540c800c1090a01c03468030702100440f859000103041c40109907600c03030002c01c0c103640074400044481c10340e8050b001351144001c205540c000d1000d00d914021200c64010307203040ba114400d82101d0300e40d52902001340c0744404070b034400031401c25203048204406401145012003c40d00c0420012001c40d1a150b06680c0101c400c6644130502d641040e6507529040c00510420034007403038104184900c1d40e010040f82d030441007084824103e00240b1940c880c8075020500040001e600c00182c00480a402d0340224003000c2e035140c10340d691080104410b46071024a08140008000040c00d88110980541d6056402407010700c1102d05100c01a48051071683c4050340c2000407580104602180c5e80a030300f101d80c0908040e02c1e040c0a58103e00001c01c0d176894090281e1440790111030842590b00c820001910b8041e001420b091001c03103218103000d0034603465800c81c0c0070114206085900d074a5030754080c4045141c5c1c00347c0321041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 478378660 1250 478377410 478377413
    0xe0102180f01230408010e071e180506010e060a0c021318080f0702060a030b3c0d0501050f060a080601060e040e0313030c260d050f0705070f03021e0d 66
    0x2060f2856a01416418140300c0480da0080901c150249500c4100003420b41c0d03414070850402c2ca810f10b0541d08008000741c142407081d01502940304004160326800031550380c8032500160740041110340c1c0280c000d5004110340c040c85a004c6400302105009450510448201034802c1081eaa20f80071145102c040c00085c180001d042c03140203098454894030950309080312540080c1c0c4a13409010b146000035252207040800386809080000c20034030600207050030354102c802ca5014581400d01c401d940000b680e41d1403c20351107400030100c03140d5014000300800e10f0050005030300301a060740c0396406401c80d103002040d02d240014556060f52001d480303820301c0c0049481044054130080e08910f40a000903c86944840000403001e4061031080448621080c206a8242d81d862000900c034005101c000b0001f0030803c038081181c90004840380b030710030341c1c9044c100c42e00c2c07800344145003000341175100b031150000b00380741c402c0c2c17030b4409507882226101c2c882002c002d5045051905860916449050b210b034110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 478379910 1250 478378660 478378697
    0x6090e0d0c081201031104060e090a0219091b030c050c0c0906060c010e0a03120603110913051501140607030503131b03080d15062c040e0102180f01 65
    0xd0501ca003003190f1920b0409000c1500c40c14080e40b013118080301803110b81000d460039000b1480a0000410151914604141e01c2582d82c80101c902030300880300707030410200d030b0f1410242a0026005010081c011098000ea080c800e100e41107800c2d40009140c40e0718a8001d41c460310032a51540640c01c018290316203940c0810504400c0a0403041d841141041a03031084607081c0506000b02401030f02802c035542c0103080203421003010b05501d284481c0341800c24030000f1404111114840700c00c1c3c03444100d5965a000281e01d0044009014229119000403810392800c0003d40b5030598040200c070000182e19074003808201c2c0a1118000e0201c1c500303100250004d07024cc5042e4142e80e0040d800010311509103400e4040b50a0a44c0042d01c0903000001c10b060720f04014026040300c0111a01510b403031a00d030240080c90011103070001c1c04000d4070381c401c280d9000c08810203001170030320041040000d44c6903105514000e6004d589500d54103000000d541400c0d240003070007680d0941040c2c480280c500302003020b11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 478381160 1250 478379910 478379927
    0x14030c01090b060f010f09032a060f03051b07080c0a050a051b030d0e0103022b022a0a0312061505030105120c030709180609030e120f1507022e06090e0d 67
    0x30b0400c5c90000031035659089d1000314180246081c1e280d26110344042c5800505650f4001d01c465520502d40b00354480000500040340c002c25001014140c07100d02c400c0c0074a09000b81020040d06e20302c100030030881840030104050300350060b284444030800a140e814940c4903110b261040002c00d015065640303243d4060740040402e50003d22640c8144107051104001f002e0b142c46080d4140c582c04903854400e44407803400004503080b45204a501c540140f0441035845100520050400200d0903200749402002e80140e03000e082d003140220b4000048080080c0740b13400c04d2140d18819100c040420419841c040303015240c0003005000342c0200b904004c501400f42c900c8083e010303c1100400c0710f54021402d28410351030fa4034841c0d0b4648010070000400c01c44116520890144680c0100e41c84c04210100000d02d40c81c1e04203445181a51a40c40e00d80590074031311014940300858041060400c091003928046032801640e01004100c0b450710380a41d03904648146207042216032000c0700306102e45000382d405 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 478382410 1250 478381160 478381193
    0x20f06010303030b030a1209180603080717070f0b1e040209010521010203150102010606080f04030e04112107030c020304030813050d03031401120f14030c01090b060f010f0903 77
    0x80b502c1c46d404a03581c0d0400d40c04044a0704d4001540386105000c04801211442002c80d038000082c4280d6046403070b80142c1c0c0c030401d81e004040288100b56030300d240007030301d0070b80b602e40e030304180e0718132001d909818500c2034031f20103c41804514450380c0781f2280345065016640d00079a000741c56400260708010a10800012854422203040b4195800c0b201060090005602c102c8a41c645a90211382c02ca00180c00d4914940000042c02000010480032100700b000081c0d0060305490180c0c6114006004100100000580c11010240000e034200c00c4500d400c040d0800741c0755050070b403041503942640c103d0407103244183c070400503001003004002150b03006c000340c5040f811a614007100700f0382d5400042e2424220100850120751100b15180c0702040c00d1a25a004242c503d01c80d804030724088c0c0d22900c08840101004021704008a1040100c80c01007040c0d600c0c6041100c000c002c5049a03040410030440100d400c0c0344525015010b40c4001d505c00e40c50107a100c043d039240c0d08849415a0703203940902204249 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 478383660 1250 478382410 478382413
    0x12050109020a0509090a060c1404060c02210d03050a0213270203060607030804021206091c0207050f04021c0c030b0a120314030403020c030d0914101b0503040b28020f06010303030b03 80
    0x100d8000d04827060006000404540c1c803040190007851040c080404250310701d880c504801e82c0121010301c0ea012903145030003042883d0014441e603c0d041064020f024100e4a6003040100c15401300b10048401d0494000424080c0c15003a001072600005090344801c9610b5504007805100f4280082d01481300c641e00a44010f14606d2407848039400c69244c070f18101c0f500513003580305299030341010110344800401c101d41440500151400c0001155040756600703403e81c01940c0c00a860040c2c0403407518078031181c5041000c2400007510007000140a00000300351544030b81040c504c00070f010001c0036400c400781030340340e100c044c010442d214481805400042080e0f00b5400380c01781c101c2455900340100b4401c0c2405440710781d4200d040c44045030202040c3e081c250302684d00150a000041d410141c2280c040030016030640e0520401e151940c02c5000720307845042d07642d1020800b40d510101c0c1120000071241c01901031a41081140d030102d95424540780d4402040e00a0001031000c24881d411012183d2800b80 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 478384910 1250 478383660 478383677
    0x2041e141009170105061509010912030c0b1609120c031412040e0f0601030e0c060328020432040f14240a0506030a1512050109020a0509090a060c 64
    0x10100c00f4441d082101e81d2085035034560800215203040c2c0085400c42070f12208050800000d4000030b0300d20f079064005d502d0b130280000305010805101d204600c2003550720030420046800c0058000240c1c454405032040800c001c8103000c119003001008441c1c4154100c041c03030596a1950f101d07150011782e00541c201d03a5000719640e20840000c1c000060008200c0740d02c2c05569443c1402c2c00c4149002c01030250350401d8100302030301303041070400201c604000d07408071411135403515a2458502e9000e07005000d43c421103080d10b0300f00c41e21291176010b0710031a010301048240e522000c0a0728400d0303980c0032024a64407025224000b41c00c0c1060350040244440843d4002001004050000052001111614003912074044000301c03040948414000003001035401d040e22504150028256000062140c07243c50790720f08200c1c1080040c0d9a268001f007032003005500180781241000c902030510020b0507030050b42c090200040b1410906074480c8103082c01405018a903403295640700c05459900f005004000e42030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 478386160 1250 478384910 478384919
    0x60a15030b01080a03081e06040b04150b0304060c0f0206160c0221010b0108240f12070905101a18091501020f06060f12100203040602041e141009 64
    0xc01c00314082c00c04100240390f2040c091800070190b02000300041030007448103004400e03004d80c1d880d101e60001421500411102050000304c4c0052101c21070441020303002480c00103151003544010360159004200c04e2008030082c03101500c10016074130010005a100d84000f4200301a0949600e80301940d52404042d0040c41c9d400003a02000d02c410380c0640074105e00da400c6440682442001206a4282030801841c40c203502c0c0c41c0c0c200800301e25810000b182e403052041d110b58915002c06108a00145401444a04400195502c1015001e0700e02c0c16031410011848030740740d0920580440e14580c111044542001e0111143c3d0782080000a6000700d54081041071a941c1100c424441c01001c2c603c080800c113554002403402c0205503013825150061010311402c0d4407281e440c412508010313200010000000003030303a0316040305060303100301440c0701009000401101e80c0080c822600c1100308040041c0b1030140007502c2d440d05100341501980401c03c150218106114629288d1109007014040259035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 478387410 1250 478386160 478386173
    0x509130b1b190504060f02010c1d0a0f14091b0a0f050d110c0d140405060912030c061006020c1e0a050d050115060c0c12140102160c050d05060a1503 65
    0x40d050307800400c8004c40e040c060745500a00c40110034140707100030f0010f00c2c0c010f04003030601d4100d0000c001069164400c1d81106484004001c8010100d06001103040b036521200300050b40d003940031551161340c000c000724102d000c41842600c00e0001c4401a54a0f01001d14000c0d1007013000c004008041c41814130542d09101504e1240c5032400a03640c418070b960b40341c14089075092052801d0b4400c140b060010404860703c01201c251001e481c001c2e110640d0700c1001d200010500642043c00140600c4005850440781001248440c0500301880b00745c036280d40c5545059844031000b8031215002a07007e90402503002c00c20350382000c516405403c8804441e00c0f403000c20780b1074bc0c82e11800e4400769120416050300199040c508801400d80b443c102400481d1955000c0100c403440c031801034408001071420080c00b43c5681280307506020384000319078030034004410013900340e00d030b85080c0c0e222000b0810025a500f0000039030074049074410003504c00c0342d655580c0d46005046424007130310454000310780030000444 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 478388660 1250 478387410 478387447
    0x5120d050d24030201140a02120a030e2505010f2c0d0c080f071d0703150909020102060c03070207030f08090307320a0b18060d060509130b1b 62
    0x10095100d10b29425800090500078503480c1603031500d5020801e43c0c5210317a001c2007440c90300707080a407180d90b2441c000700110064094028650f1141c0a040b10350b8101d55081e00c480f400304080106590413060b611801510704007988c844520100e81100c03803045000da400e034100c656042198142c4980a41960089000c10300b500c4021508021075000c00c2c07101d00010003032806645c4c2d008005048890603c011b40002e441c02c80d456181c03464820001c078269500a4020450a1411601c00040e26590302d2040010788034041e07043c2c0c05802a070010034a036084010440f403164005070001d007a440d01d540e6810301d8603004108169150242031022950b1542e06000e103000130040da00c10400340c4000051038182c100940280c0b14804003e40d5200d06d4603032070740c6520b9000c4036144a9038580301c104084040b12884029201651702540000b00022005415417108060b1102511109000e941c0c1110b07030200819004805000a81c07201d00042d4520000610102c4d1030816401181c148880010880c82850 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 478389910 1250 478388660 478388711
    0x270b0327030406020a0506160f140d050a06061115130f060c1119030f0f020a150f2304080901050c070807030b0c1c050702030702031b010905120d050d 66
    0x20402c01301710701030200c200900b581003800c00c000d01c240300e40308801c05048880d004a008042c822480e440800b000d074902c043e41c070300650243c0c0501c1149031904090005000c14051080801c054a0009100c04000079130780410007030003500502e141d01c0d80c1d620154060315040d4203d4010407800340040c00150b15008041400c3c0da02d80380c0c80300c4003400c6420203081001c0300810702c4061080c0021400480d610002268200c0900e0070311001c1c00b004a0400c81c2001c681d82405000720704450805c400201c0503a000c00d6408982650400074000d0000e00d8408201d951102c039075002440401140c00f080504001300b4070000141030085c9401e00b1040360340d00780301055000e03c0c0d00307400c091420000d102c104019280c0c060f41ea9214180b40c00c070b46016108003050305251850505580301c0000788400d000700300f1580e132a0b40040c2140d1800c810b01520a00d000b0705502014001640350b1400107a609044480d0800b80c00c130100501511300b60464200c8242d040000340c2c2005989500e030464a602c440c0d002c0c2026032 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 478391160 1250 478389910 478389913
    0x130201050d0f140906070f0503060906040912020a0302070f0f0e0705093a080a0305090c030703080c1b01020318040f090f030822080d0615270b032703040602 69
    0x145041e8184d1810a14010065418414114907500c1c0c0940d00000712039000e2401ca0b00c21005c0e4450201240c001c04072220020b00701030588908a600c40d800003035007920a442682103403202926240c0c1da105040c090720032039083e43e03900c1105100a50a12038182c1e070020721440d00c01d080c82c2c0c00d0000100006140072514200040c0040810100b01940b80480f00c2d0b19041f015410883d280ca81d00d142c418400d00f07940d2401c0581d500d0100714202801d00190f040740c4001000c03507841c6620703824041c8159101c00c0c0e42103054440e449005074041290315840b0394216058018500b0032042c2440d202c4e1100d071007440e036980305554442c5403200d8500f52140c41c02c0756000e00ca505075003101626000d4407442c0081d000310880010f00e804c110455100840ca0742d0b01d01c0d4421001d50325081c00364445c80240205420181000582c0c000c030310386541d8003507003001e46050459840d1854001c00c0c4c5035810420390314010040c0548042000030100e2461040c181c0e0761494800300d4095520b441c0c1003a0b800c6030003942100005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 478392410 1250 478391160 478391201
    0x20c160303030b10051c0b03011b0305061002121b0307080a1d093c07260c07031b050304091d1507050c0d080402041103130201050d0f 59
    0x74035a00d4425005500016100c2c40048818003201900b0f0340500300209040303454602500900c2070094000d00b0b00d20401400a10442900c1001c0d5150b002c648016031b00000d20313050020b943c03403a2400c900125850030760040c255148040f030541d0070541c4140f145000c400c8240e110b00605180410080600c1c83c0211080d079161030b118132008041c0c400c101c0e003280d4400441c040000072940c81c080c034150400d0144034265001c200c0030011030120b5400e00082280c22440381c2c60685403040107a0302a1040e10700f9039603013110007110445280c03050683d01103071201c412143c0c00034044034140340042c10400c2c02410b11041180d141b42c2034154490810504850716040814104046035450041c85440031a544010110900e1b1f06a8141d49601c1c140104001c0d21505020a0041e0f0064040306c2c9080b584c01c059852407002080040c020040c2580c04901607498003d2110460441100b0f07a0301524901200310569407098004461b1500448040c1003019035581d860b21642c0030610420304074100d0407404020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 478393660 1250 478392410 478392413
    0xc03080711040c0e061c11070209010e04031706061204120336080405060d02031b07020f010e040e0f0601030203010b030105010e01181815050a0606021002030a020c1603 74
    0xd0282a00600707500540c1800b19150000740c03c2015010310210075500710341c846400304140140408041040c0c82138600d045409510b0040c0da000a0485600a4507a211581d03079540f452080c94000b1103000c0c0019600c2940c48850094410b0301c160880310042c01c840c1414150480e810305480154bc5c115540c8120703084007580182c15016900b07903400c200241d60845011041d0040140400b88540900b42814130400f80401100c00705507400340402801c06a2525424020b01d402548150b03a1141d0b03068145e6003080d40107000d0f200315078919a0180907100303210074150045d1000d48408106070703030194903030f010401d9000e000c1180150031014603004044551440c0145400c403042003c10314002e0341060010f006c000da4014080741102d8100d00760b01c010007540301118000308030b03081c1010b503e00036000245051050158030a045002c055400300403544402c1c078658101c5540303200d0305000d40c01a901e200b00241181d4055903118401c06005817401107443d03030f0340d07003447c0d01c40d10000e4800c81900010710 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 478394910 1250 478393660 478393673
    0xc0204051603050919080915130f0b090a0608060310050720010501080c09130210050d05100503071505040f150207090b030303131104050123030c0d1b030c030807 71
    0x1030704504880050002050742050900da00c14171200060a04007000403030720160703191031040d0044581c80c42c0000391901c18120303099903012900d10501c441d645880002007200f204540c1101c2c0c4180c0300400c0603441502d080b03003d85400304010422a414060445c10f02ca9010f101c1c080c06100d01450380d00d000084200c401d00c00c04040d604003041000360714010051140000004240c0303000b660841d5440c241e555103c0c0444041c00e8403540094201c981f0005001d0b900b600a0040d081d42c1001703071418061940d0b1003c1c0b030101e400403481140d070726901c44101000f085000601c1c030a0440044d01e4914a0541c40e08440803411200703a10a0030000248a09944407503030601c00704014100243d42030111140c6000082e9a0f400054103106110401100754400c200301012046d0020744040e20a01039580c2d179000b002c0c5d0200c4080c8021303e070f010307040c03079000c580f40345c0850700c0c07a0213010040c88200802c143c1c0d00c40400c038040e11340342000c091421480100101d0001c41c07003200154414000182d0f503100d1441d00c80c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 478396160 1250 478394910 478394921
    0x14011b11041406090a0b0303130f0504050106020a0c0e07050d02030f0106031404030e010f110607111e0703060f15090b180105061204030e0406170f030a140306010c0204051603 77
    0x704030904642c07041c803240e540c039000d00c2c0b41c105c40d0b400c0d004682203d41c0d10010b81180b088811050504e44102d400150301160201003208441003150108404e13a602c0605988400c8032140007010b2512159085c440c000c020282a42c100481c1e20f44a42040039003d140c0c001c80e4819904500340116140c010021a0741c036000b181d04c2e1440c000c080c800107007425034000d003280c11b4040306d20341403014940380305084903c210142070900d0148011580d903400e0814010746118644005c0e21380c1c038050482c010625032160050300d00400c210900a025440c40d68840000602a503000014059240c07039425110412241d0100042e1600160004a1403010010002a4500b80038480358442e2444010001075440d88240e035813000000c0540012507071580b034119600e230720158009600170325107080400d0300c510042280c01005400c6003182e1441c40e8142c0381039038a000d40c41e000341c001594402c200d2080c1900744055900180107040c04003106240b070b40010141d6904444603010181d500c00c030429082d0741800741 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 478397410 1250 478396160 478396181
    0x30c0323070305071244130312050907120c05030105070914091308090d0b150a0f0803090d0510020d1b0c031209020d05030f070c0e060a14011b1104 65
    0x2009441d440040108046c2c0340c000403021a002d26012400d154041040c154803400e1308480c82802413a0800051014031401c0c4002e8000864040c104402441148140c9024800c410b0042500514000707580340c0c0310101c50030484011845010014942d00d0900030903010b0081a1036031a0b449003000b003465900030410241c0c0b031080c00d0300005d0000561003044400c050310341002c0c40ea0340da074010001052603841c480000905d0a0003642c10840ba02068441215210500701c40450b580d96844400200d0101a4001c91100360010030039000c251a001c12400c120300d1003a000d0f2610a25036001c4c1204030703040300300b4061201e40c80b411120680c02d11541060030b810114104a0224607140e140100a42c56680e1a00401379071a02e0311000c1d507460003144911590b0100840e03503030380401c0028007110f030000c030805c41d0602c180982c042035400c02c013011035200f5140644800101c0e0302c0e100c00720143e5611190164103000c40c05a803003040b0248810551042409181e401100070b00a03014441101e0140c02c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 478398660 1250 478397410 478397417
    0x8070201060e0406090f0f030e0f01020105091b0d170a030b01050705060415140915010e010806040201231305030d0e0f12070e0708091603030c03230703050712 70
    0x1410b00c0003485458030103030070a80016000846020601e481c030451100d52101070000c030310042c500710805500c20f801c61a28042592a50b03107140e010700041e401e80300c081c1c2e5104002d400600e02c004032861008100805101d004202400c41c542c15154998035003c000410700045d040001c42880b4981c05000308004403c003031230003d1070f003a16500e50b1a11003801070720040c04c41000100141200c0507a41120803180b42c142c00801007400c0c019410395941001c02091404100701d800001141034001c803400341200d004101070455a6915401103c119886000c40230202409812150450312110702410400c002203c4143c2010b080904251074a84c0d0415480c0804c01c2c001800116a1503030b840c1c01c119100c0039605503500c80f5038075410380e040207903981100072141d4000b0704008510740c1c4181d01030b0003621244290368800742001d2541c02819202c1c04050301090b07105000c5000648180c0303006c14820706a1601151360070306412a840300fa8045281a400114040f440c9000e000030500149a140d2840c00d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 478399910 1250 478398660 478398671
    0xf2c190b13111c0b16020a060908043506130f0f0614041a010501171503030c0106030611090f0d030e220f051017030f04090c08070201 59
    0xa480200040009249815a500503884042000002c03810780030181401001d0080422801002d20f81600d0f944209403044518100442c500c240c12005420484d50700364050311080005844001c0a002a840f040712208800c00c80018a50388000c11707090004000d541c2841c1d42e08600101407030901d500b00d10307646c090700640c003804a0f484009440b100001c2d84400c90040004250030440e000403086403001d00702c02d0800c030b190b4400040403280755218074130901802c654058119641c00c5801e400b40074480c04130302910160320a0328a00c008a40d03110401c16116000d90ba840d40c003084c199044580d10501d5a91904420320400031b49000d800c00d1031441080460900505100151442d0a801007881c002c107044140d22041c1841400c00c0040b0080141c2080041c22401e101c119840203c00381c91201645400760b090501c0c6164023815000e4000c0c0c0150230700c00d030304000304144030995404420030203110130071042c8050034010b8040c0c001008042030004040044101c0500390403030040c0318200710392400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 478401160 1250 478399910 478399913
    0x1c330509360717070902030906070f0203070302060c07330c08090d0f14190801060314160c06110d05130c090216060e1c030e0703060f2c19 61
    0x55002c00c4072a42c1404220b0500300c000c00340d08250103500310b510300303900000c1040410301c000038215000303140e60780e64480342c1d00011504130707107034002e13640010300580008001c9040c030783d071010180c82c610340504181c0f01600d4140d24804480b5070700050760151840c2c3c000d82495040d1251150015079405424007c2441c07030f041200540b81c014600e1008240102d01400d81c035072504c04d01c0c940700d07c1d010007803600e659120901d103001140c038202d80c00000042d50403400890482c0c0b00e40030704000340600b10002c1d052500c2e00e07001c040e244c0c00c15903414820049041540404500d0360b0149180c8603041100307540d039a141c1100f0701000d66400401c0961440300c00340703581d40040c080c035405904454800000603101c1c0d40310041024414615040503040c3c0381440817034208520701094144941510200c55001c1603003200e0181c0c1541d5454800352810b801941c0100003062441d00b00f1590072104800000d0440c24900d665211419051181a1151109216413850300e004010a44c051080141c4228503020103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 478402410 1250 478401160 478401163
    0x60a050108060d0f02030a050606040617100e03090a120b060901080d0e03010605061c051005060708091309120e0d0c0303110a0204111c33050936 64
    0xa040140144030384000e05080c000d00d80f9a13800d440360b00070243c0e4058152420b01590b9003000f0780d03c80c0c0c4980c0c5040f40000e154401c0701d400020428050005d090b903840310415007801814050000d1880f400704000b0003149548140f4802c010b801c118420070003500c02d0f81000d1254007002003100d401901c00c140140840342c400200302080013000d2600c25005200d844c046405401c05510040c2c1064000c268111400346950000c3d866468a040420003592050074024295106214840d0041c10030040c080204040000800070058041e00c41d580c20301c0d8508420b41101e2500c3d0701035031450102c0301c150440303d9118552034428401198400e03106034103902e0340302d62030a05200040910029400c01d06c038502043c012202c945030010300402407541c1d501400300c410b90103c510552000034031601100d268240d44255030306c85800084258500d421003840c2547e8440303a070042403003007805000028450b03642d10202030ac1000710a4039105004e4803282d80c184d0501400d5044640c1c2c01c441907000b6940c290 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 478403660 1250 478402410 478402427
    0xf01060506042702030f04060e1b04020a0504150203040e0a111c14090f3901090f0b0702040609201b0a2102030319021803010f06060305060a0501 64
    0x42c2e14410341031070109036454045110211005410b00220800040d014122406c2e8030541c0110340512447c4500500301c0e480fa103030003403141c0075640c1c0c04101d400700f403c140d80038004012103030a11034038098030b4620200e00d66140083c0103006900000d1b0602c03608582500c11900014140d8050006145801900145000700b0040340143d08280103801c01150454120400a9860784c1103820305041058080b0340f61a000001800c00d4031a00d0b5008001d18100c500350002c40c805e0300f10414404400807521704104081007681c40c1008203e40012906a0000204c20003c0c0400c40105603240f40303e105120940d05190b001e144090301e040e10550203083da010280719044a001c1c3d0030380d980c03001121074030a0364032403130500701881c0301e81c00d91501049130030544150145880d0541d94613404108000300d03680d20003111820000e0b03184038a0000100c2c9150058101030a400c6c00c60710301040c03d800845d084607400c401250405442d450200031083d0107110b00c80d0000019500d5610081c01e00300040e04001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 478404910 1250 478403660 478403669
    0xc032109030f110907120e0309060327100504050715120506060f1b0c090709120302070512063102010e040f02040b0a0810210302070b0406020a050f0106050604 70
    0x1030b440701403402040a400300006200000070944d2800e0b0529080080008504c1c1e00480a16460017006a10b1400b000041da54080d0740144107a1450703a03400d2501c2161600c11046000d51900c4511201550105200c100c164840c858400546403819003881c41c40c0451a500460301e680e0440885640c855008220380d00450042c24041515100e060104901c1c2c45500c0d01400e5801011403800342054001c601e1120440c1900d085415070301c248010401400700907917264020841a550030440d0446074a200e807080b60081c0180d90441d0394072070100e408060301540c1205907070403142c10005a07900c910003124511003681d00625101e01401c0308a495042003ca0213810321034882058003056450b6080f80c100c03283c4442c010754450fa5145802e200c990400070380340c408910f045001450240b03884ad4000308030781d40680642c48900e03801014500da07115400d0290114004c0700004916032800200400081460b81d000300741000d8142000c904000c44841840c0d0170780d0503c0e40c00c001c150380703400940f0b0541c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 478406160 1250 478404910 478404923
    0x230309030a1b02090a2408030c01240302090702120f09040c020601030314090d0f080702011211074e0908030a050a0c0623090c010c060f02160c03210903 67
    0x11040049280c800404400740045450046c00300801e5030013000c8050003001e403640000307118500071180d04070824600c401c0c031545a94003140042016140c00e0320340c5a003181c41c0e8015560000b80c000300b0601140d2114901c070048810000700d8102c203041503c1019181102c40c030180c91a07504583e4001d00001c038000e940e81e01108045a0285c590303807800380c044038203640070113944041c0140b40351598440c2c01c0560182d010610303644443c83c0d400c5141c0562488417818459052402e0b01c59511034150342d400e051004404031449441070010202d804560800d080080002110120b560f205560104182800e000170840301e100d0400004000005442500c180c40c03d0681c0c955518080840f0070100c109400b428060030000b034208141c80310b449501303030bc0749281d0710071000c1c1e554840060356903149102420b00285154900e40c01242c0c56501c80d40b0070129040300503140500300640103800c0c40000105540e4106850020030400c4045524001e00700510380312080f18034a000d0018008010380c0c4000b9110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 478407410 1250 478406160 478406171
    0x4081b010903020d231923040312031107061413080904090f0f03030c0207090c1b081603110c0102010c0206010608060604030602030703020705150108070303230309030a1b02090a 78
    0x202003100034405c00d2a40c2c013010300f035203891074407824281c0182041c0c0807a000c2400320224070543d0f041542c1c000030404035891080c1c9031030b14551f1100301d1200c04d0342081080690390042040101d1200e130003000c805026090118200740c0260400311543e102419101c0500000c030000e0002a9800040e0f4140840803600003800b00311504121103607940110000b82040c4a04904c0d600301605a1f0100442900b10b6007120810341c1c0340c0c1d8810b411281100300310408650628550800c0c039a00880f002d06007071280017482d0401140383c07130b4010f03080a0090102c01140300c15140801c2604d0422960030a02c2091000740500078a400000c0d454a00c18040e80d0100320a000c00940030307440d00d204640c015548403608540c0c0e0700e01454014000d400540040f5101d011f82010000752007941b94010741a85c0c40d2038041c10782540385540c280e40011928150105120f907104124000c1107085000c0e5209910a001555aa102820004000301c034101000050702d440d070001070340940c443c03a07891940150580d400081 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 478408660 1250 478407410 478407437
    0x40b0d0615080307050f010515060d020a020a1b0801050f040807080d0b301605100311130f0b030103171c051f0902090310110c010504081b010903020d 66
    0x75804402e4020240c58800020b10030b042010000312204504810030080081d600c030350284140121015a07059803018041c0445440d08078503900401442110340100d401d0380e040780c1d58402f5032840300381c4101c07101190300c0001c200c059400e00030a80d04c5010240f00040d50318060b1b071500f200d4080c4880c090308a4001041d2800c5a0741c2075448402d005400038607c0c41101e20341e01c202d00c05a079000c400500404109654200480030010300c22000c1c0c9844440e91261500b0001402030903820200750504140e160f2640100c070065100003090414900300d0b40012081c280580159456850b51007284001c0e4204010404210400c4110042c024482185640c4400e040c01c428001842100c15140b218504810720040b10f001482d007100c50407556083c3c107411aa5200ca18040380115218180c240d040701d42140300e0700b4160792213280080c15152041e401c20504500b12421900200c500319000c07000001c14000c4412608001d0743c0c0b80540d8002846901c0b0203690080d103a88440210b00d0170702c0824940d044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 478409910 1250 478408660 478408691
    0xb0919090c0e010807060e0906090414030f04080d020c1005031501030603051902040c0203070c0e091e010504050c04060b090d1115070605070f020a17120a020c0705040b0d06 76
    0x4001c0801c00107070b45565842d034403040c1e01c602d9030388a40700102d03000c1030048803681803100d0498440d142c0106518802c1d681e039140c8040002514a24a800c0d010420412002c11070401c041d002410001c0014940700f01c00032000303442c2007000c4020728480c201e250150902c05901808880e03100844210b411a43d502c040e00580141c030b16500000c119000e000b40a030054401c100001d20103034003c0f1418002000901c1c03080c0c0c0c1780c0c4a60765014001003404c00080c0407080d146200a500214160121800c140f0261030001c181040188400500d946401c18002401300400598251000c111410040c003440e0520754003441c450801c190380140e1001080f0b200b840744200881c0b580b00b00c040c00c1e00061300074051a040c8603030b00a800c1154074501d00004a1560340c807420141039216a80e800030b10180300d107615550403070185801d0b0b19121010401064a103104140300345805424500c00140e107505140340701c54108250368200c01d000d9841c04000c1851581c9025210500580000001640140d0302c510807 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 478411160 1250 478409910 478409933
    0x60f09081b121b16030b0403030b0f03030a2006071805030d08011e03060203070f090801110417210405121f0e01020f04031b080a050d1b05120c010b091909 68
    0x16213101e41c1d002040c005490341c001d100303034880d6408200324401007080102c00201c04105580591043c410700346054041c0c82e800f001c1941000b80840003052404280d442d040c000c480c5e180004120042e010000003090100310702130034044025100d480c0c1040c070024401c0105129103034008a20700c08400300d1440310081c10002d580c201d50155640d14201001411040140f05810001490040c00203440ea00610036400c42c92031000140d45083e1400b926503020a0203200080d0403406a0b0385c484101148030490750314a00444040141c48034603200400038131410000e41c0420360f8010814103171981501c030340d04c0e200440101a0000c0c4485a4682c054024060004070301c2100c14002004820311006061000f081a01c1c803180142c0f5a40b01d1181c030352035180451000f0074070742c000c07100c4c4045a4000c0350b41f10804100c159810700e100482d500c540345020040030103070111010000351030480510038025040e402000fa2500009410708030803180c1f1041c12680001c0481d503031201848200308410441c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 478412410 1250 478411160 478411183
    0x20918130b01080c03070801060308220b04060206160315051003020705060c0d0c1b0b060d021f09050d023a03030209030d0e09060d060f09081b121b 65
    0xe110440d0b840c3c2405650f02c01c0140c84507032184c80b0342034001418003414051082070301c2e80701d103000382810f40b0181d180154075541c0e440d10701149032500300407921460a4001c1c2009100035401070000b400c1000501d900b9440001c129002c041c100f07500d80703004100003080001125400d0301e440b0303100400750a00320000c1c043c000c0010281d0298405100c0c00b040c4000140c04da5002d901d02c10004c0210207001600c41d908045003400e00c0c001d0b42410080451410121680d021102030259000b50701c039940003c00c801000c1161613155100001009012a480340b01280540400d42d00301c2a4044180c0014510000540528a4a144200c07801da50001c03400d00e04142c51302c040a4240342d003507991801901035001544411f0113031180354000e09000d4441d0220b0304003c08060100d40680d00c450061024402c0603040580b856511041070303c05026982c03040e1030010713001390410350700c0700a141e00c075114070400da802c8029140d000d881c620702c85208040456003980c401214042400304e210540381c0c03c0c050404407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 478413660 1250 478412410 478412423
    0xe0c091f060305060307080d090e061f170f070c14030d090c080f12090103020a0207031502071703361e010e010510051219050a031202091813 62
    0x110701c0d4040d0003030b600500048050f15015515403040c50380e00c84000c100d590000e000154100700041008041d1504114043d0405480e41c00c1000d600041e10940d480c8040081c03082c0c4041480031017032906c100d4200090182450180c18000b00042541d8800b040140c40e20243c003480d070014110403c21100d064008500c00d200c031100a0512441804c464803520039503000c0c0b61042c4244483c0428441d0440443c1e88a1908003410200110700a42210380d048040d48030b240381c040080b440f54040200c080c0c01644c03000da5610310714070703080e00741001110132a00c0300b04051041c041028030152174a41c40d1068003a01c0f0603510308107814140e91404d01180c0040714013840d04803141c6120540c1c0910f190044d240000c1c400040070154580c03c0b16070454902c000070900c2141841107180c00d1030040c0c00e0710a01d004652031007241450744003c030180c410701201d036076002030b054808040e000103920b0000c1190322801c6040400e0f4602049440c08001b400103020a2101f0000e003510520b000f040705102c1d0080e6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 478414910 1250 478413660 478413721
    0x3020a0504080111030910050105010c0f2f0111031201091806060833060411091203130602060c030a0203070324050a050a1a0309030903030a030606120e0c09 69
    0x103e081d01260b00507225107000d4001c0b48041c0e4001111400b88c98121003060351180c3c0100c10640f40c0c038400c406130380d40c116043d08482d42d201813030141d44c42d4104031152006811700311217803c980000d044c00641042c210038541090184011000b010703102c131411603050041c0403400407003800d0000d2003000d00b0000100709520b170402c0450418000110b1040440c80080d03d00d141f07031041c000e181940e40c41080d09911020308040000d0030b44c181a00300e00a20540072840702c0c1003051001c001034040516480b0118070382c1c404030f00702811001c1c0c1810900140581d00181a150070100180e03035043c44000d08000301540c0000c045030f5020f119600c10907035590554a40024a480e204041e1000f03e420b20500d0322820341c1c00c902180c64a0300800e004200c41d42c08130803000d114a0809891541c0d0802094118180410700510315551010f100802e40c41b031140e41c0000d021030810002800242032110307944611450304284ea080c4500005503030302e00f40d10480310b0400e03950350f004e8411900c81c16a0a0540081c4200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 478416160 1250 478414910 478414931
    0xc090a18080a03050606090d03030c02030409060e2e0b0c0a02040204060c0c090204050f24030c03010f080a0305070b040c030c08010e15060904120504120804180606050a03020a05040801 81
    0x31400b4002c2981165001c2c009901c51504000040c080c4008580d4820320282140000038080c0d88016007094490040d40d081070b0b40d8154080403200d9690250301202003610401c680803c000300c1c0208109401d8501525140c01d400400c11f41441a004000380d803a400114148901000c0101011265005105551312a190300004050320259081110340c062554004180c00710703d030086c0d40640e41d014041d0400d0002ca03400300600c08503040310701c414400207001c610780c51015031030045101d0100e11450302d559505d8110f00c40f0588140758026a840d400103140707030b80082c2d845030445440c1604080b00c0f001e90f48031800c0070140010b1640c4000d15400251800091003d4190405056582c1b1401a54114660000314503441c0400312191a070280711800000c00040d600503020001d040c0a01d06139003000d48840f456071929410440903501c1c0000840d041220361f5031a841000614001d0a080c000345240050182c45030003400c00c0030040c5034001c82c1c1541c02520403802c1c0c0d00100400c00c024004103010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 478417266 1106 478416160 478416173
    0x20c04020d0209100309140c03120711100207060906021b0909120f04090b060909010603050711012301061404090902011115160903050c090a18 63
    0x34002001e503604d581c2d041484040c03280c2c90008a41c0d415007808020301d04810755101840c8e004a4400030385032170104401042101284c0d41503102d510380d141107170340c20804c206003a0f000580b2581000003607a0000d030007022110300e92580c598041c1c40b4036080361200c036550009000004c612800e400c05041242a203070b0301c445008240c50103000482c80207451607109112240c5001d901003020301600c0114410036864180c100c840301e14021a4201181403a48144604018196507000050500b8040e4051000040c1150001c0140c13400e020300000400e448800703046644100342d4000b02e541e0340100c90039480840d031000c8242c02c00745040d0810000c0e04203c2000c0341040311100e040742982000704501c0180750943e031801c1c00c0c2da03e4101c0c182c100e01e50294180ca42044070026041000ca01e000c2056881c0c1c0c03405480040180c1c0d500318580c0042c0031044580181c081c44210240d042c40035 = true := by decide +kernel

theorem cover : BRFrame.Cov 478237410 478417266 := by
  have h0 := BRFrame.cov_init 478237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 478237410 ≤ n) (h2 : n < 478417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
