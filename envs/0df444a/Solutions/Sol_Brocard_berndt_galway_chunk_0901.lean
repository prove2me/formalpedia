-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0901
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:35:41.95821+00:00
-- url     : https://prove2.me/submissions/847dc7a6-ee48-4288-9fd2-ed1d24d480a4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 161870503 ≤ n < 162050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 161871753 1250 161870503 161870507
    0x3080a020d140414060c0a03090e150108061c081c050603010b030a03050c0a0c060903030e030105040302060a11040b03250903030504180f061806060203070c0506131d07030c 76
    0x1242c0c0c041807035038152800b403405000d0408620700b0208a5402282045940c00502c4200824145079101c0d440d0f0154841c40c16480ca9940c1000814500c0280180c001d01d13110b03a03031300c100f402d0340c40841290404803850f860113007000701c100d0907800204600c41c0060480c2100100c4104007100442240c0709002d01d568080c28075090300c04280c11980c00d03902000d81c44000038000c0c0040c00e04c40c05101c040313801608032606c0d075003200f0300154020400328001c0c20080c030074150b10041642824100380c00034000340c1026a002992040d00805089002e030392004840c1d4500944000c41e0000c10343d507514240c8a041c1001020034200e0350200300d1400d14000f821032180e170340c050f61070b5004480c0c0644a40d42030514001c04042803c000e044140c1a141e5682d6101401c0e080a2181c9009403255602500035010020f1611044801e01d801110556200744141c10010f03200800000036070f80c05441aa40350110401c0b1001100c000f50003c12040c2c401c01200c0700c0c0d5100c0880010f1003200c1665091041410aa2003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 161873003 1250 161871753 161871767
    0x8010f02040b070f0311030a0903032607120204050901030b01091d03030a0504031205130309080c030304180e10050a060501050403120c02030f03220b0901051602031603080a020d 78
    0x60080b92480510220010030403100b44404150700a0606401c4003800c000528110344c00011407201003a075034078080c0145a0700c00c2040c2c1c011030000e5401d20304074801c0b00505584000080c914020071105400d541030600342030b01900d004182c00741014445507181e107403564a803c8240101c505003071412058a01124014404038829040b080165185464000809028040c018425000d0003880302010141030143c3c4501441050011926001d0b070003185070050032103860380d0000c042d0394400c034410001035802100719411100030000c200c9060f1200e1a00c0e801504100303025400c54028003502071500002c68001d50301c00ca0079140104a0903860310010740c1c05005502003d40705c102c010810009050144022014183c0028204c0310461140c95041e840c5911a95051603501c1040365100700c0034102d5103c0c4e4002e40102a1558200042000000c140b4060030987c84090075024107050155203003800300d050034100f03a243d01840a40c83c1c6c10b0806142c1d200d10009001442006440355a00c1c1c81224 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 161874253 1250 161873003 161873009
    0xb0d0e0d020a1e0f02180406110306151b19050705010c0822030c140306060409050a0b07030e0714011701050a0909030e060a08010e100302030601151e0908010f0204 72
    0x1881c2d0301c0084443c9620302000d01c500e2421034041c200d107800c020140c2d564505401207641070f4103e42c00075141c2882c0103030903110380c0788013401000c0c414000d1061a82c3e0b003080e5200059244040ea540342ca11100380c0d034554080e0740360178030072900952510030f00c11028100369402c0c0c103000d00c084a01290780c0d40011609002c50103409001d4030b10911042303103060801008100720400b81b004c0213510948039111850000c01613032144400c03111005e001c100d50b05041c81800d5000e07208880c00c004c00240e548681d610799840003c001d0228070880b00180b003044c0640d1110615800c0c9000300c0f46040e840348648060040903082c181d001c50740d50181d1a0342107604000d00c0d41a160701034101d440380da103801802800341000745011014020040d0718040c803500c618010b81503400055a5022003075140c502d0585041034080d00c2c50310a0b01e0341c42010300260b100012490304660080c1d043c1e406c407182c0404110313030703c0006800102180c18008102595198050540020303210240000c124a10440104004034031443c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 161875503 1250 161874253 161874263
    0x606080f0c0a0f020307050f03031906030812040f050610030209280b0a0504050c030609100803090906121009050705010906023003010801060e070e03031603090b0d0e0d020a 76
    0x101100020380f2406400000078141d00480342441001d6943d5418168411411b00b03541c0c3c000700400004520540d4510000d68503450200602c9003140c8541c0014850081420b00e02141000890100000f0420b110490780e005400c7d500340d8180100000301d002603e10080e803158110202150001440300e1100000c600c820b0000031554010310b0b2041c0140c9100015030f54041c50040c0700003141e07100c80c043c0500c10b109907206c050382d901c0d081c0104a00303180051700c581803e9a94040620014000008552420303400721181140b65448000040103806104501201c0303029004a00103400819008880f9980c807a030245d44243da00e0348011100c1808038410300005900511107640b035444900803040d494103005c1d5880701c01d141c0348240c03000543c1c400c3e800f43c50b1aa554142c10021440f00d01012030300211035150112010090600090f03590203190380c8a1541510f002892040602498041e002842c0f1102c1e240d45a82c000e14071040100401003c0a19034000d010680f10903901c0840d00d004001e80c0a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 161876753 1250 161875503 161875507
    0x703081f051203280f080403110d020a0212030705030406030209030307021e281802160f060507031a04021810031a06130608100b040b0403110109080d110307060f0606080f0c 76
    0x45d10845100001520980a0098180c42c028480034240500072540d0301c55001010b0100031441888050182001c0c036007901d4005201c0400041c80100482e012102d035440e000da154106a40042d040d1320400100a41c040e41d0360641003001c4408120b030014442c2c04071a00c004424421805040041d410b2381070940c00700300e05c54244610001150424100120144014145401024642d5040011a000307954a01c0481c5800c0200b00c0203003c0d41e0b5001e01c151406205007045420303901681218400361a1182d0b401169240e160380d41c420234200d155100034600b07070458000c000c01500510b481c02d4002e0300b18400c0c00c4081150f0034034504a82404c0d84024071069a02e00d00300c1e04403603d0700c01034041c178824000000006035444100014101511002448550350743c41d525004c2c4080146803207403418409140420444503c0125007120600c07007034100144405411035546003548a04e01000f80604c3ca03020500d130561050761701000603a0b0a81d140d00000d91030304e4011010303501003211005844481 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 161878003 1250 161876753 161876777
    0x4050c0306010c03020c1801150f0c0f050114150a06030b06090d14030a0206070f02010b0f1323010305010b010c050a03030c09030b1e010b0703081f05120328 69
    0x801d0790f060664a02900c140c0300e032805218001004000440d18010210702c1c3c1d00c0c01803050000d0081e00117001249800c0481144829040c05030012110303040142189602904400078000c4c29000342e0f200741038008441e449803070030103034004000c0f40c0911228014901c43c013020800c07038040c1c8640321208200800d641d040019000821450000040049400d01080c0601d80e031840410000ba00c4042280e80203404180b8003240020440c0d01518400300c11613042a100c0505915040c01030007031240140c41804d501c94a20844c0c00107801c1d0301e0b8100000d40f02136409140c141000c015054181c03031050000744a00e0b6111401100c0d0390400f880040e046400c00c0010000007802a4030100c3c0a84042c10103141d0345540b40c0b160500810200d034507050707008080817000200707206601c03540d01500790920703000d08000b0aa00d00400e0501d008241c02d00d25050801c0f080300c01041c0e03001c02402002d008240c425644c080c04800c5460750461414507100800d200c40d074408220764005401926281030b0350340710400c0c0b1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 161879253 1250 161878003 161878007
    0x10060f1202060304060207021201050601031401060e040c05090607050c15040303140705070e07050d0c020303010b0a11030912151302060708031801052e03050718060f09060302040b04050c030601 85
    0x1001920480b1130b030b5802c00421f070041e150b00400d0f071926004030000180c03d00e440030024080d0340780801e40c240240d0b0040f0042c4612034001030300221128083d600002c0074196640c00356003c2c030803049480e034445d0011030380104020f0000780800038050b0945407008040ea008402d0705050083d400004c01140b1f402c1102c0c00140499400b900805008104442000741e481102c03004c40c85060383c114001510014200d594034490780520300a40000e031000394030b990300d071005861141c001c1c40701c407004100444940380d00842040054441c1a42c005243c1e01c06000464603440e65075054a0217203940103000c00005440703c9a4540e881012600500b0542c6441d0340c5076900c0f8001d900040c910600f105903821a1840b0000902c1114450b80200d54404012010b02d0922640840000800010381b502100c06100290010a04030210b030b5004011502c030300000140320010b444540c00016264250000000c0c0307191035500403100f201d0090f1780c00c00100c0d040070b003407000b0f80d032048626070320a201c10030208a20794 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 161880503 1250 161879253 161879257
    0x130f15050706060302090f150109080c011808190b090c0a030807080d090c08071a0a0e0d0f0302010f0605010201090f03080c070203100b120a2103060e0910060f120206 73
    0x703100d0311000031250345950001b80090002d540c60f681c102c1d0a001085205200c500e0110f51800003400c05212080c90b0440c401c1d92a418013025034100510a030b10080002480140e44002d07004c0748064840744442c0e48039103841175039004800e0310020201c00c0030404941011030311100c40b410152410400701d007141ca8500d40c40e03101e1002210b5400c0100f000e500c40103201d10a182140b4803800b614202d00f45040700492074076149070000344845100c5c0204580c0380b10003000301c404c07010041c20940d001c00710a2000035a000c070784800280c60f699a884030682015810340c481c141070050080c0c100f1909480700012422075500c50002400c5060012541005c64003802506901101c0c090400e49422011350120703042420908000740a82c0d03c03010f03241481e2030100443c60000080308000d05800c00980c41e88000fa05051103051150f41d15503000d440003a01c66040344001e0701a44c626840300d4104100d182d07555548040d64580780c1d514000010882c0c6058500b40801c613601c05010620102070354007040280c2d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 161881753 1250 161880503 161880517
    0xe04080a050f13050a05180f0903160c08060c120708090708100209100e0a0b031b12180105011a13050a03030504060e0f13020d06030512130f1505 64
    0x100c602406180c50550350700d0020050883c1919004110b149418240b00c1411501d80020707206003032100f00000b44050313000009500c9661000c0d03c0c0310640790341051504600c20307412001d6820b542d00308240305000080079103004440ca400c08550b490369548520002c24000d250f002c551710324a89000c01c2c500d600c20610150032115130010f0318030407556200110315221890071001180d503004240b1856078a01100704404102c0e882c2400a030500c505400600c0c0680d0324018400810300120118090401c01407089151400041c1d01a0323842c40b181c0f180d8014842c0481c1c040c40328a0382d10305400c0b803802043c01400d0481d44126102c80c0c8942900032169039580110040c05500c0d0b03046680000c8070707036071000390074000c6000391075140e6158203140c40100500c4d0340500c5640a2000e0000c1e07012039031102000b000c0818112100180c452104802c1d0700c01a0842e980003070258803852a40301c00d61600040241161414010300304000342e038419080c20344c1c4031680700302d800003201801c218038105d00500c020010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 161883003 1250 161881753 161881757
    0x17030603070509010609030314070302070509150a03061e150521010f0c0212040602060a0207030e0a0e150a0509010b07050703080d02031b090a1e08100221010e04080a 73
    0x12030782c0310004140854001d0740034100048000c0001c05c00e043d00110382c90301442c13030348440e45c0c40d007031143c3c5010359503010300d1040c180160700b140c0c0015081168004401c0c00f10381c0c02080f5000480d42e900b000805801002d403240300805102e51110200f402c6072040c1c2c90054400003034545c4040c98042003181c4106240f8a00b40700c0390100c044d01004802c28814200300c0c0c0d0010f44001913904503040c0003440d00c0b2168162026041042009101c4580c002804540c069030342c0c44096515825481c0c1164048812600799820004204005c10354040740c14600b4400d60550300682032541401040000801580c46000d070001010001032080682100050621902640c00c03103282c03540d26039420030305074001c1c0401c0791010380c04024046419603101541100c100d1040780c0f5810060428000b40c0c69240030b100302481340303098250680000550f442c07c8002041d00c1c0301038450400691000c0c0002c3c0d486420b203005808214980c2c00344942500903e00c1c1070b102c2032209038a0541e6160340c2e0b14019444146888c003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 161884253 1250 161883003 161883013
    0x3080c0c0307051c0912080301090b0a36020f0301030b09030c060907030c050103022104030e0402040303052802030a08040c0e040f050d02010b0f060702040b060f180103050417030603 80
    0x1240080049150034100483c1e524240f221404c001408460b25804c144492400c071850000480e0300802500e0641d0441d10b00001c00c210508000781c00e2200700c2c0c7c45181405103000305507840710b1019040b0100003000c1800c1c1c0380c03504410702a88040f846240b419803c410800e100600c00300324245605540841003400b20b901e018064661186000c2c411105098942d008500c18000c02c086010381000614080c2015420011020040c20700d49400b4094000e06c03034030540000302410711510385030542c40310280003155101e4403410000d00d0341d40562260400b10392101c4040586480c0f01040b034044d46182e41c091814800e6a20049405450152064034503218016011940c044c1401560b40113610484240c1c3c0c00c2c14407854032364104040c01c1462020f42e403401d00e0301e403100d071246a079100026004603001c556841c2644000350007003035003241003604244081a0740540d00c000000078004583d107070b103991010000403c011419200700300c50040031a5915003401c81c080a00101454005400800f514 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 161885503 1250 161884253 161884267
    0x1303061806060f080c0306060d02041808030c0c070f060207061b02060a0905030f01090b06010507030909020a110708120d02071505041b09060e0c03041e080904110703080c0c03 77
    0x10389215070400c1c3ca07000000c607410041d402d010000c600a1031020380203001d041c034000002800b4001032460190140740c55080c001c80c0491008419140d442e03103c2905502c0e810300305014035568022142c0c5541078400c001c004941e49a11a00c5503007141c071168010400a82884411074020908401203042600343d40421001a9100704c042c2070003603465929442c80904d00400c0610b4900b0740c40c004401c0e0307494404c001000c05d450005ca40c2d072003402824000d5032000c2c0c0b8501110f00003901d40c084c40e146031000c00c4014010313501104900600c071625040320505a25800201c1c0c482d11114294040e12100300008030000c401a00540090b0340500f10100c60054980c0b084029904101c80884000c1d034540180d03011a00100c141c1c030050809241d00700441814010f107409114005001c446c003204e4080001010070034210703000000646034044182d07480c503061400d0700301d6410044042d4401c90819001c19401c441c0d54090341d090a40540d14080036803290f40603540ba99004426150035400704000003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 161886753 1250 161885503 161885513
    0x6091c0909060b1905030603120309030903011a03060916060305060609040203092505060403020f06091012060e0c0703030903020c040c0903051209030a062a0c05010b030313030618 79
    0x10010450720010719600e031800c18003604484c40741c10045044c080148107101080e02c0005200701a903040c0b10710180e40e500d4543c03c50b81f441c080c0c1080d01ea455801d145003110f6903d8402058100c1c00341c280c00307c41c119140d88840d183c603100440c44110080c00b859500f0800c8612a4220325040b89000d06020b18110b04180409c040e43d10440b003c9100b036010011030500c107948141c05c180c80c014114903080c2d00c81d0034440002c0103031081d840041d108406280c900b030f072580d94200c121b504002c80100380c481340d022003030070241091041c050300c04582450301800091407841c0000312403064101101c16458000140d50070380c0104146001a001c610038a03180c12041d442d00c0c45003181200b4103071685102140781d03181a42c50309581a00101e035543c0203000c076043c10b03140020a01c0404d07a00032400305402001241c0d0f15002c6a181c110a401c012143c0c0807000015002003c0700042402a40244460004141490380e01e10403500030343e03040510460108003091580c0d11149000c00c92503002d0038240d1442e00c2b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 161888003 1250 161886753 161886761
    0xf030103111905010212090a0b03130b0f060a12030c0b07091707120b0c1204111008010e0a0e010f0c02160e0f0f0a021615060806091c0909 61
    0x30841e01e081401e14400c50380e242441020700ca0003542c2c032246241c035003040c00003910f034414000ca000c01030101082200e0180e94071400c2802810201b14550b491f46070041c41d4407814070404409880c040100c50200d200180c2420000f071040c0c102401e075610091814204840ac0f044804040d002c0240d200c10780030000c2c91401d5618011310613a03464020240c20b065080c9028070711030640c444958409076041110710641c80c9840003a940008200d012030343d0f0100c0c110100d00c104941100302c01810300420040080810325601760403801e8036185a001d0300244191203a040a024009100e601207000904e100d403240c01803200010740c0303000492540700125130802501c3c8650508009238003e1203d8890410a206001c0f0040c41c0110b41d43c0482e08200d0000400902d01a01c40021000c1e9000040c3c080003042c0c04a4240c001079843e00300d0100403905054290564500760094440c0c14502e00061b902000240f50b03004d840824080c2c48070010b070030510f44840c0800d03001e80f02441580c40000951f041c803481 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 161889253 1250 161888003 161888009
    0x330e130f0b15030102070c0b2109070e0109050601140c011d0a020306070f0c03030c0309080310051002010e060f07020a0f0b0703063201180902070c0504091a07050f0301 74
    0x1c210031407070820b080b00219000d0000c000e1070191388148404001720703210003464411942e260200a50703448034940242d102c0103140c400b080301d941c0c84009000c2c45400001d4840700f2034220b829820030b44d90b01c0315104015607005581143c006105207042c0c602d604e805000800c03c0618490000565071210788034850109035400711880300350840c1d01c10002394102408503550010443c900030301c1002150101a05410303500b0005030400d41e90b5500c0e0702015001b5030000da09640c201168513142c3c580607010903041065405018094031000f03078901d04c664014058001c0320310820740904416902c00f1507120346064003d100804602c00da0145402141010009815807030140d000140d45107440305000d41a5041035102580e501101042404030303440402111420316081d071500002c1410982c0100c1c1c4d0891503050213031050780005000100900c07194001c0c48802d00c503000014240d5540c10402088400520b009171851995003069912081107505855101e025400c0243c01c20703682c05c0941903070381c1090f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 161890503 1250 161889253 161889263
    0x41107061a031902040c0201020c0a1e0b130507060e030c06210708040606080c011b2d0218100312120c09030209060a06050d0c05070f0501330e130f 65
    0x1c14003e043d42014064060140d40c1070009514150010302e40c01c0d40c540d81d510780a400f81134007100e080c020302c507a001c80c8010140c0000621480741442e08280c3c1d429900c11000300d5141c8601e59001803443c2c001c64540044600050151885884070005c1c0f001c0c941c005600e184c000300300d803c8020b45103c042c4021a0103035199903076008503842c04e46405412500c60382c1058125900c091118421aa40305010303000c80040c03d0382c0c01da00c1c5230161034400c3c0d016a54100e80c3c030480f000c600d40606602030120320184840d008a5003c040d0400318800074052100c2500c610a00b400d2400041c07010034072095400c3c894180c00d1400c0c5040400c80b420120444018008050000d00d0003581002549011035156400801c100c40000706c0520340180070b0403038420307055600059030300e0714070100105025074140c5540c641c2100d91546000c0c60323464118002c0c4035000f038803d101034408101c0003181e00c0c400480d59005100384045081c180c180b41400c0105000200500f10307410703004c2d001000150361701d51022003040c030130 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 161891753 1250 161890503 161890543
    0x215070504290705160803030f0a110d0e030d1d030a03090c3209240a0e0901060303090e041e0f15050403020d1106060909030f13050f041107061a03 65
    0x10722140112920141d0112501f68814024000b4120070303c0407403604403d01150000e03c1c00140c213030404030350103600140007400c0e01d0100729030038649010005064492901404210501d1507444c80055017014215a64940c0c0c4148440021103000740c1c000305d0005e001c1d07515141800d58981d0181c400465001c00b40ca0510408542154890b47c1814802025441100d4452842c5404803051494400f02c005020318400300c0001e2142c90f80b600404400900320070841c1001618007062441d004c0e202c1d5110031400528012000501c407000220054015580800c01707030b04600c0c110f8554114500801001c1d645060308a490340f0000b03c4d04000201c011980130b030049141d1600f0700780a030034108401c400006003d0394039010701d0107920200e25150f0003c400c40b0305140f07030b455014172203107580107000220b01101d00c0000c5080401c0e103118010707000c03244210f49440d8400380020900007074402012086800d82014407140000a07400d8101c02c1c01034030018200c48021003d040020700d0088078060f00302d041310300c07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 161893003 1250 161891753 161891773
    0x627010216050108070e0f06280e010c15021303030c02030d0f05120c09090c07060b060f1801020c030106090e0123060d05010b0d120215070504290705 66
    0x18031015040034a0481c1d12004075103440006810401d004108000300034030400504080c0e5214140d4141496000d0007464507071130401e0303030412030f2140c104020a414221208a0a10310720910003c0c1c3c010fa0180c0d104c1c4144040303680d544500217411200d90241d56000d0003070003074082806481200540c0295210b08005e60180145420414000c9120b81001100422040866001310444a00c0281109900c115035201108064103004410602e60301040c52000d00c121110650040c10711b4602642d800c00015030811700b0018031340f0649071100c0c004e05050004500c0850b00700a0004012811300585050950711000a403c5074242d030864081c0e01d0790340012030004c0d0800d00c1444004002c0a0f000e43e5980301d0120241202c480081889100d8004241003804100d002e4000780380e00c071409003207050410001c0c80c1001c04c41070f660812400600c61003000d0010f440744006014024151526a50303e094104045548401045a01000000050003043d00c0b02d0320258000c0c042d15019030007810050328 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 161894253 1250 161893003 161893007
    0x30f031e02060708010b0903030f030403031b02010219050c011b1d0901030510090201170c03040311030304020a03020405070c05030f120c0a0801050409020a050319060b010302040e0114062701 84
    0x24400c24600e00319071000007045620364003c800306041d41c03030488500b5114284100003130302e144500c8a044c0121076000c4240400c15405d03800400f074250000d000113407006c0912034128201d004203561b442170130995000a1600c070b80a4002885007000c482d00100340071168480c820002108114000700044900f483e000c8c3c0c01400480840044200b240c04e800c0c154035607152950b42d1030f20703845040107032952807141f01d00316030007002c0c2c44508481905d0048854500070800d0219034104460540c0800c1c1910740c603407880700001c000c4900c281da005110160722030443d000d1000074000182828144035a000000010900c00c02c040c00d550703042d5280040e5a40f604408881c00d004000d408001c102400340014003516070815211415a82c040e9400105070019000040c00480294411901030140803805203030f004120361a680480e00600e001c1c0003403626000110101d1040e403141d000f038900100010b1002580b401407290b00358200070400c0c2d0814420072a2000142c583c0c034142d1000c1c0003101008200c0356 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 161895503 1250 161894253 161894297
    0x50a060f06060203030c031017010b0f180f1005030f06060a151403090703060905060601030c110a0f1a01060c05100c0e010e01020a121d0a050a060513030f03 69
    0x40000c40c0602840d0b280003070203596400050425140d0920101c0081c03640845104410001c00c00c400c04001c89964510385a4002c1070102e40090142268940fa030109003401030016007408080c03000c003146035950000c40c94605a0240c00c480e0000c071214400034250358200700c1c000034071240802405090070300408101d22000380750b1120000700d00340c4001c1c61696400042c4a001c103146450382903607075501c1c8100941008040d0300020701462a060501051020005200380b180000380c804100c000220310082e10303042d05000030050960300c00117840c0000361405a002c00c81034421101720354090800130011100f10400d0304440c000850b001b0021090290030040c1c0c51003900302c000b0070815100c4010009261910249002e414040c141800c02c029034420401002003d41000d0400400b0703030707210f20040020700c1d20303103c29184032022a200d03103240c0742403c2108200e8100400501c1018a0400292501d803c403184144182020007000404a0352101c0b04c021003a00c0b03503403007602000c150b100320f443c0c079 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 161896753 1250 161895503 161895521
    0xc090b0f1201050d0b040b1302090c070506130804050111011508030306010815010203042d03060b010e03070e1506040e040308010321020c091008010204081e1207240504050a06 77
    0x54241010f000b010808818074150004e421040e40e142c00d03030710107185c2355020818503c0250090004400c000b4900c0120000d0701940d807280054a146807505240d508142111002c0540765000c1004208003660040049180f81c0700911f002244413106160000300c041144c0e48070000c150800000c00250307680c0166a140d110030007510a080c04218040001e5403409a40280c1c0e5580740105a0089070500d60b440c580c06c0fa200390141d004c0015140d24144000d4101d0720040341c0480d298031a42c652514011030080250380c0c3c40c8452900c2175642c070719070140c0c507860600190341109040102045018240300d84501c035501984905906502d10310740500c040136164100504610400500c0501c5c9038045000c031303004038085401d507481d40c41d40d07602c0c492400d0155000003010f610000f00050200300104804001d041d016414601308801100055250741c0000004503001c85e00300440782c00140403c0600c1c1d8004800460000100c9044120741e08403a010b0320f09030b4296020642990407c4981d028440388 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 161898003 1250 161896753 161896759
    0x40602150118050709050d060c03060f080312062106010510051204020f031207030e030d020f070603020708090616020906030f0706111c051e03010e06040c090b0f120105 74
    0x316624105040c402c00c103028030400340032070b1104041074002e0322400080d005001c00900c544142241c034502540249000c401d140d0119003031400001d904580880c03c0f00031100b42101071841c1158102140b00245001000300c2d5024000400034484031181e03103c1d082d1210284001400c440d41443c02300011060b4640c041d0040020800900041c50b030f28440041e0015416288034000e0480400003900b49501103542125108010481c5014503602c04c0030b9010854098080d26803400400b4800c036111407401d003400b00039520079482048401c1c4254001c120f900d006101d903900b00140f080003e03540c0c0d07009041c0301351280c041443c40c5040d403400b00d160603040f9008400400591a001110540310881403250384144601140803105a050030300030799200080100c2031145001c0e0000024040d5000031480300c840499481c80e2103020b945060450741078500d00300c820b041d03554a000c1000080c0c0240442c1c9003c00420007000108050031101401046850880454640005114814040b8016400148 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 161899253 1250 161898003 161898043
    0x609010608120a18030204020c010f18020303160c0e01090e010c02160612020d060f031505071d0310050906010510170606070f150f060509090d0f020106080f03040602 73
    0x414481850481d048515a4100403c4c140c0504288a1228826030300c0a50010300000311624484410340c49000c0c0c152a010081080b044100000d1502010100000790507910802209021000f204a0040014850500301c1d580685440003a00d60a00030b901c06000c0a44031408140c4241080c004c010320b0040920007002d10141042940c1c03100744241c81440c042c0f05000035040b001c442c0a0b0100d52070004c85c19030070702560390f07590400e443c01c8440707110542c0c10342a9294280600401c50003040e001c0c20003a80ca0500c868581d01410a840b05003103960340e410320070420201c0e01f90900e80255441084200701a00c07440d0715060511002840d1044a8800c009401541c0b40c0c001d11805603d44c0c20801c260784883c0c0b9203015203880c0841d800040000350060000d071030b00e4002c601168101080840081c103003030021300d80d00e4061148450080d41e940c1265000b01000c0000d052003200c00308002c010320f07c00821070690ba40311041c10140c2030b580036000e60300005010b20100c2c2d010010b050000e00d4502d0f1840d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 161900503 1250 161899253 161899273
    0x50301030b0f061e1c0b0403030b0d08030a0203150907030e060921070804030c080109200303030604050c1917010e060901140303090406180c05091305270609010608 72
    0x1400c104000604d0b8141c4280d5910441416298110651038200140c5100d4484c244181441003810008650480c0081c0c01c040303c11130700c0c1c05c1200c2210300685e17000d07200a0a5403600300001c00070307400040036404030410525524030301c0ea5905a45902038416a01e0004040b660100d802e4207010703004281c0c4950394040d404600fa051a0320801712503261016020581700c02c4145080c124901c280d0388080c002500404000c1033480c4c040d0302516500d1300c00c0148501100d98420b80c400c40c02e085c0450aa0b00d5001440000e0841c10607811845e40180041d80491500d05002650454070f4040410f0340300080800403e00401e02c51891200e01410000100c90001e2910f000001d00b46007050042203c08110108990440d071820820307101c00c000c0081061100b00e4580c08008080d04460007091403090400d4005480c003405030080710b00c0d041c030180428100900030050704000e0940174202d900e200c14413050400c40289030f85000c5910008040151042d42480240300e82541c000303070000103940e00090100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 161901753 1250 161900503 161900509
    0x110135061509010c05100207030906110a0c0315060302060c01020904050c04081906020705030406030f230c0c030403050601060c0c080d0504032901060f170411040506060c0a03050301030b0f06 84
    0x156900e140246070420084d41c051821a041808510f000c0c0480e50004c141c0700704241d00f14103c0320035101241d64044c280307114001103960342e10354402e0203040100000402d102042202c04400b251078804100070404036070380e5010541951000d003940e440c0e44d60205150801d407405010745600003c125108904183c01d000d511500e40e51001969044c00c040c0c40948020010711f50103407651103400030141c80c0c130f89030f0752207018000c1c01c0d07130403801c280c081d103011400743c00c90b0344074100241da41d0141a040a02c996402d4a503031003e43c483d4000e0041480284000000541c00300a1113010b0038440da280d408820041c60004070000c15a040410242c02113203c202c40304e0703400016a000c980d0072842056105813086e4521243c1c41c0c5107081e0900c0d4010a03400441c100350003091059070307400346d5503880155201110100c03110403000c1c2c034000c1c071074445001401098070f4aa0051600610014038180c1751481d4000f49900d8440c040f50201c010410200c0100148085440300e03e6218601c1424040d4610f890f03000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 161903003 1250 161901753 161901757
    0x70e190b28230913060c0e0a080d02070b0d0b0a0308280c0206030a090614040212010c080105150909010e041a07020a02040e1e01050414030906071101350615 69
    0xb5180510f0401d000151451a03030001c050780d060300602d00b008190840c403002010b074400052818081e807801280003c4070a0005054805210640d015144040c05d0031092030b440ea0007401215141ca840704124955a92002040d800442c403d0703040b5952031001d5104c0d8050143d0184084d1840d00030464881680c0341c00221405240c1e504980131680c980c0c0d03071011000104040840a494103240040403150b070300c03906c41c646000b24005c4510340400d1404080c03803401e0301c200404580000e440c0000400a5082038903035407000030040c2150f14245030314040414074414090f440840396206090602040c440c0440341e80600c54a0b20030101d83d50724203550042e58520040310000d01540d6030300d01c2c206940d04180040b601448a132074541c1e011184018000c0c1c0640001c0d10103940010b441d0000c500760000c000121111921701400441c1001010303103603488403020260100e41400300c699003010101c0501c44440342d403085910620b102810180c0a41102490010b1604d8058601c03521403104107650501 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 161904253 1250 161903003 161903069
    0x6210c060c02040f05010b0a020c0913081c0212010314070f1e08060c09010e03010b011b050312160e031b04020a030905030309011d070e190b28 63
    0x7440030009000784041070041c0100341500b0501880c000021403540d02400c001c0c640c0701000c0e030888088007070b902c0400202c0007094482c00001944900b4410000c1c0128020700030b40c038462b12202c440000d503814490180c1c0e101828490120720311030011710030000305d03030203071450784044200405c1041d0a05842d03441c080098040d260000545440321800417030301d4110a005084404103032600341c14030007140407840d001215111701023803508034141060700301441005040e1105a440f200320502e5800c44601845c0c0004007920b20780401c114414010080c0c420960185070440b82c0c5d401c20340d814100c01818806404540d922070f402200f000354030220320281d203005983c001c0302c1c010381e240c80340041035008040c2140010844e01002c020001c00070f606502c190728207641c0340408112180041d00c10b44d1a00320740d000f00c100304a08007020840c2000c00a002d900310000d124030000704001c2103000508504280703034046171440611540407460715003900000c2e005108241e0440d00c1c0c211100002400b0b104100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 161905503 1250 161904253 161904257
    0x91b0807210501020c0f0105070e0609030c0d020303040801090b010f1d010306022b150f0b0a03150503030309160b0705070b07020d15020a030507080606070b0c0c1006210c06 76
    0x340c41d00180035003941103c001a070700c0001c998000e42034404180c0604012a04880841c40c40d2008000070300b0001d00f159460301c002009420007140035400c0210348d04004d14140e80503c030510010038041000d20034410b036a800b0340000c0c08198900031581190750340e15044400e049a92000c00d03060101f0018842e410b496000c1405a12000110a1880414101000715101500b92502c068071350b000c5078800c041c0c0e10406200d000d03e090300e5945900d440c007550301c01c40c10714550070000e02911034030035442480c03d0700280c0b411606050341d070b10000745950000d86611700c540d0001e0503511050055000210000c0200e041a42c1c02c0180300c1e2100d60f103404c0107104030014504c000030028110f42d00c6010080380558416040c02403506000c02400003504008c40000109152001141100d0302850343c06200b00c2e0014a120300c0c140c81e595604401250181291265043c1448400d00301c0c2030074405192204c40c201c80c00501c1516011107001d240d85c00345220403180e1101c15030903020815051203282034032107074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 161906753 1250 161905503 161905559
    0x4150c0515190c2601030317060a0504020406020607080a0b060403081b010c0c20060711120613030311030c1b070902190206070815040b0103020c01091b0807 69
    0x1074034600d0340d01c2e2000c00da4a0751051030300394a80f00f915000410038491942c5540754400700032004420340d001100130f0101501080003002c8000100c80c0070816030b40c0c40b00010300304a0360a80c1c0d650110301680c120360464005a04900100000e641e400218039034010748030038040c46003050410114000c2d118900001d010040c0028405040340104210300c2103848006000700040d041a0303400802240c0100382c100c80c00302548842c207848000003135004058400c010001c0f841e208041e43c403400c0203450f0541990300100d10390b90410340c0320414400b131380c40f60440c1c002d0545000014a002030403510101000504180d0074001e001000b60000145c1d40c1d04685050b5a400c42524801000e151000c59440031169034000610b0818807004801d1051200803180c0880d041c0351681c0c101656070950491301c0d01100d0004c0411508245440d8020f07086000c8181001071500700414a06804d42ea10711074195080c0f12002c146403c00c4a8419111000b48900c0014010b014104051403107400500d008001e549501e03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 161908003 1250 161906753 161906761
    0x6100603020d1401030c0e070206100506070609020901140a050d0b0a0e1213090606031b081f090207120203030c1215040c200a020f101b0804150c0515 66
    0x1c0b0340c0010003242003d20005840c0d03950340390259000110f4040c402500081002207006140006031041c094001c0128802200d400c000c1406101d03002120180d4213192603100180260320b500d40058040e04550300d009001d52144400c0c0300c40c0c0c040c182d0000f80640ea078009003102240700503041c59081480d850300070030480c015107801860456a2590164101e000050700c401120383c54084400312108184180180c82e030301c0805404482790a0008409120303d940000300c018869000740c2d500c001aa00d000071040d503030441c42c1c8034512840e00244196a400101c0b002440303100d41e8a1108403c05100840c5140f6090341240c100f0f0045040242803d82c0950125140e001d02d104d03030310100308014004000c8110110001003180850340800c030740c0020004141d081c1001c000c10b04c0440741ea00a880d000d002c240c81c2d82440000300510308542d0420906000da0f280222090140104840c06458155140d038101241c0d40e0a08880d40544014017090b0010000004c10214105240d5072404421080681d2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 161909253 1250 161908003 161908027
    0x160b040501020913020a1206080a26041206060801180f08040509070e0922031404051c0b070315150c080d09050c0d0308010b0304060204090c050a0305090610060302 72
    0x1030003000540c8183c04d4201032500c01481c1e405400480500c0e41c500384006c40e00f0032114111200c0b8000c45d961038014010750004500d1000c00050b03280321500e04401d0044940840c40c6550300260000b1408801c500d08020078858180680d038050541c082c000c1200c2d0303503560105042d04907002c0d0010711900c0140c5096051024103401d49004050182c00c078140c1c0d01c1c0115008003813a000c0c5000e28070524401012498224148a150000c0f0310404007030714400816442c147c4c4d02c6d86112101015031303001000003040e03540303e0f80c40519000c01124805441704009241c44402640020300c281304140c601103100110745060074642e011549091412801c80d01d001c003040391302e070903546400f401640300017030030209084003036004030050b90040d002d90f19180ba0200400c005021050006000034042c20014061009079030011900144500e1f0300503e8195540292001e6924094101012410205156201036094011142e010040002400451401580c800c0c1c03500894000d4174100355001c07440c166055 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 161910503 1250 161909253 161909257
    0x70f060527061c0e0601091b0309110d110a090e0d0c0c0501080606070b010315060b0c0604030e01020703051f050703150b0d0e150702010b010822060204170f0f03160b04050102 77
    0x402d500300781c805541e161807091025001c5110110458800c1c09231130b40303000b4403e00c2142e04007648910074145144042d000c1007030f600300442c4c041d51500c00040204d0841d65a100610b0000c0031403100119040381c1d00c1850500701035090031903100380000d007010303000001c0d5072001c3c520079a038007401e181d1050380741c19010078424069540700074070250840d00040b050042d00c0410028801042005001c459101c414008250180c0391b4040b14aa0001000c90f000a00a00c1d4000440d0010b20495004c940d50340c0724a8500075025002404050034154040e550300c1050159980c000990304052020460a4000c0b8818140510505000c5400428004000c0185800205018820301f08880c0c20a8110807102d410300000e030340c40d0001d58644502820b031540140e0803e881120315250f4103910b00c0d600b1840700c40f050340c070324400c617807142d800c2001081240c2020100030b101d45a000c010704100195060303285c43c00c0301d200300a0030150310511010901800d030350390840c00b4580c0031800c2d0704d15459616005000e4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 161911753 1250 161910503 161910521
    0x30604091e0c03021516060c02030f030a140606030403020a03030e0115080c091f0612090212060403023c070e010308030a0f050c0703050903070f060527061c 69
    0x8004641e080001c0c4800500d030380b402d8074003c83e140c401e5444030010007030280c49010469541e980300400b050010810301d03404012444458010359203441145240000103600445400c0c0c492a83c1f2404140740900ba080c40c181e01900c29580301c0d00d1407c01b034601950310300c403442c1c006003010b4803612030040c888400e401907140700585e00c0480d0507540d2241610b541756942e985c00507014410380d10000d060455140d071809105001c1140180301d990601400700c0d10b000c0c030050360343c3e051900c4842d4100140c454910100b600704103e005811141001e20f0004d00700064982280300e000600320b08141c80c00c04a482c00d40c034100340100b1291a0003d045903080c01d10b95240d000016440b02480000140080308000f54450b4101c40030420020b251030241c10100c4409642480b2165020700242c00082e0098004201c540d0b4001c044803409992002c60010320b420a400c1400064004115600402d0903000140d4a21031071243d840ca0b00100003020907003500032458038100c1e030f6060074142c140c1020313030754066450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 161913003 1250 161911753 161911793
    0x209130c03021c03030e0703030e060703020c1f030b0f060a2001050f01060801081f051801090503180a03020315070c0b0903090a06052b110301120b070f0503060409 72
    0x50b0b0f030061007200d804200c80e028140e01190804c940c10f0705102c0c0100702241070303a9050701c0e241100c141185c00d112803604600c3c821819032041040541e1180d0f0b801000304881303404544d81e1107080481c0c81000b825aa0100c41245c0100a00071088000c0c0d0390300c8054076040e650520740315001a20030014400c03a4080114107119a52038076082c8140c0c02e06000280b81600c5158803030310010b0b6a6203018581c0d4078404410400c60030750b009030199256505402c015040b440c501e4a402c2d0f5041803d16041c21601208001c8031580e00001e40401c40400345903040c98200c001b245c40100040ca5034000c02e0300d82d9001079822040c86518400244a1401014030002e1a6082411000c59203040e1080d2503495101a2400b489901c40344000250385101300c0c120b41d44c41040142042c20641c0000910001079104617903c1001c40d161600a519803004c0c4000c1d50082c02144c5046408400328140038245030400f80543c010482c907400003a20054028040301c8c0c01c49020b0310000340500c101c1c00c005503201314100076800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 161914253 1250 161913003 161913019
    0x203041a09150c07030e0604060206010603020307030e030d0501080d1407060b03010905030c0601050307090603031e09080d0206011716030803150406030305090307140f04090206040509040f1205070209130c0302 92
    0x514245070094034040317200340c44500e0303131711650000c02c2014060b91040c680140e1004006000b9141300e90042c5401c2142e07400e0200b85241c840311404e0958000d010010b00031569807004011001013040b408806102d14200186025800e560301c1c2054498104003034149a115004c03a03161361400d60121010755041002e0f60346442c60328000646840c030a00c079040c13003841030702c0020414014520501d03003125410b850b000260605410400c0d8160030452100f018400d0091001070b07245400d0080189400c00c5501401c0b0755814402d050110f003480d94442d1000341d10411564081041051010090380d030030005803034403507640310041d80403820564078030b5400a080c86c0002007003540080181c200000e048094901c802d07110366030b468580e84080000396206922403600741003405e20341d001f55074941c0080c20742c0d4501902c0301c4c0440d01b00641074030215055015824401c090002025a507150036205103800c52400001e900080c0f010780025180c40d00780d42541403000100491203015030300650b03019080e05 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 161915503 1250 161914253 161914261
    0x100e0c090f010f0e10050d0f08031905090f071e080102130518060306130303020706021918031101050f0c010903020f0c0102010e0d030c020316150c030203041a0915 72
    0x102000c1c0b0515107015880f00e000300d4064550600703144140c2d501201004030754a84020065003e203d407070140c403c11440c0743c810b40800c03600c8004600c590481d8010440d40d4040c00450012070f40000e04049481d0041080399502c5100400c01c1421294200485580aa0707103c0c1180f68120090b0700c40d04a96100082c1d036038001101900002c01c58104072002424a0310329140030b40c008800300c07042c5500d80c0208000885581c012a500b00f499406440c0060908585589580480c1d001c00190900d0381d00c685d00041d00e16510a8465141c020700503c20001e1502e50783d03070345007032071600444541488000705d0074080c80780050040d03a40d500000301c0207100000c0e081c10069241c4075400e980c1c0710207000302c10cc100c0344ea50050003020401e440c000300414011510342d070218010034070005030030114001003290200d0801c8101d8442c1e010b9001c1c2e80c0001040e454558800121100400b0000a0500600c2004007254501b440d10701c02d50458512428142e680f6080c7c60b0408100705806a124030700d0b003080c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 161916753 1250 161915503 161915521
    0x140619020a0303060e06030709020a05090d050a0512040e06010c14060a0504060e120d020d09023c060703140408030f1207020616030207060b090a09060605010f02100e0c09 75
    0x1c000d120b020703071420407015460381c0d10341e40304841c1101d0050301940820b43c100000d83c02c03540244450200351501c07900704110781c0300040c051000d011013901c0c6903101d10391200500400b401070820008100e401c992801c0d28010000d031541e40f0043c03c07d4144110b1010f40e000b4007182c4c09400030303000e0341c10050b13034103a181c64041c03035004203001d80d0143c50303141c0f038a040035003140c0b030009100201c202601140c40c00e02d00303201000c01c00303523000c0050b4808094035140f004005032901c050044030003d81610003031281100a40d18028002c80b50045480b00c1c44503140da036220b07151182201c0001d031701407401510f0030b6a141303581034141c03242d544045050700c000141142c40c0394690303026000036007405054801546414804a07510141a100f0038001904040f03201c41040c000d0b401040c20701c3c4034510200300188400d0000b0884a0101c5007e45010f8450f0314942c2000624410a0041d00d003d08041140c1c1d410880f000b0b41d40da00300700c441a005a66018803c0b01c0e103e0400250300313240001000c03040c0c103280000f48 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 161918003 1250 161916753 161916763
    0x504050420030705010507020405100b070c060f09060e100215090703110d17031911091003051006030e07051005040e0709050603130f0215090f0d05030414061902 71
    0x555110740c507006000c0580c9180100303080045410507580d060038502c1a40801c0010107024040b41141708203804005080100d420281c06003d002c2c01500704590724101c005040440e0081810f410810780b5002030020320f40003001d40011076016904081d0036141c0c0710050b031030400c00d2490542c40048910820000b928005069400d42c0d104000c500c0f29107182109104108684c40002045d121516800801044600f005940d00c0412002c43e042d5004c81c1e00c1c1800e0440c0c001d01d1a0b00c440c440b0015041c0d1a6050543d4580d5220303c0500d42082980741c2907400c24071012541c0564810142c5803030b400078803060708128240143c4002080f8440009510700080c095500c03038890350b08102c0290300007030042c3c0d000c0d442c950121100985810f181d551544071240382900c0b5404201d070107408041075000135803685c644802d16060070104480d940c412003002c004801c0c00c050000c0340720301c4030340800c0c8000030804410740b0115800b5080c4048035420305000a00c4600803d540c6d240610150503084806960005d6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 161919253 1250 161918003 161918033
    0x91806060f030c0702031c09081501060f020703080307020a0201171b0310031a10170a02130e030313060e0703051b0102120a0207030312050c09090406020d0f05040c080a0b0112020a05040504 83
    0x40b6840b00592782c50300c0e1a00c600710a0340c4601111044001001024050300114a544010340306032034009850b5640c2c0042c03508165041801603000d019401308558024100c6a4600c0041e02521120b142151540d80b2004000102002001000c80401c48540c0800a0140515403103803001c00d01c45829070340413054500868945076250440c940000d60100c00f208640c50421869004c4c2c007481003603400303100846a8150940c00c0c180d640300310302c030101d00080c000f841c021190343c80c030302102031814140a02076900d1024510080c0d0000c00d01000090000904003007032052101829030100080c4006034240803842d01403020070000000c25010380d82e40854001d081d80d20039100c0c4003210485081e801d04690084461120b000310401140407513180c031500322036210340310f014054540200501c0c010141c0e52444150361005840b04144001c11511180c0c2002900080d03000f400d10380e0a641b20b03043c080106110354407624041b0910501075403a15042000901406081449141054942800a011511 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 161920503 1250 161919253 161919257
    0x503010204030b090105101a030403050403140f1204080c090a0e01060b0a0807090312030f06050301020d06061b0c17070515070b06030f030418091205091806060f030c0702031c 77
    0x700000c0d1400303c0c4085440180c2301c0a003001d107801500c000b4a00d43c03070b40c80580160240700b4188800030004105920190608003540b002c0e00000e40503036070641c90300342986001194480709200602607508000741b001c5040300211520f98191721200300c000010300c0e8030b42da03c112070350901e600411401e00f030380014148880e041c1c1c0c1700505a0781d21002251100c003140001041c8280446202003180c1c481c2c1c216001120001c00c00082565039940001d08a038007a0103610040d036200c410401c907540d00000d44080d070344040c200b2400c0b5881c890f81d542d410310400e40a000101d02803000181c10013103003040001701030500942025900912031034541c05070341202030122101c03038032100000c40d6800c0c00b24101c05800c54050080d400c007400c0030505020050001d4400042c40d40d150951030200f05100302c9600b406280751250703070b5120210400d0180c500c0c0c06040c40d46017511034400707004598640038120740c0e401110b0f11300c2c0c649a4503407102550b09440740200103589846031103504080001080c15901c1c00b05226 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 161921753 1250 161920503 161920511
    0x90506071202040b041205100905060106030c4113092f0a14030c13050102070b0a0f0c0b18060105121e0316050705010f0c0209130c0503010204030b0901 67
    0x80d000203a2040e4014080021021700c000c120010a0105000d003182c070941c103803030303c100260612208a40c044c03403040d59581c0c40b01004020352a098891404103c80c1e40c601010b001e42c1e2010300110400100340121000c01c6908811351502142e00c80300051480e0502c1000d03962000000403e15642d9039001c0c140c0076925149000c141d02c10792003140c00c0103080140c0c4245844002036840002034019640881c14000710340040450b841070040114411042941c101d61500c04a010707911040607260001415540110002d03c40036080760300791031040b54245085260305082c103904a0b0346d641e4242c0010070034802c000603c18800081041c600000711948126005aa41c074000c0260110ba8030507035101c01d81011b00010b41c0c0400c0d5030b410b409180011320482e803401c0800c812504140030391440031380e03c90f000440c06001c0ea680c84540e501829941d40fa000c410120320760002441c01e84060202c0e800360341c00c0c2d203200c030400501c80150300041c030009008540700d90381c0b420092000b40c400c0b26015041c1d4a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 161923003 1250 161921753 161921777
    0x52506080f06040e010f0f021305030f1c0315080f010506040213030b10051c05150606040e0a0f020a02030403050601050a0f0e0a0207050109121206230d0609050607 72
    0x3003484020310514548400841c07645504041c4801441c810801910a5482c0c1700c600d941240503015246200008140060f41c0e42c2d9901c924038814040e0340c0000b4482d41140c0c607206070381c200000b86030b804009910741c4940d0100c415001075000b08004000e031760035520000310020b050b4101242150042c210341c0b000303004950343d00d01000100e10a184480c1d500c019600014008910f04115260303001e071240001d0025513445400251034180c80285d030720100468081181c04014003032001203410190000040d07140d042c100000b80c0ca81c042c42c0a5840e843c60400006a4060903d810105008030080c808642c0c91680c844001d4a81d03026000a071981c4c13040c2400084d0904041820340121340f650358040100340e0811494a906013006000288402d0f028072103803010034002e20407040c03500e204044800784016a680c2c003034880703610000c40d40d40c1549460001c0107521407800c80c0950921101c070034992001c09550006402e007010810140c045032070000c0c00b40800400080150288509032a1000c064030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 161924253 1250 161923003 161923007
    0x5040c05040c09050108160306030b0f090d030501050108191503050102040f06021f090503040b0f040f0b0a170c0d090506010e010f0807030807060e06090703031b0b040f0f052506 78
    0x160382d114040c0080d005a00047e02e041040c00860082c0c251883e02090080c1d4031744a44d498100d06490350b605400c05901030202010041208880141003030400f4410b5601d060b002800310710009016038005051404c0c42460700005910400500030403149440f40243c0342e0401324000d4001d0f0240156001c1c00c2200810600d000103600082c4480386400c420301000380c606800040c007010002214144814031020500915180150a00c01800a52543c40d186002c28164030001c1591110f00071030410004a4041039000c0311442c0000000c01803082c081c0c50300f1610365503900c90400c00c1c01000f440c0946a504000010540380d04803640543c8080c001d07621461880c1d845500c0c0c2c85903d140d0340c0400802c100007202e0b000a0986640100400240c103030717420741010b0500c10f04803840c0071300781c108410900415801080c80010301d1045020070b0502a52a50303400d50b1031001074009800580b00500440400c81c541c0d594005103507100b400d94042c00100144540c900350034100c08040c5000c0720350007090241c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 161925503 1250 161924253 161924267
    0xf120810050a0b0c03040807060509030d0f0e0d05030d0f0501140306010501020a030e0307050d0803060301110f04030809060c070303020a0312150e07090302060c210403020306040803090c0405040c05040c 89
    0x15402826400083e14180d070301c8a840d40500d603c1c000900052000040c180c1c0b0070300080b401400251a40d6075502030841c100343c02c2c41107000c0c540041c412003508860b506588541e002c18402da041c4e9445e0045225420014a14062403003115440782c1400c3c860780c0c81417500e0304014122031400c514048202000703000c040d102c0c0400d00809005078006555040802d104041402400d10042d080c2c9856540f05d1000c5116501c01c2801580c0286000041c0302c0d850034244284119040603220140c101440c0d400c2e4100070740708501c00606400c0b00030400c1c1820340e95190488a641e00d1030070403542c100f5568640a91034500911050300450000c80da4031742d10510500646162403250a4440c10076030811021503401d2101402c1d0108000c0d44140c01300050b12000010665150448003c0040c42e9440303a020074807403a455020107100c0d4082c4000c1005840014405800c203900c001115208d03070b02e00000c0c13071070018281c0300150b0040c105400e0200303015903640c2d018161241980d041c030804802c0c5000359108 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 161926753 1250 161925503 161925509
    0x309060e060c09010f0e0316080f06060307140117011d0c16140c09040303050a0b12030702090c121312030b1018080f01150501170f0c070f120810 64
    0x61072003001064050340c840d817030b1000041040d0038070b18242e000d800042881d100340100e040070b490b04540024400c013101044070368580ea25000003041ca40ca000404241c032240544111100d00800010686040c0e00030385080d081c0703d00d07022a81d0400d60b0765110481d81e11205140d586089204140880d41c2d015580c1d00301c401900c013410107031003200b04903522200e450307400c1c40107416a0f0007404000212070350350610050059000760380216081c20b203e034586086901040c552481000180300d0b80105c60f0707000c01507a04039034046038600c031b1540d940040c1240c503200e4610201031981200d01003240c4c89034043d000380300e450b0091140001046115105604072400c501c00355038005007510b00ca28600744104140e21445128590f41d8458135907800c0520b1404655004012040e51203400c4c0206020036041600010402441d014240d440c2180040c1202d5502030000740008101000194001c0712030000c84022550001001c014055075060030711015100341407401c00943c00d0343c04603074441b07884450362080d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 161928003 1250 161926753 161926771
    0xe010f141b040e070306050607060b1011060c0306030708100c020d0c0503031b1605060114040204030804090e0a02120d0305060402090f0f19080a03120c050906090a0905070309060e06 80
    0x282a090401500001c00010411320805413541c00c04500c82d182c8070050000d01c1e100340c0b008550200a08108160f9101c0710305030780c1c00c11403245980d240d034480014070560040005190595070392075903400704e42402c1c80d0b600542d100744a03a61500360904a15442800c080e65103034262446104c4000342116918170689000c4e000d90320030300204062001140000b4452140c0944c0c07541b80a80314407400c401d900346040c1c00d45036500854010051003040001a14856008641c1145007505685da8000c841c0200d005842c20b040d5202070b4201c464004010f181c50494000b044070750540c040d0002569a04010464540040d0401c004500e00303051a0094846119000b41198556005101405a99820108456840804018900c4a506543c9050350186c18a82c0244c262600f40d0304001d0040540e03010801c0406144c072108265065018080c2c0f404254201d661030368404401c00090140c0d05940c03c41c2c40450700d0501800400d40d01903006c0304134984248014440303a200c9a41c21901c0d40340885071050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 161929253 1250 161928003 161928007
    0xb0a0b09010f05010521010f0302040e0a03170727060e1509010509010e0d1a15031b180901020915040506030c091305090309120d1707030e010f141b 65
    0x4815170091001c3e100c114030310944030740702604400004500c2c0c03500382d009504c40d0001c50b0b030900541c245030042c0074404400e40002c0403400c845582c0109158100740c03504100e01c40030030216001a1043e0340c12141c190701d01d400d9459040c20f20400e4001002540b1900001c5030081d038440049040070f0103414035600c8040d05080c18401103800548650f03120000ca01d04014820031642c0140e03a901e0f5140f000580510041c450910700ca0011401d2844043d002c176481c11169510910160b40000d2807066103211311500c40000407136200401c0900455841900319040e49000700400744205501409029404644001c1c08034811508400300e441207000d0203401c00c00410000c2e4150141030020040071001405860200c00019001f0301210390a544102480e000080d140e60545004009080000300c0d200c040d001849421801034546100c25640c510400940c00004076254040d6200300f51411500000307201d96503d003003031039000303184901102c038440203014080703001c20075584610500c01a039003030414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 161930503 1250 161929253 161929259
    0x507020a050d030c05040513050417070b13170d0504030f05070c0b07020a2d09020301060c030807022e050a0e0706050903160e180309150c07120b0a0b09010f 69
    0x1806000c084c51000c0078803a0801c000101e0740c680c0d486042121140410000707107404c0520341443e010114202440c900401406900c0108400303100c101e40105d44081c1007495400d461511094401807030b8000c1440020120b040b0915010780d4001503ca184269213490b00220f0714102580c540c0598030002d041d150100d08240104208400180421400245445641c1d5510203c1405070840c181802d40076413071481c000d4510080d1180010040d020105081d0304542c100b0000402d8401d0842d406401c10525001064055009008072481302071000c6108041c645042c2040c0c0c01800501803444c081460400017070076405040c4141d6404180100140400c40d280c4502110143c000c182c2c81e07075041c0107008101201d041c820b0921001030000e2415442c003403410801d45160074203c654888640d4104001c9054243c3d100000740c07074a00c0844424039103910540c015645005100c0d08284a4ac015050410041c01010149103210700f080403014042c40d0504414415030003404e20601c039190f51100301c28 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 161931753 1250 161930503 161930507
    0x70e030d0c020415030209040305040807050423060d050102040f06170609040f05010e070e0406181707060b0402030c131505090607150504030f030c02031e0a090305060a06090507020a050d 82
    0x3c00070004c0250340103945251280c0000d00c01c0780c81500c0c2200481d02c001000c1000d94003d2018000820088a04003c25003504d0000407000900549082d0b07641e00e5040052925660529446507c076040002152901c2c4c80d404c1076060f1b80143e00500780480c001c2103010310804103028a00d88503940144c4001c0d029207032541e900e1800c2c0709078542142c155480307950b50b8104040800c0b20740300800c800c2d06001007608041c2081412207110052404003005460300b0000420700c41d00803403a000c690399020b2590fa0200e401c100005100028000c0e40c0140000280007410703108e0390207000310f132880740b020000c11560752081e0310b200c01c500320900020441c14450311002c0d151200241880b80c0c0105e000d001c91200301c50079101101c8048500303c022403100400101d0950f814410314080e07000600095103020b09001c16900e01000c1c3d2481d0b2a401c1000240429085d48115181001154050201e454604101c020117000c0d00d4280940d400d610710b400c0000c1c1c0b4903440046c004e0702080c0c0082c06801e088140840c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 161933003 1250 161931753 161931761
    0xa090b1603031d03070b04021f020c010f0e0d0f0605060306040c09050a090f03120f020406021e070e010920070312090c12030c050d020706090e060a030c030b070e030d0c0204 76
    0x10038980d03d001004100c500202c207000400d5032900c543c401c0e446038070b05841041000000c14076001d52004036640c0d0006a150000f40705040d02c002402d14442081c4010000c1341c0001142581a8010000c0d001c0304042000c4000281c00e40c0380324030b8040c4000c0d03071200140b680d2600b0407500030707000c0d25110b0800c2004000c298801034004841580120f00c41c01310b03850303613150419040012800100036400c01c60303101c0418842c0712303e070b540c204400b03601d05131804d013000303542d40c90441c407205c1030007000500c2a1391340104000e010001c05200100c282c0300e41c5d4505210000302100c409005010784d0000c4100814443c0d40215400e55134941ca900c13210071b0f515440c640023000a2881103c520032039140105034045002c5c400305281d44a0303551010404010b142640c1408104020700041d54828041400307155004031000091310f64550400b441952010700088203100d8503032000c0e001421242000c0f090000406000788034012540361641d171100c00105265680d03100e8072540c800900c648130220014503003500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 161934253 1250 161933003 161933021
    0x7080703030221070806060406140f0c01110a0906050a09030b13080319060f0509011701020d06060c02030d170a0e0a050d020705010f020303060306070f1806050a090b160303 76
    0x903006042c140f034156604500040d01040402e40980c450402181c44e50003002d5940c01981601c01c80d003014580746010b0302820681d001d01d4502d490118104564003940000da482240d400340003070010700540e62500701c43e5030010501200040848102013510360246d421191a042030369500c1320b03050319685035900c4608004d0700310131900c2c03008068200400c640e900034501400c010411401504044fc40c110115034180d4400306810680c02000c00c960354803c1c0207141154910b80050100340e201c03840403030080c402d044080310320500c1c0090101c1d9582d030029a10003c03034403d500310350302d00304042c00a8031320400b082c1508800c4035403007001a0814000341c106100021140d005c64414000d240c0c0d805007400502900302c1c0c0140c0c821b0000308459a8800c07100141203800d130000c6c5140d820070001082d1904001440041417000114031815414840c05000803400401c841e000e18503525004014480e40c00f80c9105000a00c988101144100040c412511908071a24001c0d5410809542c1035015046c1c1c90 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 161935503 1250 161934253 161934257
    0x2120406110a140d09050d020612070c0f0b010914090c0f040e011112180307080a0e06070302010c03050a020406090509040f0209010905100b0c0c010315050d05061b07050307080703 79
    0xd0002c000444580110280e20030a00203041c0c4040000c10051000c00e8a901c080c2c4244000c3c0316541c00b51700c2e07550880350002481e901040050391800c00a461255180303000400e1219000729050910580c80c0780306050701c0141c9400c0c03020784440c192a502c1c80000350350242064020222002c92407404101040c040040508042141c400349030030b960851b1584000c4a810315400140c241c0c40441c030704071543e40070300c0004881c00190283c1503240d80d0307406161401400103400240b101c507020b0003400760104249004104aa443c00c05143c028064200c0e820340b1400310b8140004074110b86154025501030b10340b46d582d070340c842501c0d25082001d00c81029006560b01064a00040f002d43c65140d4550301130a44c0103030200d600e0134042800709040b00268069040d00c2424803c140d8a03000c040b0b8441109082443d002c1206840c8602010102a299021950088100d60072108000011171018441d600308a40c2c5001c4000c1001c5240007445030100007006504200480ca001503c1c0d1805011402e01038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 161936753 1250 161935503 161935513
    0x20a022509020a030510050909032205060703030e060106020f1f110c03180609210f10090311060403080f09030409060308030906070309020901210c1508070212040611 73
    0x5400c481c8100e03030000340304000103916941000180307003520601c3c030014001640c1c03408181c98995142038590048844078007011189008407002c02201d41c10700300c05007400038007160f514021450094000c1621200c481c21a024000000402c940041040e070a10f245510252180320101c01042c4401d011108104a03469510004120040d40150140a000b20b00c540103680c0c0300000d03c0c45248d41c24004080700d100b010200180700864450303d03001c0002d00f0304207051190b045410a045800d01611003c1d0070b0061107407501c44050b1040310f410042000740030386c0718203034500302400c07041361070300001c98002c1c2c08a031401d80416074101076000c401d50701c030380c142083c1c07400d00b034a800d0080e0a4640d01d40c000da43d030f6000401404400d2006201c42900b15a5608003040120040d50100ea549807051140c000400810129104070b010440240305513164442c54109074151521103000c0c41d844141c1100d4002100f04000464007400010300801c96003240340c07030500b000c0c03409500b1684104010002444c9001e1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 161938003 1250 161936753 161936759
    0x30d020c0708060c030103211407020d02030a08091c020303030c0918090a0b010608040201020703060c031e020a031815110c011508160e0c030403140403030f030b04020a0225 76
    0x7800302c0350158058407116a170740c1d451414401c0030256a006c085241c2d8142000902810b0340255044c00d200d440480380701e84a8515000081d055641204080e405000d2003c0c14001c02407080c004140090342221128010400b8400c2598040c00a91000b034040c1e1040001c941c0020300b40d00980b081c1000100160301d00300c1038403240c4c900100c09039003844c070f141e000c5005202009203020703005001d03003501e207000a058501500001d54030745a80c40060300c0f0a956000d916500f501c2600080b0007143c4140044581200c05842ca03c0207500030960140041c2c0381c201c8042c1c00b00b600c070080003000c60f003200d00155854420280c0000401c1942c2d80c0321307110401003013500300e900e80a009060040000c81403190300586444900303401c200b0642540d03c1c0490103000144030110039004070940000c4074515007034a1340d540340303404c0c1c540518001c04030450b03043c04100042050343c05158803158202380c0d5000d000c40c2080c0c40900059010b03e41c681c00158001c926403900c091150300c47c5840b4030310311404030111556 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 161939253 1250 161938003 161938019
    0xc051309140a0302070504110912011b020a0203070806010501120c02031c050604060f1d19020403080c10110a08150909010b011b08120a02070b010902270102030d020c07 74
    0xc4a081d58415039003101c40070780141a018000000103050a541c18402c62509006141e0300d0300c64030884601c200d07a50780d00c00c5c1a841d001d6228499280180d0710fa4408040f0214020350b81c1d0024040c12446072059040201ea0440b02241c01412248186c461030741e405007001483c00a0141c45000c403085101c14008008410360342002d250b034490800600142d04d00f0700006200580300141c012407025400240c00b000301c800180c0901041100c0a00441d000d238030b4103010780440032214140b1058042c00801c2c04000e00003814000c0408050700c40481310b4103003078061700d6415146a090000180c0e2020700c00b00920a018584d0b1542c400c82c0e1307078610002802004000741c611102942d00440d281c0d5036080c15180341d42c00200202d402a13418030792610a82c896a01c500c010310404400c03007105160140858000c480c250103445640e0b51040603941c5079a194802400250440038288515018690401001ca00c1c581d03000e0040040690140d480c0010032030000b406076105284c071440320f11942d20001400c1e1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 161940503 1250 161939253 161939273
    0xf030e06040b010305210307030b030106080a081b0705010f030e0309130b0301060b07021f0507080301061701090902010e090c0d0e1b03190320100516020a0c051309 72
    0x40d1003508908115419405c1080c588054046c1c280207840c0c140c4045180b0b03c1c00c000c26254040c413545008180e12403120082805001b40c1d0784450781c684100c603590004c00801d41d010b0f1140000b01068118410781c09496540c2d214803074807603207010902c14031032410550300c240c0206809001c210b00f2289052042400704500c9910340084141503540c4141a080d60700c0c0a0107943c000b80001c40748035081406a80001d01800300300d15a402d1907001207100002c030640201c056807001071b040391a80b92650b9603200081e00001d444050030f40151218800400e003159203105d070300250ba406940346142c040101c000e1041141c006003004100354414405000c0c1c4410703501862500005100c050030201c020307800815910380c030b81c002c2e40f0b1180e040004421803180008945607510794040c82c140c0303a0002e540c0c00c0a42d49400784560040c1d14000c0006400d0b44208940103280151400403c2c2401213811044c12a290039080000410300f00c1001800c10062509803101c2641d103010780c0c1e00142880c2c0e01d070384d040000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 161941753 1250 161940503 161940511
    0x30e030f07050307060302070b0a050901091e0605010f0612050c0408010905010f0f062907020402030708090601060201020a0203040909020f120a11030a020619030f110405040e010209060a0f030e06 86
    0xd9406040d007802542030510a180c014101424151b003007207060796070410f040400814680d545c2e03070ba443c00115140800d41050980580203c5801d0104040300060880e041560300c05564407401c00340009644403803101c507036084075205e95603070b1145c0b00400808406840d01900c0002200303401d20006c22812402e01c05c4224041c0306000000340c0320341c1039440b030041c0c0710903060b68010185040307800c100e42c40034200b01c000c0080e6502d514494182e030198214155014118001e07400620110402c00349580102c10940502078000840383c0d00ea0740d41c6001c81c242d210b4180ca402c0180c106000820981d521078201d1094140b000f003440d0b0351426a0f2010418024400d24624540c0e409500c3c1d6a00b80700603094207030380e80d80d815001b03403401c858240c010840ca8814102c04280380024900d40d95480e170f00c6640725600d0f10031040300502201d4034200d49a1101d401c9802194800c40ca4113403444c0703070071034140b0072554524806041c66041094210b400e50340d4840461040040c151210700106000c0402e010403486 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 161943003 1250 161941753 161941783
    0x806190b040e060d02010f1803080d02040311151801120504060b0a0f050307060806040e01090501051608060f0f01051209030d142e080a050307120228030e03 69
    0x41d80d10301001031020307490241034240181d1980e6150340150340d03c110280803031012405c0130034000d039000541c1c1e0301403e5103a0004d08200d40219030038441100f190010400c0b01d02424048001c800d400b4104080c0c801b04544070340d1170303100811500f058540000d80c042400e4405040050f07a403101c0e01d00750700c1900c00444048032101c0c0d803441c03649824075150701540c1c00340081280c440c1e02541030a0200303a444412b40a244180700144002452554a9400c12005191500000d2140b0000c0340703002c0303010340026581350000c0b032040d05101c40c4413441034003c42c1c0301c2c01004044108004101c012b101c40c4611041d4481d041140030004030350b8941c645114a80a600c00f440150783e1004a10075410865454000e511210502c0405102c04440501442582e60306038880181801c5c9580c0007040c440b21465001326000c0c0200c11030401841008405012080d0282d003002401c80480002240c44400c0001c0018400f07074100030214840b40c0094003040754900c40c0c2004404625880c001a1030100c0a40010351 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 161944253 1250 161943003 161943007
    0x31c020406110708060a050a02070f061401060c02092e030b0103110603091f020405040c020c041a0109170c1203090415180e1908030f0705190806190b 66
    0x400c0380d002d80d505441012041c080c03e0002d04113090152206406008450100d80301d0b00410401c407071030750481c2c1c065540241400c03c88a4549002805804440040075241e0105c40000920078041c11402680c2c90f03008282e06625524a50b00c0f1681c1002651400340f40000842528481404454000042c41c050b2229200c1585035140240e10f6100c041400c034080d02040c424481c01840000c1e119030044081403002e020555002910002801154440d550150038207040c580240d8001c6640d50038010305031018400c01041021030703c2d844401c0305829000450700c4904002484001c0c00d00c0d00e0314410042039030301d00710710400000c07540c4072220450f5004ac0c00000d01601140b5091182060307441500d2485482d0b94509014903120140c02010074545d00e071107881d880d010b66014070485120b42d50181031003001101d58107103062190801c5440384148080b11020841e554061800d1301c80c004e02c9011f0341040101c9070394085600c00c0f4098512a045958442ca00b002c2000c40b05c2e07000d024264040c8055 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 161945503 1250 161944253 161944259
    0x290112090f1a130c050d02010e040c030b0102070b09010906140d02030f01060305160f23030f040311060f0114030f010c050d0b09192a021e01051302040c02031c0204 72
    0x2002c4208050b1800c81850011042e0000064075034201800300da404844851245a050005031900d0178440c04c0303554014a42100c0540103505a4170030301110b4401e0303007102d0b00e19032035142400b000d10440c101c441c0450307011041000964818a02a4001214280f40504102508000c1c4082e80c00545103446490b1500c0e005002c030ba42d15214903948101081102e6032001c0c3c110f0000b40c500841c00c4404130030071003415245049403541c94070320002001750703102c09640c1e40b80003240c40800c0395045d40c044001615541e403071805064001070b035500681c003020324201c19903e03220985032006c0e40300c845141c041c0501a0300b00144a001e2186d141c854042c0c1c0c44683c0d50742c0094400300102c1d42d10700c50b081c0c841c09905080c002080e0307440381c1401e1514000c000c00684824000929220241c10741c441c0d41030f250401d0211204640c1c04519403480000000303003100580c8135860b0300da00761181240c6c1c02000120040c00d480242c90550083c0701b400006d1300641c1d1911a80d010319085103440d601002c003440d82c002a00b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 161946753 1250 161945503 161945543
    0xc1309020405010f03140103110105160501060e1605040e060a05130c03050903120f060103091e0c0f141509030a03090305070e070503040803091e01050703290112090f 73
    0x7000a521354513040001041c1c2d0b02501d4400e8406010180c003040e00c09070349404036400348084078114260310f0001880e841e09480d00c10b020f000103000d05080316000c0720200b0000c0218a00c80b415141840d1140d504080c00d1200c1804403a00c0284083c0e8000c080d6040090b09403195440f0110981821501064040140350003505841001d0011509036008100540116030050320140d0001e40b22080010981c4403180100d024003581e240c0540140d6851603840740710361140c140040308c140328000a0300040c0c1e98110410144078103118031011031f091100c0501652500141c80ca4032000781c0b11101e4141490340300464542414504211302003907281d42d0510601c103041001074002e2903202c549030114500307010002d0081c000900010055000400481c0241d00f0034801b00000c02a4801180303c1807820a800901a007026507000000c0f074a810103402a10078a007528403500c041c0b2041c030051307610801004540880040112481456a8070740300d50010384030151000c5214050441d8a110062070881 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 161948003 1250 161946753 161946767
    0x5090c0108090c0d021504050307080a110301060609060e0d140a02040b0607050703150f02070b150102060c041a0405030706020c0a060c020d080c0109062c071206050c130902040501 79
    0x11007800d650000700350410642d04c000e121800c650307050b01e003030b1200e00381c0f441c100002c4e000d203030041989406031640c0890300110001e0580001c5002d102000144420358050508850050203072900150629805102e03032805218440140d0401902d000310343d01c0240c4034203844a80c0c031681d5804541000c140c210643c0707414005d0300119541152140e260081c1a6540787d9615400d2000801019215103005901800742d031200c025000d1281c000c1d5a122081c1c5048070007000d0840c1d4414446140412403045944000f038014442c08000405900d89170034040040419071080e002e091a09008000200351602c06000070001065160010201114000d04100c40c40149400041c01c10020340c004802680d42c203405a11495001012140e03142c0751140300e1800b41a0051020709980c0c180410075540340a480d0000400c0d0000c084454000300300c3c1040141c032804c181c030070701c0c42e0825080071110100703080d0f03032245800800d10b85100e4a03010341da060f48110401107038003000280d03074003040821080d41c000318 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 161949253 1250 161948003 161948011
    0xc0904050f010e0706260105010c0c0b04060f1106130b061306030f06111801200115030b070509010c060b0f031002070b100b2b0e0a050708010e071401090905090c0108 73
    0x4c0d0401d00a07488241191b20b4140301d000e04100e0f5042009040c0090214800f002d071400c2c1c1c4400355100c1e11001c0c0030b0500c0c0c160f079000500241c2e180c003624504243c08038070580a404000103601c001415510751258480000c0d091607489018a82504038044bc903202d031400035449442c064203400c0ba01e003440c07000c40300324410800d25181708100c548156500d101022517582c4090824012104a0f441d0041e14429901d104610561800040281d10755500d25000d0131a031140b201c540d5140d54420301198640250b001c3c40d0b01140a168001c000140a50094802414047c0060100c505144002441d01781d000c21070102c429400201203080c00158174009510040c10282c170060076282080d01d22480c3308071250703040d540b042c82803e4581c411766101c04d11421410203d003804030115481e1496100e0030030300e50840b04c034421000000385c1080180151568000d41001401c40e41d07140c4038090340d50312401003500741042991600881c02c420f2522540c0c0c06104c0e01e1000385150401c28001400c8aa0050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 161950503 1250 161949253 161949287
    0xc0d060e0f060d1703102105010f0c050706091e0b0a0b01080609010b0705011d010b010908162903100509251413030302160b0702030c0904050f010e0706 67
    0x1410300d004501031101c0401280410040141d4030756508a42807100f40054011105408441d581c3c4800e0140d1050114490348c0260002c10441280340ba800c412218a96084004207400340420804a44558003031001c81c0c1c00742c10300070340c0240c41804000c180014080101c40e11104041400491002031040840d89042802d0807405414440002189034a05101c3c2000c2c2c003100103445e90802000f034010075a2203210060070381071004040380441c00307804401140c1d030004540c0100010000d600103050800c407858008024412401c040c03a9040100510110f000d6180c04003e9246403000350030300851140ba030840d044070760781f0b00300004c0160b5101c0207854a0004001070f100c1e241c0b152041081002d00901d103084c200c0c15540200c0d43c103030043c09010000e411346c0159440000605401160900086100600d290310807034072004841e03800e02a403e00a5010340c040007608403a030a15000d81600b09000b03600311034040706004885425075451007845a81c1d5004070381c003040703140d81029408030020040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 161951753 1250 161950503 161950519
    0x1050609131e080a020d05030112030c08070c0b090a06030c080a18051f0606050309100b010c061505030c01210903090b0304110102330c0d060e0f06 65
    0x808001201010041c00c0c515108035000092001c100c8000070340201e52080d0003902d54210740c0b605082141381c100b500e922003d800381c0d084202041c0e12443c101da06840001d2864001c05440d82c40c1200c840d070700410201c0310000b04112a030041050400302c0c00007840020260b60b40e90044070248061a2310603071140e405c0c9400c0600e0900300d00e8019000541c01006078500188681c103200c00c0c01d80043c5070a80140150080900362030401c0c43d540311642d07502c0700345102400b041ea6110b20448051204039007211160308150900c1c80104490b80081542210500d0300c0c0341c1484403a20345c0011540e404418210f2081102c001b00000e0030140840b2500a200342001c10007003096407192056940c038105a40089561864010b0400d03014002403009069000bd0060700c03841c152034105c10b54841964090f01500c01e050145083d0700004500419148044d4101611003002c80c0d500a61070344041c0c04851480300620010b210119640704040082410b09683e030081d003070060103507525220151202c6d000f030b440c03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 161953003 1250 161951753 161951761
    0x30307240605011418031903020606041505062b0617070524071403030c1e19110c040e03040f090e0303160e0d0b0412022802150309011401080105 64
    0x10640550301d50182805c08000701d24840b00000307052025590865450007190324613a414168005030041c49000141d17800c1203002084000e0311010015440303131540c060010042841c1080b00c22951144a03400714003520404005402c9200a03582960440d6617a603c2d8025644200407003046400018003058512540b028502c483c0200e94105074001083e41c400006212401c12040000603441c0700c4a0909070f94583c1002090900b45502000035005602603103000c46c1c0c18018403400b04d0710b16101d88041c10100050841041e6140e02e904003c90500340a1588041483d0710386000300d02000041101460342c0e14181000880c0005454000c7d206039841c0005048050100100b200c0d000080848a41c4900b19140c074202c401c111102140c2c0d8108401c4401e620411028180103800b40d486038023150880b090000040780d07100c13500d4400042e1141700700c490440032012469103902060018003100400d2842d4900481e50754000d46608829a5403130121140c03681901c0001f43c09401c44174001d100da070030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 161954253 1250 161953003 161953037
    0x5040504090b0f0f09060105120309030105040311150f0403030f0b0a0b0a200a060b0d060e01020a0e060c0601170a2405010803040803040902091f08070e0103060f0b070203030724060501 81
    0x10050051500070881809e41c2e0040c0d0318100261581c91100400a001c03901d49450028600d05c01c05c52090f00070300c50341201c00140300c03100118030300c14000b00c04541d0065a075030310200c014110108022541555641c0b040000745c481e001540003604241c1c90042e5110a1800d004015000d09481640c12840d001c403403445e00000891500c41d103580200001c241c8659000005201220b030300002481c0c58035205501515000c10b4010b06020310aa0310b070201c15401d07040c2030101501c90107180c2c1c81660006401840052444200d104103403c10f11308882c03070101c59a4600c5844001528010107851000c2c0201c41e28480c0381c080d940c0902101000742d81841e260602c1c0310b9a038004d07802094209030700880ca00d031050311544003a800b0749180c851440d050180014014140210940d002800a11415550f0f151940280039000484542000202c0e03805d00c0c0c002611919046081b040341e05000811030040802c00b40c0d6800b2461288080c04200d1140d00070400c1401c9584990080781800500540c14440103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 161955503 1250 161954253 161954263
    0xb07030903080612011407090f050f010813060209030d050705070506091e0d0210030f0c11030706020702031504030f080105041b0e0102071503060302090a05040807080a05040504090b0f0f09 83
    0x1034003a1000400101300515160140844d88a0149080e030b8000800040b158011f80140031101240d03140880c4584a20038004000034803114a40030580d444082440000280c100e4109940101d034014101440c0c480020b00b17180790000d05030300080000c075081052010030300c030600007008111a2640380c8003000740800c60869060b46c01051850a1006180140c1c40300c100103140c0d180d00602000a01680c1e01005d00200356020030003d9081c9840451485c081c0650b821040c00840341009500f49075090356440080e41c0880b608a801d402100c12840d184800c011606001e2403094896150a4059200040500005901451180e400c0c40100c600840d00c80c0650b22a007209858805020140e50303005071729240d210b521980005c01d18075101c20185a041d805a0b048d41c0c8216030450058551412070010345000703a80c060300f8480100405000208164000c003650b82d424240242001c0e6903000080441d113160405640c060140020450000746107409a680455403005280050912903522503640d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 161956753 1250 161955503 161955511
    0xb010c14010608060403030203040519050316150207050d0219030e0108060d020a08060a1d0705091003050f0604060c02160b030702030409060f03110909030a140705010e01090b0703090308 82
    0x4440805606400e10402c2d0001ca0280c103e41040390040d00305458010029807040f64180d8041c05003655a135911030340340300c0401419800000650500201c06841901410541d60031109501850001e064a60450004d0442d40303004030040c0c010a031803080040d00700007001c140c01440c00b2074641100e00081e0004141400d41600f840c28489517511500031810000c0300d114081d41c00f442c5100d001500700c00004499101e0300000340c0510038180b01c01c0444180710703c02101c08506401c40682071006003042c06c400360303020404031003801c4500da07252103040c1001104100b80500e50030920800003441801d000300c4481c0c40503031008101d210300d00710000d540e607025402061900d407030000200d081c1900c02c000b0390b0043d00e10341e2020000c042d91008103c2840001c0c3c402150044114003400c3c10600e4110901e5114032503580165240a034035a408440f0b003071403408001d620050900040f03000c50720901c00c0c40300c015106400090070400b1410a1240414020324590425090500303000000b940b10140701c0d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 161958003 1250 161956753 161956763
    0xf0323070807230c01201203070c200a1d06040b0102010f0c081f08030d0b01020a060c050306040b06090f0603060a030210050301030309140a0b13030501110705100b010c 74
    0x8442e81c81c9082c0d03e8003580340002c01c4036a1500008908911004202d100c0e00ca0001d8a484600d06410042d401d802c0b511460f1405407600308094540f961441c1708002c0d41d01c01c85d00d10b08510b007440e5079981c241609000610601c043c201000501c812400c1c0f00b0201d170090100d10f654a5420780000d4110190482c00505603030150340c0790310b001400d1740d0003500446200b480e05603050007072280ca0f130401030070900f0880d640301c50504003203611850282c20350304400c203580b001805103150000500010014062550886045125940c4c00001140b6217104010b40d4034140d540300ba030340b410f21808110691701100c49003441545c0c104040300030381d503403074820a03002d40007a03070815165130711030002403002403190b80b01a400c50011221004a0340c5d2110040d8180d9119031242031596454445013901110340540c0755070426403480050000000e250080c107a154410804415080e03125500d00342500c3c210303101c2400701880419454200f11090220101c10100c410041259080c0c000008225929601004e00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 161959253 1250 161958003 161958007
    0x1e050f10050706090b0901020d05010e250c02130501080607021209011202040302040c0c14010608060112050319020c041a15130b1215270a06050405040f03230708 71
    0xc020f080d821550b000d5801121130b4080c4e1904003032142c040c0d4022998540024074000010403005c0300207881e10302900888054102801030591180004110040040309220151850000585d41c0c0450800105961a00481c040d4580b180161030444081c00e080c0130f40d0441c00784004002a040150b802681003460160790304202428248000d200b82d1708041d40080c28101038040454100c158076020520a51015051140480e00c10742200c0d114010740381c0c190030040041059050f02800c1000c8140190300741ea1424204148500c1c0e4400c0d01071031030b009070300500c079610030703a140610600710b03c610000300b45414203a4100c000f601c0c80c0c03100503c0064404010900300340e4000c1103056038001c0c000c03462103aa91054221020081e80344210341900003696814411040350402030a0000c40c411100039103955514284260040b400004090391030713ca80d15440056032f6030781c134040d80b0700440c05504841c515007080c1c2402400c014a2050540da0300f803035001740f4803c601c0000112400c8c10703045402d080d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 161960503 1250 161959253 161959267
    0x1b0509012a06060e07020607080405060109090201050f07051c031a04090302030408070e1f0b031501020f07120c0b090114070804090504030522060f03090f0506011e050f1005 76
    0x120400d8941e000107840d40307103803841c00b080490f001940140215455000c40b0700d29540c920085450301c02c212001802c94104500400c05840c0c0e40d00244030003071050400505000302d070600c1c2c10b1140c110550035161540000b8800203030b03040381c806c85010a0034a2a0511503001304010700c1004000750300d10b06004945d60708503801030610910584003d02005c13030548014aa45812528015405950000042808000882c1502c140500745000c0f61101d0441c03d040d561181c00301c454a01d00c004650f415801490640310051606102c180090500c10000308a400f449040804004d0100d40000d280400300300580c40c01030381c010420072060a0124101ca45c1c0301032070318115405020b40d510403c02541000180010160400064020740c0c003a201c495244460424039050400b4107071240200cc01c50380f0200b551002e1003070300601e82050007804018141640c9507a520b1404100760301a040102642130261041450807001000070141150107000001d81c000010710f514080031a00418820005840 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 161961753 1250 161960503 161960567
    0x1181110110304061d19081002090a030b0601090f06050a0201140103020f0d0819120b030a02010801060513030804030b041b0605190e03101a04020f0417030d020d1b050901 75
    0x1d1080e150024050020030040704542c065440321501030001f0500605a04590b143c001d4801d032400719030000d0010028914507102c164032010003405140c1000380840c00441c0c1b00e800e2891080040c03546032b03542551001c030801c00034210b07a01d0f02043c00b2804500001040560b4400035844104030040743c0c6140d440a8078680325200d4400c0110190000408440c3c1e0380c00b050700414240c4000320394003018050709400c20b0030075440d4646d59100901140d503200052010610900140c400b0800e0400002c5100351242ca5402d065041540700f00c0d43c0340c0f042004c000810421001c00b000b40315a1060002016003841d03009002d50140e0320151500110801001039410701c110000002054080c094400c0c451f5030400030405000503031402030120302d812801100300d0030180701711860340c41040c075458102400c141114100c11000301500348035200a0101a01c4002103200400e00c226010800007008a800640c2603412070003048218140300c018042100e0340e07600304ca52940100020f01c07036020079481302454 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 161963003 1250 161961753 161961797
    0x406120501031109180601230301140a110d020310090b06040807031212140108010c180315061809020405060103020f030601080402030f0d030e011103010503030406050901020118111011030406 84
    0x82c2188186000001d80231281094100803d440001d00c00d003082c4154140f600f81d0305442100d00888580f02c000402050640d8481c00d0081c203800101490310130390008250503a002a00d424100302990300c03080024050503c544c959184068440c0390510785040c02154035030b01a80b002410b140101c8295090541c800c000c414440d900303040b020002000030482070a02c80c1400d00070385006619002380e4504090103409003d106807604e001100c51142160741c1c1c03203003038100c40513003101c0562220300115542032140c100c0e10170958006000242c00e07209004020554001401c294140351040050500c21091038007203a030321040031300704400305469070f2004c42d00d80244036000000c20b01541444404442e070ad50071404100703002000a01400140d2440298944020710689a00d50b004101c200b1400f030081000c0c0c84c01c07107414000010a980003207040c050042165008507886a041c8141c900c0342d01c1c0c031640d4060b4031001450300d420305259600100703940744100e0140c2b00074080403500c4517090401c2522 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 161964253 1250 161963003 161963041
    0x20c06070321051503010c09142806050a0909050136020a021605040b011b1a0114131116061d062a03161b080406120501031109 56
    0x24041002c0c0ca8030400709501c4d6000001a80d12039420318a01d0045540f24000610a80d00c2c00c00c407004405175240100300405000c00440225042c03904151406032011001c3e02c00181040d03165540d03100070301d44000703041d000d0719000f4429640c034100050210320b100c0701500050080902104035034a4581c41c1d0078010800640c440942d440c000185d400200b0341c0400c217040510340d0b00e842c5100d4151618100416909016803040c0014148000c10302500080c03070106403842c2c01002e4680c07550700781c841e02266810b0241c028034016201400981b0090900140f20886c807410000104000c800820748501140700e9910840700d4030540742144803c0c05226807001e5a100c60b800d420021042044041c80d864460071135400110101d44120710308420f400301844685200c8400d68140b4590340c2c04c1d40d5000e458000c0d0045010029014041d038011708611200e810280d001b45040e5440f0340c501a802850f2401c00307500000c1987c00c2000410006000c8070110400603011101441c00c1d980d00f0851507180c80c8124 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 161965503 1250 161964253 161964317
    0x18060a0c1e1d030303061507021201060311090702061501051b0106030b04020307050303071e030e100305010807080106120627060605030706030c0503040209100513020d0c020c060703 80
    0x109444007101e40004540344104180c0708158000d10140c800c25803240811070b002c0381c000c81404a81d0f9428501000101741d00c03440240f03007001c0d8074203c8940c1401c440194104441d080f60b05050810076140c61107820754002d40034402003015240034003c4042c0c210412468905201c07002c40c052482d08039148a0303100d48401800204401c0c0c0c5d8078102100409400d54060b030290040c0c0001040781c1c00c000c03044480140c1c02c40c000c0c08254000d02c1000d031607c660b1000c01c0d41040014566440c00396102044194000403d0343c0c0810030354113040c40345040c1811940100c03802e80c540307a400c106d440e15154404030032a401c0040010000d43e84c4201c00f01044181850010035600484044100700c100d501100c01e07224180c0442e4034950301e50409a045034820f14243c00131074010b00c000390041c03500065480d48403421f0903110030450703501d90102e4224001884c403620040e030041900a21102c5070710802040301c040344001d012942d6500302240b01032040004c013900b040805c00140b0760940d41c1000c0380071414006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 161966753 1250 161965503 161965547
    0x1504030e1009230f10050429160b0702070810051b04030c0303030c05041413060902130e091207140c150c160503060105010507060b030f010e0618060a0c 67
    0xc100440c010500c1e5643c0c0c9481030328081d010040f01c3c00d000302e206402c441261140c0f49090700b0300380426441454901c4508610210581c0c0003040301807003025102246107040b403400305541910b06040b03803d000908550031907108010820242500240c0a094002115000555a1940800501c05503040341b503504a0060002c0d0002c100b141c04554141128043e07036040000c050b0a0358210b40e07601c01da10686050b04607800c1030348090b01d0440d80da0440000c40c070b13100264060380c0300c010a0a9030800c10040e5805280c40b8000c01c42001401c4144d640701303c0d65405090780198111014546004441000d81440310103c01d45000f050108091103c3c01002880303d0000620a4050345903640040d9222707200e4003c0d16040c0907511041c000d000207503000180640b090340c1c20302004581cac03a00071400c180c84094884000d819540c80500490340749010403030001c00c801d29200300702854014007412813070460300c200c007035a1294000410b100d500807480302d0303000c180c1d082940b1040b5020b08140116207000d0f03001c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 161968003 1250 161966753 161966789
    0xe011b0803040201080c090d020103110d0f06050f010509030a03270b071e0309090c0201090b0901061410050403060c091d010906060207030807020918070e0601021504030e1009 77
    0x440c5001d1486580300f6a035413110780c0c0c3c400041e518103004020300a0780100701d140f800130066019030414400b40e8583d4000506000c01103c50030240c60000710559041070703580d4424002c0e410100c1902e0500340007800c20701d01c0d000d58140401c0d0380b01c15401c40078041100036000200282107501c09008686012298200c1aa0300c2d00084001c41c1d010300070031519840e00e0500891102e0b0b541c082200781540540740d1a10040c0b800b0341f450042c4c030440e0403010855681e1060180040c480710740c0076000350f01d10000040d2050074084c000a441025500c46840350b1046a1004220b43d406022a0141d0340d202d540442c000c48a14401d4404007501d411400003140d04c10185061a044001d000d4100c50f01403805120040c0e58440a90301d44a6038003000e00412002c0080390301504014100039000350341e801040720801c00c3e003d03601d428110690003001000d802c60050001c1c42d030b81008a0400c0700a000c0744000c0900f8035a50280c00d01d0f0004030418002c814401066503540e0003850070340021308900104680c401e00d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 161969253 1250 161968003 161968013
    0xc03181e02031c02060a0b0108041b1206090203060c031b0f0d020f120f090706051e04060903060522031b080d09020a0b0703170c0408011a04050a0903050a0e011b 71
    0xb00644030f002c014030400c4006076001c81240100c0441c1041a15180403a0300d4079203070f44001c0340794808240c07032002032500005015442028444d040c207000d03034400180b0704258070400d810000080c248202003042481400140300d540c545035a5611064889540d8441048500038400d00a24641807500c40c8042058a041801c03440142452542001d00344465030742c2c0b120020b1030040c01e0303d201c2c0081d4400301051003003034003c80007440c0031500100e0344c0004404605c2e584c0c42541c4a600103200041c1410030800811885000360364000c003204008038001c0c4400036078004100740b464005810403c028850150320f40300c096030f841c0416040070f051556024096000c2002d402c000e10201d001d402490000030396090340781c007640c00690b0316a42c1c8a03c040c2c040324524480040c003510080114504001c00101f64509115a040e411514148444504100402c010840d08018181c14489051801030000240d110003251910380c0c0500700440000d072080e00485c3d6141c1409401d021220700d115150301404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 161970503 1250 161969253 161969293
    0x70e071218140c0a14130905030c1f09020102030a05030a020918220506040b09070f03060c030b0105120402060a0c05030d0f0c170622180302010c03181e0203 69
    0x2280c00003c640c10900c40b0401c0c48031584a030321402e2040f115410340d2142070f10b44481c0d0100200220034001c01c0c0356801c0e4032220f04550011440007541d03400b6134482030140c0d669a16249807c030350100c0810140d040c58001070345a100d0380030241d040000c0080081d41d41800c0f0380c10394101c52006040c0c2000103650303c28160350790300203880c541383c454941000c40a1100281c8510200a0351202c0984596112507031003201030b61020b01b410280d070091800200340c11600382c00541c01903010340f0300816543e501d030401038102e034010448981049010404c40720a009403c1c9182c0e0443e41c1940d4803a684d04040d0700854a035452588000c00c40c0c00009034827400c0c0100c41d000a010211062010007100c03071083d40a4519074115000c00e2504428000003030840d203080d07100340800700d40c55064906011101054401110a07408a000b03070400c003c6051824140d09100d0206941064181000b001407900b8101213001c0d003619004102070910f010700000045d014040c1c8614550140445040f0166070b0701d195002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 161971753 1250 161970503 161970533
    0xb161b030215010902040b16021206072f030a080c0d020c070906051804060c0224090c220216020907050d0f0902010813060b090702030901030608070e071218 69
    0x100b10844000b081c400c0c0180300316422942e081494504d03000107401007204c46000400166881181790741120f021800c10702981d0301c0355416070f88050110111070074041a000201c8020000c80b0203d51038544400400030842e020940c640c107000c01c0994442c1019030052042030342d485c400600201d1500c00401000541c4403e90394400000d11a40c0e8451050118410f00710001ea404518881c02003000f054079584280c41400d8207105582d0100d00348007003070103910030303c051407013484048404210750202c00344051339130361000302c07010441c04440c2c02d00441e229090b034410a014070b90006035000d0510b41500414103050340a0030b440c00c1d5281614000e03101e9082038401c0c40c0032030704011269000d205c41d4800c1c036020720344c16121010350307032608000c028482c205034004840e4160b07920303220135603541c8101c4810b20411035980255a122811000101034402d17035032081d0407590041d502804107460b50404160302241500e000b10086130602e0107903015020540486500c02d15400c4990244500c50303241410f0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 161973003 1250 161971753 161971783
    0xc03080a2a09090203130f08090a12050c0f0109090b0f030a0c0608010801020a08010e070302090405041103010e01060305070621060803040306060b091503060f0a0b0a0206060d0b161b0302 82
    0x500343e4541120040e8402241c11400d6064070901354000220b004514080b8036008550403410710154102240d100149070f00321a00d480d07180c2400c0010401b0400c002e504c00142070714100e200c0e501141c0081c00034845806011700300d1703480e00350f10304c640e440300c1e80c2e2482801e0004085910507120350400081401d1035000700000664000c0010614000c14001c030b0344030040b01d0f0f0301c6600980ca400c0304c581c02c0305c00280c036074003c00d0340801c5421100e03a83c50181601031070050101e100c14008420405017152681c480068044c4d0608004001207007000c40c400044442c41d051030104035040c0d8281880411010000b0100e00340f400e071000c5000b500000180040c3d0388507240401c0310b01d0f00d840d03040b04140034152191b9400031800207003840740386158000e0354004501034016415140d2840000700e01c040b9075040414072800125007484665810410107402440648400d1602d000b2519000b403001402014244041d030980003018803644a07001010043c18400c54500e202c4c070741c07450021749808106072000300d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 161974253 1250 161973003 161973017
    0x50f01080d050408030406050306040b0d03031413020d0807020103091208011a0414010f1b0308040b0609090607080712090b0403120b0a17010204030c1d070804030c03080a2a 76
    0x10480340070b081101e041d10301c5075004600701403030031804a419a000808280e0400c0d2134411040721034540d100a0080709109880101d16800091813815038440300a101a0422214054100161326200c24031110035030003881c810342d11005400143c005d0101150010106202050f03100b1107154400b100b203050b1a210340383c64401c0ca04a000c50300e005c0c01140144a145003480707403007441560107008074200082450400e001078600c9000c0b01310050003410003e4011868400c2040304000b0000442a1f0040c4112441e500600b0100000341d40c998006083c00d0501648070027003800e080c090300324444160306040d0b061140002034500601c0d0004151021004900000e01d50088080103014040100f840580b140c4820f038a0000208100d03d4221442860355508010110100d061024003030040c100c680d5290300ca01d5203124120014038401000c0c0030030052107100f03000000764085103040001c1d0b09807070030306116110203142000400e907440c080302c00341d2411841d2030300180600c203101d4079010050315201 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 161975503 1250 161974253 161974273
    0x905010801020304020a09240902040e09010e06010e0c040e040303060306290105161a091b010f05030c1204110310060806010e27010f05070c110603130501050f0108 72
    0xa8243d010a44000358480141c40b4180003000d03803907020040529101a03555540744807925183c02420054020040c019000903050044480c0b00641e26040042940204140d5140c104030310340301c13141030240c00003003407045012880070f540b240281c4003d00003400c840400b0b4141403074044c006080c1c600c02140c01600b81008450140c546666844065120303121440200445000442c0c0507400070b4503500e440150008007501040e09200d03813082c0280600c50322600c0b4240210078519109190f0020303c1024590142d01100b030b41e0001c515509a49141402074898442101501141c0034503000091401205000c10051020383c040d40b1403110410340c165160402e450490209a23030542c0074040c410343c8804010030040128042442d8003032504042507100640e25051401804081d1020ba182030391280c42144121543d4411103810403814105001c192000b552010b0800b0200d944003032090b600440000c1c0301146280c000d004c040d0b0722600800091400b40c0e0030096040b030070b01a04101d4481d010030380c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 161976753 1250 161975503 161975519
    0x3010603110c0c102f070b1905090d0203100606030510060c080702010302160c050907050c0c120102090d06050a060f030f111f02030a08060109060f1d09040507090501 73
    0x4481141c0d090001d020142c144005200607454203403620710403c42d045c0080074a07420804141200880414500c80140a02058003494032649401c203d50314401003008170345000c0304040c1e61800301d4140c10580e45910a400015090500955010350907008111390500192907542c0302e0300c19107186440c100301684400c000038288460501070760b0040380e6070103810000b180203000609401031052601510b403000c010502c0611a03400c00003205ea455103544140001e1404400060384a141841d100703040c0b0346649540d80d500c1511103c02c5024045660000c0740d0340c2e0003901151004000902000070f060024604070f00104800c88165130b4051419001080c0210604a180f088136046004440000a240c43e9003180841521485078484001401d5414882d0702e60342902d08406250055910303141600d01c05001104010116410084914000d012003a000200020041014505201510030000d11031442580210700c40340d1224a0004000421400140c04419218660001c3c03240e641d0314108 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 161978003 1250 161976753 161976757
    0x2030f09061803091915050408150f011203021e0307050c0a0609210c060507030f02150c0a050c1c1b020f040f0f0908181c030f020a1203020301060311 66
    0x400e107010b810800603d0300e85e01d030a03959201c1d060f5072000309001040c2e03503503103005040c0218070780c1d04085800404d0402c0040014052400b00400310300c18400c4500d0002002d286121050007008541520104024103151007006054413016003050900d58000102584c1da0356500588001c40d00c07440380154038060350804a1003c8211003458589900950070640c0805144e89400c0280c001d0f1259075080d038001c26000b22215000f05055114265180ca46042c020156000785000c1c6042d940044940389480c00b200355280c0c1d000000b600b1175503d1700c00102c0111000d118860007509542705154010921500d142c07041c50480030140c60307291510a007040400c1110021940181d0300ac40141c0c0d002d09281466008480c0d141640d100c0000c00c60740030800c1e4800c8400d810810368031580301084290490010301c5954250100803606a4141240f50030710070051034aa60000301084a42d003d50311300b6500030001000d40552110201803042900c110040c020f41091194000180c24080f80560080120003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 161979253 1250 161978003 161978041
    0x2a0a06020a120c030c0c0b0306010305010914040312020405040e0610060215060d08160c0305010507050f0315150d0e0c0a1202010e0109170a140c01050304030e01090902030f0906 78
    0xc030240307007002c00502c150303805511800c0036400d01004c0a0100c0c0011401600c013400351422901031134580c100440018102d45050300044500d603d440617580c02001070001269000f58541341011072188881840c1c00a03004a03800b9a8005007032010038181010013085d040d1090b01e035920120381c5542d6840d4105c0c1c0d18a0200d0b08154100d020102081c2e55062022549082c45c2c001d40d000c0e45800103a14248840801c0390720185c0703a1410888007801000401c3c0203440c0c20440a10300142000c214070100e0500d8400035142d108000052140c030744154484501035060900c01590850b03d9100c03040000c2c004c0d0508400079200e0740580440c0c4841440c25041080035140c161240c0c10340c0300d1390b43d030041d111915451000d5040c84041c04000654060910865416200040103051410014901444684101e00f0b10050981040700c403001503981c00029a640240c0615040c580d070140000180d580d200c01d038008507400ca00000070491610101c0c80964040d030040c0d02100c00b181d41c0d5443e1441841300310f00d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 161980503 1250 161979253 161979263
    0xb120105040f17041a07060e03040503030405010c02041119020606030a21091a0c1c0813080405030303070e100c03080a021e1b1009050a0210022a0a06020a 68
    0x3151400420001501070f0b883c4103040c40c02c02d00c1c15440e800ca800032a12100c6080400e8000056510204541c0340240c135203030401c01004605207414100001e4482c02980034545c100444d20120006550b41e50b0401c440a40d409403030030780c1d100c0c4a1140900b440742e00340c4680000d44030b17540c0499028103002a402001c2900185119071045501c52010072850301c0e20080006c018220f01e020410055540311a4240f81c002082d0540d9004000c4401d4148100510041c051565401070180205c0c1c003c0301d0603030b000c071440200b0506c000d030501c0c064031240a10b801c00350b0540310200800c0007041d0022070051f460f100407109003820003486001110b400030640c400400041046011412140164002c0c050317000340c081d82c00385503002145840301c01e03810611000e0070445405070082640716007070000360b81d8400300d003000340074220654851580e02c0c421460024003d8091001812501d44240480e0b0001d101140361000c803823580340e58013000c61015a032090700c0b440d00e4920000302d4a00018818076030360f50007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 161981753 1250 161980503 161980523
    0x210a0201030c020f0f0304081e0d03020f0f030f010509090606010c0b06120a12140a0c1502091806013c0c0506010303050d1b0c15021b010b12010504 65
    0x1a900440241041815480a51003510b01c8400500350600880408410340b0000310745072880d280500f4649000444400564440301c01803504510700450303162a80d031450305000daa41c0e003010140340e002d0700c00d00e0015a403d01020081c810a03031a141c0c0c080d030484804a901105940b5000030290b1502426200540421012038141002500d0184e240b54421801442002c010282e03190250405030b000380219268110404824409500301045042030b404c5203041e40d040600f0b018010302411040c0002070320044030384d141000110340703540446072254409401d4101a80f100d1710417090641e011386425000c10303c1111042c6107107940da0400d1031756804d0591401c808500c0c1c04007a0305a10380000814080024401e60540490000c20205009511036518180e480002d0358082c82160381400b05012609001d610514a0f0390b440f40c40f002403181c020542030003e42d004003141c0001c0c0325580cc0f03100301200c104031200000d4010b5110640f0320006840c800600f51100100500301c800c101e8008201c403441c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 161983003 1250 161981753 161981773
    0xc030706050402040b100e0901080d020604030c060b120f12180603150409150516050a050c1c020c03150103080307050c03120f01080c010207060203030105040c03021303050c21 77
    0xc5400c440c0d0094000361000032810020000b080116412804240209902118050b040d0611210150041c41d21740041c182c0070100c940029181d001c050406401c00441001c241706102039540200c01900c40140070003480c0041001503520782c4421071010381c60340900c268080d80002e40004840d0448220300c46102c3c1d0680000400ca11a040030301000d007075801900c1d00013100d81b074910900217800d000300c2030315041c0c40320840c1600031782e040101242c000c05010319910340d10b0f9400a090b21600e200904003d0b0f10740200c54900c4c2c1c03811310403407414809091030184400741240c01107120b41c0c00d85415019250490380da0f40075003803040001c1c0320081540c50308000042e01148103001904d441d20343d080549141614000d5074420f00701c020f5074002000c804c0c51f40104441c0340100801d0410001c21700280c45843d18022010391640014418980510303240e4640b4a0014030960403642a4400c4184000c0800d4880c1092942c40300c14041e0a80143c44101d90040700c050914a00465269140300030003188803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 161984253 1250 161983003 161983013
    0xf020607110f01050c03010f0f0302060d0209180a0e2a1504030602030a060513050412032301031101090b04080d0e010314040b1b0901140f0f040b0405010905060c0307 73
    0x141041918140251181500b031444280185801003402c1100700b500c07541840c0f1610390b84035403680031314045a501c0c4001c100584420064822420000c2740050311144500c010030f50b0610058010311f0381c400004200284180c0551000e4050b1180408956a0704070700d00b10704036080d19620505150f030444100d5034285103400490080c3c1000c8802813241095520f54610099802c181c03140002c0030744840040c803103410804462200007000200902050409407184a03615004036180c2e0704243e11401e031200f0001e41c0207100043c41086405c0e941543da528244095084000079034075000070342420000842512850076101550384100c082c00c11034403202802d4510200406c0c0d11810f240c0c0318010f86254019107140a40b0a5000349000445c49c9000b000c11641840310813a1741042c40c000740845507450b6406909070075a100344a4001e50785d01511580302040f40a202d90030b0010520004003c11401081c101810407128203880e50391a0340d44400400840b400b41400c0700380554014449007000c21 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 161985503 1250 161984253 161984267
    0x1170702030c060108030702090601080402060d0b0f1512060d0b1524090a060801260f06040f140703110d020a09110a09080309030607080403090815010303020d0f020607 74
    0x60068011a0b142041052515041c032400340e00c0084660804103071041541800117101c0c0c1c0c001001d01c2d1032106468903600150039030041e0500c0191055071600040d01d1900c0b1490904a802d200810300c42d0320101d0301145200c2d541c40000007403201c50588010503071500306544d004490661000c0000d20350340d14100c004046440f0500d1580e0f100d030f0700001c1c000c4000301d03000404808162200c440c980d0b0b449058240000495140c0c440c60802540900422000c08031550344c003900c1629401c0c80400c00e400d1105030745840a440340b40f24403401038100340b01c104141d8001121340749100e04c05500b1583c0707a4880064507200d8a120103007004d2610480c1e1804d07890010744901c0703400d1000707000d4510b03240c5a9820703d00310b03040c2a2039406014000102e140c041500300100100905c2018010341c075200c5aa80840e4a07180054245814019130002250406006009c2d0f070010385100000c81c0d00c0c1c030780718103c0c03424411000e21068015008240c2ca0009991140d095016019601e800801d03494a600c7d4080b1858 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 161986753 1250 161985503 161985511
    0x9150902010c02132304030314010f050609030106090204080c030609031c0b0619020c0411130605070c0911071106030405060103030807020a14031809010608040b040204061d10050109050117 83
    0x4c56640c88054000003840c543c45154865111010b1030b90b0315080c54003034111411003050084250007880100310084503041c40f80240e80e4250340c01d540b40d000c0c590120f030161807540c000001540c00880e01080b802c500080c1d001c0311310402c074129012522401125610791084074880e40d0508010040b007c0c02c40e195400010003180050a01c03482c04081030b42031000e02c490b030f000310b000582003115000400c1c0b4041c000c440320403051000c100e02e490003180d49051050768900c00c100a000c2e001c602c143c00c1c400300030860401000b40c41002c0c48a520007034090b8015038013040c01100c0c1c04079820060101400c2410039680305a03400030092140703074251b45007070396000401030000045110700c000c43e0000600b0202040c0300b0141c0b040c021615012050454070240d01c40c1c0203542d0150442800400866a20550306070300180c002418034407945440c00032901419030f03a00030040460041d41100720641c1d42a1100e84590b504040d10040341d5100c000449914029108141c00144681c41205c1c0408140b030f007607904 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 161988003 1250 161986753 161986789
    0x40b0a0c05061509090d120b01030902031204050108010e010806040f02190f0806010b030403050d0e0307080c0c0a08010203011a0d02040e01030c030b07050306060403080c0106081009150902010c02 86
    0x500900c41e07807210b280075000c444071040c50f0740c80051840d00d41880441940c000751600058500131441c0c00c1c008110f08620340001c202c007501ca00880215074042e51102c00721039009800d4420b1030040c000100003a501c02d00c503c07400aa007550001803400180d2681a050720a54005001151250f40740c81d00d1805070a04c0980e803000300000280555460018000001d018040070044034a10f0b0000141c05c00344140c1c0b0204100c44100b04020009034043d0071113090502361a80050301e20304915200f1310318054078074010182400040c0b01151000001641040c43e0b00441c0c41c100225102c10b001c41c00d0380030070b00c50041d00056a2500a070511100700c0030744000c410817680181030541c1c641c0c260b005013400783d10551340414a0f0000f03105102c688070348240e0240e09420b0203840c41c102070b000b2410510440c40013501201d0b010600410116083d0000c4008004110131114065a014016402440101da0031210000080702400500125000d41c000440d016103034120245041e03001d104202c495840710510b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 161989253 1250 161988003 161988017
    0xf061b0d0b19050a12020904030f02160311030f01060b03071407080706060305100501061b05030c06011509170c010810030602071101030f050402031015050402340305040b0a 76
    0x3072941c071402034521114a40b00390b6002d000e4580070620031074070003540240300f42c2c01800d0f0100380540c546100307045d045036140c9040504010a01822402c1c000d2996412403c059656000414412201a1058009004c034103a0340c041c9000da010030300321112407040d40008801840000e100358001c40318460b0381c8143c1e243c010b00d0121103030b0312610a5070001d001141e031250340300424010700c0000c003c90380d4a5070f81e20508200c0c0c0e505244018050100e129998000c80e07004130110000c121042c407c4e80c20480ca100200ca11035611101910116212030300305e0070009641d00c4001501240400350381510a16031405403140314008070046580490003041e08800380700d1b42100200140e1070303200800c04180100d04029501c241c103030004007590900801d88034200d050405000140e035000c11020800b2000c1840018140c100c280841c0c3d91008650145078007134400718550044800700050101d49402c102d1240c100300f4601c2d000e84800c0c1070401800782c0010310610062200c114814001d00c03d001c52070600744 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 161990503 1250 161989253 161989271
    0x1803080a020a020a0801151a2a031602013b0f0303030c03011410020c010806190f030203160b030a090203100f09021008010b0901030504020a0312020307050f061b0d 72
    0x5a042c0030a50094503560341d1004a40c84d40841d2601040203806500101200c006a480c0e00101038040c1c0d14280300c802700302c540300c0d24003800305840502e0280103610a403a21420f204050b204c03034588640c020307400706070505c8150001540c1b52110aaa080b50312111404c01170030800d42e6070400344085506a0800302902901d8619a82000514070410060803d69500d42c100300e0801120301500e10050300941400358003c070810780104820580d4a000e2805410a5450200040580404203030546984c0d0b5032500120314142402240006d69009034201d0300c281403000344d6604200840d114801c69101d050000c01c860407040d8002c008000d0000701159440805240c8400848a910000c10348850352385070310504508001050b00300c1c5601c07504042c4125858043c8215031886402011410503540302c1c00241195a6100900f02442c2c02500107031900300803420295403503001b84001d0715140310307d031981400341c01c00040c00e0b031180d41341140042c520f1404a28030501d540100c0f00964425440b18290703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 161991753 1250 161990503 161990509
    0x1030506011b021311040f09020f030106050d0f0c050406110307050d081305070e011707030201090611031308010207051504080d091a0a06170c0d0f02031504050a060b011803080a020a02 81
    0x8251460445c0c1a056911483c00c0c1030030711841c81a9120750744060040c407140650345031220990b1304540060501d20380d10303481002000010b1500700ca503004c059103030a1240e890a13600c00050070556103d80c4650000303848440f0090341d00d016076030005106a00009903e80ea0314800c0d00780716045040900501d0511810f552030750309250343c5030000e40038644501d00412049410755035490355049810082c0c184907042d500020540545801203100f440b04101c400e5207500c80c1001119800c04909020054960301e40703401902030760200c0d200380c80c05e10410341c00d0300340c40d43c503490b03154019607101c86568034191001c1141c50251030208015640380e400d5140101060740100d800c28802e400507140015500c1c00d201445412a451400d000b105501c43c441034411521801540b2045c190451002c1450320038620000e442c103076080000c17610029400c024841049070019054000b2803041c1c5080c400c0c1c035114001144c04200900c810f042c041d91000013003010815100c006c0424240e070348140d8440803110307004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 161993003 1250 161991753 161991761
    0x703020103092f130c090608060a120c17070b09220509062508060609060f04060804020a0e06030606040b1c05060a110403051c0201060911090a0501030506011b0213 72
    0x401d282d043c0c90b1410064881c039040442624006008500300204054150300074078107440c84c080c1d20180036050011510941e20340c09148010a002031040a01c1c0710540b50419050040744a03480a060050700342084010001c5a00c104bd10380175084075081c409407004208250100c0e91429049002500262443d10142c1c000c1c01c1c030404a0100410b61400c0002c4038100c01240310505400c5c400c44030181480e441e602541150f0003003005c4540c40c1e203070a000e800084861041c03c010019031100060700003100d40d00211158490703030080307558030b0758240d0b20002400141421500340d58540c0110f030008840d45825403000d04130b200c014000d52950b900ba04504181c2e0010b0f039000360340302d41c002070400c0740214003806400d02c10106004ca05003800d1640d954580d41b2680003818003c0002c06a01140100740b003540a20020035600303400b80b0102d50040080c0b14140d00030940c09005084101c404152035000e0300605006007410303903031180300009030098140b13400712042c800c81c0d01c18540540340c07010803580c5c01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 161994253 1250 161993003 161993063
    0x41d0c07081612020102030105030d0806150a082e0303030905103b0a0b1b030403090801050f0103020f12030d090302061f0e1501020a02030d0905011403010305070302010309 76
    0x41c00d07400c01d109040c880c2c020f80c001100c203403c40e0700400041c80661004035821070302038080d0400c0384442e1240d1000a20070169400c25058800003c44d06282c800c4c0d000c50480e0013081340524050451032800349420f60342c245210303000c0c51160034800400005c0c0c03181d4000c0d505580102c00340c0710581c505001e900b0503240003958108010306100240c0c191100d13186a034041c20401d1011090445ca440500e030b40e29010a40302c0a400710141e140041c1d0040300301e8201d058030f10030300801c4558074507003071501402d0740d682230040308519880c1800255040511013201ca040e00e80091101d070088090204200002c0c0c0101452040d9001c10f00c04480c0740010380c01480d030114840d40150074a0718092102e081c12a1408008860003155a0010000c208128540c250080100a00c1085072551500180d1030701880070785c025010301c40d00c21400b01c001d61003040e6005030f804c00da0700c862581c041500700ea071150000307000140041d0090700301000150b00a9204440407803180046e16507001e094440b0f003000040003a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 161995503 1250 161994253 161994277
    0x1050c0114160e06030f040b0421020703030339020109081206031915051005032514011d030a020a1e05040e0a12050d02130801050c041d0c0708 63
    0x84014590b4201d00e0380e04034054142e407480d0952900c6d00440034000c1c03001e0005891140c0c3c480100d800d11400c01e4190301071042c071060400f0f4003108440020761703405092000381c00003441c04083c45840401505094140c03070103900040b64082170880c810008826504000056660301c000030320019080e2000341a10500c85134044401e403415605040c140b092050503001068201e0140e0b00c00600d088091141c1c44100040c0028240da0310030b04603184800d650030030b5905100b850000c0480002c5ea02402040c1e08460407513401d1182d0707a11680c90081c000412142c04540000c03240118014042c1c132070a0001700080031500419881c0e000700b00301e0031442d000103028217081c0303559005003402c00c5030200007400203450030400c11180e43d035141e403540a42040200140d651190380d012492242094901e00d07050200c0c115035170071010405c1c3c3d804218600c16001c56509200014064070000c20903030301203c80010702241103181c01100a100002d00030030141425605220060200e4164070151540380001c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 161996753 1250 161995503 161995531
    0x140708150108010b04050c0a050c19080306030c030609030a080a061a13080c0603040204050a0906050c04080c1512180706050705100902060f0d0902131407090b0901050c0114 76
    0x10403511825690300d0750074540034500f0071040c401c03103500032001c42340c04000a00d440c686514213000d1a81c200804448217009200304d00715810140016100114082c0c501101110001d0144c0002e064031000c044510b100300da00140303c80100d03a801001c455030301c044528000218580c071421410f00720f0030a05c03803000b111704020802c406404547c034410380c080c0c84d054000302992001600003c0301d41c40700070002401951107001181380400702d40c03c00300035182c0c4004244503900d42442d03105204d41151060030014071900101264a04000c00300c00707025034090300340c14a00329403401c1c2d16540084c041d0000d20807140300c00e0705c90b548540c01c4c0401006801560342d000e58640c80350421a103001d842031044420103190500c000c0050f80d5036402c0310083d0741504400d80d2603900d00715407600140b49442000c0c1d006403c0c4440c440c4d0f0700d2800c0e80081c0012605240140b800d440305442107402d08a0b41c001c0204004003081107003641e600440c040c011802d0144000b2982036a00c0d0101c900040d07050700e0640d91b100030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 161998003 1250 161996753 161996759
    0x905061f0510091d01050f0103020a030902090403030e010b0603010e07050322120f0806010e1203071709090c03091506060415020d1b0b04120c05030f03040219050d1407081501 77
    0x1500062503800306100005801c85d506101c005400401c0c00a9070b503050640c0000c00d1003003280280c000c045210b030000e00c840220302e020b080140190042c400c18038515440c00340d81120614052080d2416904a8104580c0a684011050f1500c2d40090259201d020141a00e41001c500c2650b620300d005110b090b05008440941a0180c595003a1070368038000d210b1010308102e80c60f40d0000c2241b52046040b520560060340c2c1002c080e0440c0300e41940038283c81403d2401da44000c12100c0200360021003520302500d43e80e165502e40c0c94030b0000381c4514040d0341040400c1b608c007210b09500250040070081c410b602d040d03a40c010f861119080c984880d00542c10001c2041039003600450300340203008840d5041c60580a16a035080e000c6c2c4001400149208800195161a80d02c2419108512580841200c0e0350f40032000034483c558008580c00c0340305250f01c84170350842d030400c65400b03011640043c0800d85100141d95402100b40000c50300501148a08540010b0008041280419410b109240c103200380d41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 161999253 1250 161998003 161998019
    0x30b04050f040503070f0606050d14070806060a140a1502060a0606091a0f090a0b0d05010b07080a080a0f1814061006050d060801021309050a0905061f051009 69
    0x8020024914180c1c18410080818000300403120107a0b40210b5003840110f0b68985031000302016040603421010404101007000715204803000450f004004851195583c0e6a0301a501c21045072110f40103568980100203020182c2168a021003000740b1408072107846045000c40c500100501c4001030348408144000e8503e10b100e808050011403800501d1a4207101b908050f00040605280158a000840b400d4817036003070080d02d8580074010044181c080c0d40f0b07501e000c441d40010090300b50076403a04000080c00c040200445d040b140d80540030038104540580241c840074401030486c0203680c0c90704401d032074000051041c050340500c580a00203001200313042200700049410341345440c3c0e503c62010311510389e01d240300540c1111070318070b051603540040c9540c1d00c029240a0340468010f600215410304480449a060030035540240010042d80d503901e10084251911110054000d0b004500400c103510321082c40914068802160030705100e40c6c8001080b80b0080008174600010f215502c00e01c0003003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 162000503 1250 161999253 161999261
    0x3140a03060e0604110a0507031b0501051006020d0905100c14010507120e06010504050903040905040305120c120411121006140a030b010506030a09080a02070513020a081503150403030b04 82
    0x3041034600f00218004460452014860140404240080420550201403182c03c10303c1840c2220002d020030a00e1034940b00d80a0702d03065464020113b80140c01050184c8005a0b03622192042e80d00d5840c924908000c5c8514403440781c045108000d48042e95802003a00011041950b8004500004403823078084002030044960400780f0b1104d034200320940094250006400b410f483c41150006041d0f2a00204181b8612550b801015000d00344400c03c403d050b001400390400e00c1824601c04c4040e5140c61010b02d0f144181d81c080456944000e000c100407440d084a06510103002410f024810009403044c0b81c944051000d160354840d481c0e007821312401215000b00084a0307020703184030b2078003411640c6805404005000c2c00380540703001302c009001c1c400307540c005801c1c094008170181ea0b29034001d0002520344d0114002c450080a91400c08483d1341510b200f1546d407512a940d500740341d6200c20441416030b0900103687c56042c408d091130043d0001f00460300c0e0340100c0c800d440c000765101d552002d020941d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 162001753 1250 162000503 162000511
    0x1d0303250905010c120207080a03020f07060905180604060b0403241104030b070c0c08060709050618010e03030708031306060e0403050a030b1305010f03050114060307050d03140a03060e 81
    0x407149030002c00c5142d8200300c0c2c6464950340444524180f00c58280100e107002ca0b9907002110510518441105054011620072040b010183c207a54030103480f00c200741d034520820310031290807000d1602c451180440115500c0d41241000f417000c11030a46d28205016250000d402c2a41c491840c1d542d030f40c8130320030700c1c840300c480100005900b4001c550360540381681c0c9004510010b40a4450000002c148900c91091030550b07030fa00c02c06803011b050711640041e40d1004200c4815001c00c01e0761401003141c0c0791030400c0d1415801800c03504034002c40e5203001101c46041c500d5410783c0622040c0315180001da03844010f0340c4190224603150100b04228200312040e55840d920064940042c0001d200200e940f207030445502d0300d4203080115400c414103000c55041e5901000c0e00ccc84083c0b4000020500c0840e0042c40b03411640a5030092110304100300701040545c800b03940c41039142d403045c079007080309040107100c264002d400303401c0c07091205c0c8000740e1410a5600c03e5440e9800a91344150a2042c142e40010903600 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 162003003 1250 162001753 162001757
    0x604090f0f050105100804060b090114031506030d0c11040906020a230f160507030c050f121c02030706050708062b0b1801061211030f030d1d030325 65
    0x2c3d5251401048010f880c26880350100b100400014080c001c0c1500607030310168003d4400080303503035100714010204008000261190290740c00206110024110060090000901a0800054801080c0c2d4a624009000c07201c0b0b001c4088280747d0313640c9510545403494020303040942e54107100d010041070340030450190711407082c0c076040c1d465508200c00240c0d40b14121031000a690341807454420a0580454040140144500d40d40841004103034540c001c05ca44050303034001c14000b8900c0421002c50720054950904e50f0103200a00a00074031903480550805060055030716041550300d41030241c07003040343c0304404680744505001c03150504e2105880341000c00044031b441d00c800d001180301540e00c1307414050900700000010580200b1400030080410200c007000300680c541d00c1c0b044500d040c103040c4090f43d43d07410306000f051032420b010a0740441441e41402031445c268204180c2d00041c00100c0e03200e0b17001159060030785030102040006502881c0301c20038007400c0c100c00802d502840741e10114200c003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 162004253 1250 162003003 162003011
    0x1030e0609160b0310062001090f03081018050c09100c050d0311030a240e061203030105060f0c19050307060c0306050d060e100c0804120806010e0603040f020604090f0f 74
    0x74801042c0c4a080c1175a02c40d2914005200c000e041101d148070100c8440e51107035280c05a04420020260908ac450b24445c2d1142c8070b030359032012215210112039204603003207000703070801c0c0303000c80343c6240d00a682c0f00b2003000d101341c184025440411240700800b603054000c17840c583c000310f0a00c4020445080c110400340781c00c0c09007003060b071001070302400090042d0014948a0500283c80e41c0a0106000e9400b9030080840d502556103c1003407030030800b0340f04540101d020b600d2036200720718041304a0341600d01c0500950300e0100a00341c034003e40e80c07045e0f100d40446e00420354200d4011060400d030381d26040c05100150344a82a9003418803c858560036000e090626040f01000780e6199100f003a01c8240c1c004000064111000515030b086c240d403440340000161a03d9540844580c1005150f40110b004106020381040414401d40b1000020303210a40800c080702005110361810400840c1d100784168003020b08616a540442e0241d006030700f15840942d21040c2c404881811072160810b5290412000c0c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 162005503 1250 162004253 162004261
    0x1d1e0f0709140a03030c0203070e100e160e090a06030609120224071103190f090b09010207140d02030a03030f0b0f090703020c0f06070c0204061e090b01030e0609160b03 74
    0x3c950074850710009050001e03209243c015540c040c0b1120004140c00c4040d403019107030022011050b00090b01503005401e0030140890660703078140c0e216842210103902c0340342d0121000010070039055002403c0481c01c940300c4a0110000d541b5001d505465489a4464080c204c40c4060190500400c0c03940301070f08806c000307141001d08041c583c8c2d041d04400d45003003d50456641e602c015055100e1051303003203076000d2036001c401441135001d001c038100b481d500d81c0c500101d41e480780242c120314481c2191403401079001c848207000c00c0c100740c401e0f000c007802c0003451a45c90850f01d41c003113814020180700940101c0d80d00c080101c81015a809107416524040302d0400c098403102000403150400504441d04140d40824405005801003040e80c61018980c0c086800c0340ca44000018003450142c64200e0165003000c00020307003003408051040002020340c9030041e500d420004088000e000e99503010381015114410400315010a02c502d501a00c03680001d0303c450182c0040b1151014210b82c000700000d04108100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 162006753 1250 162005503 162005509
    0x10e01170613180c0503120c0c15160c090f0902031e010603050f0d031b0e04090c21060b0604050102100c09030c06180509011d1e0f070914 61
    0x109034801801c540212102c00702d0200000140881d0003e5002c400b55140c0c40002e0100b1401300740101e4a040307049030380c0403042c1e0404258034000c00680200e154080c01d642031407450400b42c0314082d103900500132802c00321044600340c10005403440c03d4807641e40c503000c04d0203a000c440c010720f144540758040500c240e510550109907245114043c240044400c280348034001002074200c1401160844100c4055401c10707000a82c482504641501c0132030714212225803041103440c41e03525100c41c0d80d2140d00092408134184800303850340d00d40444080540080201310403440ba4110701c5041c030744c030523b0f80c074803126803504200710340b0100e840c03506c199002e1004000581e330019040c1c0d0701020b5090040b0303203a02005400e448003c066040208461b0281a020030007540c42280581629003415214140d550b07034006000c9a090280180d00d000102c6451400c074248140041c107400c001e14240301c00c030075181c00c00ea0140c00c4030309072110081c42d0054400e210340c2c941e000b00c41002400c07914000c805195901000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 162008003 1250 162006753 162006797
    0x102030904051e09030a021c080106050306010c050613020a09020304080702010c0c09020a051c05070219080d090804051212030a0e010b150406110703120806030307050f010605010e01 80
    0x1403548902c0c2c490740090f400340c0710351a082c0304400c01c119415034942042007459442e17400c028091350052180c030040826a01400c00b001c065882140c807a10102c0e42000000c0701e20b03600003400c2d541401103018030540015010401030b4417a0142c5a01c0e0040b9004030702c10400b030400795511051150780184240700124901d04101c4000355424203014035030b55450b1134004010301581c5e021701103080c8003156440c2c8880d04403004000196115504041001c0c440500303404450060b20b141c1d00580c0045030142441080c010b81c1c0e62168010811141446400c0c80c3d66002d03500700000c1100c0980b000701e400c1090b4140450120318507000603016042d050b044104c040351901004203071012103901c03000a02d103544020343c000001460080c202ca0942c40ba02c04085011358464440c02c0d00280d07443d02800c0b048240801c106040c0c941c03090706460741c05450b5408448241010700f0305a4180410400c100005a080210a46010b80400081070051400002500365111b034507410f814040c1011801d02c40e0291011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 162009253 1250 162008003 162008017
    0x3010221040302070306060311090c03040302060103080901030f051303080702120304032003120609010f050d06090204060b0418050f13031409060c010b031e060f0403020313150906020705010203 85
    0x14240e6030780e420101d00d8802c4070b03800906000c0c685080070007070000d040c481f800d1040050b1200e0342c0d1901c5801c00740800d8070003120081c006811503001400016005c000800280d0014980418001d6215241c00300301c48068030211800d13a90f42c81c08804254210442d50350002d07640c000340c070346001c030440c0140310b80c40021300c010708000901100343c0c2000b148150b0030b84841141002c4075200c05420a00c2c111045003624201c2c8a0400d10000068450340c00340207005031030300603002019a451656402020300181d00342241c2c0591564004a045825180a40300401c0f044240080c0d40d10050f1f400000c44801404550001101c003040014403a101030101b1299035062809090ba0003000d0009a664041d4900440c0d01200002d200e50202d03034150044580340034100c0a665100404c16040e00d0361108503102c140c6560000400103203541078012850758464040c2c0141c03441d204419416800354a6203400501849440302800c1e00381e940d020042802609650009040c0c0300e0400e00041d5407070007070310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 162010503 1250 162009253 162009307
    0x7030c031b140303041a090703030806040e0a0f060f060311010c2102030409140709053f210f130302030307050619050f0105040f020712020c0f030102 66
    0x6181804014007124071501181d8114252125810303071140300ea526580f007500c00340d805c0d940076040312010551961450b4062014100107244103840c55401741c0364150700500440d400791350341a6800200a051281840c00f0717209654114003085140b404000b00c40302000c001744400d25190081c000145080d0281741c40507401d0030302c6a0041450301c0d10030f400007500b0800c182c16100074900c240341d803034002001d4803d8030500c400901120300c1c1d03074500700b00f091000c580e000005130026008118a0404c50b01001210002c000d0b140058900001c00c01c161041c81c0e1200d600e1107110900780c55456034240041c0600d10f01000601b1506654101000028081d03184442c142d900000391228250401c1c000750001154007805682d2148554140283ca1300c02c100c44046980c610280196075039140e520403541b0801c411005011141d01349802e1000424a000380c2e12545c81d8200039460101c6d0001a0840103801c059000303000c045003580a00443d0130000d4030580c0030ba8018060502c0302c818600c00355036000121 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 162011753 1250 162010503 162010517
    0x31b270902031921030b0303041707090c05072f040c0e120102030f01080a0807030315030812010f0501020a05030405090408040509090309030c010c02100c08130e0603010c0507030c03 80
    0x20740002030034010103440004064411940c501c007044202404440d401c503083e900c081803000e07803641c00d0f0240c0c2c24481d100c640c1030f0010031040c05090302400500b03420304085030840c0c0100b0380781c2c6880390444039118907841c049040810360070700b0840c42c0319610769408042420943c089403c040230f080d00c01800040032344a1a2905004000144214882c410a00000b41450707030707011071400014000d40c03040d94419112544e030300c000305c1c42c56000103031601d543e41d01c00724003450120151002c5000303041c48100000203c2e4000130010200380743d0130181000083d4401c1100c40e652500c0c00400f0200385c6a0320190540d0071200d002e0b0301250300801502d040f070301c00307032080e1200356121702c0c0a4040d0b1042c1d40042d58030810701420b22100d4480000a080d1030b9005070f044070419807121006450040410700000c5d8000d140f250700c00070240c802c0b50304910f0240325a10341810505140414842440e09400031300c1d0b4021594100a0075207402d01036243c201b2841e0070001c3c90704560380c0b030080c09010800b001409102007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 162013003 1250 162011753 162011771
    0x9050c1212122505070308070216091d061909080c240906060604140a05030d0201140c04080a02120c0319030206180601090b06090307031b27 62
    0x100703104070300035440380480456036400080282811107500b65000142c80c0d005101ca000445400c8041c40d20602035a12450700b400c80c10369040301d0101008050b88110301941c507800352540b5010705054040c041e03100c4081040344151030344107841084480c221196600020510401980004040300300201c05400443c007540c9604101d00c140c0b00e840740f114000e20841c44040032400001900303003014528668464419150311031415501d0b101600c82c142d02401c100810050000b0781c10302c0d10815000a81649120342e55540001e08004912100750b0140c1d442e0001008255101c0c051164041c1311554510305103803c0c100141d5030354402400c020700a0100700140201002c1c1004180c00b4030200804075070782c0309003030600f0080c4000c4090040300544140e4020590b0982650310040c910381000000303040603032800800c80040c0141c6007a00f600f0440402003840d00b82c9040c0300718405140103070444030809804106240021000380e103c1d44a0390280c4008201b560503102c04048481c000c11804510000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 162014253 1250 162013003 162013039
    0xd14040915031b080607020102040602060f0a0e0607030e07120507050d03090f030c090c03140f180a0b0603070b07050307080304021503150108070c0f0209070903080a02031c09050c 79
    0x3072541c20260050071500c02c03070b2a0310750903641c0e00819600c80300c041c0c03081900d85c0c180503402c1c1e000c0e42c000d610268016800084285c2ca0500003a6030144680e000401e410100341c00300303030a01c0815909000000e07104c0b143c1d1004a4000c0000c90000c3c1a081801c2003400081c0d140d06490f205a400744911a022011040050510603078425015016804500442a13901e2600b5051016544900c0c074089007401305031225140280703d04940a5a62402c0365040c2e41c5004d907032841100010580c0305000050f07804960080c00c100580200c003481400000d405003005010503250203d41d501c617002044003007140200040c4080151150541e001610644035242c1e4070004500000041d000c45c040c078008010402e00c2807587c0205401d039a02a01c0342599a15107110445405a8224000c1e10784100c2c1c0b2195401810f140c44401e50019040c9407102d2003640300c0e5a60005540301700c0c50103005a01c007062081416620511007000c0d54000d0700c04102c0c180069031441e481d1705290001c24030440e031055010345802 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 162015503 1250 162014253 162014291
    0x14070503032208030a0906020c010305070e2101090f1a0402030a080a0203090d030309112d040e01151d0f0c0c0109020406060c11030d020a120203041a0405030d140409 73
    0xb101c4002645c1d110801d425000b488040d039842004018403400720120100e50191060500070441542c4d03182000540343c4c20f100c240e00c4d5081c5004580c582403423404560380801c0c882c065000384643d0240c0f10128482c1040c00450090b030aa00075224000c1c018800140d40008030485005d41c004012601c2d8103542d0070136400c1d8050ba03110750703401201c0701d00c000041552542c06a001544a00f80c0740a42400361801d02c000d60f180d4410700d6a40c0035280d034242c442403104c0c41170480041001000400d201c4440d040d1542551001c0310807901e00b103030300ca00c1801100c4001d0810050b1020581701d0340c1c032520342035400320781e8140060b24080c1e61000000d00c40c00c0821003074024013185c1350044c03c28001030366601c0006080760940e98094608500c030030103441051401046070174a103085a40284800d072821b0715240101c41803c0e285105500c8104400107030424001880d524446600e014551200d190900b0b1500303001c0035005d10700402c42c2c0400c4d9440c410007080161420703182000307800141c80c00c0f17a0710942c0c1d602c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 162016753 1250 162015503 162015509
    0x30a02250e0a0204030629010c0c120c210209150d060510090f020f2b0f020403110301020909010e0c07050f0607090e040b06010c020d02060a020a140705030322 70
    0x40181d4001c0003800180781e0002d00c226441581c04004806e0526020007110050140075400c0640105c81c0e10010341c801c1c00030307a00340350042c0031039088503641e0808007015241c1c1501c1120120310702802000101c102c1d0425960000d642c0c40c0c2c0301848081580002d2a02800808107140c0050203501d120740350315810b01580c1c10550015081205013040301100c4401043c41c0706800340203007001c000300301c259004e000f910402c0b59a0901c1904004850541c2d04004042141c130034851b0000711084c200700c604a010310042204a0000169903d08504100218500306003140d0b000381e004205140c25500d401c01c0b41030460301000b00c0001039403505a2200d4291040d40ca010740380748182d02c04c2c0a509003000c690079000740d440382c9a495046a9079071003410804011a0081c1449100c1c20005540c0e5000f10b000c2d050041c802810164003030306507400200a44c04c02c188410050344170740000000c005c2c1c2004102040b59501c1c00600c3c10030f00d0a80082e42e6485000400d121010894007050701200302c1072035403000703 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 162018003 1250 162016753 162016769
    0xb0a050409140103060b06090105031812120403030b0a0506030601030e1c1d0a030302030406050901050706050106080a15050f0607050102190216091404110d1502130503030a0225 78
    0xe12610340380c03142d440000c0c00b09480461030110704112918214045400c220410b854280c119592013002003090803002108988030702a614610051403480c00050900380c1358664145002c0c10542002400c48034141e0405000b840340c50b6041c0310540d2058140c9900c03140034a00405da801040f5083c44c01c1c401c0001404800c40104511141c42d103401088842c095200c070b4450b04501100c1404100680101d844003501507003040101b40540c038450710041c4207519040c10300500c3e0000c0c0340c4c1c0b50022904241c0c00320000680070018069892040d01503542d440424541d5180c3d45400e050029400e80c50089405118040019040082045c01c0d0161500000030000c00520388240c1d00002e5100d06100000720303280e5440c1c1c540814101352510840d1400c08041c50160010b1303030b5a0b9034507a01e8200c42496558040300742c05030140000e4200c1c3c2020000a45c041002d80c076080c0000d05000341040a8100510070b0300244200007009600151202034030752040302c010480ca40c08001c0c003602c81040e4112801c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 162019253 1250 162018003 162018011
    0x702120c0109031202090109061409060a0905040e0109020f100903150e0f070819051e010c0e0618010c02150d050f090a0f170f0403050703020103051605040b0a050409 73
    0x80180301944142c03203160194503140107460020240c1c0049218500109010441981c0107210981c400c00a003510b44562000307582c5095501c0e00020b003250407800d903000004024180c1032103507007014003800e440142c00b000240301001c42680040c0f550754446160502865482030070780000b6200740c0c48030b0002c0d6041040403241404810b0043d025250389011c03405c3c00e200700501c00081c941d000441c00d0403901080007a0142c103040021b110a2503c1105003603c25105161070b1000c10403000d503a135106846400000600103d4001002d840c0c4545410b480d81314280a12010031015406c50301d070074020009290030070310391501d440043c00411107112507a54070400441d45041126442c0d02c514003545400144080c96075462013203643e603d1040d980101031102000c0c00c5400901c250040f103510034401c4450a013409040380f15949660000d61003030707606031b1142c0010820b5581600c21140c1105510300d050605480615005d00144142d2050101030b250015001403403921a5007518040d002c0307100240 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 162020503 1250 162019253 162019267
    0x1a03091e10110d050606070f0b07030e010c080702191a07030e06040f03120204140f030c120c1002030a081b090402030112170c0a0605060a05030d090f080610030b070212 74
    0xb0450341211582804513464000170a03a40e1600005030358103190f109034040100344966403039241901d005040f000500d5103902a130a0380e0740080c01811900d1580f5910032500c5e24203c04001d140c0140c0054045031713075103a001c03240c000c40c0d680780001c0914803141807449215101c682e412001440c20f007260700c14600070201400f04000c17000a40f80f0441e8000d680d00c40903814a402c0c068101e11071407260001c8011080c028900b60b04180043c0c0340c00d81130050a40b4020044e00e07020409510000c41041d0003a00a4031b6080b000f032600804049106800740300941c205034003d10048c01c01000a01380300040001c101881e4030040d07082c130488210307120140c0159140d59544407040c031040c120f80001c580d42c0661220b2002d00004030800c1c1c070040490305000300301326640782c0c071000c0c01440080c0c812900070090345400701301500d00300004d985012041c2d03038510b0303994a40300009070900e589400c104420340241c410720580381c0601c55402c058a80184140103581c90700c110aa03d070803440c1d500d803181030801160320 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 162021753 1250 162020503 162020531
    0x100801090e01020f22261203010e0c03092503060c171513020403050f1005011d07020c04060308040f140904120909090b011a03091e10 59
    0x160484020312000c1c46100760400a150903801a000c40b000c00706010b1102d14200ca07989840406000b603120901000c040c1c560440c030303480070b101c40680301c0300205030341d04507403d01c104100b0840032052000000c0d04650404003400010310b0041d1180784031382070210105512100500000e9003509051052100c5030014503140c3c0150582440151900c500d04100381a0145c0aa040307005580d01000003040682c6c0c0d81c004a01c2c161490088543e0406243c42e1150002c9035140300400c00385002c0d0b801854203c0f002582549004011050201c643d82400d004114003021006070444120700140008050b581d900d10891406154404560b40a41404400418000d0160007441601c000ca11044000740d21181c4852404c8074040a01d0741240c103000014010803940c498941904003545400034138a036446800e082a07800054064032440c48100040000c10780360301640200301c0003124841d0a600d00031001585800f0310000b420341e03222985500c50100c04040c8209401c00d100d04101f080414400400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 162023003 1250 162021753 162021767
    0xf09190c050f120706050d020403081827040809041b0806120d020a0807020a0302030a030e03010506100e0f03330603060108121e07050604061a10110a0210 68
    0x341c940611a00c20316010300703080c52100440c450a000c0000d1500c2c52401000f101d095001e4540780051940c00d00c00880000e014400800513031034100804801d49040d0420442e2001c0c0c21210000b5640089406202e40d02c805070810f03074001c2d0840320f0a41c942c0b0741c210200e0301500340e242031300b088560360515070b102c0e903500583d01901554040e115007104600c0c0e0340700242d442d6a0140c80c080964007609070400045c0304000245017540c800b614142c034583d92580403925002038078000b200030034422a0486601c1c20240700d816800101110300a690900030342001d0034100c22000c0060095001114098044d10100411805651440c0ca0000514144246088070f420215644081085000c2c0030400500d40003075268181c0b48808098078580d14403070300b4040c080e844134071203440306280a1072510407441d01c500075010850250004d03200300d107050310b0070038201c2d0036083c01070054110300061130089480312140214918203908186410300c8000c580d99150005041000f9400813402610303c00303032984540c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 162024253 1250 162023003 162023009
    0x306090603030302031807080a11031002030f16050906040902090414010803090310060b0f0c0c0d030f120614040f090519020909060705030a0b011e0302130506120f09190c 75
    0x1400002011202905035100c4203a44032300c900540c030407141400032801c1d0800703002086000a04544501c0c52556241069070000c403181d41c4009140b00c10014404608000f41600042924180c0d1401a403c030006640e40114003460080507404221591750b074035241d201000010010301e2149480da03440b5103141d502e90140443c02d00a000fa40b200340e94134806405210266030541050b1410080d5135111603850b41c10401383c060b96803141814165103500e0b602001022a4026643c0c0e40881a40b15805051306440c0100c0c400c0c1540b500d803041040076040400414448000c44002c501200d90800351006002352542c040d100e4022034100381e4640b08503005101229100fa14102c4e81a524200d500703480310412600300b000b00700c08000040040743c0d03a90003001c8021050404040e034503103200203458139202d88102c1801090340000c5114102031215030b50707402000100c41c56894106824030318080305a000d4001d044407052000820f0b0100803d02c00400794034500d0b010f4025070401c50030401c1c0c0282d482d01c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 162025503 1250 162024253 162024271
    0x705041107080304020103020a1b080417191b1d090d020703030806060304020d1209080f03130e100e130309050d0201050a0c0c080709050a0b040e060115030609060303030203 76
    0x3031400400c0c11498810354200702d80010360181180e0b100c1d001074020398800540502000301c4030f0f400603007949040c442480214001d810150b110350030040704c41784410603c90f41c440c0c0751707001c150220000d050000d03681c00d265a001b026104404d0090344001d800d00c0e6032380c10051560a290801d0000c004d00c0301e49040c030034a2640c0845403691415501030761210260300000d0000381000c8001500d60802d2002140c0041c1701401103941000075840d40d61900008803200700016002150400811000f04004244a25102c0185160444c0000e440f00d42103d00d1040c1502c0794961000540c401c00c40c01c1402005000c442c210b2801840c241100643d030003134070300084011071002103002c01d4900341003040e41202c0d58103840700e81c03402c2c1c110f840c00d44100581c1c680032500c203880c4100c0442c0c881c0040c84114024100078a0100d100d0400c01e800801791080c00c10024061444e081024042c0100010303481e04441e4040d0304403800501c1000300b2400390030315030401401542410300000416505600552203041c1c80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 162026753 1250 162025503 162025511
    0x6080102220e040302100b030a060203040501020315120a03080414250b09180a0e030c07030203060f04030207031425061805060a050901030b0307060207081204061b1112070504 77
    0x42c1102211181007910060010307400351020402036200c2d0780c0f081810a0001b000c841901d00b02d03903141c00c00e9038011a400c5446035000b00504c00485803440c0103018a16045850481d210302850714695202c100c03400180030000e802c0d02040074082d0400745401064566020703101c5031303594400800c1040d08840051901490031a500284d40c031216816541c4e0700030000d2600e440c40191380400380e010000504160840da54074011450490410001031207a110303807a020f06200341c40c3d801014101900100030300d00f240e04030310030080003c2c1d002c1889000e80b540075107090f010109502e1f81e1450582816a4407500102d4107000f8980807000100200490703115036140b1040b035003503010144506105204858200c0414000106450700600140007031070f03818900094802000343c008ae00d002d140350b00032005a000154180720807402408844003981c2c040c0c00a605d041d1920b03070002d100344031081040c091000d18080540400080018016a100e4010500188045411003032901d40910748a1035115502d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 162028003 1250 162026753 162026759
    0x3060901230d06020903011d0709051509071407050a0b0601030b2b0206070c05180c1614030703180906030809090c040f0902040317040312120608010222 67
    0x30003420110040114100004884038003810b1040c0080c1c45401241c20b19001e004c14040d03030f1801d201d074595900c0c0c4400d10b514030101c800c082609090190b0010406a4200b0081214094107800c5011607400203448088803a9200d00c3d080366401e040340342c903000308900094000d0074803400182002c0458002e000d904900d03190040150100c607120190541c1006d014000d0042c016032950309030150f401400940e0300c40c43d0f02075001400304c0e413103240d04a0319440d442000780140d043c001802015424198068982410400070483ca80d0190644943e14604031030b400d40100500c28041d04400b2401c00126501ca40e107514020f0720b51324444090b00c0380001c1c540750000f468846402840110b9401250091400a0020070300018038801040042c0e8003004000001e9500440c46c080001842d6007000140c031107042d0b1400c588401e0f44200f01c1300901074240001d0003c00c0c4140740c012501d50b01d90520a03030003441c0c41903401c0030348215406074400d0f51000c51b100a14104144007142d001c00c100c200404000e071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 162029253 1250 162028003 162028019
    0xa090e0402030a14100603060608060a020a080c070201020118120e061c0e0319080906060405010e1914090703020112090c2105010903090e0a0e100c05040801050103050303060901 78
    0x10112030196041e880803002c038010800c141018020302c2580c40503203420285a00054050303507402e60048070311503035039a41080014401e0009942080e00200306515009107018001c04504000d0301c3c8800c0c0290002e6080c2c21613000358001c070340342410404201b42001150600190701d8030b0706030004010804240710301805240c460201c44000c07400c1c1501c039040c00d456807a90300041000550030341d0244410040d0144440c5a840010385036042961555043e1030020b03542e50401d50080c1c00c040c0654105001400340304854500290311404000d103440130100c945142a01a040022400390001c3d1140140300380d0180c081581b0050324004e07240e45017580c41156a40b421503140c0e11010740041034062092000141d071a06c00759030b207885a000c440038080e146c0c407018211440c0840480c0400c0e2584810401c1310303a454505039100050203001c100c0b816005014540701c3e042003111a40342e41d903d0000112440c058410388016155503c0200465a168a4074558070303882544c2d1548604c480034000200c0d45c2d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 162030503 1250 162029253 162029279
    0x90c120702072304090203060901021306090303050d05060303280e1e0907120f0c08181f020705060108010c0e0916081801020d0603061d0a0f0c0e0108030a09 69
    0x1c1c04000b0b81110310f085808044010200b80c0310305a4400e8444c0c0d14070300540d4040200ca4040c2d62403800050307a0b2003240c013100400c0d01407648550240183c1080800101750801e007618503686c03035040003013130341d44c0c80d040000d0a40c840c04c40e6407000d103040c10041f0800989020821a41a100b035192a01c1054641041208004c030499031841c0b500d40c00014043e15042603c60b0b5034100c0c1c00c50424021803043e00c5560001d542081d008403e020350f955030040052075200030f02c07a41020011380000101e6900c0e100842d11440c520745200040c01000f502c14004180543c11564810b030824269410741d41c40e07544041c080c00e09034503110002528400b200803107250003280e860080003020f044541600c4850300603100742034018010449650758480ca642307040020b0004003400200c241000441c0c0d819494640700311a1402100300f50040d141d000e402c40000700089200340b50750000c228040004241c501038540c0015038202e00104003605d40000340400d0000050b100210141d110310442d103071240d0040c1004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 162031753 1250 162030503 162030509
    0x30c0206060409081c1103040521190305060609030f011e0e06070c02030a06140415020f040b030a240303030f02030c030105090405100606021f0b030c01140702090c12070207 76
    0x60f81c41003056446460780e00c04d00010380c1201203800708180304548024140c42e0402c0b5030a46850f0800e412b480305441c0b01e459000c2c1e03000000c0125a040916409100050910180000d0149503454010404503a070f0f0805960498000a080710b80720001000303040d010f4450b03003000c150040d1501020121421041c064003002c560454000c0c800b65480410440e03400c0d4819900ba6014024200303e02c010641c2c9001d1401ca20490183d20285800c151034016005400c400341420450300c144604070b103148254007103070101c3d60700c0519103480381c543e1001c41000b0400e1000b1145440d09000700303021113800e00300b002004c5038025102001082c0242c85074805a101c02c0705d03c590034003000c2005101501d00050802d421030301581c1284c015080031015a800c90b410350b000f040142c2d020359041c1010610600100720444a4080140600d030707141ca006c030341e4415200004505001107024156440c0000074292024185c008148240c2d6080000c4181c0070365004401d085a02100e09001a4441e800002c00ca03040b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 162033003 1250 162031753 162031763
    0xb0d0b03010207170711090109090b090a030801170c090403030501051207030b040f030513060e120a050607080601050c06070306150f020705011209150b12070b04060f030e010507030c0206060409 85
    0x3480c0f82d03c0c4041c880d0300c2104125034006d54107142480944036241002d002c3d048949000588203035905007510240f4000f4001502e03a4802100000002c0d0321141c5c0d40c1c111075160451840d00c0195800c2541000b680f070001c250001245810003040c03507410b03040705040301d9090310700c4440d48807851000d035101c44090001801c0c8980e2f9801041c0090501088005403030b00031300d000b0382406406170003058105071552020700008d03000783c0000c0707143c606481080c9074a4a55402030500340060381e0b07141d40f039450051420080c802c446000500e264021022190319030045400d8030664602844040c0050800b4050034075880d11050084809900445800310007201c160010840b051a01c4011903448080c000d9810f0401e07100c10049001030340b421020f6481c06248840442c910413500107000607200c2c1c0c00d502e4851540201002c0240d201d101084505466203860700800a0442c0602980500b100c200018007541ca410100560b07158140c0c04180988100d034261002920b0780400c010960307200b010082d02c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 162034253 1250 162033003 162033023
    0x10905010515181c0f02010f0516120c050d020a03020607210f060b070602220513020310030b1f0b0405060a030902150423010c0308061309020a0b0d0b03010207 70
    0x3c90603100b8203031480d03541c00208a031016802c040740c82126032281400844c1c20740e1114000008542e004180b044a84500740340041c2018150b041f50040fa010041001d03002d8040c0032a2044124861056003056540001c21650030310300c2e14800a40d41c254200c0164018051074022030030140c81082c2d001c1c90541e201040080301721512040f000144448001100ca03550398100000d000c12a20010f800c5240c061100140c459064103215440c50b000c0d00c1403540b20800c51a400d109558400b00c0c4003050400e11400161641d6403129158003000b080e42014240c40c0d07082c0104041c0001000c0c031030a020b04800c0604d02030980c1e6445011250081b0b0003451b40c800c2040c00034007900c0d442684501c0d95a4001170110310f021a09000000b01a4000e4104541c69804c0d07074600844450711106c40500c0d00c1003881c2c1200c80400c1a04c0040404001030181841441000840c0901124039003100319540e0300205403c1e40c5035540c0840300c10382e51041c00040295400e104010503030340b806100f961f241e547c011074080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 162035503 1250 162034253 162034267
    0xf0706060806072703020906030a05070b0a0e0315072a060204180504050622080f04080f0303060a030f0f0203010c050c07080a0506041b0b0a020d1b1106030c0d0212010905010515 78
    0x40303441f100510705500352081c1c00c1030703c0204400700036110003491103280040e600c40c5803110041020103003401550003940003003820f500510f00c401d0b9a0b68030a83d01c0c0340c01c1b80040d000c10a0740c2e01d112804c9184100582c12102280d00b4840300d84d00900496240c4203103040d0070580903042d1403d03194101c9e1301030405d4000c03100041c2c81008403492041080200c0b501c0340c0c9102d9043d542c40070b0a811a03120420228808a0300b4000e0250030007007450f02d1042d900c000c40c00c501c2d00a00103015604c41e0b00005100e18401181c0d40c00300022400495001c5030b00800038045030001c514020100e03023140200450340d00c608080010542c0c004154a501c9039040710143c030031944e49450344040303100007042d81a411030b8943e8000800780711940c003918440b5070300d038007400d040e01d0002e40003001040ea02030120705450040d01d1035800100c03e144010801079040e500d007601ca5407071500120050080c110885415400003840c840400c031f02180950680b40761201c10051a603d90041c000031040340c1c1d0505610400400c039103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 162036753 1250 162035503 162035509
    0x503060a0c4a03101a0315060108180c10030609021603090b1321021008040201031b080406090302100f090203061006021009020a050d0602030a0e0303060d02060f070606080607270302 80
    0x2e050110034400c0174100503402004249054070708002d41c0c1c82e184010043c400150fa10140307241d0010f00340441c3c0b44061001c07a9146032954450903019104059907100317000704034000d80164000b4580c2d4001103440d40e25100e96468003040440c2c00301c001404450010850070360070070503100030303240340400454000c0c1090b01e0030042c031b0001051027480e002401100c90050741c0381c0179540005180d69860100a040c6840090160ba2014840c0c108204107094820240c0307500401042d4865000000441c0c1c2c035a0310300301a42003020080c9902c0215080100c20007070054590080c080e00340c802c0e0300700c40d015a91400b286054920714010b200040e0000850203000c840b068102a0f240343c0014003520055a03600c000561000d00707000c00320307034072030f0088104800c0d00b625108441d0b04d843c0b000081d6180d85040000182019001040244202e00c00306210148040040c143c0d1281d650126040206075106c0001ca035440e44200c4101e00041d50442d0070401c1a9010040000d00610001112132424216420 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 162038003 1250 162036753 162036761
    0x3022e03020406170c040b0c0a0b0c030103030f0c031202030108160506090901030201050c010e0d030504062901030f020415200a020a050618040906060602010b0a0503060a0c4a0310 79
    0x90345c0442c107814080882e0340c0740000300810044100c1802008000f01520345584103510040c190751024a0a02c010408290801e50010a9003224900b400c82841c1c0391030f0a0310740307500612581105901c084004540c40200146460b40c40b200718041402e60b0740c0d20f104200c51482000c40c11031b04030141100401c01940141c02402d514000c440000c9076025003440041e00c5e00500e49c9080001a0b16202400700740041e034402c600b8190480390108100d07400c01e410f803028205030312120504055403080c156007601500c1e03040c0e90190000c503c1d001405031503800000c0400b0406001500d448a5400403000b0350700340014180b1081d580035080002541c5031404100041e00040d4140345514011a03052041c0ea50740c2c49024112031050700001005030810500a00311a210314450307000b100302c4030040c429581e000131190780c4146c2510011504412069042710701509001074a20703d407001d00d1600a505008024220052543c0040c40081c032001d55441004411068000d80d01504443c1c1814001d41803508 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 162039253 1250 162038003 162038011
    0xd1103030c0a0318080703050a0915090314010e12030414070e06060703030603050d0809060a1116240c0807030603030c0b07020c060705011505031f1503022e0302040617 74
    0x131201503003100d9100c800f90b40e0300c84e050480006070001046444e1a1308074686001400d80d56501d544414004d0002070310401d141d0101a0015064403540ca00030042504000c401105030800c2d2000c1012462a051444c2c009441c200e03041c0345400707411421540b002032460200c1d00502401802030b142d1206010381988a542d045c0c0400d42c5a100200c0803074410081c040d4070400d15076921000303180880341c160030140c0c050803469185040c00d11443e0214034502c00c3c0e80e8104194066410384030568503000b1107000350702d8407174a41c0c5100b08600c4040c1d51100e901001c44d0b000640c60b5040f84ea80e50071012000c8695500004001c183c1b100181c0c0c000c46c03207400031194011464012102280c0d43e40c0700048482d04104000c41e020ba45800c54511003500d50001100107000640007404000138540c41c0c0e00122585480c84400b00741ea941613075031581c0d098030302400155005050710581c080ba0210b08052100500d20a112540c0f80d2802c01ca07203940719100b110100da040380e88811a201c6500081801600050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 162040503 1250 162039253 162039281
    0x61d0c030f070c02030102041502100b01030b060a120906050f0f01094b0b0a05060a0e0d0303230403020f15160905030709050702070603111b031b0d1103030c0a03 71
    0x4840407500074440841c110081c21240c004bc20704c0b075103129a010170f40390f01001d11410981040f01a100981b90201030b07901440c01410181045140c0341e100900428420b20003804207800d00040c0100400c00703070000c0c0c1c050540043c1e204000da803030314885000e840c0c8070745100c05140c0380b4010384044100300b02c6484454040315001d48a1207274409110182c070759160001015902c0c3da40d00340000a140142410005000503549681441150f20b4090081d81007024401e02480c4106100c80426129a00c01c0e650b801c0d44850542e032800c40c104c00341c8142030049400b203002d13203e00c01e102200102c0004581c1d9461010050544007580c40c1c00304644080080c101080901c48059004a00740d5000e000d0b103006403684003000034032460301c145c000b45045180e034441c0062510300103034003040404000498601a0350414408100288281524694440d190107021019140c82c0038800b41c80c1b020400103034103801a41c4041c2c44841c06060181c803440141e07806280300c1002c1000b1281503000b60000880b1480d21 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 162041753 1250 162040503 162040507
    0x1305040204090b1006020f010e0d0f020a05150103150902150c07080a0b040b010e010b04090c0504090e0708010b03010e0a1b05090705090103060b0c1506060409061d0c030f070c02030102 81
    0x1039516140415800d5580101c4151382c00c00034031150382e042115a4030f02280c0700082c0701c09248512710380d03100d807007220f00d54040082041d003d02c005402000400d16055006049400c1d02d518003001c944102d070f00f03000442e008084d2480c640000101c0c2c3c003500b00780c0c9030001c0409a0740c00150003080050780c80100f880e14180182000012941c4080c488010341304d02511422a0500d001d1800040c40a0141c0198805104540040c003104804d002a1410784003d040c00245810071000700781e1760f41c000d5034010300c0e416007060204842150041500001c9421401c000c0c003000311880201400d0b111040765003101d680c44011040e0208003010347c1d00251110005a140c4515242c3c400305602d0f21084a88001058000650349020750741403050f100148030344000e441c18004000851916030407069014802c0c00c13540c80c00304046076a0042110b000b01192802040095690200404030b420709400031003030703542000d002034900b1100e0b10031640309920a52140140795a028410340d0300c13450710182039805641c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 162043003 1250 162041753 162041771
    0x1107050a060507290f09210d0c0207050d081c02070b0106110a0803010303050903100f060519030f12050c01020301060314100b03011202010e0d060507110304051305040204 75
    0x3034098140068481c80d980d141e41c0d880182840f07895451031541c003400c94045180c409100f00e0074550120780103081103103103032119141c0401091405110a5200c601070507000100c04507a44503500420380004c0080c2c0c1400400000e6006903101d220503c107032600083c2d50401e460008039064010881c82c80502c071303110307070039020b0007400003c0780c10851048030325035107000c0140b08403504111050700c0d800400c0000c284208803603441040500041c48010180303d004915414556003e021007028080e08040c20003200c40807400c40383c05880c141c460349010311078009404210140700d0441106580e00301c1d40e09110750f8803070380d1030784041c0e0036488140d41000410b00803542010800c2c0001d40c000d02650743c1c04160802442ca8084800030080c0c04600311b083c005408010040c80e5105880c115800140481150a554001a10800d1418007002c0d405202c0502e9642041416408180280076a54455107003035600c000306a034900c227501074158000624650712068107490b0b0405540280f01070408505809 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 162044253 1250 162043003 162043009
    0x1031107060c0504030b0a0e15040f0b040c180e0312040203071a0a090e100905060616060204080c01090f0311130c11011a091501180b0304021003020712110705 70
    0x2c00c10300c42d4400180005410070a100140e2403454120148140810440e940701d80070542d20f0041e0382044010540140016041c00404003a00385519008840380b4030324a403500e8510340c03902d404e0150840101c13040703c80e40c01040181c4119110701641d0b800451905030f607e04521a50380e0000c0c130803a858030030581c0108000030000070303c1130b00d8140c1a00b40c94030380341151005400003442d6009045e5090025041101c4440300601c800100d56603482d0004454840d4400300d14944618800b290315160004240420440b8550052044074281001c0c5d486204045004542c0038039a4400d103205261b0f41e43c1c007800845c40d0740b6129005140000d24080da02080980d00f44203943c005d6104201041d61084c010517003100a02071404ca50001040c84400c41081c540003680300b06000c0c00720510840366035481c0040383d0107075107640c41c82c20152102610b400e5440b0344811160303108644c00c13400341d001c3d052210402030080c000d580d4116400340181001c0c000c102004c07100b00c4101401070708284207044001505032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 162045503 1250 162044253 162044261
    0x60c010b101206060302090d02090c0c030703020606040b03210d0b041b030b0105160809060d151401022d0703080c0106031a360d0e09070305090c0103110706 69
    0x700c5490340401d0301e4003a141c1c001260b0256100034241030041060702d119035609002d000303910f6411248a40e03e92210070f0720044a000d0017640344a5440300050070400e06400050341072050900722000c0c454610241c0a2544444290020502d62200444040c15101d1000050300c0c4401f10f9901c0022000ba200740080e00b503d038102400c19030040f407201e0391408194540070300d190f080001c1c00c0013803a22030319040c00d1500038005600a8900c00010801e0343e01030361030000f03d511582d1400018030103071040800300b124001c1d41344500c0400d601c0b06140890994008100c041503801d10302200700d80070300722800010b00500744031000c01050103402c80100014a00030b0103028042c40c8103000080c89130440c42c00c540300313000c42090b41081008490070072169284004603034000400440310001c02c003028040c0e80110050607404101c0d14003e44952005080e8411191a86d02100710344124444d11114010350131101d042d2003541c6160061003000d440781d4025080804c5034071445407440c0c0b8008254403500122 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 162046753 1250 162045503 162045529
    0xc03020c0a0f030308070305010b0d0b2107081009050c2b0305030907170c0f01090b1206100e030703020906060c060906042a05040b0402092806170105060c010b 70
    0x720b82140d00c02e00616604c5080305500440c541020401075060051501090169408101519840e8080320a6540340d07890121000c02c820204005407080d209030107501c0d481d81d070086c0030540c4100242100710b00700b1400359100301170700b040c05000d8160342c00091058041c070071912405201c040780d001881000c0c851004404890180d603c050322400c00780b07462420300da4207511405000100540311010500007140359010032401721081e0400508400041e41c0c103810941c0441c01c0141d02165a681c16000007405900c200021102d8007108840c010041d13801c1010045090b41681c4036401c24001820013252081c0c100b41d009010604000e001c01c1902e14180080b103003080180c00c860280030801540b240c00660200794041c558510141c41c911920f000d8065120700c0c3e204540710344881c081511207504450380400042c0c1003054401e070100c2c80204d00103903841c0b400b80810601e007000584c64811842091300c4101c03030500e55034a03481d04041200a4101100202195580d5064841c072507907549000e2002d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 162048003 1250 162046753 162046769
    0x4151b050a060509031c020c010603140a060507080f07120b0d03090f080a03020d0302090a050405070c170a05040501080903090306040c0303141305040f0b060406051b0c0f010c03020c0a 81
    0x41c409092a0400507500d003d8038005041e0b00602100c031701500500000401c3c00892000161220301c00a40d039409440280e2001d052140c1c00c0b001103400c81d6011880c4c4140f9070045605000300d4607106c200300c5958200310b98901110b46a140492041d5110711300514120f080104041011208030001408101e241034048003c00c80c02c203020003007416000d41c00300080c0f03840d4000d00091034064402a45039503095005008141d80054813210b9a500c641140b00600701c003401c1080380745000e400107031502080100594041d100c2c0c6111110034183c0344200c030081c0c103072236440c641000d00c0d04005450a502c09408c100b1140018011405192402c0150600c0780d409141e820410350714505000d009080c889071041e048071010405007044e0380c121501e410488006440015801e15100c1e810340c0100000540d0389e0b40803100040020f405036120780a0040240d442c009404030242c6040001c0c0e5585161080d00d410681d160f030019071035800f5148802603280203005860306041003c0015440700301035001098 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 162049253 1250 162048003 162048013
    0x306131b0228120903051e2a0409020105040506031303120204031208040f120518031b0d080c060f04030e0d020a030204022a012f04151b05 61
    0x51640d07040203400390140c16455990360000c1c500c0000941c8100d02000980f2168001004a03020380c402d0140c01c0045400205035000401103c25080480c0780a04043c0c1c6a4441c0030300c06801078401024a2020144000d0445400035186007484094507000c102a418000c1c03d0200244a0311400000e61080b001c08900b800345801ea86000340009444c03040c1003001c43d20510081c40060342004112807040c0450401c8030056036940b80c0500306074041c0400410428498141815890b0880c1c00b0780221040c0320242c8620740d00310020b05030340e030038141c1e40131990400201444e661428441c40101d81a4090344000c1c0c600a030606140d8903040c2c0035503084135118022010001855440b151049202c10708a400724207038002034000940101080c0006889584d0018030090324881d500528441150840c0c000003010078107880240c005e00900b03000c1d10002c4004241c03000d81d8001540650403401c0701c0b825a81c04c290030403c808000782c00d01d000380c1050124440280e0001003150780d0581d665449000101 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 162050359 1106 162049253 162049301
    0x110d0f0501180506070c081909150e0f15180303041512050106050f0403030e060409020d0e070608070507020f03010b090f090706081b030613 62
    0xc100790329025490079006042d4101d00022802401581c016540b08501170317601000c409001441d0510400a1212240c21040c0b0301ea0380c103415181c0640682d0301c03480542e56a01000b0020008a16007150045892416611b259281c00c410f44101b10352001c00902905640503001e208205e150001400c042d4a4608100b55001028001111540081103d0020340301800010721014903c0c1804000f03d01c6601036021901e007581d600b0b890510742840c1d41c404480ca01c04102c5c801d980b040382000f00042c90f003824009000b080c00c10250010314003171100b1603646071a4595020a041c440340c0c000300851160400e0540d10341ca074054590aa002ca065000030707004101400d0050740c00840c0f43c0610401980200030244500c0c401b9048903103203174403008299140380d01100c2c80e40000c0d08904c001c0c1300c080a0b0301d014507005180034000702110319010010707500355041154000c0e03400084031142 = true := by decide +kernel

theorem cover : BRFrame.Cov 161870503 162050359 := by
  have h0 := BRFrame.cov_init 161870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 161870503 ≤ n) (h2 : n < 162050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
