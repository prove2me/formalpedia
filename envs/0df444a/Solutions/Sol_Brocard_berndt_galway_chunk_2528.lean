-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2528
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:58:35.647983+00:00
-- url     : https://prove2.me/submissions/e4d3660b-54bf-42ac-b11d-433bdd102f95

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 454496402 ≤ n < 454676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 454497652 1250 454496402 454496407
    0x160504141311060d0b03010f060e0f1e13121806110715020d230304020418060903021b01021203042d0f0c090b0a090b010201061a041509030c0b 63
    0x61000d924401c0984042c01800155a00e802041c5500900b800c051494020760034a955403000c1f8001c0d000f0301090f14007804403498203950f2142c1072440c04030702428042e00744016505035400a48111030070f5118020f07404011200613040d02d4415031114580c5007240400c0412001c101034161200003040465515160424140030a48075050802c1103a5000703c2200065402c12080c0b550086103141c0c0324403031505c801b500c8200503501c085c0c0c0c0b5410450058410001040060010701c0c00d50b208546040c8094900c42c0540d031250f682c0d0013200c41140f000e90259100085100d2100022180c20400d84028805886071010f1829203580718000944010300802c2c858603001ca10302600d4040e2820060400c201103040c800e2410b0440b0304040715030003034a400070314400c00f146e804084c1c06400f06008020f01610303500e900d8031000300020003010908078115502d0714800505080380d6000c011910750781400d00b03a5600d103480c5854044c2061a01c0b8a02804001c040030404154a121031030221008400d4103035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 454498902 1250 454497652 454497691
    0x7030807051809060121050906011a120709050405090c0906100504170109200a06050a020606100e041109120105040f03180509041a390f040816050414 66
    0x8441d40072500305800d0740300203c0300301c1b1000c40440d001903000e40321440c19a6442c1e600d0300c0040214900c45121030a0504040142d40004c2c045900700c6907000b005890860045e5403038200250949600361b400d04003e500218890280b494405109030b0070007000ca42d100220340c14200064a0b90041d441803800c41800c0b000340b2000c9140a400089101d43e02c020000020300741005100d0041c0503144045010301c0d40050041100d03030003030b0111204987c0b66002419559200c10420040c040c02c160341c07a081001d50a0351a0f0252075030b01420503004a010031541d2a20ac40e003050120f103000c0c203e04090346a0502041c040840c5030300e4002090960149080ea01c100d141c40814014582c80341c0c8015040a100030400041c403400c4030052520a01103450601551201c00c0c1c80c50401c03e504c001800200006011610100003103003004a000318001280341c1045040015541c00e078100da844401070760060722221000c0c080b04901c1c80c2c007426044800b04403900c250040c0c4021500001c01d8039019408451060 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 454500152 1250 454498902 454498907
    0xa02150c0901021f020403050a0c17010c08180a05060c0a0e04150b1b070306020703030e01060f05010c0606080105010b09150708070803130f06150b03060907050a1404080102070308070518090601 85
    0x407000f543d0400101c1c1d02e0b12180b403400306036030741d862f1050456010125610300910603040c090500e044640d80da03802c4c1c0c9612003004006003141c40d01d00e10000c0780b00700301135803000410500c0a2840b40c603e40e4850383d11038810400c080e0100c240d021a0610a6242504901d40e03442d01600e19019280081c68058a41342501861810540314070740c07201c800d100361080042003000c56001042c1d80745c40703a64140810013000a01600f80c40c0c80340501d9948001114080c0301d254030403400801103c2c000c0001150156480d00805d084403801e03004641144400205190030341000340440700c0741c41580c01c0092400c181621500180d0094440041c41c0c04000008551041c50342444030800c10340141c46088079444a2900d000100a801c0d010086c0944502000503500d13070240a40c2d114010180041d607041d50744543c00c44241c0d0100d0f1004041c40301381000070341e0005010340940050402040016a50f60701c41c03c0c09807060070018401c0080240400007c000256260700d010070485c2d00391b85140d030075220680107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 454501402 1250 454500152 454500157
    0x10503040b0121060203010e100e1006080a09060e0d110d020a02010e0f03060f04140f0c0f040908070c0f1401020a02010806130f090c060807021b060f0a02150c0901021f02 75
    0x1034134040c0040000701e9090314503d03209000300202110034420556441c035141c0386080c101c6511640101510082008602404910354000303400e0400285141c915079a150031150303084411030b039a038031030300c058449103400450b40102008550020320402c0f2201c0e030000d41d680300070f100c024100302600d141d0845075120b041c402601100018151045442e0000584000303003030031202502c0324460062920880c00002c1040c1260000b8840039141c031005070810303c1408074403c40526006aa04c0c000c140210305101d020300401031046010725a1285403510020004429070003842684070400415a0107a800041640c0c143e83d080c00c1600541e610076000a0301764003601600e140d000c0c00d00304002c02184442e0b1180b80c2e1a442071900c40a141e07103c20086a404c4421503040004d41c4c004000403145600588100c61400320043c41145045246180c104003a0050009400980c0c00444150580d503503200791150300c0501048428204181180003e40d5094144002c1c1020484a0356107514403150340c04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 454502652 1250 454501402 454501469
    0x12060213061e050a0504030b0c040b0a0f030608060606040e1905010602010207031115010314030405060d0f05130203071403010905070b03040b100503150718080606010e010503040b01 80
    0x41901030340c40c0ca001c0c0142e05509441108195940c1c580084940a5015600034031004d50324207041c2400c2d80e032080801c02024196112445d0107000c002100071410b00200b140a0b000d40d650041d0501c074050240035521682c20480e42d9030400c2e020000799840d4001510100e81e1000d03c405550780b2104403401e00031101007041c6480354201800030422517015001000400e209070340d0100107000c00000c0c0d50301e0b100d100e4010060b601403900101702142c1825004038000d048002601d107031650750700004241c0c0e40036028025401d030700c4103a1b0641203215446103c0d4028820003031200c0c1c1da41160300081e160001030051151140e42a8000e01c200d460035030060b07080c00d9004d400c072a0100d850300c8021015802c2158219121601940012903445010322103c04807200940240f5420308100300c801075014008021600300040040e05a481d014014a07100041141d00c014201505041e00010240c0c5042d4020728148881007080c0b100203255103d50504407400d40c50781c80803c5d42c0030f040c41403c0303881408 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 454503902 1250 454502652 454502677
    0xd20192010091515050a1a07080913050415060b181e0d21020a0816060906050406060503070915051504030803190507110d030b0f030f030304110316120602 68
    0x9001c2c585002c10044501750b8204071003044409503924440200901416188104008240b21150000d00300001800d0481c0f402040340a022840e52600300840c1e00403101aa1a449407030b545100c6680746120b0b55016140b60506a0f00d0410300c044a20314604c03146251130300504402c1791000307012044000b1689000d50050412004040782d00b0030f00034000090860040107252940e0000c1600c0c00010350342a16030307012012901308100b1201c1c03c0850701403a0400d40e4401c2d1107124200003e151840340c2c62040d88181c0300001c10364100310603d440d020b138540040c1d41c036900e0204030021100400c4100411904125014601c0c20480300c0c038000c0e41e00482d44020300b00f020100600a000008920103050780f41410f000300120340e81c0d0682218040c1244036895200e0300546800e0300c00368829044400ca03041c006d40f00c66100c4045002003807800c00040c1c0008504e403c0401401708002c1510705600d5071500880041c004009100315401890069201d40c00080c5c0415000500f001080c1c0c054071200490304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 454505152 1250 454503902 454503911
    0x30c03010c0c0b28050c160f05010b030d050d05040507080d021c020607090303031a120304051c1a09100603140d0f050d201920100915 59
    0x40e000e0245940704000715030309042d840002c0d0010301d000104c0a859100b400305443c10120707070200b00c0300901020f420b403107800384100481c1100148440d46c42c0a1688120f4004510075141d040890864a0190340244a50071500000c0a41c1e81e20505458111020305030009458980707140107807501580d580400300314050a406170300d0080e00440c207600c600c440440c0460380380c0d42a81e4101e0720742034111400e43c08584036200a0000c6440b83d8050384d114816070450402c0c0f4500f01c40040c0d201580203212200c0c40e0b00004003480b0604007060404002080b046540ca82d41d0780d541e440700e40006440c8100d0b070040d1051800501500d004010758020740704902c0c02080650340740d0401c900c100502e510403802d24400d5805036081a403252006241c24109951114245901400003401a0454000e002d40800f0300d8840984502840c1001704500e41130011122090511228080c02c1c82c488003520344014161200181c40c2100301003211080258015400a204081450641c3d0914042e4070004402440e1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 454506402 1250 454505152 454505171
    0xf060a020d150b1c050105061b0a022d01020c0a0501030903050f070b04121e0f020c0301060b0a031d0316030504270b040e1209030a0512031e04020d11030c0301 70
    0x60900400403070307018481c0115500c1d5144c1c00384054450a1040c140c018100f0000102c1c40da04050809021a45082c02d980e480c0030300d600014080841c980c0304c41c0e024901820001c400440c11043c800601c4004c0c0042c0c00701d07420283c0068020181407248032b050589900c0c1d600205480350003214890501c06071003544a65480c101410038010407101115a00031603200c1d060320b1740c0101030040b445145010243d00180021a0072900c86000a0940c8107610a0507214081c1e694203000762001b9007800c548036900d5480d11f0f000102959142464584014500d00c00c0c0c2040301c60100c11600c011a6002d2180600391003071074100d446215a600800080251b0008103000f05003152881c07400c00032164080c40500000c00820003206c0c66071070354001c0da901c00881e041c017116a4102800240b44002c00b91140d40b12903440e03580c00c03d4040720804130300035000001c02401c15aa10455068428240350440c060715095000c290645c8403104050a500301001c20305449980c100240070764800080c0c0248040d480 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 454507652 1250 454506402 454506419
    0x80c03120c0406120b091b0408010f05101706010e2d16110309011101110301240314010e06040b0a080a1707031704080702030d08090f0f060a020d15 65
    0x40d010f0301000038038000b258015980103014400320004014013170325803130300d84107083c4080480305080d242d200c41d428040010358200031301c034030012070b055840f001c030f01c030b00e0821280510740d2503503003080482c5802c00900c030380c041c4030005050f81921030f1540c03120381544420541020501c14a0b140243c03500b2030004089220142104260041c100030201c1a0300300004a01900c000414401e002c0c2d203a80140102c440c00c0d845902d0103018000302400000f82d104425078103e0855009810030300c107025520314403040d8908030f0001145482c00d546400c00400220b04842190810184251407a40c41c44a010410594841d071100112120050841c200f96a0b1074401640790303070550000f6035500e011001d04592841e12030040b618450b030301d507440110188002e4110b642d01c11000d4410f5076141f81c18042100161010400c2003c4040c1e6a00c0c0c0114074a445100545455144e10300196544c000c00e0400f04080400650981c000c043c5900140c0c851320742101400003054924001028511240c5001403005c0c5d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 454508902 1250 454507652 454507657
    0x411120705100f08090f03090d020a120c0303140a080a09110904030e1309020a0905041e0309030212150606031305120406030c02030414090c0d02030703050906011202030703080c03120c 81
    0x203d03d80c640380210b9445440b11074542d522440c00040c590410031031303504a071a2140b1201d01162006100ba440c06495010440b1594140101141c207000d0502c8240240740d007000d81d0108180030301c0d607034603d0075000003801402240b000d444030300041d44030001881048104100b94210310809400c4001c50316041c28018540c1c280d9810f598041d4101038040202c0703040750f01a141d030700380d0041e190b50804c525000710900100701c001e00507900211390122401c11540903004c00000301c0c4c00b03599420315050442c010041000e00c0d403071900b0340036844242000c43c250103841700c084d801602141c490f5142d54610500d80011100c0000090140c0920040f04c0b011044c507801600658942e80e4041103c0c182010080c2d940703102c3d9000300c4000200e074a40c2c010306464041201c66004400350385a60403c4440f00141e0144d070019030752040172036261810098010000c0102c1e900408541c411000218184d40110f070302e6154031302000d811a00006078058180c00200b0450708004050090301c040b500d0080300009494 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 454510152 1250 454508902 454508927
    0xb060414090c0d1a0120060415061205070501120b030d0c020f03010e06091005040308190912030b120303100b0904060f0807030c081c181503091a041112070510 70
    0x410040d505a110840c000d4450201006c038030041c000d94946455018000c609038012910307480e102c00c0041110001c60001e02a0075100d03d005080d00ea0130200050003107a42e801c00e0080a525011450005940010740841d0328021401d22011507803181c000301c0c1084000d100c4040c0c0642c2080700c0282206800514684210503010030340b060318181002c0342064038001c1c0c0380030700010300303000108140c001080a01440c54a00400c0000c0c4200603540300f4080c00c101c241d00c8008030390341e104858004c0c1810001e5030309004810300994658608038110f80101025030150441e00c800100d0800fa154683e0b5004202a002500c9403015090f56458203030740d192110300048599035000c04002540b00d40008082400d0303c40b044481d5049d42c2c504800320340f0f01e1000480c4180840844400141c8203c5104009091404580d400324088065017010013104410b608240a104950804c10000c038444220312544500225003122103100c404844526022458106a502c600954144d1004a07000007202060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 454511402 1250 454510152 454510157
    0x150b0a081f05010807210203070206070903020603010b09040e030403060506100c110607030c0c0e070f021b0607210203091305070c06020310091a040b060414090c0d1a01 74
    0x160394035000c064072655001c0c100c450a2001c1c41c00240038070b40c010030042e9446102450828a003110b200343c02c107000c400c001d9540761403950000901050b01e40c1802520341c00701a508180b66814a5036000c9036903440140314001d502a0007207960607480e61a0b07004000c400c82c41c0d4040300d485684900b0850000c00084c1e0701940304030f071010700f18000c0724081d00000d0021070f0495141d4061801207420b0051650181e0011010018150010070000f13002040340c2c4045e143d04141d189413490050380c0038000e611140082c1d41591720008145440441c11072068000001c10355007540c03181d03090f280c5541d994000c40c0070902008941840a006268000007800d83e0841c100c9011815104001030007080752000d07201d80001400340707103c0902248054004540224410700b10880c1c42c0e90340c440d0390302141c9501c400d105901031900302200c6640f8045c00b66690580c0112102e500d000c0c0380c40340d60300400d105519114000d1413003070005600041841c2c156125000105020b00150607045a0254602100301a6031301 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 454512652 1250 454511402 454511417
    0x1c091e090b120c2b0c050f0123210906100b07030e090c1b060f090102090a0603090302030d020d09020420070609110a081e030a050913150b0a 62
    0x51070102003000c00080100058003580c070550061002c4c40c07015000214a82c0807104004002007030b1a040d4030134481c0a0703440342032040d041604201140c400420042e040000f524145514807080d10385014142c0d001c45105580e800700a85501540c46c0b0451143c540c8042a40801039007140c08900c5030301c10200b0042c216101ca8a81030703004024020005c011b0000703480840e0b44e25081c18402081e41c0c20101e0950b195041180d400c98403100c040301c240c106051034200f0f50038802d80300014005c05400c0a070000003982080c50040120301d03d6421403145000b0903072100c0081e410306009000f16060060100c80a40d41e59940b4200302001c0d010149007240602e1422141014049080e0842d140c110301d60707415245001c0303c1b0b4880502800c46000199207000503002d000d00503544441000001302000000b80150503000f10031441102401880318529030810086a104141d1020840300748020848401c540444804650300c002c103442c03903050304402c0900b840400e031a081440a041020300a607107981 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 454513902 1250 454512652 454512671
    0x100606090e0f1b030c04090506090925031e030f03110307050c0c03070e0405150c070210050c010e0705030111070b06120a08070804030b060108091c091e09 68
    0x5034000300394481c004903081c9000210302511090102c1c030740c1028020000107180c000000c203110340c41c0d0060311082183c01002504210300040c601411364007000481b8408418500542034a403180400c84040d80030324540704204e00c0d1107014107850001345400c02d40319405e40746000d03600c00100f9030489040d0302080c03142c07400e1815607200340681c401610b00090014290303210400c0c150b907903802050308980765003e0301143c0c140030b8408102e540000c0c000f09100c104d1604150800508041d10200c0c403603251808201000008100c41d001c4400541c1e0588a1540001e1000401c44031802140c2c4426059420101c6018041c840040c040059410480080001c2e80703200c101c1c1c0400344103e0000030240c11a4100040c12454000c6d40404501c4008042e913242c05200d942c0e020a55100d01021520340c84045130070320a202001c40425482002800e00c05258140311000540e12446540306810208005002440542c807070610b5200400c4000802d41c14500302c0107104400ca882400b55400d410b14100404 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 454515152 1250 454513902 454513907
    0x27010507020c0103020d06120602090a08030a08161704112b0807020a030f0f050c040203010303020604151b09080f0303011d0403200c0f030606010215130b010305100606 74
    0x280c0100155002040b04100c0c9500640294000000c00428117564034000034070842401c800b440704502c110350060f030300d80003501048242d0307650303400580c03151740148049214960422911600205260003962441c10081c00460b590035440c103695810301c143d1014002000304403002c5000024003101d0039031818211000e070191131181d85c035407401e155413500340ca0400b04101c040140420380c00039042d119003640b20389510301c030052043c208558200c48480c51405124041c40181ca6001342180c040d8a107514546009654210240c000740952281d05414400050f10f0303480b07a00c240042040c7d01d01606035580018007000021f105d0200e07103014419003520000303400310849058404400e06091103c00d60b0b000d00c2130100008000f202442100407540c86082070811110345041861002017002c81800c900b40062000c01f05840307070203079003c0000e001d066070700441d0f0002c10300c41841d00000980c0e40c82010322101e0010410151001103001d00220134003901107564501d00d0008103081c030140b80c1e1203e08 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 454516402 1250 454515152 454515161
    0xc020d08100b07020a0308040f030c08010b0120010f0c030e06010503010e070303050304030201110f07060b09040309090e1002030a050403090e0f011406130e0106030b010c05071214062701 82
    0x100c10925030780840a001181040014108490014011145094996552840a50041d000a206600340700010410011070088160140c51000000d011441e142000030702501200f445440e040728a181550940c04800d6010400c840042c41060068400c2000058001d1455501545c00c500800c00041510704050181907000345c0c2d0080107200051558800f00c44a4001800440441d5210600d00d004024110080c02404c141141150f03034508152800104449004e2000d0f401038060608100c0420340050001c0c1c2264041803020800c45d801c10601820240807040c2c000c580b52000c002e00448003001ea0000c1d00c11482a01c440101c10303100c000c40c44000008540007421204108014410103150f0b200e0f40060610140c94035040a80b01c544e00c00c01c1e103215800104c46510360000400229a040c041c0440d201c0c02820720361390359080b540301c00e92100413030f0040b540d908c4a2000716a040240d00d480c0722080d00380c440162040d5041189144250410b460201e20512902d04421070788a07006200c1c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 454517652 1250 454516402 454516411
    0x905040b090a0213091401090c0305070f0518090c03090106080604050c060a030603080309010f0c0309051207020a0e0108062a0a08061201090305040503011512080313150c020d08 78
    0xc541c0341652903150342806980b121540c2c44802c0b10030940060143c00b2405080d50440005522105a40c14400a4002c48080a48042c10141007105016116400014070f004543d042d251042d602e50524000c800395000303160b42c043d0800c030350bc804c0101094029000c0c60150700c2c050000d00039140c0e41e415013031b51140e080c1d5014000b0b070003a90080d03610345802c00041c4800500c41c28040340390741ea00d4540f10380b280c1040302c1d4a402d59464070401000d09269100e6131415400c10300301001420065102c650780d60ba201c0ca810115030034005502000d641d58100044001c00408101c080290384a01c492515070307005a510480141c001b00300b1200800c44a01c0c14013400380f62001150410410384002c803230f0f040001e4507503030b04540c0e400c5603015100000c0c0240c4035030301d0080e02c42503682c500e448189800c4881c41d011596000c0500c440602910001c501710718009908000b07010344984035001c0503451707044554001480310301070407503102d00340102d504a103800070030940039a9031b820300811003542ca00c8000c85 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 454518902 1250 454517652 454517659
    0x70906030c0b13051003050906091c0311040e01080304030c0602070e040809131a01110a030903030f12090609020f18180c06030406050f010603090b070f02010b030d0509010905040b 79
    0x509121550b18400900a10300e10b8a1a82c60803d6484022610301496040c03504006a100c40c20001600020440681c021034a5801003408146000881c2c0420100700032810426071100c8444041252140c1900e000d400c0d829000c101c19651144180c2c0d0740c0e8440e2104881d0b080c500c40300040e001c0c0c0081418801c40f0851011a061aa100d90703031984154001c101856018210b0210020560068800c182103103038041039030354000c0781c458005020400c400d41c4c07645007680300d81649000a6442007100f8202c0754541041405031802c0c400648a5900c184640500d0610b4646c508050091b1034000039003890095401448030442501800303103450030450101628100000450000a2445422054051038905480c05203842c20001281e80e84195425035038181c0360301c1441080c60400910a00428280c101007164001c0c0fa6110020164002d090030b050103080303100e0410b00c500039004039940701801004c3e40c000615500b40078100b5086542c103a40081c0c20301d480418181418800c003001c0d5207005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 454520152 1250 454518902 454518923
    0x1030318120f1407090608010605030120070201020a051903031404170906130906050f101e0509040e070602060105010c03080a200a020304030203060a0501050f090604110c0c0307090603 81
    0xc0c1c8500c2c5900480407412581c082c01c40560b02041d036800d00040300036011800011030050315114605007036842c5034000c0351080e4500951a680e8480d80000700003485509126151615020700040c0d0409001110242141c001c040c007001032600d44240c06412035101e0b80302000b4550980441940081742110010100382000031401181d05008015103500c580c0142242c0ca4606804100540400a40d0080c04801d4846009020300c0c90045c032401d070704800c10350340c41440c070700d0b44030f401010742442c480c0504c14000c030000303200503652168003121514180900103000803820080c1043c0c0e40d0140380f05180040c040c072800400d203503200b0841400c4031505559001400e80b20010240d0040424803d90003103180c0c01104602c140c08100003901c01d10b0001d8000d59265071440c0141414400c00905601965103850018042640e50b500784030003c21040d2400c400e1a505d900c0850000c150340046825031900205405800713160015500307810a00503000d55060070341e03918260f4107031419804000c10b90f0505 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 454521402 1250 454520152 454520189
    0x603180209100b04030510050603030f19050412050a030f020d051e13030503070b10150f0215100524040510030f050a020301030b100506190903170301030318 69
    0x7a21180d50440046480700080542e511003032015a070081d8000c80741c0e42c200d00840c2840074881c0c42244e07407181c0d05901840c0ba00d03e140148032100c0c0b040348286a031a482030409502ea00384240161009014002d5540006071200c0c10700c907a031264040002c2740080c4030001100d191610214030a42040c034a41c64440c144a15607858081c121066040c0300404c013010310880d551009401c1c0342340c00030342c00388024603903440041c1446480940003e101042d41e2040803410400e52140801070310125034140303001100b880e40301c18100c2c208609698012921410b031014000000f000c0369070b41044800894142c1c01c404800c0041c66882001c48a0591210b070381800100828203100034442203420f414500020a185e40600e13110484000b9a0b021000c140c1c080014010004062085c0c1d4110444c44107000c41c5919000c009000d03031265110305403046050074018522103000d804108003a6502103551800e40d4611240d43d002d42e0000d100980020758500590202018801101e03010303a2800210300010310316 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 454522652 1250 454521402 454521409
    0x80d0f0b0f0d0204091208010810050403020703060b2e030f050c0a030b130e01020d05060d0b190e06040506160c0f0201140408030c0f0c0f0105220b0a050c010606031802 74
    0x20b0190598206846039400d0700003a18051100d0140d0900b40c483c1c069030b5050103121751078142d882d0070440e0f205150034144000701c2d8002881d84101e0398004404241407255030085400200e00c04040f88001c5005601c613403500d451481500000c0010741d4040154207400480f050680b0750551f01c1e082d41c207104001c480b408038400c4d00070020a100180150312143d14841d1710208031a6400c28644403a50b0106500082841da801120341100003180c80b001c0b0407000c2c2d2582c0b04e000070040d041c840d114440d003294680301c00f01900244240c2184100b43e512a103081c1c20105d84a4404969074a0280444220a0402c9004040d80c0d00c0782a0480c0441c2c2450b40b0503401950340818650a0300184071051200050741d07001000100b801003900320191808030000d4115500d00508804940e115a80a80c041c6040d646d10800741c40030184245010340e001c0d6a41c1910302d0030a0040e811440501c00005101d0280da0780040081800700c41c41e100070410b4035611201202164450041c4c40a48441c40c50079101625 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 454523902 1250 454522652 454522669
    0x30204050403090b0703080f011703030a0e0c060d0207060f1803030f2a0905030303162a23120d020703031401080a051614100c0501050103080d0f0b0f 66
    0xb4880d00b0320882440e1102c07456000d580000700201c3c0000d0688041204410b041c0030114014010411444c090030440c21440c4d4032030000034444040980e9500201d0f40411042003907080c43d030005813002d60348070700c00540100698001d4400340c80407402d201406550035150301c646622003185803120340b05044103a408401502002010101613510343c603080d060014030303004014403581c1454185451103c201d4003d009151141c2c0103d110b40c1083c02000b0f4076425002d0b50395800350b050700e0501036540c0c241d1a040c001c05946456842070302e031907075a004200300030050450341c11001103418044084c4075006081da42c00f085640d4004039042400704803d0708840e6005006a18800c0c180407500c94000700c0b801c2440764007680040044d500101c0758809009081c4400c409001c4803d11105810f8142030304a40f0a09418411a004440112601d41c00a00c40c00c8501035040d4080000c0c022540c0da03007028131803604036681c035440e03070ba160070050782908056115901982c5406050031041217825401c120105 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 454525152 1250 454523902 454523911
    0x30905011202090402121e040203030a0c0c09020a0824030705100c060c050d1103061503070c0818010f0507020306061c0c0803120915011505041e060f09060903020405 73
    0x142e0b001d0100c80000d0b507590015244009200754501085d2410081c0c01003103c412034040341c00c0500b94800e10001d41c07404402c035441500300742040888140d01d03180ca4694000d4a602c12450309202080d2480403039400001b03940139520400e80c27503580000c800381d11200308400d40d030400e9065003c110b00704414104a10000400d001034100901d0503180c9487c2c4100761403031001c0640c00608005843c01d0592800d224440900069402140c1103181000214040c8420700000840c2818040000703449188078446c004186075201c40c400381c0351101c10a4000340441425505400b00740d40c1604041a2841b58040d502c25a400800a01007030b210801803012000000c1103050000c2e0031502050085180b84000d40c0080000000070740d0b030360b83c6280c20b038240300d00d001c2c0013032080f600000200384906c0050485181503951001c40f004940900d0281075407184242d500a080c80f0401a101008410005181c03070125402501c0d95032403400790030000c8910440b240600740c04584880360a002504007030748482d510 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 454526402 1250 454525152 454525187
    0x1206050105100203041d061c06060618031509020409051c0801050d05030d0c02070f03080304060b031f0e0a0c0617150112021c0204170705150306010c020301151e05090403090501 78
    0x8c1034405200f544208080c1c40040d0752044d100d01e400c00c002640701c40b074244061181446004258115640c2034a02c81c0c0c0380b104101d5641e100c1617000d00399a41d99010703600300d40d8000304442122070076004181d950982c00303150303601280700d08000090303604024244680c02980702c1302847c0780103140310300d600c014181c1821180c21440b9520380802c4204680c0030010146015240320780d100d15040c90304d142601c4901d43c09601030f40140740501c542c4c1050341d0b01c00041100403140841c49170101c2c0442072500c040d03510003900c0d100c200d11001035403c2d00851200a01c18040304685450b990320304050301c103003d0700c540b282e001542504100146045031741c05050349425076184644a0504e41348441d059030815048590080c0b5401e0503a00d9010b000c00018004000990320450f039030142406166550100030010341c1030040c50b01e4110110344d0298000a401e4040541d61000c031901c40309850311032172114500b09840c400e960400300300391500e0805c1501c9a54036686032503a41d41000c004446281c55074484095 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 454527652 1250 454526402 454526419
    0x11a0a050a0c150e0f01060504090b1303170a0506010f030920060c01020c031902010b10051b060115030606020a0b16092301080105010c030c02040b06041206050105100203041d06 78
    0x680883c1401442d003289078100003022082442400135007181c0e00b50780054880c40c03914001d10006521001c410742e20280724050000310000c01d081c00e551051000ba40c4003021301c0c2d2002004034a14581e400745008039000e0340c1e1040088062042030301101c191060207000c6a4181010444105c100300c000c411400c0050032241c00c0600c40c5a4060030380c0c100c0c01043c4255000800d4017940b50001084100c441c100c0ba00c000d018000003035010411180d2404011010403500140822a8034042c0c4a1003001c1c800081c03c4400640e900c80311000d07003824030051074002038148103002074010310000c0e041d150103401600300f101a071241c0c219460704141d000707001e40030b21040140024911035840d40540145140c0e01c0441285040b41c0001848076030142c01142c14406a000c42a0109510003403682d01294151000180159000d000402a0140f82d026200b110f4160500c1c0c010400341e030300241d040303440685d00c448020280c2d21059031070713004034058015064181c0726120002505c40404e2900102d0107410101d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 454528902 1250 454527652 454527683
    0xf061e06030604020c1603050c0604060503011a091306061e050306090a0e0a050a03021e0a06150f0618060323070e0d0318080714040915060e011a0a050a0c 68
    0x3814542002c6c13800c01e140205000070820300501340821390012004442d2145410b081000141060206004c0e10705843c05c2c000c0041e0030f01c4400d17012920403000092050140034417890780e0340301920300c90284200240320010103421304401100007045046464498908555481c0c00340007565a005008400d51900d401c0381024200050020440d060301410103031100070341a0402038a0b20b0030a070202c1a00c1c01040080312241e15004ca84c801d01d041d40f00c1c0c03011139024904078080c0b0704100c05d600301c4104003222a500040380754200346c1c44202c0424170300a00c10f004d9a160000c0d02103480101720000141110b12007107200c09441d4040a03407002c030038100190034404d10fa0109a043e0401c01c001c4002c51031f5560040080307003007807078200c0c010141c610041c030b0041d04000032041c0f80034440f00382e20b005a443c0c004d44002c100b00d1241160158011640800c5003e030341d42c480d0720f40c3c00c80c207101e0004908140145000300c0b01d4003501301c0301d880c0320a40f5103074a03200315101d080f1010165440b058a01d140301e4032502 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 454530152 1250 454528902 454528927
    0x906020906030f01171c052d090a0503120f1b07090203090609060103050309011812050114070518060306040b090f060312070f080c10140f061e0603060402 68
    0xb1802040d00100400066061003200c040b501000342c2048030f968000c42103182e100c4504041031002040c00d24140303468100100061942a080c80b400c0b240201c9400301d0852400d407414080c1410600440c0c1c0341610780c2d980d07000c3c140c8803140c1c451041c2400c00100010f00d00804044000c0c03d8042c01400584051040346040f40c0c14805640c00a100c52a0008140940f0100800010b80c020f51030385c015202a507d19038846a592140500c1a8188614004200700c282e0300654480c004182080010000341c8046c40c18500070520804028480b03004c400c0403c01152042d001d5402d0003c074610605529500082000310700d4000a0069502503168120500c00f0b849040031540990a402c2d084505400c0c150101410101c4602c92083c103520103100a80c040b5030201d0015075034a0b00301d81042c0d80d503c0603010403070074010381500c40003840d4280100031250704211414148200c2410380300601540745c1c041005407a005075070f0350303040d42c8040100c8510180b510700010364201c41c000300b00610307007800070495 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 454531402 1250 454530152 454530157
    0xd0c0813030c03021e130b04060801051003050105010b0a0903031b08071a010909020306061002010b031c0206060901050105070615050d1b0608040c031403090604150210060f090906020906 82
    0x11605040b40440810460500102c0d5036018900c81d180c03a0410b24007200442d002480c04403900c01c48070b0310340d058003095856540c050005440d0240c020720146c60720044040f0444401c2c030040354198a400c00004d254004003003a180c01003240c1d911003c541380745440840e051010440051500007202004000041c00c2100410040f032090311060b8040d41204946004014144c0c0108001801c1044500c0180d40118916034030440441d60315642c44c40060041340100f80070700c0001d81611800d00720350f00c10501b5030359110095500d50b0860759a82c1da01d4050001040c001c0c421140800d5081c401c030000510030750448a9500c080c5c180802d8603507980c0d0b000401d003550440d4199000240d03850248040c0b0030320f60840f0042d20844c140050700303081640d2421030001e4a03100113001c0b16040940c1640303a000c00e00485800120041001e9165a1070303080d8800004203000182c000351098290a480c280014011003040340c4600c0603030f800c01c0b45000302e400c010f0229000f00311841d0f42e081040a00907600d0001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 454532652 1250 454531402 454531409
    0x90305120913330f030221011404110f011b060e03180a143010050708070207030302100f0204122603010509182d07090e0d0c0813 57
    0xc100e0203d41d1401c01c494a840c1403141c42c0d50a0081800500140411090800490354159141130401c240045103c0c004841ca03600c604940d401c10981c40350940741801460b02071130103003e480810424241c200700800009805241c00300e100700811401c0100400e540f10001401003001140032a01720007900d04640c448446100b40354040101c441d03040c01d00c46e108001a00507080c0c859441000f03400007034103d518116598045040d030596804142c01d45010140c40c1d400701400b168140402d0001d20750280030b048610f070b00050003040006070340340e01c00581d00003241d40540241c5484c0900c1d0102401801101d2210024682c0030000000c0e1104d020000440341c50240120301d1020703488400300f50150600044002c1031030b5090005111940d80c000802d908020080c128001034005da002c840d0802e081008103031049200307040100352025140c064407004207240b0302910200740c2c450200c141143d031440d03500746507684550b2a0003035850090340c960700114080c080d01824480345034440715900705281c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 454533902 1250 454532652 454532681
    0x60103030909060e0907030f033b0f2b1e140d050418090212010f050a02070c0e220c0602010c090e040201082503020415090305120913 59
    0x100100603032500e921440d400340020322a407110364103000101795900c00c42e82c000603160140b180d10170005c01d0300070003101a11601106013007803025204079007158000d00c29081c112200480304c440c60050710f800e04000041100040c145021444400f10010f121328107a030380704c1003070801c00d100e4101040e205413004110401c803003000c141c4221689085400300444840d4410564490310101d02400e4020003590140d800d249030f90580d40a45070b0f44c0c240600003070a03001c0e404c107140408244901c47c064215401150002c02c0900031030700e8a42c4103a00b02d00c240b40c0040c11455040c0c10070320001200c85a0746401802403042c50035021514400010300d103044010880d80c0b0486241c4c02c000982d0280144a006411800c0444126242c15a40034079228000d000038108400c800018102d8090f2105100300958070210881448100e0040640250300c580285040185060962409184600000015280d014002d404030107070540f03001c0b45c250000201c0e1a401944d50b201207550a010f44540025040501c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 454535152 1250 454533902 454533917
    0x30213020c0d0c0602210618130b0705120c0d05061504140d02030d02100b0d02060d2a0c03080f0405120f0706091a0610020706140c15061302070c06030e010e06010303 73
    0x820041c44a140123041e134a0545000f0000307a03c40005a185025800007001500765480201c12185803041039609140c000100c024484c1002c1007102030003076809041c0c0c00704416241d8408001e00d0311200925520002c3c81007009002c104000c1c0e10141884001508c2c05100000e140e0000c2e00f000503a0300da00d00183d000070400c005458150107080b502e04030540701c15000e04240d8001c51030900c1a1000f680700c0d10740b21490f113880b12502402c040000c000c40426840f880c2c40b043c90040c0b5011080b442070300081d8042002c5100a0016403076240220f6000000745a04503581c2000c03041a0003881c450415880c1c248030200c0400d00c14012410341c54407500c0449103034068002001504200580454001c50828031411440c54001406000b40c030240d003005100c51035821081c1100340f00d80c41c1010380901a03062914414000c000c400381c0a000221100710030720000e000e801c8228019080c018000200e10081040054065404502c1c0c802480001140858944800364a0304100f13030b03c00c500144c041d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 454536402 1250 454535152 454535161
    0x14161a280209010507030f1803321b01180308040f06110a021210091a01062a030c0501140402210a151b09030213020c0d0c060221 57
    0x280900c42120000045045003003140b1940020098042e0302c500405100c5040100c4091501402d4036040c400300c10b4502582c51602c80c030f403050741e41c02c0c4011040c07000001c0581d01403914541400b4000c6124958008044154419440d5203c882040801c1810f1050010032401c800c81c00304030300b2028500401c20390ba0b076503280c40320002d0134071600e82c0910f0030800000c4082d20740e0140808c610b1350b0160100da00c900c0d090b40d044072840c14001c1100c91201441d147c11021010802c0c80e42c00c5c20311589200c4c4940300c0c1a0b132f8400080d9203041c1c1d07411402000029880d00707400b180c1000ca0794042d0700ba020b072900f03814102541c0c0d15a4211117a00c01140a242a403e040108501c3c01411448050700c60a04a500a4044000c441e0307940c0100d42c0000c0100701072035079000400b01c6a6002d4501c4030b80300030490302e2001c07070094003500381e03511030005a009040040e00c0e00c8402c80240201c80000185400404555124620442d00c88a01d000d088a02a800300424608104d10700301406103c14002d0080c0040d0030f1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 454537652 1250 454536402 454536451
    0x3021306020d02190807140309041d0c060304030225090c081f1203050f07060203010e090606060403030e0f0a03050304152604020d03090503060c0c010c14161a 70
    0x80307004882e000e4900d134900b420010b1104000d407204164800b00c518020100703020480d04500a001c20b00f07070030928101261100089000c17140d25031583c00401d41d003c4104103000e20a80f803104a9000d80540d02c074038503241d108d01c0b85100100a10032101c5c000c1002c1a1205200010351f03a0b0703141d600d00022a10414403424041d0201d0781100ca00380c00341e80d00d00e0b461404500012040f8681c070f000d01888004200d41281030108400c440303a240e03003c50215903d40c1c484081c000b8a20098450780703818400c5000117056804c1100c111030543e0b4041c0c6644a844010008102c25000d50102c030a4200603040400030000b4410409800641071580440c0d072246c200e4040103040d90300ca0030007035140c1e500200e060040201c510403096009601603800c11091604d0b070405580110302640071640600c9400100284c0c0c1c0040c8016040a00740e08000b440618444941181d0a070414059881100350400c01d0241c880e100c00340949a140c4a50199030744c0c000c614841d148030480880d001c0c80350001050040d84640c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 454538902 1250 454537652 454537663
    0x405030921030d0509250b0705010204030b09060f0c0a080a0e0f0f010c12020702102d051c0902030c091e0c1308070e010302010305040609081612020f03030f0703021306020d02 77
    0x21ba01c0380844924103810f030724100141856104403028a100000d61006200b0300790125806990001e0202c4c0301400d10800844c1c1e83d0314212001c00c100290300d07011403aa0001b40c4104e4a650072a661060500d4031401c14800091041030603040b6a44200824040100c40500014ce40aa00300340001285810b5a001070251101d88815405c0d59104001c10300040ea500c06121234014480d1030324070b6040009a181705c012224052010000079122482c428040d98000b0080c410803100c821905800030356000d02000780c0e0300c0801c00a6054114001c86030203030500010089e4000c44d4010b40004003540e52240308200101503900d0020050002851220100c8000690004106a00c010500d480c0742c550031803020170060000038101034640f004a001d11500d504461109a002001d1541c1d6940d1210b003d42c0007404294101c91448040c0000d1700c0250002c14036000351080760001d0b52440d5101006114420707401000e80d01450750900810500800c4000301c140a42000d030003c04014101640107450300303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 454540152 1250 454538902 454538923
    0xc020709150b030a020919081c0507050c2e08010f08070b0d0203070905040e0a11060a0f0c0203030408070314061b040302010e01030b030615040f050405030921030d0509 74
    0x101c08001000440101070840f64484030b01e1000507110031200c400201c1541081c2d00320001c41c40403220128448401040c0d4056182e8402e506c03009800c1d10407801d6425004840024103180c01902c2490402c0c28070303103440b0340403111075885101002c4800c07243c10600b1107003540990000e15070200501c10207411b8801d40c0040c01618008040461501d030320710b034251003240101a0141d402101150b0454040c00440c409400010400d01c800c01141c003c85941c0e4840070b800340c400355200c40004100e8109030003290706014060b640c1d401810b0601109588038a21404200c1e0148820000015280800e000300b50140d032241d0301e100740b8a038502000518201024004440c24240c84c0f908500c0d247c07641003180c04699080c2072000c0c600c4103107801600103044201040d034150180800f0130000405003003c0c0b00700000700b00c808000400d8805210f000700d5000300c0e4018125841082001d905140c01d42d2140d415480c02e683c002c6e803840d80004a541950480c605c100d011984072010301c14002e40901c49100034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 454541402 1250 454540152 454540181
    0x6110c161a0a230a0e03010b120c011b050106030f0b090102090a030209041a01080f011104030210030b0d0f050303040c2715051207050102120708070b06130c020709 72
    0x20440e5910462814800d050070181407140c0480442c036607907106041c1d6200401c0e6441c043c2d80f00c41414078083e0034440d9070b003407080c800c3d4a0081c4844081c41c200841d0580c802d43c2c0310052080c01c03894001520b4103490031a844160f47c0c440e40b07001000980034020500654442c2d09a403d000190749007009c04045c001e4444109a40140407481c483c0d00d550000070b0869404464200b840d407524100601c001c00340a61941040703903040008903441000207488050003250701d00030090140800400d0749035000794080254031402885a442c4901d100380c001c80c01c0381c20000c04540740c403440d07076449255411003e241224140c101104220030701180541e588024511b900340210310000319080b0b8a0b4425a030994860f900e507981160705240c40342c100c143c401400b005000c1c01c14065000b1304950391003c80c0e215a90062113001d8402d03800c070341e00c1002e464119502002c154246517850b41e6041d0320032002400300c0c1d0059480105d0388582c0900b4060602d640e10ba40e000b038400700b81007030b8000041c2d50300800e0b134082 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 454542652 1250 454541402 454541429
    0x16030f0f23040f0213020f03040b0907080a0c050d140604150f02030403081303050c01150323060c0c011e02180103050108190203071e0609060c080a080406110c16 71
    0xc248980d074001c4815030b044030900d0a000034025500c00a008018248181d40c1f004002c010030003030915500c13030007058400121500f84d5074440c078055588900ca40c0081048400c644100103500307100341514451403050781584000422119a41c0c5418070456007070303c0b04003800b01e05071044041803140640804818806524500e03050f20060050b04026101040c075810711170800d01850312900940ea19030144400a003c2d03041c203c12031846504003400161402069002082c0d03000f400717108009620002c0b02c001d00420343c0c44654917482070700101c03a600a19500c890f0b143c20341030000c04214101200c10b4500603100c4070380803480361681400300003641c14140340c04010b1081c0310000a2580340440111a07194071501a8404030703042c0040d80e805074017032a9410b45840e6140074480f20300826102c0c59522959041d94070541120113003828a8054044607040261008803807060100b40e602c58000c11000c075540f04130582a4a03542c0c00461560700359003240f0b2030500307001c00940041d00101080d10041c1e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 454543902 1250 454542652 454542661
    0x3080d4703120d05091606082503090611090a1e15050a02100b0a052107061716090506490203040b1515070c0501080106050a0816030f0f23 61
    0x75a0741c0541c0203180c00c2c803d00800007001c500074041204030210f02000827817048064900050090304030740c441201da140c00d02c100d41001540243c180c3c1c0d0b1403240140442e20075403804a00e501600c40d4040394183c926585600820030f50100d88589000c0c00455440c280c2d218406103000382041c000c0480140900e040203030a00d5166648043c5c4010346408503512107515410030090f05105d08068083c4516010340100054001c1c0c22a00650441040d007140344041e6644601303c04c148040d540d140d4000c00d40200d401d001034100302c8090a4100080009103041c40c400b0410414081c2d400c2001144030f0001d0b803001c010012104242e08184881d0130410f609604050f13403480030b2100010300c209000202042808103070703a2464070000c0b0440b40b1000865681080d81084007080c0090300800f40825030850002495a02c0384003151f000d4140e0f80d035001d0003038031100312481c619821412528109074451002c3c0500043c0d52051a0f045441c600e0b0004d44d404d450074644214800c01c1c822a043d07041000c0410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 454545152 1250 454543902 454543933
    0x8010e0715020c03061005041b0210020904182612010504020703050909010f1415090f011e0302070c14130902010201021303080d4703120d0509 63
    0x481911001e03002289602464802246040c00c0144541e515202c2d0200784040a52910310320016100e0a643c1030041d40e8100640060740039400040000680c0511000011510b159010740345040000b0004201e0901103643c16480820714001a00c02088448150799482c0c0d41a04a4081002c0300d0015030070034150020180c4541014402c442c00f5a0b00001c000040610407000c6519003140205400c17140c0d40c499a00d01c007030081d90300070407141001030a00b0015600c6e04090741d40c45841d229684524140b081001d2010b20703820500304a0501242c00c40c8180c0384c41001e245041c00084c1603030016202d0304103091114804e5116402400c202c1e041e440245040d446600e6000c450b007403241800f00301c1206078130040b4020720030705100003807000c04850003104220140b0000e00040000070802c1c000054164070f140c3c410318209118500c0c4028181001a880008908010040c2008100310b40c580200c0c002083c01c141c1ca510744101f240400203101c0c080250035110300c45c1c010300404010440488102080b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 454546402 1250 454545152 454545163
    0x8031510020d17040501090b09030d1107150b040902041a010e04050c040510021911011214060d06091403030f134103030a0b06070803011a0f13030c08010e 68
    0x3e0403003410034006001c3c0403013500840d401d00d0388a440c1e48000d20780f00c07429a840350010b90070340c51101d05010061490402400075101100c0d044041d8142840d00c000c50031000b003001d40c0c0055000750311914454090313075461050340350b120484851488040c1041000414040f0441001c0380700d0b82c5080d00340460480d0a40545058030001d4070491070342003840000f603140100000b07400d144042408408410880d07000d800c540c5403042a00d440c00d00b0742e00504054180ca5680c4800c00503001c49000140552030070290701c1740e500d80142d00020350440c140d210003003070066040301440a50300c004244890b111310120050b40c01f0220b618003034078114440c0e07a060302c812030080400700310401040c088079401454803002e045d2414241420070509001c1c04c880c5071280c004807161031505140c00740c9500d240c00e0840491b02e8066203d00b516145a0820402c40c1402c030862072030001c1540103100900740e8000540080c00402034805c02802114550b00d4840c03150550703a0020399080c2d0412a8500b081c0714002035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 454547652 1250 454546402 454546427
    0xf050114071e020d0c03050a0b09010c02061b040911032203020d0804062703030507050901050910030213081c21090809100305060f040b0603010b1608031510020d 71
    0x820b900000490000440c40740300400094000d00b0003a0000040047c0010a820300314404c0c0c00f80881b6554990300b050895500002d080b02603007005000980c10740c00002e0360361000d04020f011a05254a03010300004031600701c1181e07100f0850000c03e0000007100481c1c441c10b44250b155a811000400d5600203461b20041e140001c2485800001302d0b0030030076142c11805c04141d4641790417000074040d0481e9850781481c0607054020030b141c400403481503445a811101400e0301038460920740720710b5109001180044c07a0040c4109582406443d40301e43c046074025000f4010100102010b0b010001d07001040c4510701c2002d0244542802003020000d00102e07404001102c609002940100504006206209103203c180c4d102c03203d2091800025010352205026035026149440381682d005d05000451301079003407a5a208030103000420030003a80800408d00b0030106a4920700002c42c82d50b40074040d40080d03800010020000c0f100802509201c00450340e6012139100070400c48094003805070040b00c2494 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 454548902 1250 454547652 454547693
    0x603093c0203070302040c1e021204030f1a0c0c0c01020705010c0b090c0310151a1c0f0c0c120305010b090f030c0a170601060c0c05010807020c0301060f05011407 71
    0x1080402995003d109150003990050b0003408038212006c00182813010141501a0611611401068081c4006440e03001c010760180b1051606046031a006100381c11848122038512120380c8111804001c440342e2030103189140c074400d0304c981e08504504d040c036a40540003411036004100400031030380e00a0150603e40e0300700e50000340c691102900d80d410043c0644102d80c06100e4810100304111355a803011510b00c0b01c410085090942b50810704440d4562041a035070050414020244411004280000b0618082e000050b41d41d02d0221f903a01030b5881c910000002c58041402d140034401a80034400015251349003c10856041503846c0625028404071540641c004c10126040d68808000d50240d880e0000d2200348182d5540c035000f0f030500d044030020710441c0640e03800010014040d500e5489460340c05400d41d411a81828011241d010300141910114440c2c10f11951180e00d00b0b00c94500600003100c141c202c00b80c1000d0001d4000d44050842a0b440c8600b0004100803655480f407000403103c040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 454550152 1250 454548902 454549013
    0x20a0b121e011206020d0603030e101422031509060606020105100315110d0605100f1b2906040c050a050304021c02030f010501090510030f1101030f0204060309 70
    0xd0034070900a0286e1a11900d200f13180140c01710505800c055150445042115a90708114035044115144510f6402c5050815018005151001400140b0b2000000d014490768070703941c0d40c0d0f00c6206c4000c0081c221030341c0260742d80d580e91050129600510015001ca80000c0c0503904002c961038401d02010702c4094142441c1f0b10850b80e400301d0503007000c3c80c140d8101110350748409021180c400107102c0d500ca803501c503007034043d81580224012101d84080b0702e016201e15140c800d0b10070841403c0040e2200403281d07006000c90341181c0300e401d542079050029801100018602e4100c09000846400c1c1c6c050800b03001c4240100c4817065841001c40313074001c1c0c0c1510700d100c070702071000641228440d070010002d516000d1441d07580c0b881c6005512040c12900d200b0014400b9440c0c180c02c00f600000c59001c09040c04084030402804120207000c480c880c02c006142c0001c0300d03d50a582c100403a0030981010b000240c481026009200700c07103450000024038413084003501ea0072103403445524441e1400c075440440c0035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 454551402 1250 454550152 454550189
    0x10309030210021b01240909030c020607030302070501140108070b160609121805090a230112151104061101090b130213050f0601030e0307020a0b121e01 67
    0x1e02265801c550080ca09544131200080c3d000d20700c0705410f241d90b0066181c0650000141407041400307803290703001d5000000043c1410300d1907010b401c000d0030a80c28082074019031001038440100a000060195800584865503484c10f54255a03600d040b01070b4503c01080140121140072561600700c454183c0c4d40344e40c440c40e1903480c0e041d158003808090400e0b813500034140c0a12202c9400746603014142c3d03403403018404a0780d145204482c268014541c1110494000902c403030308640c081440400307883d5030444a0118a00c080d1400c142c00d810000300c0d81c6038801081d080148400d4400102c00e041d000a02810000350b260380768034040e1744180c8081050148d10044030007000e50050341050f03041000043e103860035a441c50002030000e50704070300403071240110441000b00740c41494040d00c0c0d03805003000780340c035048011405000d401c6c0888a09000c10000c400043c0d5441325448014803104d04001d0300c03840d4140b40c4204900d401841d1814185060600607120300ca480701690544d40c41c05003a100d10f110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 454552652 1250 454551402 454551407
    0x40b09062202010c0203030c06160203040b1c0b0d0501020a0e1c030305040f0602030424150b0307030216061d0a050d0503040602120f091b031b180a0c081e0601030903 73
    0x10f413801c01039014003001656180e43c000c00320300f81c1e03c204002c4106c2c505044002804a03940c0c4194032980039103460a0040c0302103482001c24480400001c400d01040103005040015100d01c00ca40003128680c0d070003d502c60050703030410306001c00000708682c054050f01c0b060758610840060101d0040401d65504006010010b80000c15070780c0c140c006108544034545840e0182c041c9840c05000c101c08494044001c0b05641781c0e003c2e04049410000250b88100d1424048808680002c0e0402c07051640078810107210906c00742c100c030195406240c000c5545148580e8900b51a454040c40300321a030002030101c408101c0011f00c0d140c0034075840c6416941c079906c50230301da4028043c038961146120810000d03c0084503201007080e0180005505072040e800c0401d41c0000d0302e0811264441e0981c000010301480a8503e864138a4500c20250094104900e08040f5601c10507003100d204845a59a00c000c00940e80d0103043c60b9031180580d5400365103060790702152488404010111410507480f04e41c210308062 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 454553902 1250 454552652 454552667
    0x9090a03050306210f060114090103050a031202091513170d0c020102010920010216080714191806050303030421030b0a120b0f0c030c0a0509031005040b0906220201 72
    0x7440800e60300021030103017800e42c07030344000c0c4182c00d05002d0a01a00e017441c50040421030480394080c00030003560300517940070307100211410a00025140c2c00d00800609480c1d202030b10002c40c004200440c0c3e11100003d1201c0c6036038658000b1005a1507000110302c0c03c00c000902001700500d01e01341708a00c60254130040340544a580303c01888039400320900c070052040c03088203400c0e00a09800780c613005001c0710013003003408141e03104402140e4482002086808024008140c2550780031f000d00c03007104800701164070b001e42c40d43c0c00203281e40060300841170000b540b48101d401420003180036520b5418a900c88400441224504410500e02e40d0700d0030508900992052400c00e5002d041c1010445c0e8072441c0101e11201a08160381c44110980003c00001401440c140300314200e000041c21500c600e4000c0c044e40d0041c0402001b840030810200034555003c00c01c1214138200301d407000c5054034045c5064071603440090000c0c0c00e164001030505c101c103e01c00d841951210008500c0010804042c00101c1e43d21 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 454555152 1250 454553902 454553959
    0x5130b0d02030f0f15010c050f07082506090504050c090d081806070b07141c0501030212010506030a0822031505070c05031c0e030a09030209090a03050306 68
    0x1100044031124494141c000d14424880c0e0b400c48885941d6549100020920449140d8080d00842c0306000a80d809a00040e10880c0160f046601c13054509142518010843c0c2184210b0380c400444039110b46201d41d40c60303690030a040088190300c2d2400e1806810788003180201803145865100244080345403000f42c13280344030010910381c18201c442c108000301e035001383c45401d142c12007401c9184042c1044412600d6040e4032210b20b85496884101c00c81d28642e4401002040750800c100901c2022002b0310360300e01103111003500140a514510400c03c0444445c916959242d050008201d555036005c05d10603032007500007414a98a441041c0c1c000079011b035401c180030004000e040c011003800600c0c545130b0512103030032004000356101c0b0b0205a9083c142c4c0300c8002c02c254010091400d0711884495007040321900c204001c2640b0354065484c9045400104190b40001d030044002c02c2549040084180c004d11820701070440080c25840080c014400204214003c00072494140c003e42504030310315012 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 454556402 1250 454555152 454555169
    0x15030c0e0d150605120601120f3003091e02040f090501051005030114010b0a0c06050103030f080c09130b030c10080f010504180201030f0605090c070501050a0e030403030513 76
    0x281050b180801d04415000c00780107815251003008102400c080f07800380100e40185005041503880d00c0d681e01c0c04150308847c01c490f4101306409440000c5d85850700550310380d5003031389141c1c0c9060141040c3d03402c1c82d268281d078508050501c0c01d10740200d46540b6040c4901501074070b40c02e500d00418004078001d0401d803419100700d5840c100c681024000194403440c0514075400c0c0391041035a582d4100350903540b0002c1c1c000d0030241000010021221503000a0202d00d14900f0a0b404c5000140c44c4c00003210f07401d0388184c01060b8480940205280c0c800c42e46a8841c084213a4103080103110380c0461801380d03400c40403500c0d140d034486035220699410030012040c03160041c0040d80313814010320020404032003030303440c00e046030407000010070320345014000c14030000c400c13480451b040f41a680045001c1d1034401c80c80510140d55070000716842e100c03004045e10a00071085126039640007441c010b07003150700090191590314a401c5204034048408821101202c2d0549049a150709108001044c0031440c1e9009a94 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 454557652 1250 454556402 454556419
    0x603011401090f23030f120d060e012301080403080106051308102906072a0303020606030f06010506092e032009150a09090203180d020715030c0e 64
    0x61061020603d96400410143c0c4c1c00300340c1000d0710130b240d0380c0c209000302600180c000c1f0040c036803264541e6001d03044d640c102003000b04d281c036512000d0002e580c0003a00a03012030940b1031500018202c40402d507020042c02071074044643e03e0991002801c0c160103014040c100400010b0390310f28030604a010070003810303da034151000284072031b41c154010100c2c403000c0500745503920440c81107207500035284040d0701800341c2580e1500600d90303103902960074001c0450300d490030032515900c10a000e0102c900007540c03080d0000c16140c14070798200342c949400d803080200c00c0da01900061149840d9842520030034a0140c0e00c801446a0300075200c584034000030000040e4451941060030016030540040c42d446a80400d110390601500914018074490103400c1038000c400a0b00d0541c08008207002400c0320f8004d0f02d0240c11490b101d90081c005c2c0c0e44203942c196081c0b4000244200315031000c4c02034201c001c80c0c43c001815907030302c0c102c900c2c144a800708081a041c103035691640299203001d0030380c021095800410201 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 454558902 1250 454557652 454557659
    0x7030e031908060303040321030e0a11040b0d020d0f230c0a091b0c142a0423060117041211011104030605101a0a020f0c0603011401090f 60
    0x6161420038240c41e4009500341000ca0140d0902000f21416a50040d411610f0760750302c5500c012861070450400b41c101582c42a603d84030020078449040080d11609440300d02c6c111190800080d42d000800141c440d1814030100001030b66034421140f03078507a20842748401c590041c1840c0c1c07401c486100b440d01070720140f0b0000089552002c10030402d841e00459115000e42e4449040794100d8005107108540c0352450b0200c98982c074054548002c4491140040100c180d040302c0d00d40341811800081d0f90920900302007403103a1140d503401d03d41e0f280c0310700703560401c25070509440281803209070ba50540b1000ca8882d010542a920504189520b849640b020003498107080ca00500c1154291000300000f904494150b40c4a40060040302c0c1040400070f6943c0c14242907845801c024000a0408903405003c4040092600c40210280415502d0310401c1038507200d4000002c0d00304070590150003c1394016900800b00f079907542003980d0646115040300c562424480c0016a200c2c09150490030440303800d220b000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 454560152 1250 454558902 454558927
    0x14040f06050403120306030f0b0604200904110309070b0d0902030114160207080d1115090309010809070506270301050c0414010203090306040303050c1b07030b130c09020307030e03 79
    0x800440740b03d00c0080c06200134156080301113800c0d41c0002441e0341114203045021070588035649030444001000022060450740200000c400450107000103650702044000451800340f04070390045c014840c1551440c81c02e40c800c25214840741c06004000f0b41e021034810f40d14081a4000006030380c3c00380003006001441d5070b0850346000101d071840c00844000e003101e815640f000c28503104855440c402032400044480e0f080c1d4002020b000d010072103215006080b210100d0764090b490054414202441e900c400d50310005012000081a500096100034800c102540701c140840f150400c0800c81701e451640940109071075000451406036240d800c2505100c45e500154000348211043c0e41c4108014080d28030040ea02c0e40602c03501a54150050000240842c0c00b07a0403890784000d03001402e901e4211050180003a1541b43d4064000d1584115028410000c0741d081c115001400340d14035281061048c2d07584091401203005030217409802001055006001e500000480c910060640f61140d1144004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 454561402 1250 454560152 454560157
    0x5090105040b010902131403010207170c060709150e040603051605190b0d0902150307090608251d12010f241e180e070b180114040f0605 60
    0x141e402d41415800000e80c0c40311803080320320f080100842d0401a9260030480302141b4882c040007505550204001c03400988101c0400d00381c1044241d0207615060402c2c02c19282c108000c15040c10b0000c045400c1c4034030345500c05400c40000f414640f480c0306101b000c0100380941401e6000401902c01c85180150b410240d800280c1550000c0c1d500009010240c0a81c4a0440240c031030f80344140401c000e65804081d8503040101c0300c2d40041d01c8141400d003076000480403503008644100000d5411102070048543c450300254001185c205041f401c1c3d00000071441d02040710b0450103080c00016044110209074850b440f00e40c4041c001c15030181009c0b070000d042e028007194601201502d03c0d044030b00c4003d540e40c84000446890200b200a0442e0505550f40003031051020b0310055034012040010f2115030400024455494490010036101410010b0500e4a0740c00e4200c52000c1205020303c0d40b1a40d10600c0542c0410301c01d00c2c15a10403040d070b4044028034461a0400c0d43e80c0c1e80082000714405400000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 454562652 1250 454561402 454561411
    0x14a010c0e0102010b010c080313020604030f11041a010305090c0907030905010b0a0608060d0809060f090909211605070602010b0108010915060309150e07062607050c070905090105 79
    0x4400031030540c1c1a004a08907410b50440314041441170b60702d48040b600c5140699400b41554076480c035480660713000509107800550089540040c0502c05c0010007040d00003100c124401582c1c05d100350071444841c9400f035407000d901c943c10156901c00080302e440d020840c2000c1d40001819000040c1401b1900a0207098581d4050750300e0342c00c1c10b0805016040c404540c004980051b500c0a81507290310041210714000f203601543c045a0038403d03d4426500d401c000c1042128188101d5590032090040c40110702008000d09810f402c817043c00d0403000300307446a2003480c0d0340a5100550355051440d103411080090310b0b020b0018070801202103212a0151b010080d0b008007601d5407101c5a90b210a40020394402000c0f031000c1c0c1e481c01034100081c90181e004611854400d48a99651303061038107081003154000c120210303481d400098100060358020f002c401510a9a04e000700070200380200030510000d02400107410041c00248540340c4a801740b1034400034220500b01031082d418104400c0d80644010341d03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 454563902 1250 454562652 454562657
    0x7060c05040617100b0714070605030a0501121a0601090b0c0d0e090c071101090902030a050a050a02070803130f0506040305090901060516030311090402040306060e09014a010c 77
    0x218a003850500820301600c00d284d00408414090b00300800c20841e604040e500302c0c4c19000c100700c1414200d20601205014045aa4030981c4a02c3c099056509075481a80080369043d80c0e82d042801113405540c100407280240c5054083d240c03100030040ba00c03540c4c654000608050007140d00e213044500810041510503165a9041820703440d40c0401080d039806440103e480c03901000104000307201003000070940441410b0501655a41e1a48a01683c0c070885024210319506d808001000129100d0a500285114000c50031b0818541d200c299611010380071a962264040303d94003008022801d20b007540313610009032000c41c20945800b40c039a80103098020b210b414464004a421481202520000802c0c01014000742c0340d02c1d14190010031074002d80d042c0041c0108552103072501c030307400100020b41c0304000000e03000385000e5030b1844ac0540a4011181c0d070341803609030302d51400b04810300300c54a001e243c42001c0b045494407011151031000030140d221070030340d030040c9604031006600c1000c3c02c90864 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 454565152 1250 454563902 454563917
    0xa09110c06090106060c06150f15120c050f090301020403300c0b010306050a110a09260a080d0e240f0907151202040305160b040b04030209040807060c050406 69
    0xb02060030f851080c0201c000050603000d000000c00e000707030443c16040b443d00d11081382460f142c440f0321202d05240d4001120100c07501e0b0a040f421a0310500140c2030300c046081c10010f126503070000410510074219a031502e01404034025100351f90a5041b40d00030b5500c22030903020803000130300c1d07007404180252030500c0741c0b000c03103001e4135400740182075059450b42c2c0440426220382c01d42d03403040001c2001034880d00a0320790750100703080304452803401800c00c9945030700c0341d4403540d280c00c11550480301c00c413000e03c10302c50030715080054031a00011420500c0d54040b402e030340c4429400d40340c0c20042201c901c040d40f80d4420403640049200000120400204182e40c041d4203540d549a1003c09880082d40e5500785503000c02c0d03080208002d0001d5001d4944c0705490701e201c5803a403030003210041c1d0f04190001c1e0345036001400360300352080d44900542d000304035007804103051600d01203050320f8a000d1848068002c00e580c0300000d003041085002c58104942c0102d0400c864000343d640146150054003441d130208449 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 454566402 1250 454565152 454565161
    0x5041a0108030406122d150501210e160b0d0e0d0c1b1a03011401260604140a050702010b030a0209060f01050f0d091209060804020f0a09110c06 63
    0x1c012142075138580d4079010400b484070708031400200001c01041403d0f0790f68410210541c200c081310511079800c130142c00700d0480405d0403803485820003030388a5410b122211280300b0b83c140030607604503210708104d1f40010348600b14101003414601c0710100c500b1000d17444480861a800b030385014246009142a0811200e00c0c001b07201ca95035855070030080003060085e85028002100f00160300e0224105045102405a0702c5401c0c00e0311101c0403040d4100701c1d10110061080750000c00c42501030900920388125424480103001c2e03038000b448003401c190306040c0f500168407611103802071070144007004400f02036460700d034070038900504042d02d803003006500b042c1000d0402d03d400107800d80c207075400400c40482a1540c104120584001d018034605025040c41002d02110000001d4421031181e2003001c5294402e91400f0000582d9010303d142c00d10100c0681444035030343c44a40e0541c80f5034141e810400356249980010240621903104070040c504040d4050b0902400798045c11040d14841c1c1180c03030307a41b00e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 454567652 1250 454566402 454566419
    0xa0f150501030b040f02060405060c0a050114010302210316030c0606170c06090d020a030c0e01060f0e12120d09140c0105031612090b07020d0905060d0903020705030105041a01 77
    0x802e02c400340c03e0702e07203c0f40498003154007004040ca0f0107100500071854039aa60002c6411030308100360500381c6800c0498080c081c400d0138001c1d420a461910303000342280d0704540c00181d5444441c8490401c82d0424451111100d000700b040340c1c41c08110041d0180030394030078036000b004c0c0072826000b00d485900700100000c00b00c8007905460080c443c03810180c02001001400e201d900d03080003c14960000c40041458056101d42e403044000d5801202e8025074141041d16540f40750704180e10800802c4601800241130551016090314030000484990710710080100300185040d450100e140d409600000d42029002060790010007038034400d4600315290349013842042d441e401c00001d101e02007074040000512941001c3c0c40500000d4140c1800a43c1d82401c1c0704081c100c0d00d0301c10044901c1808001071100c016010007072160031207442c0c80c0a485860908002c1070550051040c0d50494645882c10101050700a2181c640a014094001c0000d45014100031000c118a100d40d00006458903002280454 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 454568902 1250 454567652 454567661
    0x3d0312030b10050f0a0507020a03050607020f06041a040812090304050a170706030b0d050105042f030c010e03101514010503040f02060f0910031407021b0d0c080a0f15 73
    0x40b4161102d5040290000c0845040d6000d01403200801604100000040c0e942c0c401c06d501a5004034024500d528149030003074540f100310008025a98802c104210003e1313103d108198100e084105600b10580b02c91401e10344900a0100d5188103070544010840c0394a400800380c8211a0200e80700b4501c5580c480a01c0b5030030301482c621030039070741103d0410300a060090708902801c1ca0701a00102d80c160440c1c486c1e508441050780c04603400195480c21640911070702e00c20f903c2607007600c0742c080e01c080384074000650789502c0c0c18202418070160041c4541f65580910081240d4685c0c0a0140702c014895007000311412010b00070759401801c0c00c4011885944140300f560f108036400740392034102140c00c0d02085151381008006507001007080003200141d40b07030715285200f2805c441c1c5000c6905a83d814144600b008001c143c0e4085503ca5202d9121480c0703090b031800d142e4481a0f0f40e000301135646042000b01d070025500b1a5565104014841081103440584035078024001c0201c04004e411003081c45041c0c6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 454570152 1250 454568902 454568929
    0x201090f08030d110705100c0e040506031e01110c010b121c032a08040c09110a08151008011d07084512033d0312030b 52
    0x207500903c08a100e40b615036020038400102c2a090905240d003d546aa25040300c910122200d03a4480c03501c234443d240c100c000701005440442e170500162134041e0110b907035100f0000b00b80203120040d5003d40704c0d90000390302000c1d00201111600703540d01e4211170340a004e0180c1082c0c050007034000000c0808034000106601c0c10048450108038407107401048110b01424585a444401c0e0160750140c40f00c45c60b000035800190001501c8141e018134290a00c0d181c41e4000740d0000724228140490703000c002e01d40c9412100d4007050380c10901000c1d01c0344880001506100f03003000750807480c1240103014558101040c28100c1d00041c6400d80c3c000c014290307a036900e40c804d640703000100b5000d00101e0100300e80076200c1010150501030007103600360743c1440712001c0d10442c2140b05104440c003030640c0f4943c100303201d01c1c2e00320701007954924a1070030b00b000c0007207903110000560303519165040492042c4081c0425103e80101c240305407541110740300d082c03071708500e2400d8400b100401d16003000104103007030410700c4113003c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 454571402 1250 454570152 454570169
    0x402090117072304050a0b091f08030a0203030910150b07050a0501060e0907090e0d1b05061f06020a0f03210615021908180402160f0201090f 62
    0x803a440c0409039064040d031001d10007030354015007401041d402c4038a4054030300702005400d05000c02e1458400d1004660f009420040050700b0004009040d0300c03000102030300a0103401c0032840e085918000000e150395aa000344901d4040080c4109032154000051402000441c3c1556481203031a0b01d51400c40700714485e54645400304480400c80b5094100151494500410036a074104080383e035000d084441d10380080c841040e064051000c0881d040000030086c00f1581001c0000e2200c819511380e641c0341a1680d20b003001203068403c0c511546c2000c0070310302584d10000f15540303814003502000050a139110f5400c10321588050005081e48001400d810098001c506461001c016031001c89002d103949171001003030590f40307200e5403220403207100301401040b015480c002e041d004c11800038244074410002d80258100c902001700407840903402c5400604d4950301182a1601c2007001c1800fa006601c50300c0c9100708070168180610030070290b0841204c1c400d981e024104d07500da509908041159001b0b1a61 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 454572652 1250 454571402 454571419
    0x50f012301032301021207021e030301090c0c0f0602071a0705070209060a170708070602030f1b070b070b090c100e01030e150c12061f031e0219080f0402 67
    0x8103071032030014005040f2880c0400f45215840c21042c0c04c3e41d11020f040082107245404214129a06000b40c0860386610f10202040c9620110900d0740c3e4001070103080c2205030344400c102440f40c001d04008004682c0300f50398404d200f202d070900d0380003500103460959000030001100071178800d88008092007004651109401e091450702806501c510041110b90800c2c404803000c40c0c8101500509241e0b8034408001b8428541040d80c03d508149103540036800355031040c0310b0040c07a04007807401c0d00d003c09101c5507203001d48004c03103940500e0800160321202c841d0380b00140070001d0012403007680384030f10042000c55400010076002e01441d115102e4a84d00000e0754180349403c2c0d5032003904004031000340002100d041c04100c0d180c85032690419192a1190a00002c00c24680c40e003042c038403580f1580480d011500d09c0702c001d003c0310041d8040b1030131500b010360300c00c061480001a902000483c07030303401c42d0440d100e02d94072100445ea14542403216000c40c0c000c800240340d90030402003041c40380b0307400342840d071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 454573902 1250 454572652 454572659
    0x90304090e0106051c030903050f030d0b0603150607030302040905161806120f060312020a1412030403051b0a0311011a0d0b090709050403020703020108060108060a0b030c070609050f012301 83
    0x2105c14494120407020040d0b04000000481c10400c822680d03025984082c5a95070440128401140d0340e96115a00405061003004603588548142d41c210001c250350403507503188245801c4000344500d4100c8000146080c040c01950300c410200a0f10501d079549500f0411100b03000122520b150910500380010800c1c0300074060858250403800d50010600c8020074010389070b94400418500d501794501c0160b1120008d0010702128010302c030300c0c10307030307008042c0c030b421a02da0621400303078400100085c052010008402d50040060324460f120b81010b0300648004940614ac000c00100503204401d00e25805c100e402e03000c11442c80d0441e0200040100352240355443c0341c0d00c95201a01c0100000d01e1402002da002403071016601480d403107240f1aa000e420060305501c000350003d00041c1510b4104030085081100a407243c0000d034050f1a18014955160b644801114425206161000304034a041414100030000001b4100040c00001e00080c0200c60340720008008545500f42800301c1032003181c0040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 454575152 1250 454573902 454573939
    0x190c0c0b2805040f090506010813030203070201181d060108070f02071401170a1e06060806091b13030b0109020f12060604030c03050c0108060405092d0105090304090e010605 76
    0x1d446252550500c41d00b055a1001c903100d41300d54541c44a00b4141d212810400c0d19a03005100a52003001c8040d041200f142d01d4800950b680280e103c020f05020b11002c8007074000c10302d042000f008080c0194084a05442c080c1d902e42d5200061340c1c6030340411040c201180e815801041440d030303010303016401810210f1500400f074a4103070241c01300c82e051200c6140400d441030f060f071110500c50700d00004003041e41103002040895080510081d04c6140b880c0c08014000f0359402040c564110204072045512510784129045140004800c040485940051400408080010701e603003100e0140404014a81e0f843c1046002d03441034261100c500d1a0400110840020010020360040340142095041a403aa5035045c0b2010b01500300b0340300c41c0e00034000c40038150b80c403410140e4800e405440511650900e002c0d1140d41c0d10003c4042500c003940d103038881a503100204d8000407501e290034000e00841c01c2841515451398414014844201e040c00e40088020034140140d2088401c080c0c40c3d065402c0310306910 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 454576402 1250 454575152 454575217
    0x1107050f060313060c0c050c0906090c1b07170c09100e040503130611160515090409020d0609140c03060c0a02030705010c03050601020c0a1415190c0c0b 67
    0xd9078501c015160b0743c00118415100f0341825002c01d40324114040800c0c14550320301074035070814921803580f80c0e0410940340c81c0c0a105581158920008607214000c00d041d08822000c0e9441405041c4a485130000d141021b0749485454019440f0903140510b401ca014099886000c6071203658001c0103000c104080c004036030f103160b40180102c0903603081986045503401d022005034011000142141c1c030700880440306000644940d040c1c000c080015a180102281c2c1c40314103000c80d0705803141c001c40c8a000c5500d99400c24201d8035801420b11500450624280c00140100e0038181d96000d040002c0d429440400504ca5540c144000d000b4506951769840002d4264003505440381140010311038100020024020914441c03229107000c075607890322000091030215594003007131080c01318080c1081154241d85161440680075074a00b07a11604c1400ea100c003034030a200d440c890790302100700042c10b01e035800745050140be445420080d005d45e5030364aa407100c50159000d0f0900d142c02c25001818540313100b508 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 454577652 1250 454576402 454576411
    0xa0507090b03160e18090a0c090b1f050706050408040312050c06060613081e0f031c05100b130602060f04080901210c03020309120f040603020f04050a0909031107050f0603 75
    0x11141791390414181c0714500b40041d1001000750348500214001c21801c1c10041c805090103000c1000100b003200001814281c3c001e5441c1d6007071510403a0184018441c000f11440c1c550003800c18403482c1040e1421000d0b03940103200507210f00c1c0380755040d03003140c5210f803007241e241c2d10526005244a884080802980e5403007500900c44c46112039000180e0000f0901001100e2131400c040c0016004ca5003500701d0404171044605059034004000b1000100503584c1d001000014802c40080d990b0703140d83c1c40c0c50714000d50345c0250340d5154000c18031141d2807000e0310402090f1280c0c0d41c01c2d42c1f400e49035030000c56400b001c280c2d00140b40050500200c41c503544242c01000c2070074010744444403500c515810150403940c107000c0703690010340c002040003000181000440b84400200c0d00d1240707480310f03180e52090300d4000c83c0a00010103030001455400104184140c4002d8400100020b0101da9610b0288009065001003140896042c8040085400700410780c2d1044a10180c071001440e42d05408221140e44010f0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 454578902 1250 454577652 454577659
    0x9060e0103150b0904060b10030b100c05010e0a050d11010203040b060607060906110909060603060130020f09100c3215010e09010501031502030a140a0507090b03160e 73
    0x1000c0032081e0340e80703038001c5e00a500070070740025450701d00014000a03104001d00072081c50f0030310620009580b40c076030f0480c0c0d07510190714000c41c0039801441c0080c094000c0700f5a5880500c01e0040840900002280d5091601007a0311036000001c0040e0a10b4280d0004440207451100140c0000710141030400042c0921445600c00280a010329a10001151186501e40e610031001103001d6a00707007811801107070031800c204da1036800c40c504400000c29580d5008001c906009000404803100003000c08402d81201401340b065444506100d6482481e41081031082e10030505401445060350080040d10b842a40042c4c1d0719400724a003a40412402c9900b501c0c02c422a013045070001032800c001c1c050480b950000b10300f54451940340030900792000202621580b142c1c1d2510004100040d41100006400850118050303180e81e241409040280b09e81079250003200103850130030050f0340182d80320a2080c2d03442d031207102e81ca5884551142c03a80c0411070350102850318008800c0d4025025403214228658000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 454580152 1250 454578902 454578911
    0x60d060f0e0a11030106080a050c10231213020a2304060f0905011a030f1806040c051e130f021603050c0d0302160b0c0409060803040f09060e010315 65
    0x10030007189030110051050f19107044100c84400703285800e0150354002c10100d0010701420619884090700d842c410319105219510b003010f584040c0b4040c1481100200480d24950301a100b1310141c10201d0340600040044144401c0001c3e0400e58104150003506070040c09280f40d55081c0202e2040c041d2900255139203110600ca59801c031541c4600861019210043d04032540c02c0c607050003503007500d60680210300601858881c40d040040200c05503688440142c1d4103140c00d484107541c00d9040080000090b2460003141c2c00c01c420300c88040b5240048a01c141d4002c26242503901c0c40041c1d5418010f00150b011034a03294140004440340c00102c0382001c161801440c2400e0384250413040f24442c10120041140840c81006a84040c40741020075000c83c1410343c505800d80041d11146040e030407004180305103403008103004a00e1481680c014008510041000684803042203940b50428031130014a942c05410103d42c02c47c0b180100c004590307080c00d1820482e400c1d542d07180e554442c60022940b030705655 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 454581402 1250 454580152 454580171
    0x80610030e3408030403060608010501210f060e01020337050c0405030307050609060a050c07060e1606021506060406091802120403030c110f1b011205041208010608060d060f 76
    0xb510400200800c00007903503168a140307005030646c1d41c1c944c81802030ba4034000c0100110303010320031850304490480c03002c0c108208a0b490106054601039002510441ca0040160891001540190301411042e034554100d01c02192142002c000c0501080d00f03016040100309503840b200350807143d00305901140b0035052989820100f807460f040300700150740540c481000c0c08100403081c4030041c0c010b0043c007400d00070f9203031250b07285607144607189001b03100300e50350070100c59880424401c40c00c6005103401011481c1d996000000e5990b00c1104001c01e240034004082201032800303100311400c4803003540390146800e26012210319080580d410443d07205800300300200c90511702c603840a12030340c80703601c00141c1d25226280c0246069190521400c5d03992000b4030030881d0440000f10800301060803440d6045d8440b20100480e04441010150032007241850144010031503500d0341c600b02c0c0003032035a422510707a903621401c8035074607019a000343c3c1040c400203284020030385c40d801c050250980e08074045400b000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 454582652 1250 454581402 454581493
    0xd05151018062d08061e0a0b010e0906010c020a080f0d03090b2e03030207090f020c0c101112030403390624050301060503030c06220b0106080610030e 66
    0x404881c403c03208640c1b4142c0c40c1d403d00243c0113550b040304000b1820040d0b1010140060301c0360506404e007602c00c01601000130402c0c1e226602004d0745a80c0a0a280141d554403548a951a0554a15800d43e8040c2c2c04081904610134460303c0004c07500942950a00d49034203c41340070341d0126410803016641c01841c2c1c82c0c0c0700c1700d907400c01e04021803181d4000e1003940d281c4030058040350340900c0c14000d41c9004108007010000d0015002d00855005c55505050b051095800e440c501c1504011403114000e002c80000044000405940315074025161801d140220740034a6210f20003041c04121070900c50341c0038140041c1e1201e0007a64041c0b082078000b4000c00611049201c00d0040344240c440400300c80305c140001d003428007072113004250990003181410814941d440c4c498000401c40007048841641410302d55038406003404038141c0285140d9400c1d41c407100010907801c0d080340c1c1c240c02100b140d03600711991031182c17207028861010000034200b14074104103000310807421454010600700b07040400035640f04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 454583902 1250 454582652 454582663
    0x70918020607031e0915051c0c020f16030b0f0417160606120c270f020405040c05041712030f15040501080c1201020c0a020d05151018062d08 62
    0x413919100d8030700d600e01d095031101a4014100b0f840c000c0000031b1140b0791007175a1415400f0003520310243c1c045052400d48104030300d0050202245289481007440246046001c0342c00407003a02d0181481100d02d60720100203000c0080d09845c0148640007420340c5041407148030780500032007510501c2c085014600c50301d40b6000d5030441d4000d00c13030424640d000c0e0401c20410050502c01003c1008030b29007030350315103e01d550541080700c100081c03140e11a00c80350404c1c2d0107541214040d100040c002c1103802021140102107400074001d0f02c0000c1020703900c6605203100040c01c00765065180440a255542ea03101d040c2c50703030700d01901c41110305101808152842d81e403809064040c0101c40c004140c0700e001c620800c0386031006075210803e682d03c108130205503010081078071a240c580640b69080c0400041c82c1062928103010100140095074602348400740d85521111070032a41d50f101002400201e500c2c66800f2501140300d24810301419403940c1000c01050701c20016000080f0310607603102c0360b80754011410007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 454585152 1250 454583902 454583957
    0x5090403021630021e030f070f0510050903060402041e0f0203070e0607051c091d0403030c0302030f0105040b1c0503070209100806011a190c0507091802060703 70
    0xe184070010b07094824502d400303071001d083c000060746444005401140076040100f040b80e92000c2c50b1901d40e000c6440c00c0049084912040c0300f15268660383e004500310644990040d580b04040a01094150301c0c8a10242c41d0700d480004e01034803458540e5400c0000501c0301c080c258107400140c1c0d50030080e126140c814642c00c2e540c54103000d41c1d24940700360010003015015941c6449190700780700e100c1c04100c0002e001408108102d4803100e2080b808001581c104642d9404041502d5010442c1d03d000281c0070440d6016500c0ba40303042c00300105012040d801d03400122038001480a08400411540c60030350000f0140d02e20203040c0d460ba0a64446040203089540c1c00d00f507445500c00140ca4086040080300b42c1c1e40600420181a0310307504200019880704810312900c02a451810042c40e0b22540000484105100c0041c00040000c030380c3c48083c1081e2044041521903000b50a40051007429601038907820026400310008903400a908000c6560040755080d000c0101074200c214441c40d44000e807040d403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 454586402 1250 454585152 454585169
    0x80a0801050306010b07051f110301080705030601050a031e03050c0a050714040b01020316050316030f0201050a0501080d050d0b040212160306050f0f1519030b0307030c050904030216 80
    0x541c108800d0514150301a4056240b19070108003910100380042203000c0c91146071140588000d00c90401c0742c026254104000e080b200d4004000030b103440001510348121f580c140c094a01030b81e61030080165041980c800608070b0710b10000e02c40c01d9031200c050061102407080c2000f9051104015025103000c98001081b12694014102403082084a401f02d081d2900104c0e0103002e0100102d00003500d03030280301113483c1c40c0a1007804240801038240305403440c100c151523614201c00450f0800405c80d4008403003c0c005946030030007113000000e090140d5416a04001c00400c0c41e81040c0004591a80c024a002c1d0843ca80e13548041c44a50342d0b6000804001c10114006016402c00d0100c0a07054100c580b50b42041c1860008100190740701c1984005a501c0c0445800080f1200400850441811483d02013030303600e80002c190800e0b8400160002900d240c40c3c2e4100602c01c40c10302032660310f40326400b02030034200440800704240d26102c00aa03034071138820710548003001506c0400154421040e0400d010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 454587652 1250 454586402 454586417
    0x180e0327032508060901090c121511030f0a1a0d020324090d0804110607080c010f020a03060e010e010510050f040906180c0e041d100f2d18080a 63
    0x2900f03200300111030300841101c0080010709281c3c0c1e10361429858904c103078002c0301804107012052001001c03401c0c00c030703150000e0184200802441d08030665403041700c902c001441c0013404980c2e220030600c51011a96500038001018510700c5080040303008503150b00300d0b130522610b055a0070900c400c3d46d02d80d0001400940d041068144000f0090504c001c41211400b009030507020440880c000400c0d07074100403c141c9065036511080d040c6401d49215101021840d0b41c20801404100310312039004014002050b0b500300700183d00e4580304a56a9402c5c0300b42c029074410a00140028a41008980c0b05940c1e282005403030110b0010940006400c01e03404980100e0396107008002e010000701d5003403000000303140104401c00d01181c2c003031312078102e8201c000c0c00741c1e03981c0b850707440c10280105040d4031040404007190307042e0f00303520192009819800a103649890400c0304540c000d0202240c2000f41c81114854540f000924060035001030103210800403a19111514140214010200420503a00e8958400f00c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 454588902 1250 454587652 454587659
    0x210b060c033705040605030406090b07120b0f011403090a0f050a030f08160c111503010305010b0d0b040605090111030c0c0607050c03070803060f040204180e03270325 73
    0x285071494002c04a0220224444005031680700c01150290f5001d0b0406c162a5152030030100002e142c03d01006107007002038010300410607000b0f0840c6240b0301540b501800b180320604c06100b001604506010702050310340151b5041008910051a405103440d81110344250b0239071211461080850004c2e41d45812030400c0c403040c1607110054903042d11031424519010308140c241d04d5988060718600c2d60811160f10b4821081000c04411103281190051400c1c0f6250440000808035038000e1000301c45562810302103880b6404d14054000302550400a0380c0c0041d503860711008040c00300141a20565540c94941018401425000d10f004a00e1542e80c0d079101c5103070903c4d0038034203c405813202d17003841824400d40c101280000b08990200e980591401c0e2a602e403080170520760b0441c0d24003582d0250020401041c1c0030241002c000304101565030502c01c01004111181d12846000da1061210503d003010341680020760f021650840009000c031411101507601026070042c3d1030031054200300c040c10302007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 454590152 1250 454588902 454588957
    0xc0f1b0e0a0204030b010509061906030b1c1113020c0d1106060a05030d14090a08010b090f010b03041101170a0c1106011203110708030c03090907210b060c03 69
    0x116404003200808528040c04e541324494a40d005224a070302c51080440011095101e100c0806901000b20034807080481d150b410203400303400c00384510340c020350280c4e4088c0300344c0303000415864020350004181c03040020f8000a204c2c41c01c00f40e13080104c0091b020000c0000460007005010003000042d03075003510100101e4001410701d04090071442c4200980c05041c407181d41e01091800c41071445080c07209003c68038003140d403040e010b09852284c4c04100150300007848801034106100928040b20350300000e541c2e402142403503130750038010a003e110342440007500190785441d21203e01c0505052040e001d24112828211850044580b00c1190f0788a000c0030101071340101c1507242646c03c3e8005004158100300f00220000340c50034000d02009410704d00306006c40c2c01842400003501300c070825a561100ca04401594030340c0080d0400d4000e0100800040f04280324120100104140c40000069003241c440f00501801c1c02203181c030b80c42201080540034450040004008940c2c89600054800c4560080f4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 454591402 1250 454590152 454590179
    0x171018140a111b031b0102030f01090b0102010b0a1509080d0f18030203030310030c0f0501051611151207110c0111010b0d11030c2710032a05030f0c010c0f1b 69
    0x5405d203138018030521105061080d10701f415a03480060006c1e041001c180100c4c05401000003a0b03030008003100001c01c2011070008000032840351b9440d03400003140d44446080c0e441d0781180301d08000038195074040f80b145214500b9030740050005801c1c2e17600c3c00d4480d0006800c2d58804c2d0b500181084500c00300704108802510624001d01902c1c1c00c60900e41d1400f0000b030f0451051041103650443d00700c03c84410405460106409100094440c00a182102c0300311409239020005150020308240005804944110702002c09491502e018202807101d880065805a205c1011022503548036841d901903070300c41c100c2c808000390003803003500f4101441c40d081c142450740301c260070390013800800321000107030f841169030501b09082142042c0590b6198082c13a00086500e030001000c00000c030b241e10039035242000b1070342505841c410f208003060382e45808040d030321983c20004000e250050341100c03450350b0040d0b0301d90510341e004900020f00ba5155544400b0b41d080915640711511b00d000381b00703110360040f4640 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 454592652 1250 454591402 454591447
    0x308040608090f030a0e0f19080604031e050d0207061409071d0601170703060815070810050a0b0903160b1e0412060507171018140a111b03 61
    0x4d98680900c401000302500d2420380a203000b810703d47d594504548507600052400d14640f100911001c1e116034507642c40780ca040d2010340004541d40e40e0124010021001c80c940050b280d2076103858110010000006908004030585000e90b586c1c41420b01c02101c65151031241c03901078051b0280303a05060100c04551041d00b980403044a82904029603079800080f102410424003c59100a5403900c0c0204d01406c40c0780c211b8103d40c02005903920804400040300c500800064541041507a510101456004224450301d40e00c001d2000e4100481c503003d5000b4440100f025094900c401d138000701c40e001106403540400c01c1d8200004c1c0c000c03140b41042440300c083d48074551015203010301c0c1070741004800180040207801603640710041628540030304881c01d80c0400004e1440c42134541134580306e80380c80c12407003000c08800304a030175500c0b0498144590443e4200c07025070307011704c0e89590000b00010b005c8942e040341c8172030003042440c1c5402003600007286400c5016008541d1008065080013680c1a0481c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 454593902 1250 454592652 454592683
    0x3091801090608011401030201270b040911070b0408131710050907060e09060402070b270f031617040b030a150b070b0721051806010302030a0318030804060809 70
    0x25030380c0407180d17180e100e41180d40903e45015849a03103406807900380500302c2c072407101102ea4600020240c0d200d1001d403003100c5003002d081200000d0403d0018540c820710720b000384205020000107000075410001340100131002d04950340c440340c0395580080d0314a00c81d07490301da182c2e111b41010701c00311482e4021a0360101c480e00150100c035140070009084100a44009885460300b0070000b0403588695040e619000c0e00700d80000c880f41885240d1a038080011601000d2519040c2801215a2800680510b208510b00c0056160204040e17040520145698040381c00c5070300d012481c012071001c2c01c0900b01034a00c504138540d0300c2c248804070104480740c2c80b03203041d81e0210500c01041074516100c241e40e121034203c1100c1e485c50341c82d08001c0301c422040c88100d0307180a001000c610101c1245034003180c800c0ca5424280305a0908220866599240900c0020341c15401100800c0009220f0301e0340001640c0d0020100841c079460342d5542005400075000b00c4002103e5a0805c448003070704015030b550000e00c20307 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 454595152 1250 454593902 454593911
    0x81e0f0c03030a05070305191206080d090b0f0f03090d030513021005030a060f090c0801360e010f0e0c0109030b0a0207020d120302070213021c0c020309180109060801 73
    0x10220342c40c0c0c00303402220414014045480340526010720b04480901d070082030403124400c0d86440182c60300400000181c01d030342c9420345c00308160394001510f2291541685600c503000e403a05400030320b5540200c800c084208818850b1a0751002101c000d58015424600a018064603003400117003203a0300213201c10600605400b0351005600c80a01d81030070320a041c07620303603600e513204402030010700980e900c80003080b0701e10b000001c0d541860b9400810000c0c0c00ba960035200340d0340c40d002c8182c44540f5617090405040c80d18a48208a800c0d004900c210b080e0400c0085050254080c00300d007154106070710b020a8603203038880240b024109000315013541c5001d00701000c1c1c1c141103407602891503d00410b90f4804981c0000c60740213540e5058042101540d1100c6e0b600c06070403a50100601940020342c04074007840030248a070b92009817500170783d0040c011010041c40000c003142d08107009001010081c006500003040066102e0f181ca503200441c1c0851031101002c2075140201c400103c5100e0b0384041d460b42d150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 454596402 1250 454595152 454595173
    0x903110d02061312020109050f060a0c111c0c0605010b0717030f01090e031b25060827060a06030311030a091e080601080d2019050304081e0f 62
    0x10b06641003440c2d604608201305800c1000420390040a80b5400540315116040c443c1c4201580040c40504c075070045a030502082d06801000d8038203e05218a038885a04008420400461030301c0300600d8440b628030740307007008403610b840364003c448080c0c001000c0680001100001d2006108150001c1e00d1506101e42c81e601d040e410f0041189030601800c0603964941e11131031030903441001a5481030381401040c2c603081c0b413244001a612860025900000c448108221100e0419002d000089443c0c42d11005060341d01c00d40d4000a07462480000021881c200641180300d03079081141a10a10760003000185240c20b500b0301030002d039806842110b1550080120610160384100d40400b00d034480b140c000c044c900c2d919801c098905070340d080400c85214000001480c0304000440707a031041c0c070704d4982d4044103501400381005140511010315103680800155044c070703031200087d80c000c2030180c2d0641c0e040584615210741031407482034a82803046032110003200420001d1002079265000b510050040807007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 454597652 1250 454596402 454596421
    0x1b0c0411071104110f0c010905061006020607030b22090515150f060f16120c030f051c020a020d1205040506060d0c050d0b0a0c0e0622090903110d0206 66
    0x803070a00780c5002e43c1d1540703813864a014942003501d03503100015113100d48803071a40c0e42840c000e010400080d01c65104802c042040e20188543e0b00059903120b50150190341d846e01d0003a000792295450564002e1041440031184018500c000d07100c41d2400080428021502e04000380f9203040c09080041640e12002800b031480218070584500b18000e072131600b0780400340d2000070000d0040e04640300240d07400165030410715064420280300e00340318582e1645410200401210250513070f00008004c07502c903000300b8070001e0081001e410540d508082150413010b080c0034443c01d98110045c4800580d00942c021460140c0108028090000c03040302001107180584039196108030140095001d240403600d414284580c400094028100140903002842c0c01817500c1585414200c3d5040c100c01d01d000384e0901414400c55242c510302e030008004504100d03000c0011040071205406c01c0c0c0440711803040010303100c801401030b4048a4007a8503032440411781c4c0f040036400c00e51119014400c5404c5002004100c55 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 454598902 1250 454597652 454597673
    0x30f041d0603100b0f04051008071a030f0c0d0c02011d01181e0b0f01140102010c0806090a02041e080d08010b07030311090402070609060b0f09010e0703021b0c041107 73
    0x503000d01c030102d5040000404034242662010441b0341003070401080003110310144d41000100c4291070202d820701c640d2240c240245080481004100700c0c03003000440c03504240e0003412034201450300d441601c2d1002841503d41121031306c03860000540d44540d0ba102d01c0026030038150700c842c0c0f44407001b80b01480c840c049400b04882c0a0030010102380d4a480c007a60460159200415600d42c04613035a0443e0900840648000c0f0091003245a080c1c40c089a15046510600464100c8040c5403229000364955108200c50780000400c0304080303d90900c0002000c3c44c440e5407000300040c00e000c000003403604283e05242010031030326500043c80300c0100100000690402100c000b03540501d000690542c080b258003039a84a0f11403201c0d401800821110107100150344648021842014104200505101031200019800ca441170340543c1500041090800c0c81041c40c1e8082e109180062400d1000391040b00450070b44400010f10303520038141d03250941028807408a5001c03005c1d44090500b891580c6509845 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 454600152 1250 454598902 454598923
    0xc171e06130c0c020a0f031a2205060a050a060308070b06120a060b0a05060705191506030605060a080609030a05070503070f0f1506150c031418040f0504111908030f041d0603 76
    0x8d05000a480ca100000d203c044a242c1c910092180f4802e9042659590f402034580b41c89462030140803500c07990081c071881c001c130781c2e22031300e0581001c0d1140c58842c0590401030245812103103d00006010722800c3c040080003e11481002a4409000085c080d90080075040207015920070007521011074000111140c00c00551000e0095038082841d200c012045044813045070031b810300d0000300070404103400035482010165058002c091781d4501003652000c045d10b07840c0b81a0810409078142a1156004003a8240500116450000c3c02c0d6603101c40603a17812000e0b0313041c104180c4084c0801c500c41c118442002d0ba603007011b001581c2040d010611085401079074005000c01d03c28403000301401484404116a03000404030b48a020151010704200341100c0d0003882a0301e4000340786800b04c07492040c00d02483c0c001c90302583c1c1007100380900503d06a0a901d00138100380b24403001501200800080c4075881c80c180d1a1515a0310b0031100703540d83c1d20180c1d000401c82d0800030403c403090b100000d650300030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 454601402 1250 454600152 454600193
    0xd020a0f03020a080406030c030e01110f13170f0d03060311061b010f050114010c080301030201050f04031e0b01120f080a030608010504060c171e06130c0c020a0f03 72
    0x30440ca260036403402c081d050008001030408140050000c1e01076004100144041e1014890030003001c41301800c8400b642e41a02140b10148500761000c0d03a00030190900030700f100c1401d034680b92600307000c108103000c5d0380e0004c650740d101245c0301b042c40b58184800905d07060780d428107103d1641595528040d641d801440c013030164a006c99041e03540d02407111004480164a40204108840b4031440f81c068402402041e10203419004042040c0d44030322078800049400601d402d08590840e801100c1c0c80d440032002c2610600140004404541001001e0300441724113005041101002d09d000c80d403048059114200071540441d000020444600c18501c00d103510445031a5240103092040e0010100c94004200342d6180c1000c000802106600210b642e902c81c1e1104007020380200100c010480e4203d8000b40849408070700c511150081c8000d06801900040120907890040310b014401c80b07080c1c05c85000080c50080e980c41c00e5041100e00a4040e144003d2101034050443d151b10342d000a400108481 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 454602652 1250 454601402 454601423
    0x4060b0a0f05101e180503030a0503010e04051e061504180b1008010e0307050709112502090411090708070509011206080604080406090801090218040c0b03180f0d020a 73
    0x5504d1140030042c1288105161289040c3d07080300d001800b554824501003c21034503040d000c581c40c9000000d0b5001281c045e9102031440c1c1c24041e0040748820f000c4c2003112144038003602c074120800d01513130844c078a00d502d00c001c01061070032850f00880319054840383c0e80181e00c0c01945c441c0c08080c0000d141c08a640003401d08119464100304d2a51a42c010350140c0c00f1075181184113100600f004c0001c02c000717809141100c4071103403184440b10884001107403828124400300040344c16035242c8030700c040608c952403443ca200c0c3c841540214010410844003201c1d00380300031b02d0b0781e01c1070300d0304c44005a00140c0ca450914403c2c60040320282581c89009800c0d41407210440001803810020b030410005480f0a000761600c90505242c260629001401180b0120b0703229140821089414480c00d50000c0d00100340d00385d01201d85683c8124a01c001d04183d07009441d001300401c135107200c0001075004203124803200c40d40350052401242020b026020008080e00100e45d2400942e43c0056a40d80303007a0803070003265 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 454603902 1250 454602652 454602679
    0x25031404081602100909051e040209180102040e06041802010914120a030302070201090e0403050f07030e120706020d0305040c0510050d0c080a05010803190f11120304060b0a0f05 78
    0x702e0341080d81c0290b001d429192000710711079111410108603100a0070501030364440320688000c400c41c000e0001c0d048034a010008003d840c00030003407504800040380109200e4500c05c07c00342607074444e03003065180c9041d05047c000141058801c140c00d10440e10018080080103034002004d203403543c425204448072206104103107a81d001d01240003207084c00d044030802c20440ca4050b019420840c0d05038081070102038009140100c647c2414441c56040e9105442c01000b4041e9a02540007000146d003000110880800641c030307042c9200d01c601031100c0c01001004d2400e100281b40c42e900840c48005c2608000c14000045c0b24405190207942e400c441d60400b960f5001c2044032180103809100c02c00138201508006d1080e000030b2294041c1c50303100f2041c0456030701d50b500755a40703100c0e0403040c1caa03144502d030308005034034400d01d010b41c03440310030303203000c0700106a90f410b181c0c90811000302c00400c904000061004014051249213601d0f142030712081410352034031200c4130318804c05100391401443d5010094 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 454605152 1250 454603902 454603927
    0x904051506030102090618040e030a02101a10020c120304140d020103090203070e0412110a0f0c080a080d0c022410091d0105060111100e0a0503032503140408 69
    0x1c0301070390740240c0005e40769000211000d144501c1007c1c1c06000e03a28218007002c08020110071141220319580041980040003090f103c0104040340c110a8034044011304040da60756907004030450110b0f1540103240b2140f80300c0400108000e07904400c54036600402c4100304d42006101221441c41c030840d02d005254507a400160050305094900075030601071078001068006010920500960040420180c644020391082d15001c103409903100041d0b2003011131030f00260f440b501d5140042c0c481d800e01c0c4081a0b442a6244c54084182001c6408030000700e80e98421004d2841207441c11080307480100350341c1e5092500035100e100f556400c40607690341c000011b6038601070261880000c04d10000100510790441c1044007514154118410055080c180803900961003000d0a1004521007800b03024210389000000d8018281107002c12240c2c0500c00054010030703002d2001d0741c46031902c4151503040f0120600c07540702441120000109161a191030040105220031b4a00d40c0703d980702991507600e01c52040351 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 454606402 1250 454605152 454605157
    0xa14070203010212010b1b1506040b13061d09070e0105092503020d05060102070f120c1a0403020307060212030115050c100618200306150a030c0e0904051506030102 72
    0x460036003840400014400840300f0041c544410007c5070703c46101440c0303002e917071600e5807007803810200301c50400415000e00d040d5005600185000f4002c001600d042c0e841d0b04183c5105d90b01c5003090712980707204600c0356100505440d51003059000039141c058100600b6281106c0103025842c0070f4403c410001d80c9140682800044401c18241400100e11086a000f406136200f0801624003e0805010920755400001c243c000e566480e4058030340142403e1826903404507141c820394035440712240c0022030604140d4610f01d10140d04541a40d80c0d403c0d40181480c0c800c5a6014600310752004d035400300a8070589090300e05403545000010406548020210f509020302e2400040900039003504015a440d6a032000b011103404681c2d003a0b40c40c2c4c01d07190007011944010000c1e20284c101c2c403203414aa0400d900215844400100352207040122000f900d859500415014000301f40c0c0c5043c8010959080074854a4125003210183d103503140a070f88068648402014180b040e84540004c90b0302d0b40e0f802e406 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 454607652 1250 454606402 454606417
    0x150d0b0409050a080f1e030103021e010c060c140409050109050c0a020607030b010e100801080f010b01021b2205060918300c07090f02071205030403030b040e0307060c050a140702030102 81
    0x401b10603111010070304070660700a10003240729440c4c10040002ca01c0950b0b11801d80300e103058450500722500c544400c0040c0c01b0346110380c402c220100d41c4001ba0041c2540c050805001084000144d03581004039040407200003810b142d1100f5814000c003201142e00240003540030701c00d451302003900d81841005942c10950a80d200794841e000004511059034019a01c0d07041f94004001c071004040307444505801caa003903042c40c2e4016080b1500d100b028240c00071550784409006802e00255005a00803002c540c400c00c100b820043d0384038010f01190b0f107400c0f80f080d500042840c19103100c2031145419540d86140c00b040e00c5840c0d030120b1b00b12441e4004c0480551740818000c6603840e0341d840c00c000d20f182d240d031824043c0b039a0070740ca070064020803c48140f0944154541c07108170690391001001042c0c41d035400c018400c400b00358031044410b80c0c5071118001e445079401e01900a688560aa1901ea01500d14194940042020031310189440b01c2d07010202c0c00880c071501545a668010a00200340603215801 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 454608902 1250 454607652 454607677
    0x18120c0b13030614090c01030c050706021b070315051e220b1306060806010f0b0c2104050102010c232503020f0609060702030315040b150d0b0409050a080f 68
    0x1c108440d1550481040391042c07811100380c46446d140d60005504440003026103900080d8144a404005049980104802440c03030343c1191058010a0b4640d04d0010b1a4008407034182040c4000c00e4404060f010b1660081c071030880c0000030216440d140708480000a001080d018000a40e00780d034a40c50711010800513402132854011071810880d8444c0048070054100d441c0d6140080c0050500c1011a905042c1d459060a8104443c03a102c2034030340c00e40040030720184c01d016001c61002c0c580c0003069100f41207000100015211440c0c00c00190864a80c440c01405000d00b101d4046907000c03103552070000504100001c0e50300d801410340c505200c1c4803205042030441c0c240100200074541c00090b40b44035180d410085410940e1181c002c151242c03420384e00d1a000d684203101207046125900c03d001d0000c83d01910000b100007010000170b003028500c0d1a2602612400603807201c0c440031500400a0340e83c0c0a80c0d041c401c4813400d0351a00c0d076a088040703001e0700d00400810440325441c1288202c440541040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 454610152 1250 454608902 454608911
    0xa020d0c083a060e06010806030f39012003040b030109051b070b010603092f01090602151621020a0215160c0206130618120c0b130306 59
    0xb100d5665400004454a0a8011004010040129030301070001a6503138203145950681341d24005461150300584181e900d4014100c90105610041105055021454038080504905480e6410310707800000401c014a418680d800640d42e600460080725100c1640101c28211b0455007580c0c0c02c50046401018085400200002c0d80340e4158201a000b80c0036080c2541c01d1070304500c0c05c00e6481c0b00e61800203291600c0d04004100c010300a9101001040c041c81089040a00300303d08985d0401c1401d404140e100a203189042c45075038803c103c0c002500340707400185121a01c0000e000e030040c0004100c41c4a1400044207050122320800025000c0030035102d41c034048460320700d100e001a4010150f5400144183c034180d202110001c460280101e02000d071400745c1914000b82283c0340281404243c0c1c0112041140c0d02d4040a0440030800411203941c1701c0d9070181000078804012181c0d80c0c4803c460300706107108000030441c00040c07903080f2000030140135561228112907510000580d400501000e182 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 454611402 1250 454610152 454610197
    0x1709040c09050405100302090118020f03070c03080711030f16060e07030516050906040e01090203071d0a02070320010603151a031609020d0e0604030f0f03020a020d0c08 74
    0x640070015694101e6007804280d45032800003078403898034400690300034024801004403030f4021000a40040c400000076184c6004c800101d5106d61003900c1d40400074038140502824180e0080e409500f150080c40c05500c0880c082291690701e000f00521403036040c0f00099810104428100c01400b400c0c0d001209000c82100310341f101d516000244410f4aa43c0100f030b80c0a03502000700248407095990003030080e099600c8400030f00c4010314200803111459035945e5240300140c0d0f002c01c100c1c030084c8011a501420340040d0b00c400a1400c0340036100c52460381c01807003048006600301041101501c0d12620000d03000340d006210302d01400c0b90742c2c0081c00242000660b11140d044075003002d0304001d14901c14030151404002410795480304203038036082c0c0c03544052007800788101c00c1c1c000b4185190f1608010652000b500d4000e42000c1040e1403c501207003041424100d000c0c1c200c60040b4054080d42800c5003848007100000c2d4035841d44407a05001c20090104850802002c0d00c2551400b080f001e00d00c2010080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 454612652 1250 454611402 454611407
    0x1206050a0f03030906050c100f021204200102120403110a090908030f06010c020a03031b1a01090509030406090e0a0e011406012a060b180a02120f01121709040c 70
    0x1c602040c2d0008408510102c0c00354092000c880c2100c00180c0100b409007012200c104c02090300c0e003101d421894007080300d07001c800c0410000b540914000e00b112201d070f50550001d01d0301da40004082034150f4105e4441113990362401016901120381101d11501042a501c00240088401e82c10000c1164030304105001813100c0c00001e50320600e80070800031481e4542704015180b040040308000e5104031040000d00000c0c0c8a12414040898640d00d4021488510350728800c0701d081c000c15051170340c910500108402031484c011190044200300c0614036081c1002c2004241140350701500e1502090311000c14001c000a40c021181200f480000300900540d204400c000240c0035181240010201d100842403440e07120344ea0782588061041c3c043c224942680c0f810064040b0007099603203d402030401c0c46519641d100303124407400f682080180d41d036401043c010030541c0c02900d03075a48100f03500018020401e0a400400b449134201402803806c6440c10b020301801e1185000340e030340081c02c0050480d0000e4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 454613902 1250 454612652 454612679
    0x40602040609060c0203101a100203090901090902130903050d020c0d0e010f1209080f0f04031b0f060e040603060c0c06050c19180902180f120d1206050a 67
    0x80007682c45100007503440c60100c03807000801d00040e5150704945006000240c540d44000141100c0f150310030160059500010341c0080e07020768490258100041c080342900d050110300f405801d2001003082031100607004201c5c024111101030320000d54620b100070903d40580185c07103040d44840c07002e642e01c0624408554560310716041a40106244550700c07a103941c0200010b0005001e2a0fa6440401d95411212405021551402c0d034203030004101c00c910641c41507006140e610700308003045650300e14500d44251030840f075190030040d01401c010305100a500c2811500120b4540c1c0ca850710408100200140040c1420b510050011b885c10000c90541c58020759440a0300740915800c110b03d6070b6009031450b4611070802d522154044030003101d54080d000d040504207040d44030080000301178450001000301d901c1401d085019003000325558026152002e20207466890a0303480c000320b05500016103540d032510310380240500001c174034501d090384242c0e0b111b4001040c0080c4142203855540f01c5100058 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 454615152 1250 454613902 454613909
    0x140c0f071b090924090201080a0908130609050108090c010804030806270105210c060a09150203030a060b0a23070c0e060a080a0b24040c021507020a0f0f060b0904060204 74
    0x8410640700c1380c0020313000c0e1103854901d81d010307112080c49603640c1280a0090107910800c454164041c0604404401e03000a510040c04043d00c0f130440c01400e100001d019694007c04032115135000d081c458029903400359501e500a40d050400700c0e5580c60703140c001810445440d4814145400a0364500e2a505010303807014121001680c003042c4013002c605045034601c14248000c826a400120803003000d0500500501c180015454000a0740d0f482c1d03030012422040c5075105400690010081c090103030030600c070740c500134071894440e03928108810310050115891820f2907070100c175410782c2843c0e00b040120b0890b110107601c00300c0000940e4450040f29050348090304c09500501c01074601156507200000c61782001364025211810075521818415529106800c0c0d200c001c8140000d04030085e1030750700030f10441480680140288540f20082d190643c10000c0820085620022020004c0f48584000011142c2c11031b40c0100c2121141c1440703c050480d104441c0d40269242003000148030703840e4050000e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 454616402 1250 454615152 454615193
    0x60216080c1b010302120c03070c0213050702070e1504200406051308030c10020304020103021308031b0706200102120103031709010507050a0302130b0409140c0f071b0909 75
    0x400040b9004600301e00808418000d09448000406c01c41e8003660091640900300e440c28550034280c40e4003054880c1054850203d0b0703261540c081c019000e0301031141d81c028003110340c140001445d045800c492200c015810080c091170703441d11130315401002d42900d1140c03601c0c05e100c01da60b07581d82c8020080c4158004a6200c0241c21210800310703185030080100c4030101c5185005180410365200248001d51010300101d061560030001d00040e40c41e61843c03503000301607140155403501e202400c0303030700760403205079203c1c8160300040000c0c0311040c1c0041800010030f00641200540d60072030340d25a8024801c10080510341d540c42c000000805510000000e40807c4000000d4586e07180c0f4000c0f0b9007611002c3e034038034011840c05e1044810705d03440303540508030404041200304880e0355100500035030f6503c582c00482001d5146c1702d00b50865402c44a02c90b0700005240600c0b0700c0c09a0280b0030250a009040300107142414074510020811040450580a04007000c400c2140000c113107044c00d840842c40c2c0e040100c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 454617652 1250 454616402 454616443
    0xa0506010611060c090d0b150a06050306011b051c020312090309010909020304030c03080a150311100c0206041716120605070305040b281b0801050d0c03060216080c 72
    0x100079030b0340060b03407441720b00508465886000d640d14002820001032110020f07010030340380142c0e5a5503030303040340c002440c03540c65481e601d0603c030000400d40c1100004045581c2e4481c00b032040050f07030010b8050412071114080b81013450810408a00314400c1c141703451140041c0700c00b403014280022004180f030034426210050000e5032030030b0031800d0f40030455024011030000180709001c64000c641290f031000503202c00280392032030184080b140110640040c1e400c0c1c0302c64203000680c2e04003510740043d0380b005800c21164a1000e580010050b11540c001c2d1004031a03d540c540c07915400412000c240f810401c5c101070801c40c1c903010407010b551400802507900c10f00305400f140304030b4000d1090070b000780d420661130680d07aa1140340c0c0710402c450003078240018070214040d804404400344188441d240c402100082c203074040e240d0050050070180c0060340710340619144640001d420185a1040b6980401c000d61107401914100f202011410030240141c40d0015901e159800d0102c0c1e42460303a1503080c2c0414 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 454618902 1250 454617652 454617661
    0xb0603240106082205100f02040803160503160308090d05041511160b030402180c27060412050105010b0901020a0f0215040b031905060d0b090a050601061106 69
    0x216144000c92a0032098880900500000384a040c20a80c400c60000780308444100083d505118540114800d0b6103581000c1140138101406018110146207002001c0d4142410807040703580f01c0c07141055014440c1012450364041010500541d54039030800f00001081030201d0030007412408040b20b1095250080030300701d00801e03000304213450591380d041c80100e9020982c642c0540701c031300e00c0038004922803141440c070b6030400b222250008054501e100c44241c03a42403610500c11611942048518070a01050400004002c0101034410040481d44011500c42070424011000e1010120554000800050100714440c88540102041c2c1c447d030004c1000b0380c1d03581c161004901070322013420b006811404510001c280040c480c1200c00740010054690318000d104001b074603a005500c003511412003c0300b0842491141c110794918090001414042d038500f4800141900001d000c0040000521102044098400b00002001a640f0a040315400d503100e84001e0001d504000b07000806100b07401c0042c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 454620152 1250 454618902 454618933
    0x50606030f04020105030a0e011b03060b0a171803041d180d0f0215150a1215020f090405040501060515132904030c05010905091515070602070b0603 65
    0x40744691000c0c40c4401e810349840d401103079154800313071000f40f101e62101e0409003651404c1c418100700315901001680e554071441c1c40034040d11016440014003c0041c0301004030940c129884007699180101e02c40c03071551701c00810a1100581910140c0644000715000c00c43c040000ca8482102e0070743e9900c2d20082d940c00e004030100c0303540b00750360340d426400c4420500714075030080101154031140d13801a900a210b40c031031740b1410705408417102c003400001c2d5441c0c2c0307699060880c4048090b10960070f4172901d04215441d8054040301a4000c188090b5002a103009817402100a540303540d24001c1c414012403d00b41002c40c040c0143d40909803103010200d00d50b07441c0400000403140b0403040822000b6440d494500e00a481c807000b90038030300c056041500c0c494140c2607031078018400795204200c0080d116050200060501d007090300081d0098942c1c1c1c082c42100041903140752481e43c01220807901b110804c046a60150003031500080c00e4600125644081082030000d0602c178080c00c0d03003154070012924144 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 454621402 1250 454620152 454620157
    0x611010b010e0105090f09040f14030a080610051603080610110c09150603040302060108120403020d110415030c030b0c16060b0a0509010b1c0204050307061209050d020d03050606 78
    0x2907800b04400740b002500b99409080544a5210001c0400c010b00542501042010702c0c1180d0444400544502c000c041203c0b200d004850200410b004608144000c803015203880d20251440740714240d040c0b51000e540d07100740100c40a401202c545000c10842510700540600c2c81034482500c500c6001038404d01291203402e040031a516800d0041440007249010b101545030083c003005c62100c8915003484051302c1e80b4000307602991107035008054561402000d60300705800c4100c1138a03040b404000c01c202507075541440380d4442d07400001118948004000203070080c1384404031860074541002000090000300a46413044a0149284121a030350700000000d06105203114a4050501c512040d0003040c410740c0300d01c070904e00183c4198002c2e40c07241e00180d44a5402da00100003400300040c00c090034220f0802c881c88400780b00c80e0943c101828000081d880710600d0142e00c041040840c011312848056800241c0307e0398005060f1070701e40e00d20324402919074032941c49a0007c07a083c1004120181852001c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 454622652 1250 454621402 454621421
    0x303090a060c0c09060b0c06010e01030c030201030507020721031412040803280b01020f0727020d020c01060303080106110601090908120702060915010308091009080115061101 77
    0x24401410304001c0d0544006040c0ba00944101c0c0354408041480350302d91041740c014040c11030b08aa2242214149a440e21105030441104002644010400100c044550f00140d0390309080100302d85c1d1711030400f00c1c5400c1e02944400098070442101e42d8505c9840d50280303030058002d940703a1001c01080c00fa5910310b84500c0ca0326180180c916000a001701d604000030b540c0214101c50403501c0c03a900d4200310f0f1030652403030013000f034480e60341d43c42a40c90b50b0301007041c09000005400a841e125140041c502100c0341d0410240340303028004121381100d1303e519412a01040710303400301103403a1501007950a001700032a00044000c142000004910140180741c264031042140d8010a0168200562a0080c01c440c80084a00f010f00b4000040030f200b080ca02c0510541d840e0380106824a0614051440c0c03411b20581c003000500984010701c0820030000440344003031000d071614491304d40b12500407074001200f42c3c0004065484d00202c0c4050642d095040000c8074100d5454190300c1c0810311509003201c8070b112 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 454623902 1250 454622652 454622659
    0x30e060103060b0d050d12050a0b0f091e04061a1f030911060c0105060f06090904020d21030b0f06270109150c02121522080c1b030309 59
    0x400410002d112504070002c40c1d04094489001091260f80e07003850928512100000320700560440302c1c01012902c60300e07610480d400c5042c00b0b00052a80880c407014413012941d4060448c40c000182011402c3c4824081c1303e03807030b041d0b50680c0d25144c180103009041c2d40c42e41c46d090b0031260700c80346802d1510075903066840d298481049a0042a50000d90050401c41c4041b1062004982103040550b9240c01811100c1400740010400345003500400512098120650784200014811107070151189250594010346c1660150340141540c100001c46803c40e580c00040f800e1620501410180e154105410b501c1c0203503445001107030940108000c0e4000d1482083c25800100251014039075001c524285100040c100024007507101c0c440300c402280300104020101c0d403101651011810981c1d8000380e11800c8202030904082c50409440d1074240181c4106800175a42c110795244140c82040c3c402001c1d0b00c4200c0075510310503420901e80344d181e802d030007222085c4802a040f043d0705010040715903040004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 454625152 1250 454623902 454623913
    0x30501030803011e050406031103060c1608031504020a0c11032109040603020307091530031b0b011409010e0c0c07030206030f0f0a0603050705121624030e 68
    0x2000028992007003503842d4501501e1842d0001e4540c480e845658040c0d4001d41d550500e031509d56061500c0e040b000b40100010480800400d00d1043c07503c403440c07003650341c00322001e43d480d101d08445400380f5176000703140e0f50311a1001139045005504003050952042c81818011112901e0200305a06d030140750b00b102c620703d20300c0031610841080381e0000f0022410001c100240450700c94021900e400c0c1c8940200051507568019a010100543c400c04001c180c04232109400d81d1016a4102d40c8aa03a1511407041071501c2010b98201402a00501003404040f41480d11091940c04c00d104801c0080c8214003401d0f20b400d10041340c070300306030ba1540e05071003020360252a90344a5200020155124a01103592401400404401a83d85100550041010328000f081ca410300b48941c40d03003504007a03d003c0646182500800c002080070076590100ca108a0b11000500300218595051400e44407a69002282914000c904c1100b48600396604c07840c908484580c00740040419011920701c03080c4982c103980704 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 454626402 1250 454625152 454625159
    0x10602062404091b08100621081c0603020a0801020c0615120601180e030a14031b070303060618050901050628020105010810110915091c0b0703050103080301 69
    0x8610301d0303890790312000e0400100701206485000062043c1398800c0c0c00d10822420810007400100000d24891800f43c404200d0203242146504100c001c8217030320040180c80200f00c40074401200152444065950301410381d01c9210751000c0e0050846001c00ca10480800c0004954454148240c030085c03401d04c0f00424190b25402d5001d6001c9001c001a141d10600340842098030903001d002050003408a222070368105401c0e48800e0080c0d031003521000882d90305c1402249109503001078420b220300541c8505a540781c0b2454140c0418609806040d4180d0b98001484020141e04d50310800490b081550f40c82107001088682da80c52010502c10680d01113004801802249008402442240c50400c110420094080e100494685001a00d9000b507592000100140b0a00384881045804689010095a200d407030303021009016032002c96014182c601c1c03100002666000450b11004030061038680e0319442900444600c45101d28204d500c5d1204902144004d1300901503503068a0348602e0030b07410b44c5e08 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 454627652 1250 454626402 454626451
    0x10e04060905072105070e07020703060507090b0708030405070f050607023f0607051e03060103110c0a0c0b0a0503040311010b04090b04060c0f02031801020c0a090b030601060206 78
    0x41e51602a95103008030400000d00e40c1481404c5108184030b05a4044148400c0c1820303400e2040350340c41403071018000030800c00007950108219041c0d070b5105000044c142c460560440321800c2c00c0d00071206c1840001108003e0046001c06148118842c40071035880e80d44a240707108100307009200b5580c100c081400268010702d480902c1e43c45045403201981050815944090418542400c0007060482c44008180d03460314140310a0354013203254204289080b200c5902c01c030120b1b01c0b000495009940c0480800c485030320a40003000c034214030455080e203903101c400c015034903207644171800c80313040b541e8200000b011010300c400d94002d41c1680c0c4801d42140d07160344094500d000c1d581180d038a15542e41f201d500c100d94543c4075285072117010320380c0d00d07580345406d2801c0307401c0390004000d040034400c800c0480142030f0f0740001100c2d07c003199210302c00c1404000d080180d20348007181407440e6000c0021640880c48040d598800c981c1c5040803000c9480c81e0340e8504c004d80c1c03100420380d003420101110000a1080c4034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 454628902 1250 454627652 454627661
    0x40b0102100501030f170a200a0209010308030901180803040b0402011101020a030516031401181d0a02040b01140904050408160f110a08060a0504030504050607050c0a0e010e0406 78
    0x10600584909000102080040792400d810448220702540b41c5030050003405015044219076001c0158a06101c094000d0310403c26040312182c190901d60001001d244113005c040fa031668040c0c05291507584038a0708520f03942040742d414803558a00354011025080f0b90411a58181d00702c1119413454036140c846400440c40180203905110030b4001009040c242440240941c10050f500000c490410407410b81c101c00a07001c4070313020181886200c1c642c0300c103c00251030454914034180c44047c12030741d640b000909000e860212268803406000842054040744840c21300c1d20803941040f0342c01c10000191541600c404041000700c100b4400c1c5030841c2403c0d0b010325080380c080c081e160b08004c0e007021400000018807404540c541c5c0005120001c000b2406500d0203c0c3d94116040a080c0381000ca0090346c89400410507080180c480002c03605040c002c10072035002d00750141c61550381c1c3c0850b00b000d55540c400d0103c0280140d880d130341c00007500c0844844050586a03641e454058070703122a01c9003400361 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 454630152 1250 454628902 454628921
    0xd0507140f03040306021201050f030607030c18030521030403140f0f0a0c14190201030221010602060f070e10030e1501120605060d05060705160b070305040b0601140904 74
    0x14860700c415400c91800030006440110321500001d079480c2c000b080c4003070b0105e5040c1c0c0402d00440d6007140d00c000c01d42c0c01084080d8441401d28001402d000000400c40f1f03814a030030f01d00c01c4081c0307006801005004000c00c035038030100e603010317429081e036100300d43d01183c0b92200b283c010b8009000780e00c1d40c1719500e801c003008101004601c06094100b052811041d02183c1c001070524002c240c8060008003080304081c03000c00d8112404019104003e41c4030075240d10741413000c50007810141d00059509038191301e00016a841c0c800c112100004d0360311100c003e0b5803944d0903958110488039601c0000e2510b40709890040d1035020241030352401e10b045500c26006000c0026120907203004540d103040c000340c207401110340200344c482c500300c510a1050804000702d03140542801e016002c03c2d01e204001c82c0000030515001049403034007583d203c0200c038896040c80122200181052507410602861582c15005540254040d02d240101c9448200064401c1c01400500120090080c400c03460245450f41c05038246 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 454631402 1250 454630152 454630193
    0xa11191e0503210a060302010e01050901051207050a080c0306180a1b05030a060b0903071208070602030112020108070e0102123708070203031302060304170a09080f0d0507 75
    0x1180d203941e10390460f04a416440104164104410307882074080d0740700d503040300c84044200000c1341141c0009200b03165100d02c050601c8000100d0043d45d034440d000b281c20140788031200c03058a08000e5401417050b0b1042d81007030001042c040102c1c0c200b00c03040d4100c81c010403000300450800405d414000442d100c00824520a281e540c0000740302c1080610b411249441d82c5a5403507071b076854000b000c4070484503550084100600c051100b40e185031400074440042e112083c004040200b038a1402071894803415400038251070021000144c0070b00208042c40107035100344c0300c2c00525510070004582005456489a0040e44064040f00480044400500e0340c2600903031000c1c0d065100200c039080440c025000b0444d00006070940301d1191754040c034469000041b270720256245081c250744020f00d85000b0440a1300c135100000c0460104415a040204444007034100c00e5258650315001401076030040c071844110740a0707003003605550721000c070f181c1c8941d2449440c3c0c01c2c140311407901d82c4d02c0210480300c40c0007039 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 454632652 1250 454631402 454631453
    0x60c0a0b0a140a0501150c0305030a0504140f010209040b0405070c02010810080d081b1314240306030609010531080c0304060207080304060e0904030e04110a1119 71
    0x14140b409070300c040d218030a403600109055240c401d0100c2201820b0004400b00300036074003000e00181e404421260000c038402d40c0800c082c2c44a081030152201079884c899040d00c05c0c1d04002403054030640250001d14811942041a40c15020910040d5a800c40340c1c0f0000400e140403090040d800342c452143c0000c50000425041e54403641c0700d900d06603c011031800402c55140c00c021042019400c016100c1c15030403c0d040c2800c00c0031888603604035060280c03a05801031480701217440c1c4c40f01201c00c0140b014403404514881e06842c0e012000354402d803505c600a0103070303100180c0c80340d5050150358010414a0300d900700b02b0407084508080044545844039110b640c21545101290401d1301a086882c075000c040e50b40c441c9040406460095903600c15051030f00244010000603421861180c03180c0340580380c0980c10b41c0e692800f25900d20740d11007102d0384285841c0c04080162072400160500010540fa01c213114690325032226030b50607410782c01c041d01c9020400b000002900b444066008050040b9201030f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 454633902 1250 454632652 454632671
    0x70e030304230301020a0f0c052d150103050706120b030714031506090604022b020a09050103020403080f1312061a060c1005130c0e060f060c0a0b0a 65
    0x2815a8800e900860710b01910807034440b101d4120601d4142e801204a000714034002c20000041d0000682c54003500a200c8508029030502806210320200c01498080c843e48004d40045500c80e800803d0311200624401c910440e45501e51111505068907000001044400d141400864109034002086131100d03840b081141c3c1d06480801150300940101c2c200141e81d803a18034249450a07e18120710403403441400e042c0700e465200c1030940380c0c2003001542c026907034440e008001c0c2d010445441d80001c60010704052a405c1100d2a8080e0081050541d40c42c0315403640d07100114241d004901004d1b113080e004110f0a014072041c3c1008003502a000185081034a03528490069450100f100580700380c0c1e01c0d21a4222004100200e0285504c0102c50b00340c10a420039944c0c1d0354031400b500710120015038038000b2800e01451102c48034022980b005407020707040d85599a40c0c2e209001a80c4032070103803075800702e000c0701441d08074140d50307481c1b03240401002d001800780c998006d00070024000d0788800c2d40e00e14501 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 454635152 1250 454633902 454633909
    0x41505091c030f0204030812130b0a0b0604031e03090801020c100b0409230105010f061205070207150c0b01050d0f110105120103050c01200a1b08060126030a0503040308070e 76
    0x805c015401990f01607203540250801d201d008074010b0600c03a855403020f401d040003407009403d680e00010b0502000400d4040c0f81c011881d180f18a81003d005000c1d80e0301c0320300d2458a03460b01d000d200c3e8840d54581102c15a583c80142c280d0040601b0740040303800180b152181c01c3c61660040d420420000c0000c0761003107050b00e840802c00c148031001141e20312001c14810004009014640c010415000d0310241685031010041400c001c1140905109403594040b0304094030030401c0703201a00203100d21490480c01c1900c05000f000c900380088030039110940c0000360038909001c587c00300907008882e0342161000be54500440720b101e9007803107044c440248006501440d8070507a030f50283d80708071f0051502080c505e001505120208400b0150a640302c0b0354104805004074001700403950050034ac04080c4a070300c11502003180560032030040c511424000085110008265031128510031054140303084500300516168440c0b0354059000c07030803c001003800640304110080d40072210b45401400603110b007000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 454636402 1250 454635152 454635157
    0x1050f15070b010f0f06020304060909020c0a14010902191d07090e070504032618030330010602060402030d050d0b1e010306060504120803060612040506041505091c030f02 75
    0x21041130f0305038400e00c00980340f6020400600b02c41c2c0015401c00b03180c10401030102d44107015011085802044010801508201c0340e01d010707900c6109611032100c42000c2a008060070702040c1e20400d040c04101807034085004042c0155990f5a40e00c410a2700380340640c0541400103020a000c20190042c0001c11203070f070761a0180600300c60340d03d41c2e0307803249182003a20340300304a00c03809115084d042c1c05081012031140f00300c82c003981e152011402c031040c1c0c4e880080c0c00c40c020f818140411040f04207001d400020000c216500002c0ca8043c080709907601c84000f00d82e9110200d6000b50590300c050418910780e8041d50140014030702c0200c0124031101d880000c01d41030f8a0130741580581884003059003100b5a007501500c0007078070b5107107066030600b071602100b15124046480050280500000890f00a0f124542143c00140307007104064540e08142c03401303564901049805807801c54003140c10300c0d0304c40d8142c02000d01440d840d10042050303551100120400c1c82a4042000501d80d0f90f107050500309829002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 454637652 1250 454636402 454636409
    0x51008150103060c0e1e0604030501020d0b0901060c120e1507231603080c0c06120405060a020306010c1407090e01050f0703060f092309010e0f030301050f15070b01 72
    0x3040c440703500d03500e4010140d4180249440030302034090202c100719103034140004088800035041c4000103800c20f01264442c403440d04050b003d5400000e018280711f059401c41201b803a800c3c0c034680c20680c2c3c5d800080f58044a0920010310191001c641003c3c1c243c8609014055078000034a4200b00c650551100030683d4400c2e0401c480444e1b660903000c01c20407403070320010b214182c0b4002411034229241d109215124003400000d0903144049035510070a10100312803c102c0d0005815960782d109000e076890340c0881700f290b00326058400e503400654102c1c014020380303004030010303101d8450301d0999a03030381e04001c1c078a547d5080e000d100d030302c6000031104814010007a462080f000001980d081138820309802240050071401894103001d4104250180700f56068100c1343e100200058422070001e00f04c2c1203d2189007a00c402c00c07050020f0001c074030b4040d4484c0c060300035103804481d401c070715444425499000c00d206483c0d001310406850301150a10f01000c0d0440c000b41c3c426280b0300700d05540d40c075039a14400c0c0c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 454638902 1250 454637652 454637683
    0x10809030f0d14090a060c180e150312131a090402030403020a0b0a230103020109030305130305010c0f08060a21060b04050a0c080c07230a06050a0f0b06040810051008 73
    0x7881c1849498425a00c0541007403070059980701c1120201c4003d00c1d034a124140709e061000000880b60a0520104032501000038180c41c00c00c00e0140e00d8048075008004408a481c00710800054628406100b41504a50300030038281040380781010000207402c020802c1e003d60080001c1000000d0140e007130103100d801c0c1d606d07000072203614800509504d40c03954040d22082041e200c0050000d40e0f0080c22020460707a06145c0f040d82c8820a0324803c00856155200074110340c00c2c0f112181020750000b42900500fa01e0396203407002c070303511102046013001e118400c1118605082d45107154042c444c514400c101c0b805000089145031180b004a0100c0d6001c9441c0360405a541e102e0701c0381c030b5500c0700305a504452900483d50900046071924592141c0311000c1d000c009c0784600301c02800d020184054621150007202c104220b2130b00d010b1820143c01000741344c01200d40307400460100d9280c410296015541100d00402c0303854900e0040e0130007001c0180400c40c4000143c40e00085030203040017013a19241056 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 454640152 1250 454638902 454638913
    0x15040602041a03040807110a0308070b04030822110301230708130b0601080709180506031207030c0803180a05010c02120301050915190803070c05010809030f0d1409 72
    0x480e8501e20300040301d03080a0200702c01c0080c88040740340003045d070300695004464860132400307103000103050716215880200a200042088400e0150b0090704034400c60094a1700c2c44181e1740c4040c40346203a2a04001e0200c0360301501a0180490003644c0b02c030601c02c50141c0001150700342840001d03411240e251103244444d00000c01c001280b584144456040803100c42030030422000741d600c028000074020320716810408004005281f551044241070300070208000c9000103520407010303c2000d003e040321054028840e980e0b00681000e4402c044907442c43d003540d40e4201210190380c40b80308030360020f81110785001002c148074840c01010300050080e54418000054014910701c1c002c2d0a01c800c81d081000c100409100400c1541c41c0d441c241a8042c80c1c0700034040450250302c0003d0090450001b4020084010306030100e4001030010080c100a4010810f07501580d64030b83c0111880314040b1000b1a2a40003400311102c03001d03403030300603000c000d00b03500021584030640550070f5200b1000701e4641e01190f101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 454641402 1250 454640152 454640159
    0x804141e010b0a1a0c070e04030305041a0c04210618050129060c160f1427040302010b030303040f06141b0f0d0c09061103040e060d051504060204 64
    0x9200b184051502a640b1505503880c2942200091003c8000405001c2002914120030310742030042401800c10800d40f181c0900301400c00030020182154100c40416440b200b2114990b40b03030b5a098030456006034103174030700b6040003141c1d50000701100500e00802c006124040c0050302900980d80d10000d240318840301144282000b9080d5144a200800b2001060414081c20f074211148403400d8402510307001c0d40c0d40f040400481c40c0080e9011403c00040c0402c0e0302107020342e62254a5000c8038860459004924208070800c42d0300500411100c1c5000c6d00c5141c02140d40208408081d0b019000f8000003440145002c0482d085520407281140c54681c0d0503ca14100561032140441e00c454280c050741c0546008202100404040c0c48a4001d2140100b000303141900b61004850000070600c8060110202510010380f04021382e00032400801c001080e40750700200000103071011600c40102003038941d100d4000f40b21034410091810390705409241c2100400da550042c501d40190b10855005079294139 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 454642652 1250 454641402 454641463
    0x1e071818200414040203040305090a0b030603070522240617010b16020103020f0f040f0306050c030907030f030c1406240105091509030a060f0b040b030607080414 71
    0x20700c411001080c40d007070100b40500c0c900f1180400b1409401c1d01c1c0140c0d01d41b9076080c1900e50703021381044103502514058010901d2000d05001d1405024282c0484202540701c80800c00f00003500b40581c02d44690f45c4200080a0700c440e04004443c000106103087c1a00000e0000751800f4403e40148e40890340345c40030300e403103c05042c2d281130040ca00718a07000c2c20100c114409603901d0520000c040e0405030049420201001d100e400c690021040188440ea80c5594040c00c40c805103446c4800d85625240c0000101d100c400031086034407515030203010305140c1e8155646d00c1ca02c80c0078028103504005a0481d03070000500070880b08103111190b0720017880319241c0741c85140500136a40480b055045002e06900106980001c281e074690030044521105001c914045c02c6441d010700301841e5814480e0b00038450500540d030b4400e0614607912b80341031002c00d02100a21066030201e10090390903902c0320002969541c4103c000d0ba4006200e8101e442c00c0f01c1061010f0391510070303045c1b15804840c2109803010070100c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 454643902 1250 454642652 454642691
    0x909130602211005060705031206030c040f06050f0409050604060f0b0d0f02030c0103020c031206130c08190603082703011d010615051c0e0706050c01051e071818 71
    0x4e040392102c0c50481256078140d00e81c012180610800400c20000c500160340c140001d40c8040c002030801c10041c1481213034100601324070f10403d80038100d080c408030080c0c02d0900804500580050007042c00e90ac80d179840400410001c1c03010840a95542889803140c1c1c0c0703103c17a50450600405084a0004680c01014207080e0040172003414184100714680300c940f000b000fa03c0304450b041e180c00b8100c5da40d040104144401080c1120b100c640b910404070342c0c3d00d8111010601418100021041011070121081c0c200d810358000a07104034420f0040c01240b035a000b483c0780b84a507841c0d4032481d00c2414400441c0c29039040c1503d448036000035030140c54044009100b0b42005101c10808a1405201c086d409031540c407418410070000184611203600301203141d0440d0356044030600c01c03a002e40e46c1d10600101542c1180750002084d5080c40f0204068282d4582e0441e400920007207501d22640702c0f500207450021494216407440210402c0002d112401c011900090b0800401d012401d0701e0f00c0b007042101e14 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 454645152 1250 454643902 454643909
    0x109020d1109070c0c050d0f0807031e02070f03060c0c02091005040b040203060a03111807090303110d20010e010e060403020c0109140103050a0b04020313031409091306022110 77
    0x40780c21107002c000301e008a40300c5c001301d031004d41382c401c2c00d90502e08140085d070a00c0c01000c0c12090f800128070041540c0080005070003050320401000314480520201d85400051150b207403900c10400b0306002250060707000c4c2108000034144191590301c103601003007280034112500540300e1003140f800c1001e41040d000d2145100ca0441d000c500d10b01c0c0180c0021104d62180c00060007001c8101111403079520f5200c180a084442d00513000300c14607101d0343c0113007200001d0200300c0c002100b40000c1582000002a10140ca1070903455860030304980200b00e042480c0b580a040300e5941d2541c0700342c4c20140c0c081c4111000c0001440203000c0501e4a401c001e890211800151410403c04107020444149840c1c1070603120402441d011170f40c1d03100ca580b41c10243c00040701d803540c014800001c1c050340c070104000180280e880f079203d040c1031140c4864500385c1c6000d1108466048500500000c0d502510640318100307281c46804018142a4441d0903904103500d141140340503071500c441400035440c0d82e00d040380d004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 454646402 1250 454645152 454645157
    0x50a0e0a050342130203010e060406150902030108030d090c0f06090311090106090603050a0b091e0f01080c060d0e0303190e0304151d031c0e0d031b050109020d110907 73
    0x2100b83c400d10015030600401e8200e2042030a07100c0c00844d0b0702900301110550a420031500a030030103050410041110700e009400c410941d040002d0307402458020b40f4101d84440d0055410144010041c0010306010301084981c4180c501c40481c65000d05c9106802030715069540c00c0710307a402c40c9800102d032407180da03030288181ca0140041042c03035844944c0c0e50a0301c6203481e000c54a074a40c442c40402901964402d1030b4060301041c1001141250042c0704480141c0d0005009119180c000d01150401820301071001c00760800c1d8125030342e03030400030000c0500840c510030010b81a0b901090b47c50454106070760310800b4000300300c103041566416000c2c4000c06501c1c90041e41c60640341140f41c00344e02007601c03254004c0c07166520b159264414980000c1e0300440703020702910041303810030618503402a0072500c01008501d120b40030382e20500300010409881c0398180c0741c400069010100d105030030f480c903a00407696903485202c071a0050303c41200044e10b9a2240000c881901c4043c0300300801c003400200000d04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 454647652 1250 454646402 454646503
    0x20c10030b0f041b1b060f09020f010c0c210b070e1e062b0f0b120c090604110d0e0313090902150a050d020f1206060a050a0e0a0503 58
    0x1c80c40f400206820b04c07102e00c0c1860081c2c50b00d1110740c40412024460302802440c03409401d4011351041c0d800078044c00b4821205100d0010040d0010f5892040307448010f0b122511900040c8442030600d100440703d00143d0a12403030403030050fa030b201e400140480c3c48000041410b0800911820301e07a0460100044110381002000c94100220710b46000c0c40314603610011090100c00030f124040015003401050701e150500c05043c8101048002d0902481d000d4080d401c0580036000480d40801c2400d48640f00402d0f0b4640d9850712001c12000d800312000c1c84491490801034800390107454828040009407a0003d10b0321071125005002810354903902101c01603040c0016000140d07100c04140f000004c004003125291424441e0840e2940200d2000d100741d0391000801a041c040d180c1c3c00f40c006007101d0042c4006d565514000d01c680ca000e240f2440e0702107070b0240114071400380a4011841100c1001e030490b03040d030f640d0328000b0780781c01d421781d000c030800c0c3d03281c1030140d241c0b0760401c03ea4201c2848506900342 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 454648902 1250 454647652 454647671
    0x612051207051506060702040f140c0c10020705031204030903120807120e1603030815061207080a11030f09010506040204050d030c1a160e101e020c10030b0f04 70
    0x40c1c45030919100410003d0a8500003603a0b96104401c0da59502d0b000f40003003094440c2d040800004100340c00003d41c07400c803040d00082c011603079031045840342c50416000d0440d0082d94120b42000e90411041229a2b020a2008070301c1c1070342e0312252921541c0a41c1d42c01001e107286040c40080e04800400c1c0c10100b2841c042001071007600103070865030b40c42c200c110008801500210480c2072034039410160f403c4400e028000418142d000d0f4540d4050500000c0003038817804c280041141601c03c140c0501125850781c0c5c00180e410303006444203644101c03148004104e6013401c02c40301078107900031100d035242101314200b070041d00c01d02481219403103070050b10114a028101310005c1c845030200b0074010100281d03100800c0800000501220080ca9a020500071070704054810300000c804c03501c005400121110f1800c04546000000380746055210b865a42d00318030381140d1010f014010070701c188103510071510f0407003079611602c0ea04150090b040d6000500424481c0402451204040c22140305078100714848 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 454650152 1250 454648902 454648913
    0x70e060d031403040606031b0603270f170a03020d14010806010924080706171e070203070b10090c17181006090209040b0103181202010e010612051207 66
    0x60b81c20b03a400d4445641c9998070b6180000281c142034000611900c4040c1119102a81d03861134003094900303580701400040201d00424008c4c0c1c1e000c0328036620130340755400f07040c011440420000211038010501510074100d007200b41846907000c04000380000b0350010f0f642064030300612800c03140007051041104194908200302d50348010601030020301c50742d680c00854055403000c1d400e241c80242a00c034200e450f56135440460301c0d003c0350301c524000300700c00c1844840b4080f40720075a01e105400d4869000203541d49c002c20781d40d01d850024000000c0d07200c100140307408151002086441160301c800301601182c2070100000c00d4802c0e4500d0031081c400c000003420318050301e081103141c1c403918009034507480122103030141f440c069125140901e51460904042031488240d0001c00355140155018800b0300003900044044a0703005070080381c4a031940c450040050514803800680190610000c203025003c84012800c507403030fa42c44400c042e0340c000d42110400409200c0c40001d0003004405038203100154841 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 454651402 1250 454650152 454650167
    0x25110603090703030302032a030601020105011e03060b0402250501060602030a0e0409020f09010605040806150f240409141803030a05070207030f050c091b0a12060504020a02070e060d03 81
    0x4045c1500400019010240304862460880848041d403407403d045451041ca03e0b8170950341640107500b01000440c1e07000d0714441c800717040903400911140d01440c60b1910801040075021042e80650201700d400d0801b031058100c6000d88410006004d2941e650b842c1c00c03421502a54032a030b00b950030500c41100300e940c0280030721100c89070507240801c85026a00c000390300034001c90031441e07103c0a081c00106200d6800340184c0207689000e41142c640b62191a84143c080c000c524909034000c0c81c0c041d000041c1d003043d2001c5072584000301207005603104d40003141c40c0e20390400e402000005a40d1034494254404224003203801c07441140b4001001c0909542c620b45070700c001481c2d503210070741300c80108540ca031080101400954118a21456074006071901c11b854040215415100c1e106801c0854070100300c00928a00e102c107500e0365546400c4a450381900c116201c065006a09a600e80380040c070b9484600084c030098810f5030240c05068203040300c4500c0310001030112405000c0d030b0300c031032400039411812 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 454652652 1250 454651402 454651409
    0x4320901080c04020906090402120a150b0d200c1b0f0607141f0603030e101218050f0d08010902070f0b0a020d0603060e0f01051006080c251106030907 66
    0xb00543d9072003900011901b2440340e15a9503404c03510000300300e040403100c184064002c040880e01480307541c0010f00c1b0b124201c14103016080006004120300f00790650340ba880101c0c2e00141c0302940c03c50b0f8510814000c00c907040500da0800340d42000764007a402c101091110303800100202c5048030081d24200c041106c034051000c0c020802ea03041c0b0350710030320603800f000400d2445500e0380b104903070140120012409401d02c0d00c001c0f070210300c030075610544625080c08072194024240d1354640d07c0301c11054594006c0e00c2e40e4170121590810341491000421404d00c00c40900740300c0003000b000c14130704526005140001c142d100f514507a01c144440c000083e43c452800061503005600392040e5154210f42800038419020803101ca18504000003082084680050702c001c0801d800703981c5500039089c2801e090f207804036880c4c48803010b48041482202d018a030b47d180c00c80600f4103d07504000c010b2880034070101109040111040c80c10a101c0204113542965a40010003501d001e400c40c105481d00d6940e9140500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 454653902 1250 454652652 454652659
    0xd020f030d0c0203070c030303062402060408160804080f070f1a0a030618091103011103060409080910020303091c2f01140103020306070c030c03050f04320901080c 72
    0x1140c09480c0c030301c2001564000d540040146d22601c1d41d910b80613000b80b07414483e00b4a45103441018480e114030a80c2707a52502529074014001617034503980c1c0d81100d41d0000c0f80d11284420300584600215074134ad0301034005031001384000c15604082c1075800c0d01d0003989a1169918800409081c001140903001c0721990320320000e8071070340f100c1020300254041c0845422800c024448201b0000c4495026084070205034010f003a032131181340703031903043c14242e80101e48201113400c410804034030b00d0300f019400b416515000d56240c908081d000d50024002c40143d52403a00143e0003c4180310422505003c159089800000c500d402c0c2460282c01030810154400400140910744038000e130241d088050011a45250f000208041640300810308140720080c001a402440703528006421107004a001510140d00b64491489444c007542d02210710354000d400010702500244400514429038101803411840030303034144101c0c0412020100c450003441d6500920807500c1c2c0c0c2c0108034908004c2070005003103c017903 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 454655152 1250 454653902 454653911
    0x1090501080a0314041a09010e0f0a03230609060106031109090c1b030f0705060a02040308030c0a021005071d0a0b0412021519110c01090e180d0207080d020f030d 71
    0x100415600e83c000c940c849246d036030100302c6803141843e02200038900190241c86e038604000f828070511030540c00b07007280c1d40c1d0016201c2006001160000c90030580c8181d401e8040000d05604800140c20410103032003440c559802400180031454060181010202c0b220500c030341080100400100c1c01b17032002d030250500102c0081e842011581e0800f50000d03001e4407500f140e944d40400340b81050039a0014005a03190f0041e90007142d10060380340201e034100c94221b10361508681b160078519296901c51044002980b2904202041d05010360180905c10501615211207040600d81c114040c480c0b0a10a2842034500f040f00b4000c0c10340840659060b50030761626070807080510b10218007244214148a070001001040c5d00201c9155019a02880c0c40650703907000098803810302042e070702d040c4801b0036070106864280c18040c0751a00b180c41c3ea80701c2c0d444c5841d5080300114400060410060118010040e0013a5201b40000902040b204004c100c80b40300414940c181c1c60384882d01c0c0c1c01518800c2400507200d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 454656402 1250 454655152 454655177
    0xe18060a0911090405100b0a4502030708010501080906040b07020f0609030c0c010504081002030c04050d050d0e120601031403040b13030201020c0405060616080f04090e010501090501080a03 83
    0x40007059040b40c440500445054109801c20a0f6618142591148047c0c1080d18088203401c1c80031121042398400340c000442400445140b045004200c05600715141302203c0500041701c0360400c800c2d5030301d0f0040d001a540d04101c2d0b0000c0c00c400050b00480d0510000300d0901c80074140006002d40c0c81a0044c00e96501c176220703800c04a00300703245210090120701c00c0c10b0610900c1c186c044002c010203007001e01140c00c0840440300560340ba00680c4220405074200032600ba02100164000715030095a02c402c0e0f51800d6251000511030544a1405841940c00b141c0d02ca0301c501c0d0810340e9043c04e00d108480614040d01100744144d600c900501004040ea070b01601c020b10322000410503070380a010b203143c200392503000d01407480c00c82103080c2c8003da00620884450603030b6424a40b1400b800740401400a9241a2114411039451110101e040f035070400100420100b0844001c06040a004042004a5000e0b147c2010500b034990680040c90698980001040b0110300040c004d01e40703a500d8106150525030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 454657652 1250 454656402 454656413
    0xc09050c0a080f091c030b0a05030c0a0b0a020a021203030f071b02010e0607020402040e0910140c0903070305010612110a06050910030209041e0f06050f040f0f06030b010e18060a09 79
    0x10707003840841601405d03541400e0601d40503085024403c03003e40d034003003c880c1d54004156540881c80c0846400103900803081c091301ca205000dd000d412890700450702c040c111680426882c6c81208404071140e0404424040c4840d0a484805d4000240346801c03141e8180ba040280b04c082d0040c00b009043c844141459002d40d11040180d80303220b60014811501c0e2990f91481030700405044580c12220300070408040d584150500c264198603203000200103031643c4104155806174086031200d585442000e4000002400034041c50000e00078585208400803032500d4280803001c07042e15460b20600c0d5508046c04029440000e450030880102d881c600442c0c003041c0c0c103400901c078240d201e42d00542031907000c1410044900310415160009a0100801c0010203a44000c0b0340c03007405010750285504041052514040e080721a0204103c1000904110f076062204102c1d105075200f11450f03113030100100585900c1400300d0340e00c000700c804c43c41c841424502d480f988501000f466103a205940d0500e4006101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 454658902 1250 454657652 454657663
    0x911061b060703090507030b06030316080c070503030403020315070c050a060b1c0c05090604020d0e010b011103041203030203100905040f060c11070e040602160c09050c0a080f09 78
    0x40584129668030440c00450310182880d114048180700c0c41c80491a8280b0a10500f0700c2250001c0107045014210b9031a031840b004041c2c5103a07030603c01405100321007000c8072030074002035115110350303969619500010b506160301036122612075003040c44100096100881c40c912408001e0140300082c0e903a084041e178082c43c900c180500140708101652040051310703030242c102858205e800c3c0440c02c0c02d1491300360288181341d80090818503e68010403080c103140d1952600318100400141c140742c81801c0d22400c03a200d00380f28840300ea45540f80c8242070b58004820260240342c4001561819040040c1c90000b8202080000d040607800000280351650081400000e4594031000f070000f41403c1c20149195044240c0603101517142000b1140414001d0380304403138900c400030203802007525000301c01d0768a4030001d00c02e43d00d203a020808040e10f8101e01d0066480b261041c41e00081260901540d80d00300c0d44002d05030002250b04011540300d95410140c490352100c0204010030f100d40e10503202c0d50812 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 454660152 1250 454658902 454658933
    0x2210c0703051c03050f060f040902150c16090e03040b0c01020f0f0a1403190e010e0a03080f0a020322110405070c0b09030a0804121b0b090c0108041509 67
    0x34058100408030003d1041c52607048015240d03000d001d00e44074000001c40110060301c07029030159407280e243c50907003055085a00c03946d0000b400c0061101940b01c01607815403101806070150b4001036201142001c050038910050510394204126110308003a40f03540e03e20039401488070103c8045400050640c01350104c405c1280092009a125500380c0340c0f5440e60b4200c01b20f0540414a00014990900325400c20380c1e03c00c0b41307400c41401e003d41c5883e4210005107405101ca00940d52100625110980e041010742c0d0042d00c25910700c5940c3c500200711041c003e2014103221303030f114010400c1c030110121190142640c65101100b2601810140c5002015107114820b4a0742050900d000c04c041c0c0c68001d00da4090b218041d0628529940d5090292a200d12480000324046040000450042449a480e200304e400c007604007030707103482845c601d941041c7ca440d8400301c6a6501460030403190800600c80c00107210020b017030100003400e080e62007445442d00c8543c052181507499800303101f400341c2d80e0b5901d0b811 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 454661402 1250 454660152 454660163
    0xe1f032306091f06030c1d030d0f051b0607080703061203050906070501050106180b0705030f092d1e0f3a0b0919080901030603050f07060f02210c0703 66
    0x143c4d15140178016008240029000c41c0c800000700d42100c110345074031014810010040d2045040b0644140c9480b042c9103550010007905003d40300003407003410a90704003110b20400030b104503c0c0001c4010720303404005281c0c0b03080505100041102c0501e683c0c0352001e06606090407074075407942101065840c01030240160841d03082400000b000341e001000441c0f0b1202c80d682400e00720761581920000c6118a81000741154010802c2940300d007201e4014105000004084c880c3c5000da20140780000410102c0d04401c61003148241580c80c036101c030640c402c0140c0f0045c440e8a0207540d40c000b84103036031a19082c1e80107020901e01607440015490a0281c10160034040c04105c1e000e110000b41d24003003040003103c089216901040b04d2010004002e050300c2808007030f545100300381c1d50320003102d60080094030341419280d65020000400600130201c5440b0b14000a001807032070b04400400a200309003e030025508000c08409a1480403607101c0001d10b8a110100c1d501c0100b030000b81c0c03400315194000b821 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 454662652 1250 454661402 454661461
    0x50c07030618022e050c0303060607020a0e010b03100509160e0103021306080117030903060103060e010b150711060a0e04181a010315020f040302010c030e1f03230609 73
    0x1110115090488803013070f5868550a40b11181100c1035a51b40310b01035550b820b582c014800584903140c610014444144080c1c585a81c0300d94542c52041291003c0e081245040008070801150221a088400040408072740400d071a0a000304600c845009080e030007000c11003901c9098880380d0280c0c040394499901c2c4050042c10994030305005040d07400a0060400c08031104032f0503403401c0f0000042d200c0029004014210591866a5050007442008143c0f5000e5403602401e510315a903006034100703145c0c0c3c0214002c1e550307002c82c13400300b02d060b1201e0005445108248641c203580b503407200c414404894255400107910708038a030116089142c03688020300c000c482905046902d000410301d94100c034030841c0c02000d40545803603c4030070b0b030107130301c00c0c181a4401c180070400c0958415800450000d000b07050540c031680c1400040788504400f0034406414000703501034030038420383c140b1800c2d9550000008403211103035084074807210010080c003d207104121450110309047c2042e88482c12080032000c03000c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 454663902 1250 454662652 454662679
    0x309030204051e01080d11010b0307051009150e011704030818121603081005010f03020a1e030e120310053c09090a020d0803070309050304090204080706050c0703061802 74
    0x20354842c1012102000a280300c3d00b141041e0005014278000c03060018080d140490411003070008208030b40320a407040040701d180c0050844a211000180e9200507a03c400b4859070f210005820044000d90300031002882504000c00301c0d601ca80b0305508600d044406c0c2c0010070805000c0c1d813925244004000000f417000448070f6180134807080c030f1203400340709450b0141e40765030f40440010700c0d540038810103004c130300c2e1203414240040c0f1075402080000403030b040c0240e0110003a0102a00c1d81003903450080400e6481e800a91000d008005126072504041c40980c5585455034030f050882081d44a5103004031141240807103401482e0124000561102c440e6050650303540481c0091500703000706181c003504141000c1404e4041c0428840b07043d90300600504400009642c441e4030a9000401401c2015039a40a00b000204240010001881c071400056296414042e01c42e04141c1e41d94400005c0c800200b20141a010020403540222908623000103210a418046003109410301c1b00025841001e1311000e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 454665152 1250 454663902 454663919
    0x8040b070e0109030b1311090112020d020a0e1017010b06040b090102070803030a090b06180612010e0a0501140c0403020117040201030b09010e1902091c051002030c0307020d0c0309030204051e01 85
    0x600746940100f9410300087d11490900016010a010ba0a0b00d41c403200106000b500f8200c440c02883e520182000c1581c9503601e076403141c40c2d8400d40308650195007082040140c0404003407901d08600310701c4006c00000000000290341c5104603c5080e9a1950100c0d00d0704003a8028844a0003c028030400e881e56858441038140092814240840e0601009800b2031010f0502d05d186880c07850590000d0606034880800300410304c06d0203040e4103401d64894a01c10040b9406001c404509032054002068142d1303841485d441041c0300070300000781290180030803c0949e900000c038030100400c1c54105109500d5900048001e011001000d03504800f44e0000024482028058540700d00440c9540d008000300f020103010507441910036480c0d200c0c0e848012286c00e074421001c0c40418074800d900b101e00b2541580034030010f03a042114074060340030010041001d42901030000ca01160090301c0c140c02c425550b980c1c0580703503801c2400301038000c90340c4500041b0070700428034541c0020f0b0002c000824080da07680002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 454666402 1250 454665152 454665181
    0xa06080708031c0b010504090b04110a0c02031b01050304020d0c08072706050a051e03010c08070801060906090e07051606051905040c0303050c030d020c0115050108040b070e0109030b 80
    0x807444070304840749076034983e019124040c01c500c016921b09291500d0301c20200068803183d61140d51003562000c0141072000d0501c002c10442d400c980b00c9040610302c6004060519104c00000c100b112511407034440903030707803010460754400e80c103c81d00041c14103e8117009028620b1074000229920410700041078510b03030611414420000c041310310170490200c01c080804d869161082d190010040d0406201c030b45000c0e441d10010348802d64055040032500d90001e03013503c0b1030341160400f258907a01488181c55001349600c0c003421207424080719807880c048009040209502c11604000c0c180000302e00901d00ca6811582107043c1c40c00707610080b1a0f5810400010842901d0192162405113020710f00c0700154000c0342d02c40e07500540a10002440e6445c20380d002d0b8440c1c481000140010420384282582610151000b8181c100c00055200a414030913600f8161a81126040c060b201c0308120004042018140c2d014100e0b240c01c2c205544200c0060700ca2003404d0308000d01400440c0108000407601064 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 454667652 1250 454666402 454666417
    0x40314160e0f0702010e1f02210103120503010605030a022a1f06030206090d0221011e09260d060b03160c151e020d0e0f010e070501080a0608070803 65
    0xb101000c0d84480f1026422a010700010110302d812001e654022201e02055581c1e526454800140c600040740500041d5241031020b03203041c8200c0c000052050224082d1804034400690814510b55414504080c3c031a0100030851400c0f103400249001186102c1040d803c020b120503080e4006843c1000101d0740c07140381c4102240c15484c810401c250b0f140c90f003400f48804490f009004585040500386c14412101c03100b400507a0001405039045505d407080a0400d400005000f0000460781d00441c45807030120310102030115894100300ba803101240208034003030034214035052500b0240382c421001000e58081c1c8100112400c0c1f0700710300046d044013507500a42c4a03601e101c49ca000e00954580c41541c0d900000d103001f5001e03540329801820420b215a10031000540316400e41030810050741e0192082c0e078800b840e0407030101d803908644a0700d28410030804851000c1d10000340046408803509541d960f940e071040e6030400c284407000c10900700003035220344054400b05040d150754507254500743d1341e41d900940 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 454668902 1250 454667652 454667671
    0x501060c0b04021c06242615010f1707180218060a120612030801060f030e07030804060e0909060a0b040905031209120304081206061603021e12040314160e 68
    0xc0681d60520292814001c0e107001c0c43c2c5807680c0247e0010180c1c14036804070360108440c03080d881801070b000c44260300503008202c08208040211308200f0413841c107403007008060003503910001c001e1000322216880e09101c160102001600c50006500e1012110b4490740c81540115000510110440d48054800c0824414034424818195604400400741e8407500000e0009640000144003503031040c541d01a00030075500c2d005c1080980c070300107107091180581c01152203140018040140d55003003103001150600884003115a032811481d41c5880d09802041d02c1c1341c0c5a580c100c1604e0a0b503840d030050003450307000030460752100c420305548801402e00f550050700038030814030080c2b500d00c06442180d00c240e0b44404014248502035032200e4a004000d08581da029505015140e440c2902c46541080c86001740d00400a60414101603c4111074000b030380b00b8640c001b601c1c00f616580001040380e080f250b1051824200c6440c501e0110b08201078040c1881c050100700c0c0f4001810914500c00c82c1c006c1c003811 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 454670152 1250 454668902 454668941
    0x5040b090f060121020a240f0807020a1509080711090c07030504031b050303190e120a0803100e0106020f0c0a0e073203040c090501060c0b04021c06 65
    0x1c4001c1e660301c02446450741045520590316203da48003030405106500c0900300b141c6240d11401041420807070b80320400000811011504910b550001c041c004440403403d1807281810071950003034640300c1e40070b0f01501c0301c414a82241d01d0f002d4294420305200c2d411000359030f01d40c40940b5004100400306041c4900ca50031020110f0841400e50044404841c1e05072241490541b03981d072428581d070500c94003240300d069121400110fa813014001006140100c0b4401d40e03190030500e001801c90325600302c02900400c06800d44030260140066641e08907038005071040e40303950341c4940303414000c5c846412001903000c50b040001001a000600c2000c10022101900c403a00200e005110710440343c0d1043c51854005039010482c1039002d96448100740a0484410015541c2c01e0448011109010144800000000b0410062050ba0030200016003840704062006526018005200c1e0760307a4900038044002902c00b00c0e04540e692548036022a8403141601100c180d141003400042400c41720280e0441c1c4603 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 454671402 1250 454670152 454670173
    0x210f05070f0915090518040302070b0a05071104020c01020708030420060f0a030b04020310030c0b0703080708090c03060f0103140703050d1b0606171507080a0c0c0605040b09 76
    0x14101110340800035680e14182c1c00e103403079003114102c0602250201806000c91010480b516012094003110424000d400d6990a1519000749068001e60001e11802c000703002c0941c6081c2e2020403202c05c160480b00d80c00c18010320070001070003882442000071440d803000030750108020461001c0c0d07100394040e014410f0100c40224148001e182070b80c030300d241d03c4103042007840042540503003d041d100343c9500e800640d44604101160490b4000d89410003002080d09007001009091032075000030345090b00082e410b01c80c15560241c240f0f0008ac011405102c105000148444002c00c00148503c0c0c008045640c241400205625081e07400c1c041a905105112a40c0d00070500000c1c0c001c0840303910200410b20001e24070b5085070780d003886612203001caa076650122000b0422602440380034010340b0031803401c49202d450300d1918207085208a6001c1c040c041c0104001960003550055206041d10310110b0940c0c1380c681e0486580c140c0c0c00008240502d0541030000744200280042c2c481c2e3300d00c03800c0f113007036286 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 454672652 1250 454671402 454671407
    0x100311031b313e0a0e040608100b06070c051522050f0414060105030a0b120709051e01060e150a1d041512020402070203030a08160e01020616210f0507 66
    0x3c940c0104a0309107100080034000301c0101c0c004103290b418925041000d040340708009003c1c1d940503800b018042d40440a649480c01003442500c0c29950111295440c00041e95240c1d50000b0140c415280704900220416410060083c1111721807140058000442c04400d41d4850400700c403805918000c08242c10500303024101442110401580040c800c2c1d003540c0c032a001101c49600c0205000039444d15050383c1e0700f954139082d60801801120b200640005801c03d040308088801c0141481004140b21070801c080c8404018214159041c80c50020864201e00003c10f00343d01e9070307000490300100300080030540258404400b50100350718250581c80c2d603800800708426159221110481c20360404410000103280c190102c450f984007070000350030320600d90001f07400c0d50010b10300a8040780c4501c003003241e184660100a0380a6240c0d040c00410f0024810000b992410001e1a01403400340f018038040826024901000458120924404032180c0e25a110301c090510003c24808641c01c08020030010350 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 454673902 1250 454672652 454672721
    0xe010501060c03170a1b05030114010509090a09110a03032609070e042d110411070209070c0209070c0204053909030105100311031b31 59
    0xfa05507880c14912078444440480f403c0f405040e40c503c0c0daa1b101c200d59603072100104031440010791516010340303d602d0054280006d00c0722000b25410001304006520884d9034400410341c018040300000901d81006103400c0040c230f07220400041e40184070325000400c250b40b102900b5504682101d4248150f42101c5030b081c00c192007a120245542c011032420700a400c1c040a60541c05405001d809011070400d182020f030708280c04580680103082340c0c1002041c4026015601c580490a075070420001007540044440d602480e20b00a114111000c0824206442000132440c0d0303c4d0000c10030030480c00c104401518040d044032007280513a05100005081040700d13551580718001c01d50f01807030418104982c00c2d100302c503600c110081614040c000101180ca003441410705c82d8410b08262001e140c2903007090301107510400300c002d01c0313a03001122015009003588030509030800181c030103a4200140b03a601c1c14206005041082420011840d00a5500041d03000810154413868901c81600005d000010344103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 454675152 1250 454673902 454673927
    0x3011a03030a140909070504061d010e0907030e070902030a0c08061e01050f030c090f030307050d0311040305010905060f1b0306090408090310091e02090a02090a0b0d0e01050106 78
    0x1034100b4040341090b640508411400d01211001c02498010300c54005081607105485440005030301040501000e6000440e10102c010400f40c401d00d0490031000080110f048000300320f000e104a40c01040c041d81c000c0d00000c5c1181c000384d0549617040d884010640003904203c130b02c1d0b01c40e00d00f0810b6210005016144240c01440081e2500120f00c16181018403281c0001d804181048001c1100c80f01c2010303580c005d54040c07040c1f450b03c160b682d2010300401400582d40000d80384203403c00c101908c00075000003006010311101e400e0105556100440408440c01164000340c443d508045850701040303800300c0c0f0304d4408d83c840e800207012a12355000d40260255010643d69080300c081010409901d8050380b415401841104103906e45524007000c2410040003645815126841d56004070801c40d086003009080d000100000440f110143c0009115041c080c0070096085d80c00035480c00d440d21142c805102800500d4070450365025205122002003814441c1013807203510b000c002140c03062081c3d41281d040c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 454676258 1106 454675152 454675159
    0x50703020126070806040e030a0201050604050a0e0307110d14060702061501020c190b07080309070b09090402090604090512370f022104030203011a 65
    0x110701100075141601081c08094491207841e042c1e18650061a40c03074003000b55102c000100d8000c0c03840e1b26400d4668040000c01603c00c030b40541145010303030804d960401040c4d45e80b031104c03000c0318042e001203a01900100039000100c0c080c00340e002601040248102c1c10102c140d039890410002c08250030764242c0000c8200004a030301440501d07030010520201c40101140840000d4561400c0c60385288a043c10304840203a50303604880308000341c0303400300c03000c2c2d5188a5070520b10300d15001101e2080845c851924007083e0403108030305507041d1200c040c084a00c1038649508101c4041c10041401c1d81003540d611040005c203208110038400e001380100f85035524040c0314a056007900c4240c20124010011441542c41082030720060881c1985a182031003202d200450101c2c04c1c80c03504049510107100340c000c1c41d40c400c049580100b0850b44220300030030101001100d031a808240803940c1552 = true := by decide +kernel

theorem cover : BRFrame.Cov 454496402 454676258 := by
  have h0 := BRFrame.cov_init 454496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 454496402 ≤ n) (h2 : n < 454676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
