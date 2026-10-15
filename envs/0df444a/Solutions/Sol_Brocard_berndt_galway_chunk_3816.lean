-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3816
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:45:53.915988+00:00
-- url     : https://prove2.me/submissions/f0969697-e609-49bd-a1d0-6e79850ec34d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 686151079 ≤ n < 686330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 686152329 1250 686151079 686151173
    0x82406070602210c0a1403040501110c0a060b040c02150a110d0e150610030507090f08061005031b040f09120f0219020d0b0405010905030a050406020c04060b0f07 71
    0x100c000354588100c00d80b1a84281d500350f1021418940001b042100303814090355010b07018900000e45504000001c21955006210360840c1d41c2018000c00f040010710710903088403480540301000110038549000e503444210100003680d04081500061a40740340340c0140c00500007800171240c40300008900580035003101c5a01a184d4000c003903540d41e625038001b051900c281801050000e0035400300d10154000c03c405001c05080041940004c1802e640c16030382d044c001e02440008005a24101c0c2c20800d20600c2da0700300502c80e8102074000302480c8480c1c0c42c0748403543c200329000a81e10515150120081801140040500a04a184020407074208183d505281195002da9034000054004210761a200c0603000b54019500f0021002003101440c3d200d510911801c0001107000c0552a00d034559000181d1410005100103000d016040c0c2c1440030004041e8140d40500c03a032420111072110030f002c1c07509203507501c80d0089004414010f151141c50303c0c070000203040c1c1c0880b500a10710902c8030b031116000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 686153579 1250 686152329 686152387
    0x20406051305090c19031b0e19180c0e0a12020328030e0f0a0806150405040506010b0c0a1a0f090c1e01020304051c02010f082406070602 60
    0x100040758108201854883c8036902001031500380b0305c40c12640c2c02d11149517590101a83d0f21030b0700241c0201c1e01c042c1114900c45856060070b005040d81088200000110204c210071002c1c6800c00050600314265541559040c0001c00c00003a101d6040394440d0403405a640d0000915800094a400300c400c040307451402039060340c440750130342c1c6140c0d41c0c40301e840c01003801c9860f135615401000c60f1058004465162005119030300c2c503440b83c00020006041c58020a4694106400380310017450b821060303150242c01628203114501d00780c1c13291034640c001442401c074407110014008841000c14080791503210b0303202e041051009104003690101450403034800c5400d0b1a8200850f0600da0001075441a111000b000000300c407044943d43c240000c0f0510015040d07100a000214159070350f50007200410714009543c84180080e800018a503410f81e00f984014000d401c414840d80c0c140101c01c1c1c0f414101c40040303854650201101044151041c614042e060a10200740e0128441503555080019214180 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 686154829 1250 686153579 686153617
    0x15071d0d140f061b1c090b01050108070c050c0904051905060a0f06030818130c03051603140408030606250c0e060112051b0307050a11010902010801171002040605 71
    0x45680d81c00c030070707103002c1841e850311402008500030500c000c0c0100d0642181d05001c5d8a81241c800c1d0a075441c8032012103082c084d18005114550780304041d03681c00b141d14640165021442c1d16002e44814120491601030940f4600281c24000c007041401030400003017084101c4070445047c941c0e107441c0282e8221986509111038246410454024001901e03000703a203003864508800d030303036110050502d4035143e0400350542000d80720b2505841018103d4240e0b480121721842c2003a0f107801d03004802000b41007410325100b024861100341c03071040ea0f4480d90041d6140d5880d2148400520103000b1141d98070130224030342c03d400c81610042c8801000643c850b10100380015290140213007500001c840281c009072420340e402d80d040506401040c1c11240301c6505101c20075035820045030a9001701d9070b80b8042140015011030341c55007d8101e4001950000080101c1021680001c3c11410180f14001018608800e8040218024040d4140e00110000f08550340e642d10032001c0c05640100d043c40c0c000041e000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 686156079 1250 686154829 686154853
    0x90c0108010b030117010b060d06050103230726100501080a0c0806060d150f1d0910050403020c0a140a0807120303090f050303040605060f0315071d0d14 67
    0xa115181a07800340c011440c03d6a0030019810790042e00c404000503c0c1d0740f181c4200d5a15111403004002c0d14458000218880d410240094255001c42401c50030040400d00501d2043c014014070303a030445107a03e808045030040e00c0c4803141c0c055a40d10049000300c00a020301011300c590200010031a0402c0e03c41c0354155540c008680f003103400003a80c0c003012030b11010001e590b51528100808443c50804000101264580c1c2020b505003060781028900c1c03044208148a55080c0c60394940980c4040785044480713151496003079483e0407842c01d0b002c3c20192101d012604041c028410081d0003480501035044060303030341a010701040390b07900e01540242804000422986800305284041d81d0b01101c840350200c0041da4110010000b2050a5440d21140e41d000000124184015400b03940a28808512030400030204204800103030071291090f8080480105114401c1003110f500c0000c501f8000017224107070b50714014803001003071410b502551220040d400c100d600014003850344100c1d811124885404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 686157329 1250 686156079 686156087
    0x10f080a0209070f0c06050a0209030105180a0f060f1b0e01021617030f0406081b0a0c021210140426042313140603030a0504050d020a0305030a0503090c01 68
    0x100c20040d400168507070000300914080c1d1300c103000da1403407490708852810340e54407a071080b500107450708800560001018041403509020342a04411808c20001030030442c5142541e840081c008000c02c03015081c2c0d000020b1040603172015040b1144a9010712540d66040f004c0680d00003e0b00c565808515815520305255200203442c00150541040072000203080580b41c20300d02100c440401000d120400c03051542e804036102038401001540c4800c01141445040c03011b00d10044808a8014403052204000079540030f0070424000e41c06a8940d04005200c501ca64148407091520100d46428120742140e10b58210944521890051890b0540c09192100c6002c0081108031007003d00d001c00d0200f40850071015210300c2010f038204400d602101d05090212386418002c400c0c44120540e60301c4a00c120481755101903901c86411070240d490202081d001904a000720b000d203901607003002c8403000840d124003160300301858101044030f0b00c4c0e41d806280100075910442d000101c0340602c050300250340d400303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 686158579 1250 686157329 686157343
    0xc02060a050a18030e030c03030c0f070605180d030c051f1109010c03080901060e07171e0a110408070308070213060e04020904061401081617100c2105010f08 69
    0xf034840440e01429946046440f8242d07000d0082e454040c02c001d01e20b090742c0c10001003000d0074280000d080c600c0d042c12141414400c10b6800f8005000c410481440e0500b2402003031403044004035045072105456080c00c50700b9020741c070401001882207202d115032010325140328550035240300c0014800b418082450703c00b1805002c0c9138502243d05080c841b8000b90103149460307842040007000042035030f034813146d0381607068041d60400089880c0308048043d8074000fa00c856404010300c40400c865608500340302c0c0c8144c0000b01844403a56a9400210303403405814203c2d001889440104d030003254403410910126480504200d01c00c81400e580350040c0086401f8840845200d42d00140380c1ea96642c00788000e40800034821200716560b0b00482094401c0b805801e8064030100f002841100781091001500000700c1e0003100c2c040ca08030040c050313441030016121913019050340c40465070304910311f0207a4680c840c1d01101c4c0000e0340800e2001c0d40341180c1342c5c080d0f412501c1c49001c030419603644400650b12441 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 686159829 1250 686158579 686158601
    0x61d0d050c162907060c0e040e030903120a02100609061419091815090c1e121103071503060902030628150c050f0d08070f0c060c02060a050a 62
    0x5031090f4440035640c41e092001640d03000c8101028070f041c07019620001118100800701010894686074003d417818284035018200280c60021450105070b6000a40c0c1c820900d01880007020001505062030b41c0309000d507480c40c1c003007000e092260503140c030354101c050000350007014440d01411507001414a040f80c030703995002100c1251410001d04017440200904150040b11202c84044860301000030701c0ca981011118800d510006541d803020700c0c050808803215446222241c69801441509100c3c0c0d0048104890050721130302a11005880c1c1f10403e00354038010315034180a12a000a22102100e80841c00d4049956081205170b40701e401d204109e00007907400c140c20030801c80c100340c0d8610140240f003041d100e0001c0c03003521041e42e82a1028000414003a0f203400100d4480440e400c1140c03c015241800f000c403000380540903203440004041440c01440c2d00e040000e103003184842a805407107102000c0d074020b41c082c040301d04405000307580c441040d507204940d18a84000130b01c1c100746a1183c038410903 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 686161079 1250 686159829 686159849
    0x190c0306081c08070c020411031e0f0702150a06030f03020a05101104090f0f050a060302130e060c130f150e030a150e0312040b0103150507050304061d0d050c16 70
    0x14407210011500e141040f58126040780e40c40d030308107402d04801c1002d944900d048003072a0a007020742b2a5401400c0c1c8001e440c2c1c0d07900c11244401d05c8011030300440c1201c10b40b802504620391036940c000443e000340c4050340c07014000180b00c4140b40d0505901013540c800040c01481220048221401003e084030003076007204150150070f2100b0b120168258020350034008a800b40812000740c01640c0d00b007258425141d081042ea03981008008609103407415511480c003040d800c200c0c0e408440815501c038400144000003e5400040f6071003906103c003900b00140040003155140962900265a9003442000550000c05c104200040c4c02d8500020030341c1c5c040e0752162222050320403c20340340002e03161b000d543c0f81d61400144070754400d8002d01144503120724047da66050180d4514180000742e050440854010700c4d0501007002402d5401c841101d4109a2183e000241c404001c0041170f682c01215803082054064401c4419005600c44040c020801c0c000066a00c203064075440c1d42900c609070b21034420f581d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 686162329 1250 686161079 686161081
    0x2071e03080c0c10050c0d0b060310030602071718010801120c0501030509150901140f01230f120a031116031202031603022a06070b190c0306081c08 65
    0xb8600e41009485001004022140c000500b020311005855086402070042c880c00300701000151000d0060405044043d0f80080c518100405400030010307150001800003500010090200401d80c1200d250180c003000170291140002d002d100740295002c605940041d0303004002051303d402d0860180769681d44000380209580c5084015805004000c042c509180a00e581d4880c00301c081c100118494290b10000140d00c440c13041c42c444080f10081e02400f4184002801407014092201c01400443c801c0c5800d0041484901c0000324081d810028150700505030340070070358880400250b00241c0038400d0b2250703481c0b0050314441d1503441d050311010a401c3c40c0e2407181040482d121008181000340c1e0b80c41641d02d4912403060307040396020840d40c210b0060f1301203a20000c02c0355800140d01900c800c603949100310101d8601c005401c501407240c01400c004001e5011030484440400b0724015881140e000340114104e04030003900404c843c1c40b5000c9240202c00400864400100c0d1040c2801030680f504c0c1e01d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 686163579 1250 686162329 686162341
    0x10203090f040e25060201061523160c06020f0a060506030c03071205011401060504094212031b0c051504051009050303040605091c0602071e0308 64
    0x207590074030003450380181e61415203650310f050500c49900c00b2250b0a6071408610503113280180e05842c6580260116454040280201300c00819078142d2030402d440c080c00300c0007000911104410000000c2e00151000260200110049044080150b40299000206a45d60311400d81c0c0381c0c0c000007500400c40e000400b403400010681d0b40b00c90340046d005000c42d5100030081000c41d280407400d40001490300c80c0c1850800401c5400d0107520780520b0085c0040c9819403403d60040c11501450146041c030a448400c80d691100c10344441c480d40504826500441d15600c109842d0b03510704070120569000041400455110814004a01d4150b4959110340c1c1c2c11034070b080c089003d24445801115000340c0048001940d0740c4440480c1c2d0044000e00c0c000d80d5582c584410458980c5881e0208401c0c4440e14004010ba03580c04400d45040b180c450600c15621011500020403502d1035200702c00444c0c002c01d07144824410b1590107052514401c80706030340e002c440e540d41503480c03140340c0300b005000030410070000706 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 686164829 1250 686163579 686163589
    0xb0f030f060123060309030c07060c02030304170c1306090f14040209061804030807081602060a0f06120503030403140f0f0a0c0816030207050a140402090105040812040608100501020309 81
    0x24500204070f009206070740b400300c0040d045078425245003d250740040b448804107802489000e0092986042020103103100d540822740701e0065100f055507070b211252403000c10a20500403500d10380001040703600d410388504500002000701d8042c031081d1514002d00800c4200c0c480c0304980d1280d076490000c0d0303481d90f034039800c0001501008044a8120400500304440c1c0d0210345d00f85c90003140710784c031417248516000e14004c101e020f0040411082d940215002051240c002c1500d940020130f4102c042100561150301c0c03409445582d1084000181e008500000e02001002860050f4825900c0501d4000700c1031a02c59a409650b0030464503007800c00000802c0184240104034070b080c5401e14015120064235080e003150404a5880b1202011425800c209039040c440403014040842e008510785040c010000e1110740c140c20020b0080354009468000303030f030080040e50000c0101e602290742d4004800c48032042a0003600c1030401181c018404030b00281100c10f000000d445048e80214201110401005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 686166079 1250 686164829 686164859
    0xf0b070504060e04020714060a14060d031d03011b09031424060102010f06090507170c070b091e100b0a03150203101802070b13020d0201052b0b0f030f0601 68
    0x4560409445d120b00250a007400014030949000c040090251290003041e0350840000703050313300c50300100d0078000009412012403400c00c03018441102c040020000401c0c014200e02490a5804070038800700f20000d5030007010002664400c5101c0801c00685060641e900c1580000d1610803040c0d0700312a02205256a80566001d07605100108144400340b041404892140c7c2200304070545030303002c000002d80c00c200d484002c2c41c1005500300942ca042c44010b1080c3c001d10f100141450742e1100401c001300e008100c1c20815901c0000c0800d48410115104d550703403032018540b5141c0d0f6003010100740c141e142000c41801101e40120a041140303400c005130300e00035800100142a000d840070740202c1c100d80b9400c14004a8016010010f0f074440c0d4500f4000e02c0c8000c01420012409004071141006807140461000d80b15030a0130b01c2c94681c0e03d02503180031003202041d902d00180d0090b14145020300100d4101c0b9003c554143d441e800c0c5901d4207000d05032540b1f0701c040004d00991100c00100015001c02d0200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 686167329 1250 686166079 686166083
    0x40f03090e040c03141513080c0105090703170c1e01021b060703060506130e04030c0803070e09010b0331020901080a0b0105060705100b01050d090f0b070504060e040207 74
    0x840015407107140c500500c41081d036081d40c4a040d0303e0300900c10401030400b60f0405000110007012803613400c261801d030001c0c00603d4032070350103601003203c3c003046011003d80304060641c1c0000c6c0100c1c5403800c5015a1100c0c2c520003520300107425402d11006030380e041c0840d104c031b49040002e081001a03451001c840300ca01000c2c035903865035081001540548900310031300606280d0b0000f80c034883c1000c900040c150b45050300064401c1c80b040206e0041e500c003080401d0111524490181e80c1d55403142015510020005009000c100002041042c100da210200040c051001c440a408907601c8a60000b5140401c0b0342d00d86010703102e15040f039940c4840d4014101408550300040d0090b21042c0c1c08a109040280d0004007564400c64260042050400e0700c1405400199003803401c1a245490780c680c0c450349408412501076035100e00500070b03441002140e016950b2514240464181d91400008840c000d000a44100d56031f580450701d107a03c55411070301140d905030b99030100e15200300e040000951100d0700c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 686168579 1250 686167329 686167337
    0x91e01090f1406180a060c0c0f0c0e0619050405060f0604080313170d0c11040606030b150a08150d0b070e010807180308031f1203090801141807050402190219020108040f03 75
    0x8c43c100042c3c001c89201211071181e00060006403030603114120300310300940002c0c403500d0004c11a0300c1c4440d50f85039100841d401100c02041c2ea840d00400b00744010040451a50081400140411900400801040140351a2424081003560740b04030844503c42000f00c40b441e0b400c00c8110030803c074420701c60b0b48031081c015801c100003481003600150445040381c1c00031004c0381d00d50100a40d075140412030052a0f95040e040545049400a0b0061034240d0041040c0c05030401400025a00e445481c00720306103030344c0040e03c0b03040c03401c00f2140585031541300488075000400400005c0c064a00c44c142003440c0440380e0701c64400b014107594881016400c000c01d44d40b1541c00342000704049043c0072100758018401c020080c03010401900340140b4505550300b020205a050003800e8500d07100000455901807007000c20600300302c07a0030614070705143c4a5071040303900c18008a25092564004034405040812a8084501e9800408a00c152002e010310010f400710750204002008541c4840d0075151441c030902e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 686169829 1250 686168579 686168597
    0xc180402181503010b0906030d080c1e183309190e0c040b03011401110d020601050103060f030510020c0709060305071805091e01090f1406180a060c 65
    0x700d400c0751a5044070b081c0d102e81c00c0d5450082c281d041c01c1c46000070000090f507030020185009808240e503120945681000c1059000005020708225411390360324503036070303d41c0f6100d404510a14440a80003400c0c014800c61802d0f00c00c1035640303800c18141c145544507088803050070b10f003148000c5400d140090b80c02440002044110796592301d0000c1e11410304044c11110400506000d200b03421120010003680400008000c24051215170000b9a4111000c20900180042900380103c8009081c0c803008816445528900419130313401050b058182c62082c0d03402c03c806550381004203070560040c800581142c100000408841c0c2007900200000c03480d000481d40e100c0d5854240b201141d03003580c4207807543d801808042c802c880501083c1140044442030901082c1450500300da1502d18007480786040c3c001003814100c041c442904502c3c11103030070034540c07642c0900785d04000c0c07400f03140800280302c2303400784c030000413603011030b20440b800020800b000802401d900d40e603400300100061006030083c004c0e152 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 686171079 1250 686169829 686169859
    0x10050603010308030406060b072f060d0c030f0902010903020409020a1502030a020d0305060f090403090801110319020f0f070c030c0b07052b26091e0c180402 69
    0x600214020341c4210352141e540d15140c20050101d481e2604080751b2028200083c6c00407a2490307075003100c651003403001103c0007110044030700c81c4c00204212403508410301040004000100b5804030f00590b0f15900d0070f000c1910082000c1c0100d445e070003402408940c0d040c03801e00150410754406c0a46510141c00c007409951034400035006201d03d0107a40005030f01c00600c02c1140c07941030141c401c1124079803c0602117030401c140012030381821030582031700480c0d407600000c0c00e02d8440e1100100910081000b007080c1d03100c180200d106a8022640312110b0407880520f0304c1d05406901c2240c501e0f10416840c03d047c160564407000503a8402e1a0a4407415041030001c00410140c04262006022181605070345607094900107082130030907070103000034174144030280d8007200b0305000508420307140e417510300c0301c18001940c203040d01c081ca0b80e400c2e1140d040305010480c10079400261040644908000300c031014624011465854010200042d0070032364060390920225042c1003c150058401002c9110080e011 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 686172329 1250 686171079 686171089
    0xd05060307090e0a0618020a09050712050a06170601060203030117011b030b09061008180f1c1205061509010c1a0a0c030b030a1b0e0103080a09150f03051005 69
    0xc0d0f40f002c5195001807801e01c0400c400c40c81810206004d60460005420340d9400251910722035210b80b40d13006403240300182e9800c1c8151380303a0045c00d4480d4020495410651081401071032640a082141c00031600d012480400025130300e8101ca1150380194a141c0c03d0200c1240c1e80142c1c0e0045040740d40d02c1d050348480b42e44950909198031445a5400583c04210200300030f08000050203042c061503176080103a401350760101000b036122034040614240c00b50141000303407424210410101c401d02031002041c8200814042d51103840d14590340c1c0c84180c85d18420072000701c0310305460f11540440511114418a81c00781c01424100d64141425003900c1025203d02d00c3c0192510040c165180e404001c0101e05401c51050002e40d24080c0b070b0400001c00800003180d0340303a002c5071002d0402e50748510b8842071040c00111860243c01443c00422095940340b80c00200b036000314040b000410181c134008118040120b00b9285246440d60360303003074001515002600241800351441d104404503003808580c039224 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 686173579 1250 686172329 686172341
    0x70503060c07032d031401050d0302060103080a141914030907050f0a150806030106060c170315060a020a06050f0c09010f140f040e0a0207081206011209062f0d0506030709 75
    0x1158070045001b15943d000388034801c4058002d944180b0300902d400e000329600141c00b50540740e000312280d0355070754101c0b01690500348115600c90b0044000641142280c18180d00406000581c0c40359000c070b9603401078110140c00f040707800c04d5099209a908004c0b40c034010310380c0300603180094450812203441d81414400040c1820005001c16041018054070303080c02d210351801081a842c1490b0342d0441b80d070b03451a01c00760003900100d440300040041001c204440f001c05022000041031103030b80e02c0c1e80d190041d454541711642030716070038038040000349801c40065a16214490000c03882d45000c0b4400c2c015560300440246000800407400b04842c0001c03489401000180203a4072a651240e2a00a500c1400c10300106060449801440b0303250006400c007050310340320b02080d00d23000d4403961100012100a03440500d400030503400c021151040c0300407580002c00944544458004c101211100c500c1d4241c0309021103c080d600c20464a821502c941d800550400740040564503041e40c0c4a69641c16542 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 686174829 1250 686173579 686173667
    0xf062016020a1a090402030a15030b10091125060e0a020a15230c0d0c050c03010504030f0e030705190e0a0504050a030c02060702150903070503060c0703 67
    0xe104981403095107802c003448002403075460481018003c00d4402207a09004e00c84540f03000303a4021011801c00e02664000c002444454518200c4090366810111000003042d0b41040070b100b07508401145500d1107018060784140f442812525045a1080300c01c1010705c0d84000c101c8400407200a40b0015000d4010354101440d10300c000d0002e27070700740d0042101005413a07004540c80423a0031140a0210b4000354045a40d00c086150043e8007030201d40c130201c5902c42c0c02400402c03400b0341030300004e4641c2c002984601c0d80d8095404c4410103d100c00c103041c00c0310000d0b03074090081040266130804a1f889941c81683c4120050143d5284d80d50b5400170070001c990309411110b4000f1110001d0010765406100184c0c4007800c03000520450600341c841070b441e2170590301c02a003000f0060060400f5511043e00711081c10b80c1c058180d012442080300d1420540d000b140880380729020b2488001841c0c5000141c0500400c0380c100d9191a00c0b4040d40c1c00c0c0d800c80840404011000c0c2880c4c00380e4504850031401c0d02d1118 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 686176079 1250 686174829 686174857
    0x60e010203181c230d0f110901080a0b03120c0604030f02151609181e0b09060f010e1806181e090c0604031416030f0620 53
    0x10a101d805841a59058900010030f5400284070107103e4904141d001c20284041c04c202014190b004000e0140050040d452095240001051061522035034044007080b000a0380400c000014140002c07020b10500c417005001070400e0021446503902d5078010743c00b09800038100c400e8250301c0c641141c003e41045410ba0107507000ba03001c01c0207050300040040300e0b4240c02c3c8040c01400c8215490200710030006001d410420701030b21a1808000c0c014081d1001071700201c411a09036030b81c42c82d40300c4040c2503502d54010f01107841c5e0031640381c04c070342502a00102103401001d40c0100c1d65440b040c09000c444d0541103504006225a9a200c103442d41d0b61041000c886880c5105040e140078028420401e0308000c0486600186a080101c540b15040004950721030349a084000c680315500c445217042140141c40b035000400103000410000cc3c9403410b0250340504c4169a070301807000284031080d40d26440702074a07606041d429200082c03201e07840b030444980440003840d44c87c1c06001005100d40c0001c0d40707a00c02d903 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 686177329 1250 686176079 686176081
    0xd08070e031b0a08010204050d0b04020d0b1501020d0806030c0d020a05060a12051b180f03060a02041a1602091f140102010516050d1505030f1c1404140d060e010203 72
    0x60f0030030203400000703490b0a030f000354034051420700890034120002901502c81c45c0030001203400c40d61101d040c039a074543c1000d00c00140e41001c030280b076400380d0302102d22409442441c0c060310304a4090500c01e4428a001005064610708420500c107402200c80d03c2280d00c92400b007070108681d600d0304043c01d0198810382d1002000e16800060104448010f07218000c101d881c10300c00007040c1ca0000444503401c6603182d1502101c44090040744e0b000908040450b414010307102048104052680540200c0b5074180e051103103000038505443e00d0344910300480e0b81d00902c40006202505040e801250000c1c0b020440260a0540d21541313140040c99400c10880702105021340d081541c0c0c24020309400101e41c41c10004400007042006d0001e2281c8481a047d80d40c82d130240c0c00c00c6040740d111a10081c240681614003900386458400d80350b480041181c030b120007000103000101071180301c050040b10400a041403400d0b083c1014440312200301e008542d40400751941304000103506000320f54401210400141c1c403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 686178579 1250 686177329 686177383
    0x1090b19060902041223070306020d09050f102307030903020319050a03111c0e0102070b040803100e0702120d09060f0c12150504051b07030e090105040504050d08070e03 74
    0x80c0c08040c3c01c0341b01212411508141e0390034081440c03c216030340030800507a40d40c6c1c0900390901821218001a0a0b802403044642031482e010448003180100900c080008019008090343d220f101016001c0340482d40314000344986019603c180c0109019004a80c10500640c1020301c00d82c0a9800c034400040d000f091a844041c4c144c0183d0781407020741f080541c2040340450411914240d0341e429942425141c0c280d6880882085d41150381040c6c11100c04015441e20342020784c441d600c191814410b050f20310000042c00440d640c8020700031010382d03014200d01e074403502c0540e429030410741c40a2402580c030103602000030035511981d60035030300e8090081954505038070003401a01e540100f005c000c0e0304068007440603410b81050141600d2048400003402d80301c01c0c002c40c0f05805030030521020300e90001400024103801808070750318041c04a450390012380e200c10a2000b51841a00e0080807a4851800c038604540121503d9138000304038900301d500401d80c54002464060b40c280c40940003141c000b48189 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 686179829 1250 686178579 686178593
    0x9050d0302030a0801090608061512070b0910030209010824220b0609130e07091d061f03030804150c1d0409050601031b05030304030b160201090b190609020412 70
    0x80102a1810704001c04c61a2023074454440d14018030135003444210030516a0255102045442c0c03c1e20320408032a4542e407a01051402d66101104242c8600341001d0002406c0740709000301d90300b804042c2d48951b074903164000006a180382030410080700380031441980b140394584e40c0c281046240c18690000003243c0e8800c2c0314040343d44d448075403401440300300125181a19015075504100b2408440024402441100507041901c0ca8002014803401c03c810640c501d440c440030803282d5000001a01c1c00342c1c40c1d401480d04495891803080c18007001c0c403002040400d010f00001c0d50b11031302840d4a00882d040080b914070449036594802d1010500b002040041300310010700c0f01c030070700ea0251001c22491180ba00d85030768420b4144801030940b845a071490070030303000c0303500144002d11020301201d80701d94903860010040101140c02c640d50030401528029003600c14041c1c184903d070881c180c0e1200382c450f030b0343d00750401481c03403a022040c80d2100030008906410348000d10080c524111a20445640303031801e03030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 686181079 1250 686179829 686179831
    0x2120402043603030b0405090c090c03101202030c10090906050102060c0403080309030d0c0c020405060103020324040b06040305010603110901080d050306010c050a03020106030309231009050d0302030a08 89
    0x3441e00c0c84110a070b05040b610315a45140c805a0b03540c0203540803200f441e08902a00344c00c10340940243c10f29091054004001030ba2400c0c04104071290f208a680341c1340d950030540012107502d00b94850040f8100082c3c00d901007003c5583d4005020b0b40c2e00c0c0c4143c0c03004200d810882c070b40c036580001c40b030301c004218480144c49018060030007403001c6c2c44181051a00d1442038011408050528240040030030401c071010030488000c0410120203024841290350080d0005a0b040400e0b0300960804000620662103442201d00c01c1e610311200000d010040d00358003550704003d10b43d50b504a5943c1840c0c40e03a507035030b18001e403004601c90800410500d0462500f00c400c030000d03500300c5005040701c5005011b00030000c260039600009514040e9140d0742d0304001220041109034024083e800b42030a60014543d0641003076003a20701039115940c58680d203150f29001c44c2240402c03212490303403860141034a46030511940300b11002c80d28104500740d84602c00142c0c0d1840794001100960f100140301300740542c20080c69 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 686182329 1250 686181079 686181101
    0x6080114250518030a0c03060218090c0711040b0604080303091c020607080c19050a0206010807120201030f09050708031213020108070c0515010803070c0b03060d030c14010212040204 80
    0x14807100209031005803090066418226036148102e8054600391001c100e240249030b08038418540c1d003507030703814003074003c2d4030680180800002c13003041c80300303203007011012140101c030160b501d07528103002c545901040da044880d81981c015241c00e98807d09640c0c5202038030181c01c01c200074544e44d04108003104d2030905003a40e642e000000c003000c07600355241c0208995910044506069050750307501c9120403070340d2180d43c49403401200d0203a080d02420342d101024000240c13958003102d6183e40c981c18050790b1041c1c107115540804a07006640e400651098001002e042449100410b0344022030752240d080c440c0b02e41101103650b102203589140c1a1080519a030441300304810158828043d8000034101c500040850b0140541d0071310301d9013000003c0054444c54901000d48842950b151161305469522050099039a003c0c000300208010a800341103d0003088002c0600c82c2424240c0d50903140e4160980e000c0d141c1d1801c60440d03081641007800102001721100310030100c1880c0501c1040201c824a0303500d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 686183579 1250 686182329 686182381
    0x7110319020c15090d031b0303020307451a072015090607060e0106050312180f0109090504300926070803030402090c031003030f0306080114 62
    0x201141c21801a0101ca04c0803806440c42805812541000d41d552080b020720b015660f80085807200c10315516902860084090341d403101d40c0c00b0b0a4461343c5114000703103030000c820310020422041325120104e08581d085c0cad503890044042c0c1c540d2000f50340515072900000e44101200010800c041100e0302c03000c605040300d031400c0106802c0088010a046000c204083ca80101000070b884c0c4290390341c00f0981d442c65500203014413040100c007210501a101a2140d18040c0c41204011100d09109900340c4800c07031400d11030401d405024004100c1242c1411070b03a64148040740c40045008851401401d105901900c14030903040100d040515044820303d50300d2880c43c1101201c443d0455000c2c900d4400c98040b109003c001d1041031509a101c0080142214211301c60300c0800a44148040040c52040d4001c81e0440c10503510b490034120703d48011104405001d840d10400c2c00003d0080b8021541c5504510b4000394160b150031009007180c0585400b604002c2076501004143d0b0079480055402d0312802403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 686184829 1250 686183579 686183599
    0x130603170408031204110d060b130218040b1903050d230a030504031115041205031e0403050403080d050a0606030c0c14120304081210060c060507110319020c 69
    0x3103042c0c43c0c0c01008200c1c1d20402e00440802c081c0103080300d110840a0b4000c041450b80c0d82580b030224021302d002c011003402816540340f2260b540300c25100b5a81c0c980860700c001c0c28204003000c204030003002650b0640d580300e0800c502c4940b80406014851020314849c0008061007480070101400881d079188040d10010221420751749000c08400c00c1e94090381c810700300421540c43e146001e58000f450542e06107554402c2500d40090000940600f900640c0110310440141c9000c0004031094070040312464140c40e0707040612075002000703940e45503005000389040b906144d1039543d600d00300d91083c00640101515070043c000d601000d4801c6000500c0f0038282000f0745d51503035101506100b4601c00144c11106520b5000001c2c0c241032145440c004000101c2039528606458a1581500100e6258203903d0403100001c41c5110b01007030000c1602e81d1b0f41c807540c040e40416600c14007d071400074000001c001c8034414400d0b007840104042d100c00f111003000281c0c1c41c00762440007031825610403441480b070b4408007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 686186079 1250 686184829 686184839
    0x4080c01240b1810090e0a0506061b010b0406032102060106210e060c13080f0723030a050616020601050609060903070e1f06020f060604020a0207051306031704 70
    0x180c0721040b10345030b11140d901c0d50107080808241031211080c00c0e4103c2c0244403525040c0e42e00007401d0003543c0c4141c41541c3c854584520320750407241d0844440303800000030050a047c1000203089134441c07028540000c15207407a0140410140d07034965200b11602070500c103ca440c1d02284841d1504d0300716480c070003030606624110000f4101c80a403580c0081c2090540311080c1581ca00350440004000000c00b21040e90914400d050015402000c6440301d55100100c04a020140440c240300c80640c107000803d0f90505120b800440c0e107641c1c804040440da07001101240340d0300d00b0f000c8880424000c50243c441441e2500c107140361a5072306038a4200315004080140310700e03610744081e107000f55820303103840d52940030f0307100802c4c9406244e8005215002401c0100201c515120100003031007100080e888013103e0396020140e81d101e05044126110340c2204c40003034030301e051039800303841a05a9841117501541e0355501051060341202000540184c076040140144060115040d1007031881c181c1c0b0629080c541 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 686187329 1250 686186079 686186141
    0x1b0d09060509010c02010e060c120301050103051003150515030d0c0b060a080703322b020d180b0409020909130203070303030e01020d02030a0b130b13050a060e04080c01 74
    0x3104000b0306001c030f0031495411f82d84401040d00c54035601e4a04494440c03856840400d881c0d0805d104050009060400081d50f2502c1800b0040c112a40410b941d80842030170304d00302e005400300608403240c1e45101c408d500d01d02d550070050102c002e1882d844001201a81d4240200380340401407a050081104100070459003100003907a50403139420004140d2540903100308a942c0c03800030040e40740300c80d501c45d0b940f010005000c9400390b81c094003603409070400300c2e0f9070111950203840b200d4540090307005030542d400c11a0082e0b040d0820403205111100810380c40380000ca0454006821003000250b001c42d502800d420880c1c2032a40000030240544080780090b40000d55070303c19408010100b503150341c2c101844c18000d4050383e900644102e015034480c90100c0b102001030174000c01a501c241000c4083d420428510b100740c00d4003c40107000c11648481d42a0b0b02e0000e130802510031800035645050010301c408401c642c203030181c0c0c0310310b400300d0b130300c4081c90001401d440c019124440406111000864200c4032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 686188579 1250 686187329 686187347
    0x20a2403181709030105090d0e01090b0d0c0c060c030213050f0f010c060b09150126011e120321020f071202012d06060503060f0f061b0d0906050901 65
    0x11040c00c00045900209240b000d0b40680149140c040d07017071105009100c10f0100d00b80120044955a146084140742d0044440703041d94428818216001c026034a041103460b006000c00e80e070301c1e0a10360302d40c4220341e903250101e07143c8041040000781d020a0241258003c0281100105011624841c40d085070b0400600d0000d800000c003414001d1490b900c50801c2201d03040724441410090000c0302c0c5141107a121005507500a262a0000381030281055207a5100c500b105054441102c05010503030820210b22030342c400500325440442460707000001d420b00170305a05500c583c440ea503203110130340d0658084104c00007040c0000395801c0c018000da5600341403180c1581c54184c0c20078541200d82e00050000c1c0d004151403803480990040c40ba0710301c40841161484080d0300c2107005020852325607a1039042b40d050000f640c1c001e50005801c28104c98628108896603901440103000c2c42c5441801c1c1552094a0740d410545003940d0401741321804440d4010441034010700860920a02e4120080002405500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 686189829 1250 686188579 686188583
    0x3030901030518030301241701031101111c03140405060708040f0b0721061404020d0212010810060e04020105030a0e0712030e0a2916020a240318 64
    0xa50b0b070b40014800c0c0040c000440c1e00702c250750300b503907517a50312810001e00da5581054112481c0c1d031044488006544100502014114940c3c0308511503420342da6a961402c3d108562a41000f0740c108091141100074001200440410081321030f07401030882c1c0c0030f0161403074112060036a0403800708020210f1004a21550301441c10f14050685544502d86040c4d00c0200d0a40a440c1c144018108400da61b000492103e06602c1c149050301c084000081c0a02903441134018540782e045100364070702c070a0230260054080e11803d140050b080c01032440c1e6281c1c00c080264041130f5035501003101c011003490309216000261003142004c400618203900060302500c0f014100c0d114084d55030780704541406042c040344010340446d4203102500145c0f402d005000b84900d04590388100802c400c005141c60440083c84c1c080134030003904288074864207011480c181c21681d540403102051110304c000580e58004041c000d40b000030540ba041c100e11450a0b032105034840043c800349860000542d06c0c0321389407000404403035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 686191079 1250 686189829 686189831
    0x4030c0b0a090b3702070504020d0b0909061b0f07031d030706030b04050a050103030e121f0c08090c0a0b1309050a050402010f03110a141902010c02100b0303090103 72
    0x1688034008031942c0502e41e104840040780440c0720020020402c2d448480212a03c038034a4488540103040c0030441054294440940d0000c60101301030304240c0c001d85111140d04000003841e031030b014042008140c0c11541c1c403083d40c1001c800c1203441902c8030444841c40203c10740c10b17800d01910904c041214800c408020303003444071812030b464458000352800084c111014054840040c2c1d1450041c0250995400882c030990070000040c03500c0b4024881e10b81204d8150b501c0084200c581c0061007005586030b80031802a009400c4803c464610380110207072845000d10b0002120710149030000c02c483c8025140c000c1c590030003552101966925003514058600405005590307070700b041c148106404603517100f1951581844100640820a1f611003031180d4002e032511a81810105000c508440ca030a0034014004018003403212070501c5a50300a032401c022210440c81c08100101004406400c8062000141e4403240d802c4603484c0e041c446400c28085005d800d021001d031800000b51203001d024541d80c105 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 686192329 1250 686191079 686191087
    0xf04030c061d031e030c0a0302070f0b010806040311061626150102060714030f06010504090216170a05030c0a03060f030b0703140424020f0406091a04030c0b 69
    0x841410b90212800300459041800300d0524804415200e401102c580030980c01c95200c1008800340714070840344502c69804045180c40729400c402c1d0300a4010040a588149202a105000030180d0311000c0c082d00c00038000f46000e00c0c11b441c00402500c0001180031041e013005080c05082d600145000300101c80b141400a1610a0215a44018203d01d0076a00907121900103010b40d00c8808401c05161040070b0703003a42c500c0da40c4c205040e00d15541015000210080400008004c07000c5040441d400400525005180503642c0000d1426038100310340c1001034001640d820300800882620740c0c4500700e1610411401d101d814200503204c0d00005080110a10002410300b034200e10950016028209800c00007400b151241007400302c60000301c66840100c0d2030021140c0018112401d05441150310421040b111401490000804500c1072902c2807030540034411403500c4c00746d01010740040e0001d41d80700415036240c004420030300c41c0185180c48036131408110600100700440c1900042d601910362055031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 686193579 1250 686192329 686192333
    0x20a12030203072a141809060103080d09080403080309011508030d0b0424080f0a111e0402220918170403060203010b03090115080c1e041d0f0102030f04030c 69
    0x101044c0200800000e9855800103e50000003c0311000d40b49411b80b0303d2070342e840300101d0400d420b00b02514001c0040e84031400420005409000800110011001c0820160b46503500d01c0c1c2660080d03041115007400201c00c00a480f00c00344240305407e8148006114001c0c90842c0c43c1e522817042203500341420b034903421b04042c41c1d1034030303080141e40748021300a0f82012006200341c2d4804030a180160707000f038019000204040f0000140b030b0180240c1105901c0746c0101654204a6046c10f1420058000000d0002d5444603075074510281210342c03404680403003414010138200201c0c1c0581e810800f87d80385400140c419040c041c400c0c01c00542c1d40006002d03130505e0000c0c03a58003207006c0c0d070380010103040c000000441d040f00c0c031901079070240301102c0007880b10843d040c4220407510168020420580d02c81c4550085a2400b5800d00d502103100d1713081c200560b128100400d06071028218410380011891504040c020020880710b040242e00f0802103041d810031030172603005400040e2015041010008107042 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 686194829 1250 686193579 686193623
    0x2070602040b0403030e010206070f0207090906140a0c030608070e040206160f051506060901120515040f0504050c010c0803071d09040521040303050301122409020a1203020307 77
    0x1900070550495195a42d9160086c44841d01c0c40810340103000789408a04058042d11041e014951590043c04089084c0303088080100310001d02524482d03120f28444801c40b20b04d0701120f01440c0c500c900810960303000000542699001d40c003001c0c007a070015504000d45e518940c1650b401c558102c0e040340c0c0d0790201c60010302e04000307203120240c121003044c4207200130008002043c24001035118480501542c55a08101d000d02a0350303d8140814030114803082c2254190b4803ca500c14144c1c6010160341c80d6800114007101c200038141d082050b51b40c1d051009119003000300c1d00b0341e01d2003464101003454560b520f03402c0b01d01000c2c0030300082c0f0640c0c0408e45145c0303901002c0c0102a55000d0300440d01d81c501824810354030303141d440982d03050041a00c0d41210003401101241c080da501038443c245941d20303040703d0045848404100380c914414910308a0001c0428680710700c0381041011001c101d5000500410641510503404400700000e0000c1d1000026004810f44458507044482403c8020100103465 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 686196079 1250 686194829 686194837
    0xc0703020901170c01110d120e030c03070606050f03030d0209030a1e1101020c030a11060903030a02030c06070207050a090b130c050d0b090601080c0c0f030d0b010e0904110402070602 80
    0x2540610864004211039800665100b0040d290f43e040b0303603440050b400190b0300f0004041e5684600e4100f0b86c0c0e00008240500c80100804d4200c0c5000038420a00d4100c05007160003850b0301280c1e030b40000905006102c0540249405088119404c2480008460001e5039a1084130710710848140c0200f040c0500d55800c2c4581c0ca100e5030001c0130301611040b1074411428092600108a0b40b0381d0803c3e1020345254400104090030030000303002002c890096482c2c4d0680e00306048491540603108200310807564030f050000c0c08070f22041d500115190010340c180c01d030030010020684000c55020240800040e0f0301c44c00c1400450b03004210003d9480240008600203c00030149034502c02c0c00c0064401c943c030350100c01480b010744d20610821641c1e03401c0701041105002601d115000540081c007103588800c030a0014038a004801040300d031030400003028603041d0307004143c032850440d982e80d250401a58101c090410342c40821502c4254516047d901c2d000c40411807507107503015540c081810b00401070380390304132 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 686197329 1250 686196079 686196083
    0x10b091e030718150605090d30080703110904020d1b0509010813051f021608130506070507060806180718080d021e16151b0c0b0f04030609151505090c0c0703 69
    0x124000da492746041301000b12003c9110800165a0400100503038400c0c810004903003a401c81e42450305000c20200700181d0414032410070320556a442001c2c182881c503c814100e518140c503502d450351908000036200041c02841c2c9102454000c2e84400080c2010407403000c00383d0014404129a0080c0d80d400009005d000c1e010180d150b8503046131030a0003400809841c45140074030310340d40d0441d158010f01040340145503004000742d03c54481404950700690303090754802c9015040c89420509003410b00030074501035403148042075421901c007120390446920b0744043c09468005005900c51a48003e40e2582e0f0321210040c00b5214507040176400034207001d80b050100340c55a07445803207500c9030356070302010700250040e9000c11203401008189141142d100d102c1d040d0840f5920300e14600c1c03c11201120b40c4103009114071080b08020201c0011490b01c19002c500c0d00078001b81000c003801c10300003021600c11840c001000d1440d200200031035134038110010303070000303404100d6600c03030400d0700d43d00d403800300943c05c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 686198579 1250 686197329 686197373
    0x7030908030405010e061f090b03150103121d0f04050c090d030e19050d030804060f020301090b030f1c0c05030d181109010b091e030718150605090d 65
    0x2032009010054110a170781074030b0501a1041c1e030f140c43c84410560300403042034426012658801300f2a80d0940e50000401c00805001c3e00d59480074a41d001c9444803090b041161844682840000211b40c0442104003007050f0141d65440f061454000441180440c96a40e200b1074a90b0001011071010030181c4410b004090100c0000390098980601030b2910101032030b0103200d0034088090062002d1036000102c03032001e0000621700d5420345080303130f0003440140140c071056200e2511b032180c0303d220301c011402821080c8000454843e1182010f05102282c001100280e00444020b001102d014110158500c030604002c00008141d161031405d40c040c05011040d03042c580210920000d06a0b00c585602c6407151880c0b0b03040200e01810004070307140c00c0c0034945051a0030f0140701514144643c00355003407440784980700b255041900c00030f4035002c0c0c6500021250143d00502d210030255601a0303200700038141d100300300c1103401e000c07005016005610019105016509803c818025440c0f408010100c460328 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 686199829 1250 686198579 686198581
    0x9060f07031116031a010e0f180714091506030606070f0f05010b0a0b0307080a020a030f051f08030c1504080403060c020604020a08010203090c041a130b030c010212120703090803 78
    0x1548504a0b0451005030317201500d00103600b90000000032414140c2e036100070783c140c0d2519080d42450000800a21108400d444000c0e40003080d4002c00200c0001c003040c000b0b54a0b015040d905000c42800050074602201120301303204041540e9840699a12400035180c440d2100741604080e020040d80301c001030107168a0070f11140034843d06412085101d00d065801d80a6103640d003107075690354802100c1640000e05160007180170200150014008040d0601d0013043c102032203401c520480d07100b82e6088010080c0070090400d40a65403488500604003e805981051420400f0b19200c040d81041410520280800038042250000583c0c01031a00f0100411501c0c05100001e23658a6059030264480c0303c0041300040d60910500840703204d0310040010b0400881000180400351118280303002200c050022480036030307101c540880e58032000340100070660b604c0d44014907007828010000607045400c0400301300380c03d100c3d203c2140c0300c141c03d492841c82e40b030355404d000700d000f03216041d401042204000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 686201079 1250 686199829 686199853
    0x200a090f12020906030f06040318090203070801080d05070503030402190f090603050c1c030e03031c0b040c0905010f1206090c050d0e0d0c021905090403050c070b09060f070311 77
    0x20400c1e94418400d807041401c54440c08101951000c011002e0b0200da4442000980028403030154200300d03011500d8480100340d211003070002681c1040381da202c000384045004100344001084407194456907403d12038540070f441e44030301e500d030322004001a01600c403072503030401c101d51010487d030010240c5a078110030450300c440c1d1f660040d20321440140c48503c03400c0d480361828604640f03040001d9031a01c0740004440c0315a58152801d12017501c890b90f05000c24045905030760840c940c808520001c441e000218281100108400c540b594800c110802ca04c0c0381081c4110b036040540001121407a083c400300e109070840156019100d030340c12403d80a4206851070303000c96001400b411030300031822014458500100c0031140e45e502440303908000035041c80038980260400e04601900c00c02d880c8541d14003075440b41e000c50180c4e081a2030844c0000c40c0002c150b049401c003484200060705a2a6404c0e10b41400607001415902403c55015482c0a000a0040806005003000381400040c14140c07a903040c0c0107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 686202329 1250 686201079 686201099
    0x501150506121b190324060804110306090109021206070f080901060f030602070209090a020f060f220303080f0907030201030b0301021207030605150f0d2409020403120201200a090f 79
    0x15070309840110341030071000901d15001400b80740703440d20030012011b40c0c0c504d400d004841d5100c3c064004c2c0e50b094500325500160ba00c09000e564440c0b1000307000403e0200071031040c8001072980e07130384080340d0f50003c000380240240c1c000606043c640841c50100000e8540d081c0d45401403500d54400101c00580e45400010401540c024011442c02102c0040c8141e03560b103000742d1520000f1000035444841040c034403a003444c0c1035000d01403946140c01f915042c4410410140048901e0150038040d01080350702c10800c02d40e100c0c0c00ea0ba40010204009807060400c10f5905030386074183c2c04000c0c14961104003000d0b564034258140c603181d0000385441c00550a019001600030f003d54090035000d43c071803002403084c038480c2d002201c00c110880d140f42e0345891140000c520080c007000c00303a01013039607415031034402811000c030301d1801500014200513510351070352134046800403480c0c40c10340640e410611044900340792541112104030400f40500e50b1610741740000ca8550b1020b4000c12625241404003003242c04038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 686203579 1250 686202329 686202367
    0x1022b0804021f021b061602090c0d11031503030403050c01050706090602120702100204030302030d02070203150412080a090b07140c010c03090b01050114191211070501150506121b 79
    0xa400c11805d98000c84034248000ca208040f15a000304440700c40110050401d040f0007644071448a00950030400300d007101600b034501c8600d50101440c004010301c940207165081802038504101e0045103072605e19921180c1f540b018002e02d505200c2c0c040b421500b407004c42d03000340303040c0d81d80840119682c881c1d50f52295045078003640c3c0800180309110b80c101c0b03100c0443c400c031000d41e6050b80056080110010b5248007940c00700d00102d070103010f030000001c2100e030030044440c0907500c41da40100d40e07210040c2000300a0789001306440b14960802c4440000300300c03550300084c0c00280c10324104071051400c1c015541f1034820800c0c0c10415610382114414100d1303050340862140761080c000340c03403141d80e6030004440c0c1880846c51400310010400419a20000040002860420074204108181052003000040f200c0880c0c8449108000240b010304000c000e01c101d038a0361024000c140d21b9241464080740903030090f51075a07054019624040b40d03600d9000e8000742517600662400b1685c45032003070701c05a05854 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 686204829 1250 686203579 686203603
    0xc02060a21020406140306030a02090705041a030601050a12090b01120b0a0606021f09051504050f0d0f050d0e060702161505090105030a1e050601022b0804021f02 71
    0x450149081032010090003142c040b1035080d41c0d100c5c911109954036540d103600103450168940f14150110006031201079295105212a450300d03901c552500400c08021040d00d0741c81d00e1140810410049242e1300002030ba00208035500e860340c0202880c00005009200f44900600341b404020300009090784240704c500c00d124821400010b036078560f00202410307620304c1d000d40009600440e418000d40d00c4141c01d074a01801400c0004502e03100c064032038605250811003842c203140601020041403200800000880411400091803000e0700c40030028007001900110404000c40052222800a002d0f04101c121100e000d0643e40c140c107103c240070f5aa011060005280000d03c1036002440690b005c40c42032000020340c40b59813400700400011a065800242000301c034560f52002d405041c00c0711000c1d0500c44800c048001001e0411400180c981289100c41c0030300125171900300b000d003907140b0680c0c0c040008a4100603500b42c42e14030020300e1442112113598000540c12440901c0f8542c0010300b450346032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 686206079 1250 686204829 686204867
    0xf030a110117040b0601080601053903090121060b041211011403281e0b03010c09030605071403090309040c0c02030a031d060a2106030b04060b010c02060a 68
    0x61041d503001200440448002c2c00150413240002e15035401040040d50107541454010714002074008a20010800031064040891700c9030508100890b103015400c0806070507200441c207140300c071390000300b4400d0b044241c858010b85040001c444c2e040c540d00b2044c007070304080b806c0c0c030313140d40c0c07102c2e0070b42d01d007858a00c03040c0c07160303800f41195110a50142c02022305180c80070702003e20b103548000c50a80d207001102c101c03003c011105030390210100c0051182e0b8911a0000f8900d5814040f160700202c11754076440c80f0281310f40d144c03150008880c0d0300b0502c10021298480c6000c6004d541e00d50060f40c11800c51441040542000000c011880300044001c00e08141e0481d003c000da840e0401c030840742181042c00017501640300d6420800843d0154100b400100100e44140c81d0f111032482c080341094001c03148042c0070412070126010b0103020304001c0d41c1344846005007008230343e00d15114078003550805400900714030ba070341002e808203074803c0b2403250751190080c240c01e070780d001c80e0080105242e2110507525007403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 686207329 1250 686206079 686206097
    0x110f0a170c03070c200d1514060102301318050c0318010e0708032109152211100e0303031b070212010501060210090201051204020f030a1101 62
    0x42810300341568000c0105a8a0541c01311300b503510300b55100300c0b14111005c0c0c5290410f044c0240d0703542e58030000b8842e2103180441c0035043c8180c00c1105644540c1d440c50400e100700030030001d540e640090b5060540400c416224464102200c01c1d40c2d82014101c0d00d0100d080740003500346113481e40c0c8081c09040f00d104043e0240c0c02481d48030301c0011a4070a4805800c24401040461840ca1048141d6203091000d5000001d1801c0211a202d00c0d00c0c480d41d00a80c841d400200745842000360705e81c540000c66003d900303841c0052821050241c0c50351042009051500c5408002c508070050b01950a01626400c900e4407028000034140078540308036020486200e1162501c00e42d446610032070030445070b002c0140042d400c0d5103031040f0a0304440300380d40f050088844180f00c54030169039060718a104869521000007099414030344000d00b00681359958060040c00c01950340c0050740c0c04411103114039113200c84003800b80c44510010f90044541107a02d075042c0300e03120400051041c40b03c1c203091501c1090b08c480c290 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 686208579 1250 686207329 686207341
    0x60a050117060118020f130e07020f071206150906081b030c01200c0414070905030d020607030b041112010e0106110c0d0501090804030309050a091e110f0a17 69
    0xd03840d400d0150034201c4001c55811300ba060500e4000e070070000880c8112074104a41c600342c90010740f40c1940540040703169101489041501441040c2194062a0140030142d040c0104410300c006d090500070005559562045611019007460324040c10046506029299440e04001c2d0f6485801c82040b03200b0916141c0804940790014144800e154180c407020462084400c1031144040700185400d5607009502442280d40d032039108400c900c0d44030b000c000f26541000032004090b5105038100c0f90080c0d001c40f20030174100e0b0700060219400102e924012402d40e04441c0407601070b22803c042c840420f003010030901881180c180045050301c0541c220000036030390301e640498200100c1162140107412050700d500060600c0e141304414107000780008109400a0b945800c4250700a42c826000140c484d901400f8518210110340c4c01071884800070322200c60342c500308021240300aa4035a4885550b184010342e0501054240c0d5110b100000705580c4618441c00050104c001408050248040000000780 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 686209829 1250 686208579 686208583
    0x41e03051209031b03030408240106020109081206011808010911010905060d02130e040b10080c1e030c0a1707080106030f1502090607150c02061506070212060a050117 73
    0x10316900014028070721074140c0c1d440301d01d001c0704e0007694a405000c1084041802007003042042150b41d5500c900e032001020b031961000480806812080859041c188460b0100e000d85c013f8440c443c01144032507801d611a04010703542908122031044c1811403003100050a010117502c1600101e000d140c00341200b020100044800035858010298000410700040ca440c03151a405400f40403040f181108003161a17212060900c0c50885080300e00e40e03101002c000d041013201a50b40001e02225000300807210800c7c001910042646584603070302c4400100c89200c1e0f580c100250300551038040e2180c00700c103485002c072004440350009101101d1141140008040805114100c12607401c408411044401d5503944400c550304000c035152219005e0203101d805944620003004094450f881106212003c03500e00c9058402100801096400280400c1001c45600065603c41c100031036000e5030f030741e0a81c80000d0166551100d810310512031201004900c185640c4070034141d5032807808440c0e2030a40d110181b6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 686211079 1250 686209829 686209837
    0x30905030301151403010f081605220b2e050c030711060403150606090608040c06050f070b010807240210090606180b0406120c1703041e030512 63
    0x108160300c1040108400544101402082d0300c10389044419180702c60341c0070b00c4580081c0c200850a40b03201c02d08109085080080c01c13120741d170b5a80154049440c00c1c001031203e004080320343c0c81c4201240102c00c0740740040e9000c2c000910006254442d0f4032003600003492498070154403034504510860700440010700490035120000040c80045182c803403290f0342d200c91201e41e40304894121a00740004400500c010300554844100404002082c628002c001000f0300079548c840020b0041c1e0b002400042400030705020280c89542c10915a11a6030f005896407902c00d00101400c40b023002c00000c1a80800801e00a0845008200764048466060124640008100281d1015034400a03074084034800a03044921140d00502000941d6030760b402c1d032401c1d01d00b042c5054050942e961420159585800d108503806400e1080c8461040b90b5aa502c4803135103107050141c601107500341c045040e5903c10800458014011011410003907280b640400b0207503901600003222640140390011410008510642e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 686212329 1250 686211079 686211083
    0x4110403110d140304080303040506060a03030e091f030b100801020a0c03080403120f0b04110901050703030f090c0b04090e0c1806040603051209120a051f0609050109050f070309 78
    0x39407808008401080300d40356070b0790310450369030b02284068500d900307051014100410a00c001b55541c1c1ca843e14015092140013006c4901c600341d6140140040380e4014902400413a042d07030004529101d600407041d00b0010b00070000395030740311035001004210000c0e04a41c0261108207400000b251a204d4260a138084c1403088000500b0171001d51001c20f22032411150054080c1c01e101c00c40c069010311907030a0380c50b403c400100301a100e4600c4131907814507100b80c0368080c22654072a400c000c0c91600007000c9110b4000082e0805071a041119029a059070140c0f1486a00c130240501050b40c88080c49060381203440b41c05185450000503440003000451480a00e20000700340d0081248441000140d0b98006000d030b54106603511004400a0000c0002c0d400840090801c3d50302e5100d07103010802c003c8040320520480350031070504e410010f800000c41001d0f00d454450b407404c2e041d4548031020001c1a5680c00180d509060500000318840240d100f0740c01200300084c0c10701d455503178000940503603043e00c1c80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 686213579 1250 686212329 686212343
    0x1501150e0406291c020417060f01060f031107030801030c09060e01030f06020d05091b1503070c03143f0f0703020705060c1b0607120c050d05100504110403 68
    0x140c6405031840710701607040715a014000130f080c12114808506507000f00c40e21115141c0d0b001500740100c00b4a09428210426102c0043c141442e0855001100d564103100c2c0c1c000388819020310003462402074002044910a5240b41c5880d101281002016088207100964801d0070840b0041421134103809003100348c40c2c282240980d42c0c2d00e90303560050002e881c044250748203035081c42042e59442d014060b442c091022140240b4143c240945e41c41c035500c4603104218415000a0f50383d280d4036052405581e2b006442e401c2042c0a44164102035604c24540a07508004480004068420b03500b210000da2410201d60b680140c0e181980008001c01c009006150718101c1403480000c014004440d170700b1f0f1f40101545005424814030b603540920382401514084800c134000b1402080d6400790180c280008007400004008504010030040c000c0c070f800c2030703020f90541c0e01e402c00c1110841c0a401203c000d81e0b41000c00b00510b151071202d003100007206005051180b800d202c0740c9904d41050000340c40c01d07640c00c035031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 686214829 1250 686213579 686213609
    0x40f03180b0906091c060b131e05070c050601030620040e040b06011101060305010f0507321e090a050a0609170c0d0b0708010509011203050c1501150e0406 68
    0x400406401091031298045400d99005c4540c03102c211450844602c02c0030041070444452041203c44214004041800d91500c000303200e9400c80c007030f10000b00261449001640b40c84980782203c00f2030b940100030f4030500c1442d0001040020650114007401100383d60892807524141c800f2a4521481c480c1200f005102408200413980c5807964036004501410421010f0103050700c050300707481181c0d10076509659600345150762103015020b026480007051920200c1400d0180080710f008828000c4401040c0381d148a04228004040031a003a400d15071410754483d0f0340b503918444e1590301c5000c8003030140345d481d80005007600301442d9042c261055500e48a207500d040c87d1240c540310201d4600ca03d054451040d0810551b220f82e2000d040c0d15000700b81c2d403405441e03c1040034001d0841030f031115001e103040034010803a400780d0b859100e200c0350345131403c143c4d0f40403110410703450521074400b448071b900d03995000040c0440e1a028225041c10041d2950490b030702e0240103b00841d0740500c80c042d141032201c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 686216079 1250 686214829 686214847
    0x5190608090a153918051005031b070b04020315010f1502071502070f0b030f0a0c1107080607020d03021201050103090f0803070c20030a0b07020f06040f03180b 70
    0xc3c01c2882c00d200d010610450684041058030b4041d09104403c40e000403400313080c5a5455888084140341c4d11080005143c03541c60000400d0901d10b804030703079004010005c0003103001d1168148403010300c0c1c1034505c029a142d1a1504251901e040140c0b82207209114040031072950003a0400f001d8101c0b0a80150340031841d144c1540600c0c06240ca910210440c040c800000c00c41081072100c05265007141e40c0104800b500f02070400310a11445c0c4c01c007020451043c010000070141510312254049040c0c4030108819449442c150381c0406d0600700704117a40a55803021440080c0041c43c035203c0d500e1030782200c5c42108a50011380481c4101e0760140b0315001440014031180d4081d07003040d00078034880c00a400d0080034948803004560801e0307421900250300c60a03c00c041c400006034190b0342e17418814100546420300c20010f980d40e500c0d070364000d0420542e80700140b0940d0080c0001103c100801e829515680b81c145050640d8003420b610450101c0c141c032050b001880000003900f015102d43d400168a009141 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 686217329 1250 686216079 686216081
    0xa02030a032f0606040b010234090e28030e0d1a0c040303030c03020309030306120c0a08010e06160c2a06021f0c1b080405190608090a15 60
    0x100c5000d40b1038410034424000b804102c641c0302e0440c116102c06020a41051010001030350b03080c081450455102c02c2000300c04480c20700c0003000c0341e074513121181440545890b078040c1161055201b0420f591500980400d180000302c2c1106120031401c030101e02240e02150a035510680822020300010b0004a400362103050100c0b070051003d000d00380c1d29008900ca000b0394081d00008403104030249802240400426415001e100d05503482402d0030750451800380c14050392400024a042d104800200d80d009058009028202210030042c2064030301540324104103002e4034030041d1101c034610440b00044c080c0064240c00b9106119036540f501701c8c541994460101409081d09004c40d01007034840040e10061181c18504011310058001d8142c06440700744044e035581c03001221030749440c01e01040c900469800701d0101c03900c0a40d482d14001c0d07006242402039903030086400042c0c01104800038003240202c6190944119400c640d2030040742e0752114030f003c0e00c030b11880c4001840410200c0c0094100c03c12 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 686218579 1250 686217329 686217347
    0x9070501140a03110d061203020f0109110f010903060e01060f1e1703090d2a0b030613060f0902092704201003021309051006083c06030a02030a03 64
    0x90401301814000364040f2201250707030300c0c5d0059168211300341440042540500420124030000002086211501c1d2518000002d0707051541e403144002e0300902e42d06a000c2e0b140b08000e90f4010004102603500c10400500030041c902505c10421070030000042d040001c0d407441c01e46004d410014482e0b05103440319565031902501103072101ca0105020ba070340c4544911200004807070207840150b41a80720b100c0b00810b020b0b81410101310340401c906003808043e50742d1044030307007004040d144111002c0d583c014060081c54035822820315051040344c0040c090603c0d801174100b155040712880c01050303405482408083e03415104d40d11202d0880005804104010070b64460803003040380414050441100207000800030900da5404240c0c0480e8410b80b10440c2c0036214003509c50580e0800160a20000c00506a8602d102c2c103010003660a00080711302122010880364900c0c10605001e840561000c20a855061204042904203e00001500c581341c0040d021421a8003c0d01a08540803541c9080300c0d6500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 686219829 1250 686218579 686218601
    0x80f07030605191103060411030709050f04020c061003020103060b07030c0f080904091b0918020d050c061602010201050601030203130605090c0d05060405010e0a0b070e030106090603080309070501140a03 89
    0x110f400c6468040030007401208400f218015186a40e403420104200468800100c9a00d1840081c002c01155540160340f1100b40e03581283e0850401c1d1000c000038019110f841d007800164001e1600b40145541c8a03804002904c0c400d80301840707416200c200c826141c0c01041400740008240709138180c00b15100344040c2d00b041d802101e00c68900040100403405a070916041101d0f05403002c0c00e00a240505850514094603ca01c4184030201440302ca500c0104181d00f07000c2e00c6500c0305010311040100801409904100107080e403503c80104800780301d55036000d004144e0155082c82c0014100d58403a00c201c922820b031007800c0302d050b070801da100d0400404004026141d1442002002c1d6680e5541c4098003201d2445940201780c0392515181150a490360031050340a07680c00651490000f5180e460303850b034400c4c0e03070346411080d96000b8000a409461079600004c0c0451410744044240082c1c0001140b00740da401040b2001c480c0c0c1d581c0112091401c2004d98498150280002170560307209800203a036100b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 686221079 1250 686219829 686219851
    0x3020d090c06050d0b0a050609040b131503060e030a0801140d05010612060f0e0322030206030a0516080412050d090828080601020d0f020319020115080f07030605 71
    0x1019030307456050034038040e042000840c8000c00c00650b4400e89020b4000313801800c2e1181e42c1e1607031070880801c400e03001302c100c00f911464450144407800c6c0c4402e54160000022200c0601020701541d4484007800c041d40000e0341d41d00e081070021120704000004484400e4100c0d0b2720140b02c0c0c0e20b040b004456600e4a80c001c01d40c881c03240820720000c90401d00401c0080e000c4400c83c00203541403407814004461266040a00035030401e0010840c410011081d5414801d0444d1420014005056021001921604001e5210754040140710a850a90740400d2044c103c444000010070645c61040c1c4000008031402403050500603081e01041f4868800380000702058940428641c081c0e94400741c5507046001c0701c0d0864110350300c0d00300c0602030000146900726420700740034009080c0000001e444e4420707003841d80e0500214000b4100d04900c02c00407100100c00ca058611442028660700902070881d412904403031f04803081c1c002c107401c40f01040741c48403204800c0c000c288030f61941c2d03141005000e004003ca4040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 686222329 1250 686221079 686221091
    0x711010e071215110406030e0a0206030135013206100302040b030405150c0301141c02120c1005090a1809021002030702091b09041a0d140d031b03020d 66
    0x803850295210904c07103060025103550501600070b084034400003c00040360b01107100400036031034200403a41034840340e403541e4101d4620001c58550013040900842d2807520906081c2176149010f5005190705122003c00864041003d036104014130150040d000c0792491250128056203094032140061070110308000d400e0640d03440e6220682d41080701e00340d60680008140f042d11010044e8000da21904420b109030655040000c400a5001c1c40422240108000800a20341020046400039140e81c002d112813600c81103e82a507807100c20040d403541c0150400f140d140c210b9030158003503501340c1c1c4014080d6040c4910300b44032006012404962891203940e00c0741a8030140c1c4503646800d02c12040f503002540d031072006205000d41504001d04000100d800b0f02080b50700003400303004482c1c50503821100824500c1050624009c8006180d4203264040410f024044c01c2020403240d20720602500ea0a03035400314582e0f8801c1d0b00381e5440182d8800c2100c0600d0f0052a500d009901616588400050010349 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 686223579 1250 686222329 686222363
    0x3020106080a030909060e0f0c0705030d020706020904050f0112021e060a0f0806090105011d131508010b15030105120705030106030818040903020c0402160b07080711010e0712 77
    0x100703040c4203001c0d0001401681c00b0b001c5e00c034035401844018060405041010b2402c2400c603401010301414411030201300213210740501c0803c0080c1c420440300320f1800c40d598a0185041c400950020800d28016404c04002a0107031101c001c0c000d04032695482e52014020703c40d8200002c0499071060078481610f19040b0f00000d840e03081c0500341242050f103a0164600e841d80000d4000360000f09100e101c1d0707041000502245c0d92003000090460115140060f02407529400503194102902d015140c451401111610001503080d500d13045a400314000c1046426080c240910000300c80c5640408070f508000411503428424070501c04800c1d41001c0c0d4000c2501c0703200280c2034401551040d20005808107048006d92944483c0c50385040c0304035001c10101c065940c010b5101c03000c801f0194450b641c04100311002c041800480d01e10315910bd8510007042c40d000401600c0c00d20251041800107070220ba8000c004103051045100740743c2241d00400590345452001402c5074004801240d07540415800105 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 686224829 1250 686223579 686223583
    0x20c062b0207050c031e190510090c05040f020301030f0b09150f07080c070b0c0904110f04062705040903111606140f19021207030507020108100e130302010608 70
    0x4045208030040c0041302e0341401014500060a0402e80c00e020244440e446d03d0480050745140c45043c001030002d002c10103042480c10403101d0102d5a9a02d03003400301c8081080204080d040a40340124ac04000c0110041c003080102c1c0401d0100401010004044e1404142c0011056501c00c07030762030440c0c250041c1894205a002020f13181541503038510f000b40010180c012603d158081803d07440903080a00782c0c1c40c1d2510340ca02c0034040003200d4900050030403181d19150003142c0360314410118540c0c0c0d403020540c2c0400da903200e44108400244071041c0c8075002100342c4020192400250640c0c1c01103030404041000401d2450800c5040c80100b0110760440340d001c3c014000d032140343c002182001803800704054104080d0708031850300a50b0400c00352038070004040070f4034814400310003404c2106414400607403814161050501ca40440850f9250070140d01200400c40c4038400ea0350200251200d4440c1c04800c3e4460003401000b1840d0340c00120581c45070030700001d45c180648004118a507458801368 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 686226079 1250 686224829 686224837
    0x915020c060c0f0709140a050c070b0a060515030118060807060806030a06180b070206090d03090206070501020c070f150e060721050d11030603060106050d0e0d0f0e01020c062b02 78
    0x106686c3d1145070141c510604500c1c03070340d80003144c0181480030f803400d041480b40c14803640e0030003410245c1d0503003c5003c1d8082c90b445807000d080054803029200c409130701e03084445d4109110b00d054050300d2040440b80114a40a654101e400c041c00134400b00d401d1100c16601940010401605441803800c52404686180555100014070340420508449942042058014010507541c10366003ca424040d12040000700755064085614000600596038400640688500600684070350700200e07120f003103000003140440071507201544000032260340b4180e00010004038407080c0701044140700d80720901c0c141140140b004610401c00001c10950281c0c8502d00c0b01342c00c501042c0092070200b20340320f010341d5a20035102808200000c9505600e001030001e5903a410502428080040101d00507240d40450341145d004121440c05403000c050358920000d0807110b691080e03c0015840d6441054a0350012907142206500900100d141a0801c00c2d03810348003d0ba8005007005e0300f81541c6080300420307684090 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 686227329 1250 686226079 686226089
    0x20d17040306020d0b010e13090201092c0906040203070b03070c020d030518121b0118030b040c060f0f0e011403090109170406050d0b01030605030f0d0915020c060c0f07 74
    0x50b104e10b522201d5204a40500e05190305008a200d41100d655448860705040c005520502148612841c80100c544076026440500c40042c6040840b4584031801800a100f41c1c08056905c49907481c0c5101c10303a078010a0790080e415802918040c400b031013180380210362280550403c86202a5140e000c200c411848501c203400040020034542c500341410640180e1005c41110780880310f01440700da90f40c40d041c0050300408403d18000c0c0c501d070f4a03400f4001c174602400c41d0b41d00300b4400035502d050400c1c040208403011142c4400084001c03d0040c0941030141e030080850b61074210782c45180310306942c10500714500d1410700207002c00c0c003040d10404070015032280c0510f50000c20307640c00d18509400c4102c042101d100003c43e05210074048994007800365007000c180c0b04800304544840000603001400325070485a01402040f10032039002000040003104d0041d0b682d00d032140caa540701040003c12008581c1d050050700603000391119803030202c1c050a210000305041c1c90700040319a02c41451b00701290f001c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 686228579 1250 686227329 686227331
    0x40b0907031514010504150c080304050f0c010c030806040c09050312181002030304150b06070605041101031b0c150524011e030e151305010f0905030304020d17040306 73
    0x614225050361003040001010006003103800f5401060000c4c21034016801900308051100482e10380b80c41c81000010001508450300d1542c0c0d040a0400d40d032a18480340504401e842407a00c000d415510428220030021b816a40300950f03a21100704110280c42841d1000b002c0206400022070165000d000c1050102d4402d807800382d036031071104c5214560542d40c1281c00d03c40c2070010200002c6980200c1140d43c0141e1004180c26002c56540c51180108504c070340e49a0448804584401041090391006002c3e50054040207440e9144600440c2952104258041e04182c181c1d4025101d07809661103282c05440b907100d034060b407121620420101d4a08a503076504440060f0140c180c030902c6080b031120801000c1ca4a82a03003800c0c412800200d50250b5411000c00d80d80381242c7c0c001d94000e001c0e80c0794841904c1444061420716a051003941407400d40d06031255460100b0f2001c54140d03510402c040150300501850030b6503030301e0b02040b808000c03400041e11200001404061803194400040003c1c52084c1c2c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 686229829 1250 686228579 686228591
    0xa080f0c06090708030f0c0f0712020f0916030e121809090703030504150c0b07021605032d030705010501060c230604060e01090c090b0907020a120806040b090703 71
    0x48241d19156002e4958880d94011103c1400701030f03000b0084034030b1702c08080300c440e9a6144401c002031414880702ca81034064064100042081700c00c00d8800c06081d0300172540c04c0301200202003004001e2501751b800ca02c903482c01c1d06040c8055802504010b100042c80300548141d010710b0018484240c1c080ca0784d00b1418a20010044454a000003407113810003452002400c1e0141541e40c007900380d100c0c034050b44048604075560762442130311440307003151000d502080c0310001c1d040260307010755142d0f4a070741d81100040003000d0200302801c0010341318104401030300c0301c291021924116040c0809407213441301c0b4180010048600401c909000300c1d030003050300da90740440d20022801c00c29409194262103c4852030403034152211100005415a0800c0c4c010100043d4119501c1a460043c10701c801d0061110100b00400101c283d031686c0440c1c65243c1c1034800d68036580e0707002022038440400c00002803150810300b5090035454402c0380100c0d8498006400003030134500d1040021743c0240201c91000000b900d82d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 686231079 1250 686229829 686229847
    0x30f0304060f05091606031505040221090f0613020402090607050c0f0d050c0910081b100e0d0f080d2a18120809120d09140604030204020703020a080f 66
    0x1110f840e5104406201034885070019112115400c21a4800d410425031100501031841d8200b03140c6100922008104568458111003034031600800c401410b501c10141d1000500b4420001c01d1040304103000001030413032a90f503003c3d01794600a503a4801e9030015401e115030941781d15248000c08143d805080141540500c5004001d0500c1139102014044c008041d0303990000703440001c40040610003240d130420301ea074801b800490b641c040d5500c01c8116100c0e40041e14610380c034440070035a9440c000d90340b801c019004640140d0320350814a1030141c11500c0c40c0c80d51000300780e07868008581d044c498401d09142402c00003d2000b41c40d0110703d00249401001e64241402a50483d000a624076a017082c02d51200011907c0c2110b4045108d6546c10298000e060010881c0010495081800003002c0051440001003da40e03141d11500700c1c00e001c505401400700d0f06016142511500c1d140040a040c40e217800c43d42488083d4124070b40407015486001d40403800555580007070f00c5a010142500d54450b80d0310 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 686232329 1250 686231079 686231081
    0x9270603141f1401050108040609150c1709071809050303040602030105040b031507030903200304030c090e12070303150e06040b0121090201090b0a08070909020a021e030f0304060f 79
    0x2050028460316148903001c0f0040d45520242c111907090a1800041c1d903a0b0a0140c0580340081c0000c0600039912501c0e400040903901c41c444070300701e6689022025449001303202003400c042d5818040b82d4080c95040103010787c3c40c104040005550480450f0703500b00340e52202d21f1030300306a03170072103001b40c002c4010700490500e8410b84510070801c4000342801d000c5040c125594100207441c5501b007584504180d0140350290314031300c68202d5a540c00409090b0080c0c003031900c0c1d4005000444d10740403402d038001998450390003802245407461001d00003100c0a2188031a1613400800228145911805030070907071190a0301100c000c1602114261041c40c1071020803080311a0500b01c18107102124545424080540078401c1c1d404032040e00000f501c80d09070005984130b00b0740307030b0094100d804000f40c0041c42075405844035004103555200c0d50845515100d410082c0e00508400b100103900070102c6100158130b8109480342805000103892521940150440c410341c0200d90a40f0802e4035011519210070b00b07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 686233579 1250 686232329 686232373
    0x4051201020a09210c2417010b16050f0105070311040e1803040e0c0d0609060803030a050a18050304030b1e0f06030c060304030c0605070927060314 65
    0x11000851a042082c0300203001440f00740180b40703401c50702086550103035040030f00f000803098100c000498015a0b50020400c04200505e4031340034001036402d2502c046024a5001c1e800c41980d0098809030f80c24201e6684403500301c080c8600494144030300141c0801d4040c009d0035600c61890001148524000401600382c0d01d501c1c00441c44420308000400a4030102081e03581c002400300040a107202d035640401d80f55000d240c2200201c4903d0200b40321340e5184101c01410308100e03104003480f500d030f907500000048411074405c0c540d1030303042040000c1d03400866030301c02c50307004245140020b01c68130303da000550040e0342c281084401d503000007400d00c24070040c4d0380000d0b801100300d0080c2c891408121718820616101421030103079070b9240008070343e580d60107000c200302022014000a4803480c142c14018801022064191441c03490200070034182031040c454002500d4043d00702d02c3e921324240481c10000c08444031240856a9108400b00014a4004804106460030801880045003104c80750600c00d032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 686234829 1250 686233579 686233609
    0x8280905120d030b042406030e0309060301030615080d090806090c01140a0c050a11040c021506101b12090f03030c1103010b0409060507020d170604091a010303050405 73
    0x61210700358000c2103000180070440561500e00401d02d051100c01180207480c4401945110a200c0e40102c08082c3c00c1c840c1c40340c21121940e40a001050031881c0440d100e200382408140c01500800060010421176008400504d00050094801c03030f41c4e071003d541c2130603a100b08000005a02403010000030343c0400106821003d4000900b0828181b44006042c5101c0c0c00f80394402c20a01040f036a03240c40c02032189040d429002800e40323003480c0b00707490a20001040c68240b10720443c501021250b116100003901c015034500c4140200d004c2d102c900c200101070212060700b0081010310507205090101c0124440300d403a21604030030792800d020700c1000e4044419608040a0064400400c10200303602040a00c90305411401030480c010316000443d01600d81200742c0344d0050300f45120107040203169800107110710100d5003500d40e861440d00b0100c0f00a01440c038034295040b02840451014a050351103030102520031003641c280d9101000403106030780381c242c0c01079000c10301c041820401401c2c007103001c030b007514 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 686236079 1250 686234829 686234839
    0x60902010512040b09010b0a082d030f03061e0f0609120a050c0a060f05030115090b0a020f0c06040b04090216170c0106060804200105091c1208060d0f08280905 70
    0x8d0305000d142c966600d00a0119445510f60b503403c044c62a0094011a11660b001c5040d01da540183d0420448282d00513105240201c0e10041000b07040c074010b0a410403007960051011982000141c10044070360400380006501c065050034180a02408007c0341262138881c81c054460001c107a4100000984079a000b00240501e501c0d880074071b5580801207905444c03400040200f01d20041e00e084034018820340025024240000c1c455280703540004107a1401f000c981c040315010605075081c0a540e01a078441d10740d42800510060010980c2900900b24226a42d001c1c0c4504c0801521180303040310107000034031a0b207e800034003052403050a000c2d6901805c42030400400d5420a80e80f0903601c02d07a2003404d00f0f00c0d02c1a20401103040e0b0310520454500c450010b00c4401c000ba1142c0c11440d542a0440d070481f030140c040c1c1c50704a10940a02c00080c800c14000b80f11a0202140340c5403400c1c440c5a0350402c9440ea2403c21001034500700d0f4040d5034160702d640201c0303804c0c4100c00c0100a4115291b42e00014840c0f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 686237329 1250 686236079 686236099
    0xa0204060b040f0b070f020a06022a0d030e040f020a09090f09120809070329100b04030b1009050f061e06041e09050f1f03020d060902010512040b09010b 67
    0x10b0b100e004007000840b03100103212170703407445503041c209040048100025801000b061001403401d60004080580107007081007400c0700038003850400c800c60007007030b245908186415100c0d00843e004242c14a6a1038024001040b607205004070081280d102080040205200708030610040e0140d1056103160309604108010545085e120900c12104042002c01007010101c0080c08007082030100d0b400440d8020074515040e140c1c44014a05c98075110812031f81c2401c2c0c080010700480342c115144080300d0700000d20501d09802d5403208107a1590060100728200071031003002030380c01c4c0c80f4030440c1c2c0b084107142a1a815810711508002030144030076511070340c91400c0315500aa039540c41c42203d0443d00080e5100708a1401c030982940680c4d0650b1200742414540000c004c60307240061140351140548440306c1001040140d03460607034480070701020b50003851340414040000c60690000c2c0c05140141446400c0607041c2203100c240080c201c0e02244da405440041c481c601200340915402c0c504200c4030b031912 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 686238579 1250 686237329 686237339
    0xc011e110708070204090b0c0c0d02070b0d09030504180b0a05040b0f0402031005150901180f090c0903050a061b0507020f040b19140910080c04110d0606020a0204060b04 74
    0xc640104040640100320001c0c01d5802c640c0c6030340c0a581030913803004111001d0300c0c0c500140780e02600151840c1c10640501d19003d48211310109407042542c58403036125092600620102d00140801c113000c5092001c00c10020414500c04403e0300c00226400001190040c3d2480078451f1152a60340b1290150381010f0f0304030032580e142040441048000d0b100182c5a40d40d550b51442c03440c0c0c2c40d500458104030f21445201c13034403901c5401441c0c41082070701c0d90742d8882401045030400990501c5040c0c40c2184c2883c051000001d0380e004044818014035007040c9044e00d80c0c850b18202a5a6030b41115041e80d00c5000d8580c21840310800662a03140381082c23404c11685802240c5005080000300740300b10703514106103290f41d41da0340c0498582554078040990321070312415555092840003040600c9000024002103518000c0b0702010266101e44010301103840303111040c80041c1c6006d0203004440c0105100144115501c0c1c82103c0040941da8001e04d410b601e1401407104984c281e0304030741482c803010441800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 686239829 1250 686238579 686238611
    0x20091009080c010c0501180812060603010b0703050a03090b0930071103100905030a110a0c1e05060d0606120b060415090b03013b070f0201020c01020c011e 68
    0x40020b00a08005403200c0417441c1450041003201c0311714495000340e10700d41d42400031000c058901e103e00105441c84607101c107001c10410f40424400c0700d095180c10082100040d2044014001110b41400c000c241d40f0130b10341da081d509000454000005500080200c2803d040c3d614180c003d078803004221101400c01c1085184807072080c444050500360f41c40000038502e403800c015111050001c203a040040ca170452030526103e910101204000849151000000802c04100c011196070300800a896082c5040c1e042e4200000601458210344150100010b068a426000742742028500000090f018148080640444107411081030002d2034001103d0030b0b51600011102a0b8403c50302e120b0749100354542c2240c02c880d4039000204c05050200002038150000e62080c0403503201d8001e046041d4108500d000d09400b4104c418030400400b01c0b02140d0840c0c00741c2e00c3d42d42120858030000d440c2c118440001402d980c08100700c804540e544070303c2d0140340d4006c038039004261400c00b1810702200ca505c2d10500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 686241079 1250 686239829 686239843
    0x7080103050d0c050c030d020a0210021b0f131b091d04170c0304060905130e0a06020c0f0a0f12050a1d041409010c180506030c0309012009100908 64
    0x1010b004803c003a0340f0a2203401c105070010100004e084810320600754800a40384c03655504124002e049075408101c000f030001c9200f504090b171007100a00000703101d02c20414401025080711b504070903030b400d00305090f51841c010345031000011810302e28440e99003034008010340e8031580311072401c1d200700c00181c04000d055100941c016800584400281000015104151241e010b81214510001800203036140d00704030158111402202c0060784e80c0340c5942100140c0d0304098015041c1e0f00006180000190f80f68050203440480784200c80c040c3c805210042e00e4078801080660b95a6a40307661042000f2103110504801c90161500500740b503030410001c0c0c10901c20030300130115001948011b0f5429141c0c1e5000c11540d80c00d030384000f8003d040415015008020950003c2d0005584200080104544044410450b80040c1c80c552460792040100d00681c1c1015002c92941e54803070404050f0f41803803000f220040700400781195903854400c003c003d40c5956000307a02d0180305000300100052040420b0320 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 686242329 1250 686241079 686241103
    0xb0904060c0e090f0103032019030e120a05010506180f132a080f0a1b03020a03030207080d090e040b040302012904060b120106110c0306011202090708010305 69
    0x1107108000c41c94141d40d01040e15034083d4210465804100b113003100244140d040760b00a44481c8514100d90b03240b85c14520440954001c5940400a03205c9a5000b084c00c0d60500c0d0f0080c07900018042c42500062000440d00a02403440e5008118a5007030080070700c17906401020445100c090811b074201040c5007154020001400d00c2000c0300050310444c3e510700030328042980f000a004100d100c1c0340c04102c108a010104d083c03800b1500c0c10101d9051000500c140b01745602c40000d05e600300b445c1c4c0c1c50034900c030f51202c0f11076012000c0480c0000141c40d041c0c3e61002440c400d4025001e40307400d04808901d040700b20300b503420810955103000c008150344040169007064101042c010140c0d12400e050740902101d5000c180d558152104a411049100010b100302c450121810300c2190780c0c900f501d5406d8001c0c010040d8003040504010003849000b1242814403e001000b030b00e055070b100000090400000340d00007005a09050248021840c100003400e5104005050200c5154155100c2960341c0324100e1036 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 686243579 1250 686242329 686242331
    0xa0603030e13140f0f07082703040b04031a0f10030204050a020702210d090b03070807090b0f0d0506030303100315022512080708130309080613020a090b090406 70
    0x14000070156040b1003e694600c0a43c3c80081c00c09544c0001a480201c54041703100341e094000c035214a1003000500e01607480803400c141d04456180c01c801c6003c00490301c804051000b000002107002d4102c0c06800218080c401000b40000781aa0080c24900c00504240341402d1440402064200060036507003900d40544001075141e0b2840c03413104c020720809201941c01005010180d9101c1c0c2c0481c80840100d040710242e401611401c88182c07026542802800720750201480012001c074410003166a1040340303440c1603041140d60749044406070780b04200c11000c117400081d46821440c240c3c090395410400a0340114958079101d40d14000e070003c0d0303000040c03c5403c1c060310044880859019a06c5203c120009045140b40c000349140386207504280031560301032046c1042c21030500480c50148a4a8241c462012a6481042640701c8003c20f2100f14144080b800c5c0103d03808108003c03451040c000342d00d01030b04d001041d00400480c940e440d8411120a8208000c081c0b590f1a1100d42d03641140e4402c2c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 686244829 1250 686243579 686243599
    0x10c091a0f030714070609110409050a020d030e0a080303090c0a060c0b07200c090903090a03140a0c090e070506030702071e0509131217042004110a080a0603030e 71
    0x98115613281c1c8180351035036900b07408502c070004d021196110307591103031103041941c0030f0007900014807040c0c0320340603030240c420303004907068001608044e920b01c64958802d240034210124035800149042c0b040e604240d20590011041000c408410400c1c20581c00d011602301c50300c80e1402c10001c104540ca10001000389000340e020070100c0b8052f4003010800e51600f80040304407074444002c0d69441d6180d4600520581c0c11340c01050010001008507841e501000d014403007402d0440d200c4103d18002210200680c1c8900340d0088081000c01c4c03d0000507001d2a80301044d110041c41c90b5034580003140c0c0110b0702c102800c0040c4012036800141c0041110f5100c103040180383e585041c0801003035116404281c2018002e0100459040229030b80489603101c2d405000841c0d990040c21114810310080c180c41e01c0c0038200104020580401140740034003000f9401c810300f44a8030b404241541e01421000b904890042155004c20742c0007401517500020060042044602c3c644000703042e80c408820b00350052078108 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 686246079 1250 686244829 686244841
    0x3020c06280e1203130506030609070c03050909010e01031b0e01120503040803030c070b13030c0212100c02030301150e090402100c170403060b0301140f061809010c091a0f03 76
    0x6070b0b00c0c0303801c41d0001c0518298124410038280c4035400502c18603482c22000401051038070307104c4140c071b02403400a40003609a0b0343c0d898090b115040040011b4044c07000600c00408107560b0300d031266001c4c09030040503024a5241d4544401d1a0128011000c1c1c1c600e000c440c207100c0070a40f0700d042e43c1182c10a0718030340f800340410704149040d03100d25041518036000004c20003010b020303d40c004010b001d100340c4190100d41d0b96124080300c420200039001f00010103a804d091f002d481e04081c0101c017210200d090300c4800c03070303030f1000c001c1298080403041d40582c202100410420040140701d6100e0012805d181d200c441040d00000c1074041c0040c4001d12403a1904551002c881c411203500c1c01081d40001e260034407008540c821750490308140310498a10b81040d10b170118504040c0540c01903040351384004210354448011454080d2001400f25030040d2201401c80f0410801c84087da0180d02e192000068031040ba00340108000c0d050b401c10520743c8000c900404105070728400301c80f41852035155854480c0c5910b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 686247329 1250 686246079 686246087
    0x14010c020f041a06070606060207050a030308040b070314270d0c0b07091503024503010e0102071407080d050301030b190c020f1606050405041d011803020c0628 70
    0x764043d240c00c5107011501c0010440c00380e001406844213502159001d517520810884070180c0b0b404001d00140340d8038003107000122010003554118a103414042011a48810414130703d220803501580c42006e02d5840c801c0715003609417170380320080c3d600c1c1c09000601c0364400c018140d45c80e0124001d101583c9000000e140512550021020f007514402e09603504050003c005c02a4028800000036000c62405503041007510034002c60300640e240980c10f80c4007081d1030008016400326a002d41d01552102049010703100c0a2004041c414481c0740c14201a000303c0800741c0c68290641c00207641548117111a8003069001010703a4112984540c00c40125550804032841c0c0112030350714a101c031810b181da10301c14590007149078078050141030300b19680c0c2500c0786071450040543e4411140481c07010402404281800e4125840c03202a4881940040b188052100e08440b882400d802020b184800040b04150381803002060004040701c0407401c101b141c0000032596000c00c443c500020010403985d541749401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 686248579 1250 686247329 686247371
    0x250503150a030f050d020303041101050c010605060a0306091b020c130204150f1107150e0409020306151206010e0c181801140a080304031202070e010b0414010c020f04 73
    0x380c02901c04654034030301005000d001d0801152030380100d000301581d845c0f000041ea4492500722034042c100344d030360708010340c3c40350300064000459548801c1d000c50f4130b441d145c0007080d285d0f82564001840380d1600d400c4008540f007800203500111403d040c00008194002402c0b542c2060807206038401c0703122000b81d60004d00c150380c02040d940192180410001c0d8101080c4001405641c43e04645803040814540c1c0b14400f5004514040e4803200b200ca500c544140c0d40b00f500f0380d20103080010112429000285000d00c06c940e41c00c0d2000c2e4040c6008014103022020080c1c2444040060180707506100003070781d545100030011000b4a001044051109982d20080c100e85140a030450030503260041c1400c0c2880400d0266114150342e008a510712410b281040d2001c5600c04409503007030030b08558940300101120116042107105034400445c0031600b221115000f81401030030542e4891138542c040c411178101c100b189040c40030780305001000d600d4480c00c03003000410485d8001003100360b101817039040d600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 686249829 1250 686248579 686248621
    0x415091104140603101a040e0114031c0c030815040207060507270b0d020f040b070308070504030230030a080103060624110102090409050a0b250503 65
    0x1041541480403900a040140191180d5254801d0340c2d4441c4003c2c0407092006850101201100480401030080e0300903400a10340b0140100c5803401d5a80d5001c0b420002c4207800c8032400c9400d0070281d00940c5000c1092025501308038000b00d0000e940c111016040c90440100541401003680c0060310b07081c00450343d056110310081045444d00302c0c5042501c02004211140d80100ba81c0702900301e5405407074100000d001c44003951700c00380030303040078210b82e65274102d00b1480030080c0d000d0141d2480045500042c10180900f1100c0c0d5480c0c000c0c0b0f090041150742e02404890510900700414400340c1c40f02c00d0f90020f0100c0c140740a20000301c000c205030544443c401c4490300140000328140c142030f6400031070303070f8100e9000c0c00041c041c1645800c15a2001000246072000000084001c05580385c09a0340044000240c0400113080840041c08201a29960101191150400d050050030070522440b160741000030b031103813000081e0208007103400c0310406540490600070040b000a80ca0f8440c2d02980101d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 686251079 1250 686249829 686249831
    0x80f040c030f0f0b06120a14070f15120c0e104a030c240a080a180201120b06070c080106060f0c0503031303020f011407030609020708030105041509 65
    0x28071900f400e00711152502c80c221204c200c003c020030410300e44500c081942e0855800540915a800e035038500804100c0c2c2c2c50a1814040c2d80740004122604400140c011f10780d0703642017100c0b00c2140000511003410800b40400c400d1420001c100410b0303110300003010440040d920840034040340c070030a4820703c2c070b00c10030020b10000c82022201c0e113080e00042410311075107427800494900101822100c407240d62040301c0360191310120211301d20b8a441240792982500c2040c180170840003030200c40500b039201100d02c10100380303188280841c0c40860310590a81080803803404c860302620790b000a055540c89102d20134415121000c152040d9600340031180704541c0080010035081e650070b501c0b03000e081c885c0f09540c040707103031500d020f1310320390181030f4081c03c56a004000e180b070341c0e4900410a00304007940105401318841c080203140020030074450700c3c5d0b101c50800100816403078810310041c152a045c0d0021003100f8018031005c0005400c4400b130300c0c15100c003142e0200d04030320440c10000c106030055004050351 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 686252329 1250 686251079 686251103
    0x30103050c0907180611010f050912030c04030c0e15011e0809010b0604140a08120706021b030a1e0e0307031e051c1403010e0609040219030c170a03080f040c03 70
    0x1e030400c00946c800e00702a0024400f03180c0c01c0020300d08648040341c0c045119000b40c0c00c0c0c201c0f1716000310002c503070188450044608054481d113a1b801c2000032504690319030741c0c800303042c012004184014004524030034a01081c002041d218101004070204c4031110500400d4808541500020340160700d112202800c06600c80c0d075038500414000c0007540500d40a0044d910380072a02c40008194070f000003d550700813030f103400d0075135a42000030360044030038061064200191365040d80040c40102135251240d6a0302c003800f01c1d500710102042d0260103940e411b02c018202d156045480100381d0704100c0f500000108200340510712010125103a1803002840ba00801c18115140340c08100030060816090741d5608490b4441003580d90248428020500800d0651b00001d01c07514002c0d6005038000e10240880c1d030580d9580144134130b8003401d60012034444000b144d09120368000301d10755205100c14000100303a54511a00d000d0048000500303070b00c1c0601c1b8a60002018045070310b040308000d641c00b044200340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 686253579 1250 686252329 686252339
    0x3121817030904060e0601021f0b0603250305010503120c010b03070f0303020705030703080d0203060103061806051309210c0b010608070e0a03120f110307030903120203030103050c090718 82
    0x4950050002c0c82c4928030700300003c5101152040990b20482c0180c004000000c811a40c0d14107007018880c40d8051551604030402c4c250b1102406180500d44808aa484c03c0840c4240803012440300944002050702d00307030041110391b9000503083d0081031880210340c0e0301c00c07050a0351400340000100440d0180b003038070b80001e50707040c43e01426021039000740d09945580751500101612070b2820b20020302940810b00203403169a50b140e00035900000c2c14140000d01e650384020741c0c0c00104229443c00881036840318108031038101860080144403c0000802000015a44071803035114002d00d08211140c003050301120f81402100e90468942d00110500b60f1903035180310041c441c55044030008006849041f02e07010b07030f080c6140803c055a502420603400c140381603404403804400b003440c01e0308109070000c00d40b8200009200a000c014041d070303180500a41141040d01019040d603610104642c0308000400c08200c020400018130101142c42c2c030707103075122028122280c030624418101c003070404400c00a8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 686254829 1250 686253579 686253583
    0x3012709030521011a1b0f010c0314040c030609080f0c0303041202030a02060a0509011d010b03160b04090903030b090a09050c06040b0306040e0a05030a0203040f0f03121817 76
    0x16002e203043c0d0160001e01062180795440c03801c288035098064403906030110f20701e42500007600d4a5080300060344010740d2540c01142c90708907500703807050281e55113081800b00c043e4580559045990906d10140c81418550368090000c2c0191001800166035200c05004112003001201c00124024903141d032900d1060400300d489510646044804014481d4900c40003400403043d900c0051303a98016000d80d40c0e4000006020b4000200510142c2d50780d007801d90345107502c4414036500c1d05140b4000141240840c001c0c0f40c078281000040c03038108007000100b045951121011201031381c18041c00810760075075038038040e030180050780825580080300c00308000c1e80c113459910554074203004000300c1e02e032044044103001491146028007206040c0c02c0001503414245600202442c480c1042214100d5009850f000e00b5600555000b40050700000f40400440e0711800209000d07108071803e4001c06455955040e85070025000071006200180561340400c1e0303074005254000788802c040c81c403414011240b41e16 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 686256079 1250 686254829 686254837
    0x90b0121020310060c0510270f0507050306061c03020a0b0411030c01081504090c0b0406050301080c1005072003010e07081b01020606010c080c0106090e0c03060c030127090305 77
    0x2c000708090280080c13854441c000c40d011590704500540401582c60304024003415001e08001940d1034007440c4801c131107000010142841d8010032401d000075943d071070300d54180030140d88400e104c2d50108003400025542c901002100ea01d8400c07122911807403503c0c00340d0500380181c4018003d640c0110400040c0502c1c032030402c00e00d01049068601040c500f000555000e101620113400d201814110114541007a502c43c9280501405200c0d200342e9842201b89125805604424002400400104980c0c0b40800005401303e1044507030340044585448000c00c1c0340104d0030083d1031a00c000030b00c0095031400821040e040c0d540940280245038544011544d110264407401c42d403842244401110a95086056109000140d0181070035841e1003004440803507600b00244c2d0150801c00200c0074080302480340a0007403d03c80d10200321040040c00b01070801e030034805618003e810180070002d80c24018011241075410906c0002c2d0407040d000b682c8543c0030220208501c0d401d01c3c01c01244181030700100a4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 686257329 1250 686256079 686256091
    0xa060804050c030d120c08041e050a080f1201060e09040b060d1a090d03060b160503120114091e070f030b19090e070305070b0913150303080c040e01090b01210203 71
    0x6d124083c0c0e01d80302251680c50850340030f0311240d49440b02c241004a906d4480900030b00550448400d0314140d1100b640e254003520080d02c6801e000200c115620b580140902e004045c9824442503c82c180e101003420b20b140200b00070890303459240081d210740e40700040c0301c0d69141c100d00b00c40507101844641c884e80340000d40340f584d890300c074100b29048428868022001901c4070711a40a051900c00d040b10001c540c0c003000220340070301003070000e00282604200054004c6c10001a1052410721300800d00100500143c02d00702074400d0001058406031400c05510340042c01440c05901144d4039020031070040c07444510303150b8420000da00b022203038120b0004007400d40c6e580309004c212264807842b020b03a423602580b10091050b00015030810a1483c0d01d4054000c4100151402c490f00d4038410369202140c0201e85007800314003031282c05100780b41c0e0000c600fa40c050850410306150a00740704901100040520a8220f0152654440f1203240d20500c101f03156040842c81180081120107010310281d0811118 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 686258579 1250 686257329 686257331
    0xf2609010906111e0706020f0d091a0408030f04030909090804080f011509110409060b070302010c0e0d110406030b010806250801030b0621101503020a060804050c030d12 74
    0x1401420142124111100001c4c056854100d40004400581107141d041e9210781c1c1c244200343e031800c3c4400c000c0254044450f00007420100ea46400c1031551803031034403810700180980801c8002a02a4116500b12805812441c0140e580c2d01e07003111504a180c010039146818a0154801c004802c400b43c0140c078000000d903200e00030200d46003400c0300c0c201607143c01d403004800420046512580e101c0a40884540d0119140c16215030548056075815400940410400285001030590a200b611505ca401d86401c5641d80b40440001c2c000310f542e002c02821198643c40006085c1d9501c0d884070001355441168a8030b02d6035511000750b140ca85c2200c40c604000483d6242c030a26441001d02002e0840d40d41c1c541800c184d080d51100350b0000030041126400081d8035045600c100003114601e001d001c0c541c0024000b4404005501c42910300032109070790034a80854040c0010382e076820110342030352210700d461101c0b41e40b241451417070100480c0e0840d41500032120319034002503202034800010760040714 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 686259829 1250 686258579 686258591
    0x50607080a031b2a05010f0207291f0503030f1c0b030c100215040507030506010f0b0f0706090c080c01030608010b090601052104030909050903090312131e051507030f2609010906 78
    0x81c2c0750440c02d80c26040c041801403441c00040be1754414200860020074160010100103807142e001c07030300d59800f0f8003070018002e00c00704855144100c809621841840144024410444030801003a555070312240315034030500d1441c06640c8424803c000303030070f00350b1302c00183c50001d400c00e07003002500da003542c1c002542ca6000d50720010444180148442c401c48207a07400081ca0005220074440854209000c00c88100d82c9402000c0046030352400e2840c0079190344006403c001f4910000901107410b180d07c1500300c4c0c0d040218640c403d42e2440005540f081e02820095911400300780390901c200c1c000480d01c034848110105010a040d480f09480c81610020038041000707881ea92400d90380c234000c203003100ba81680101090a4091542005009034030940102d5114003034a5541c4a0340131041e000c403c0d4100c15040c0400c10040c603210340e1104070914000b031070514088150b28003c2502040491031004d00c80c500494000300040b00d10a0700b942c003a501040e14060801a0380d4901034030190100b0b40364981048 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 686261079 1250 686259829 686259863
    0x1021c0510120c0303030504020f18090d1407021306180507080709122301060803180f01050f0c0a080a0804030f030506030a1b050607080a031b2a05010f0207 69
    0xd6802c0c2000b40c1050500d4403c1c3d141d541d08070041e1078001c1080380c0007100603510070001d46480161601419001d0780300c1c1c40c14549078142501d000368100e010020070900c6815407042c01d50583c00c41d4401901611035107820740d1400b203060043c21150b8811520703015418100ca000d221203502040c083c0180e5900d8010684034050b08640c001c186000306850302808555801c0069215244a40039540c1c400e582c888496600c036007242180c1280e400251950030008541180054095602c0c00c0048201c81c48005452400002060742c051810a01ea4201d000a02820345410030841d40b1080b96100c1002e5a8440d081000200710001c19101200032452440c0040441ca010b80030300380c0700d6074001c0d0090801946075120070300100815080c40403890756504011425449100007014090300409120390746200b020070043c02c44440c0b400d11b5800404805001502c00e610038001887c1c402003290708203540001220840b00321002840c010120342c0b81041c04449981c0e0381d009029102d00a03841000001503e03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 686262329 1250 686261079 686261099
    0x1a12071a04050f04050703140a0b01021002070308060d06090507060e011107140609011106070e1509060301180f0609200702031005090f100501030c142101021c0510 72
    0x29005143c0e0060001400700f5550415500a40d4026540d00d00440c2c0702c1034001402580390341c1903607031080311611501c40540c40e5804110103c000c02000b9011031901c0745c1902e0003404060041c0c0b00c02e01c616007070702c095030502035aa00007000d076603048029100b48560300c00c006440c941d816610540490310a00c0c4030394aa840114a5104440841180b40d0580c2144070800c15544d000d00c0d0a14103000d9030a1405000b188208502c40c41131000ea00c4000b003100d040c8040118845003448051500c00007089221441e03200c88050780d04442180c0200c02c00e0107100410100507010050311452114070b8194001100d0380e807508107aa8000710f4070200c203048554503400968600c00d0711070194143d80701064840070080640e005d264011503000c00c2c1c0c5c4203596004c00312400c00c0c1c0400c0c4050141601d0340014070031b00400c01d00c000c00816162004030200780e01c40020030380d40104241c0301c4110300090084c0004d5400290115940004003058901c1008510305031400249820366103031441942c1d1240c007040304018 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 686263579 1250 686262329 686262337
    0x250314190906030b090604110c03030c0a0305130c0e0a3308010b03060c070f0803070e040f06060c030f020712050a11090f152202031503030a121a12071a 67
    0x40942290302d170740d03610405d00c00501414a40703044140340404c490b40310340006001550080c45426000c0e0b60768102d02030700070f0030b82d44041c0042c1d106040001001c40010030300340030003048030080e00710300c100f998660920100600d80840c40c0c08500564208102d4540d801e9512a116124801c411500c043d407030700281802c0b2240d0564450300343d80311a0108503004429006000a41c0c400c11862180d1001c0b40e8400c03a094005941490210750a004180c4803442d0030700807891503a1071014200b01c082d03d4220018440041c2c0000074013840314080740507400c03034400c0c0b00c8000a44440118504c54919602d4460342c0d4020305c64066a081d1469072400741c040c54122441c074010b900e20154034006403200c0e40a40141a8641d50745980580606410b203031241d0b8410350906101c114100040e201d01d080c2e1207200241d9107682240d4441d400070015039034601c0e082240b00034829000c0d0f00014864007010032100510b481c11440fa507008100071592018500009072241c142c85075048070160b2440c15603c01552806 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 686264829 1250 686263579 686263601
    0x106080705120402030307121d0d0309030803130b07020c1801080304210606060806031b220b1206010305150601090e090307021806041125031419090603 67
    0x50401400d10403080788040c1c583c1180c001000e4134135149441d80c83d0080344904110220100d0100e0b650340001c519110000e0890b030600707403248507207140b2035940184000035500005000b1040400460340380500c11103035207030280d44024401c0700c90800c950013030341d98410078640303e1080c010100300492109461a41a04a84c41c107030003907040074144070313003403503a0f84080c0c803640d400031060402e1401040b0319000c1c15000345059200c03100d49062100a2506106010599103560203501c2050384403a140c4c5000d80030401c4400940320359000003085080060300d40c060f01c0c640c0c090200807510100c0e500105005048900c2002154ac40c1e94400780d201e00101c80031104907000c0385150a0030041259400b94040d801040901501e20308840c540c0014084031510284407203140f45401044800c0c20180314642c0183c0380340c1442c40c140036003000101540d4600300ba0b03181903841c4104001301018011554003803800c103811213203600c800e082c000481250003083c02d01c6002500c0c00e500094001d00922481240f00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 686266079 1250 686264829 686264837
    0xa09020c12070c0e19050106030b0a1203090302120a151d1b150c010903030c0e04140103060b18150f06030c0a080c0f040b04030c1e060e1807021501060807 68
    0x1500c0d002c1e4070b01243c134009003840140110028005070079034172446102e02130503079600c0000d8046001c0c8244002d600017508144038078280c107410817000c240c01499040842e9030403108806415800910f0302c2c1814000c8000910703540b1a0b010365982d08010350012201c501c89110002c48203410a015030356280f50303040841040c86402c0d10100102d00f4900c2e0822020404482e1003490101c03c80d200314211980c44d001540002c2d40c039000c100e5040c0d404604603c400c0c0c401c81d0244440000c808032501888c00c10b11009044079500c03054403a01c0e80b21040c0303543c0d407a180740c0886401450801e425008000388404007611034900c44811541d1498441e0681e4029001c101030701d42080d48102040e588200050a620403410007404054440c01200006202070301c0380d844025111441c1d450100e00d40074558000c80d48503007503440b5040500840c52614801c88125203441e4004440301e10100748185580c41e42d5015140c620000c0045e00c03a0005078220034641c198800040d1a83c1e03604044904000a070380305030001e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 686267329 1250 686266079 686266103
    0x1502031b03070507021509130204050109060e0f0901061709030f0a0c0f080309011418190822080d020c0108160e100305090607030e0c1e0a09020c1207 66
    0x344085501566100d4800d0415601d410f013580c000078100d4880e10b0112620307803000181c1072406e05041480010141e00840e0541c1802d00f44030000c5c003845070901800003004803400c508806641d40034544c804110300602482c07010750310b0300c034020169083c084202544d40092008621140700000840706c1131400034841e281841010903088a00b034500300400d0700d001a00700345000126088400440c000c3d1030100000808803503082807061010302c02410004021240070300c0105400c0f01051401d24940013083c0c00800440710714024005003d00303514000d0140b0001d60308000300005d407041100740c4401e40221619040c60103070407680c079068a1003ca0001d980b55010843d04a0102c192030460841801c00095401d407800100b01034016030808800000e40346c100b44100003c0500000d508810300389020302000c00e1880070a030b40d0b070300d00040041c0101801d00040003000d0100b500120074203c01861605601d6458120700086d4000d05070303c2d41d40340035003200e000e650135910007110680c540c460004008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 686268579 1250 686267329 686267371
    0x302060126151005040905070501050c07080601080a110915040b030118060609061e06050310080d1107050f0306010e040f1203060f0902030c120a0213060507150203 72
    0x540031807030190005241d401c501403800014284900311034241c00c1c800c044481d181010f8200e0401e525640801c2c0282e00d0000580041103010804005540003800e00319034518000b40310501d0001541e000041901a4070004030300340c280440e626071040e000701394405210894400300081c3c003106032580049200e0010340300d191401c090b0011400b24800600001d20312020f40c03480c60709084d104c04215000f81d81c4050521104102c0d10a00307000d4400d0515034881e000c440d402c01483c001142c06000700f07000d000710000e4215650008000098184441a945510044d080141524120000c10380c018058994041000c0c206640c2031161038400500800e096480c003124074004407009081911840d1014880c030020954903e052181c0207029a0300007011481e168802c40c00311010f801c9444041c0c010030512910b1040d800c140c49040c0c842e45003046c0f407a00c40702c103100000d1280480240340c11100da40300080307a41c0c0107000b070404a4054003c1617082d82d1f000600344124813040302c484079401c080c90350b4003032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 686269829 1250 686268579 686268599
    0x140a050d03020a0522150e18060d0b0417070f0303050105011d040504051006081005090d051209072304270803070c060501090203070219020108070c05160b0406110a03020601 76
    0x5403074020701c1d44d51000c05c1c0d122106c2d4607003881c3e65140f1002042138441c078a07490342021004d1200c0e038400e843c10f004580c10840d0005034030a0308a200902340302c01c220081010300000c0051414602c038448005661317003480303182001d417445400001f0342c0402d240400018030365004680f403080d038600e0300801110342085001000000c100182080c0c45500c03a0004071054030303d240c27003020050000c6034010a1a080000503038020b40d100282104410f8000c2c10140400a030004140c498101489140c101e8a507207100d0b501d03180480e258818085540b288080d1151891840128151044255014000c5281000c031506560490341802a8004444051134001c140b68001030360700a252850a0f505e006501d40395407042e5802a04000e441c96800000d010300c2540400102004030101e000155041d0419000a0b002d200004c10340c005200c900c043c404200081400081c10303807030309103d801c2031403a154400f00040e60001c1c0104004150340b8018074603522000190b00f041c8035450350007070119a0078441602 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 686271079 1250 686269829 686269867
    0x90711070504020f0903060a02121302030a170d1505151b01140712140402090c0f0d05091e121b011b030f0b0102060c030c07140a050d03020a05 63
    0x1255000350040071441e039a81d07000a0422001030740115489108440400d820000040c1c41c145419104101e0103212035580004241d200c440c580c0000c40381081400441e08181008a000f004040220001010310380110f0203401d1640b031041040000e001640c1c0f0011204400c5e0082541c810305c1002d45002c88803140006003043c04c285500352081c0e100c0f040c0a942034410007000b01750020003400811116640c82120f40b000c2002c25a414041002c9440d04000300350005007010f402070060b440094560000344c021100c00c440841c0c8129070b684d01100030580209000d503803540c640d001e1107503601407461118001d840004c008070040d0111030410240c045080d4440c80c0380220b094006002054651400e20945808445d00c2c884041f009445420041c200c0300300300c0c40c00007140d140c1100b07d4002d91340003540030303401900703100559525210000941c000d40a0058000d00c401c4e129250101c6000001c90a0200580329400300d51f1800005542903081e4090403020300e00044040c402140c070310b172807003645c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 686272329 1250 686271079 686271107
    0xb1807120623100e0c1801030c02030421050d02151302031204060509031e030d02031e100e10060807050304060608012c0109020307180f020711030c030c0907 69
    0x404110340214034454a03081c201ca1142c44100c1c1003404000f84a610500c0e40d0307000c01001c0000d4a068180f1441000300d550b8030a0791b504144e9100c4250380000d00800444d0050b103854900d402c0594014000f40000c4101400201c40d5400755101c0d16442c2c0d030000650344000007018042c2c0403a0780d0b801700348040c441204801030f039045c03040c40e61050b4800c01d507200a1015013255900d0035591007045043c10b01d0021a4000c03000c0109450ba011801c581011054440c00b07544182c5c090b940341c8a0728030006000b00082d015802d18a0303210107105503615245075000848030340c5000343e0407950b81d00d11442c41004070351082d5000b085824000a000230310a5000719030080c030641d030000d4030380d480e202c80340d084610601480041c000c0d120601e5400303445400d40302c0180b88a841c000d100012640d4042a22402a4807881040c1c40d81444542c05811507600001080414150f00310344461701810000c007100c2c400e001c403602074060049211040e09000c10039034042c90f4090700001d0281c03135510048400300c00c1c1e8885 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 686273579 1250 686272329 686272361
    0x1b06121e0403090302040b1f0e12030412030801060c02030a0210030e0d08070e0a1a0306060d0f050106080f1506032a090108010b030114100507020d0b18071206 70
    0x224055003982455040c01903000f652042199400c52051004a84401c084036210b000001e00d1504141c00d00650058200f00320314100c00440523080c045000d80c482c09000c8a8980030101e004100c00f054040b205200302e020342e0f10340244e80da1b100c0c41500c4074000204080e4050b0021100d000243c285202000d0011946250000f00052692201810701c0c08042c103420002c3da441d4244500d003907100c1444140918211a80d04110f860200744144901d212030030a90f50003030200009035940e90328401d07500001240c000038000d40a40781886002030009014000203e002e06000c1140c1c1c0020f00c4005200f00d5a580c110902c0d18284000c0010641000341000c20880e0392400c50703080c0002000300c130041010f9060304c4a4460a0150000d080e4400507044900782c0d2009000400034107080960150401c44103840d1502030880d907201c21560703440b80f64400b0350032403450000e40d010840d40342000b40c0726403000c400c2c0c05206803013080f8043d1128000c2c400c4001c0c480d4801c1400b000f10366542c2c0310300704514027014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 686274829 1250 686273579 686273611
    0xb041221151212030f020f040911120408030f070302070503181207030b0604050f0402220603060518010f0605030c0111101103090d080c040b03040309090612051b0612 73
    0xc0142d00740320301c1c504485075100f090f150111940c141c0110004040314803c15424421210b080b00f1a03030240741700781e0102c03070b817241205450f17060180100c1d20034003032031020286280351a0910000680c000ea40d08408924030000003500c1a11a07c292038610744d1240242d4980038011040391102d520300000c4c2940860308641c484054007040003103000462041507502407a240080c2000200c9200500910042c850282084010313070780c05211405004240d400b25070340f1382c50810010010b00d826000100307260710b000c0a10141503021b041800c100c08104009000b8401001d244c03805542e05440b50640607031003004503841c40d60083c1080303100d01d0154011510402c02c0700c2081420385841c85104403003110000284038047d00c045c8031500000145e42020461401e11008000c1d051045100715202010b01002080402d407062110400030b0280c520148440e54840f07400521070480000d01302c41500c5000034199001420201d00321407804020422400d00c244100750f01c0444400410882e010280c0b01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 686276079 1250 686274829 686274839
    0x303090b0a110d0201140c070b0f042906124c02121803030a0504050a0614090106060e090115020708030d0b1e0f13060b03040b04122115 60
    0x80710701050f003e80d002081100c9240740100001c03501804441a0403020003581c2d0200e1801c94202d40c01003811181d132402c96843d814035410000741600500b8070000200844000c00e80400d401c2c41c003c130811900764420401203181603540305030800c2042d010340a400c90b006c05260001d4003902003148400349484040c1c0e0083c0b0103070a141c0182c01c3c01070015901082d01420a00c4840207154450320f16064501c4841940404039500d0000600b240003490301d03000010708000e4184201c01c560341e40301c802480021100a00c0000580e011110004c0540c6003040c002402d03446004100c98000340a0000b174082d034204043c201c03030b003818000e00c00e083d40b09000d400510b000c000c000804459070200c00c001070102501c400c001201920030391180d0700c0d907008900002103a4076180c408901090440f800840c02219029240141550340d02c900ca655101108000a0002e12400144500d10503c5118244c88102509a5500b003a0840c030303100100c4014403850b60700040d0703440202002c2c100c11503401130a0741c030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 686277329 1250 686276079 686276083
    0x130b1906030c1e0b160c0815010501080618060f01140f190c150b1c03030902040c020628110705010b1905180a09050d0207060f090303090b0a11 63
    0x540c07045032800300b100001c02140380c8150108065110600c00ca280c0503140024501c9140641040d002d203a0707072036055113003c100c04030b50401c005000280545020100d81003408401c0c100921500d80031031125030000e40d140c0f5002d0841e6070070100d9110800c020340c0f01d120034880030200c144a024140300c12101e8450b07038403d142c03000c1c00f510700003901c03401c2d903803240902c401d040c01d189072402c0380a00c0084450440003544080b081c91460340c01034000182000d40b10700284103074000010451102c02d850003403106045c0c0c15000703207035000d009441c24041080340110407681c402c81295001e000c0410003244141a180000303280310401456500410269025800c00707034640c1c0700301c80403209607564071610251424041c4003100704642c0b4500301c268042ca44000b00d42c1d070070f443e03034403035484070100c82d0004051148961201500759080f8084030898070380c24202941c1c500c4240500c20100794182c440c0302141e4071410785801542d600d60b854204061410b00f02558542014043d1340c02d101c1101d010400e41401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 686278579 1250 686277329 686277341
    0xf050603191e1202072903060f0a06020102071b08070608150a0e0138070602040f120c12020d03031a030609010219050c071208120a06050405060108130b19 68
    0x243c0c8003982d00558441c006441c000c0d40380c2c060f80d4080243c8038000b407880221217030b9207451045217034403540e641c0e11000011142503d00b00c400764403036141c6001140455055001d808000e100b4038403242500307405252a10858030a2043c803555074270032201030100520900c01590081c08139040d100703006000c000000c104c000b141e08200401d600e40c00040064070b000d4480034000d420208001c1009000c00120000c200301c60044218402c4000102203040080b154111002001103a0300540456282d0701c2d6800c1c2c50908240c15560030785071050200d400d003103020404407529070003072401d41c0c03111060303400f03a01810021412042a40003d01d2070780c0c19403024006a407045210b0400140c1d241c050a5040b50301402007081c080410006024810740302000207000c0046d11400180340341d5030821031401d100319214165005880454038401e003d105102078021100359031003110148200e555840c0111400ea201b240c1d152001c0f0f07110090301c1c010903204060359811a08002d072648060510300b201c3c4040d110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 686279829 1250 686278579 686278583
    0xa090c081c1e0c02121f0501090b090f0a05061507030215090c0603010509180d030e0c0913060f060b070b0105100905010503010605031f0311040f050603191e 69
    0xd00109150000c6038451002c896640c12a018070740220b40064008081c00e480e904000d020344503201060076264020040b020b04200303d21102c007584c503401821117003e44003e2145400c0c40f41000e08282141c0f034000f49040c814007500d1040d2003d56140c520040191074003501c4075800211103d60002540745000061020900030340040406040c602840c00b034441c03005080e24140d0700607100761a5103550700402c490464504403840007568a0361000d50030070003491010b106192107132006001005030140c0129003c0b1009e038040d1a541e048113401e2206040081350a010151408958080010065445080101d00c00d0400240440d2281c000301419481041e01791612668680100b010745050780f04580341248070b1030200c2c895442c101c0041c0041c0018003c0c0c40501002000080c070007180340d008036089940c0e0449140d4101d50301e040c0300100b204d8072043e4601039420150284c0404805002d450300803a00038006040c6907024500d50b030500307440508229106200700a001050f880080e40c4507a0b658 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 686281079 1250 686279829 686279863
    0xb0a11190e18150f03030d1d07181b1416020a0f030605010902070305030c0c0111030a0207050c0f13020f090604091b0c0209070e0d0c03080c12120a090c08 68
    0x1041400c40c070b800750381c08501c0f01031182021011181c0c85480200565210001e0000041060395420650401071403925202050707612503003400003448044d81001c0460541800c00c10044101050300c500c0d1659000c0b0200c1011900303001010408041e03000c01011501c501c818100c048903070750340c00500488482da101039a0304004d201d040c000d001d0359118990040c10003100451515016540241c194040100390001c808004a854000640c0a402c021130780307201988907035681e140c0518030200941046405071000d00c107101c000701c0e490420200d401c8421000400710748840c0c0724014450081d5201c8458455a42024000303ca6140c0362400a040581a4000040360603100341003412114004400c0706006c201c481c0305035030301680711209803d400411344c1c901440740401f0351001c030780301070f90f10000100010400304000060220603400381400340b5100040c4e1b40894407258404101c0c0c0036400170130084200060100301120940d81c0040035561207005c60ad11600d6552444504100340c542c0d18140113 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 686282329 1250 686281079 686281081
    0x6090501060e0a11030f060919090501020a030b120705061c0501080a03030c020a080906030c0f0310051207030314090d05070902090f060c030a0e01020c10020a0b0a11190e18 76
    0x25090180454030340254036285c1c2546052001089501030150145000310195008102c0f042c1c000380b000403007181d49800c01d114445003850441e00039405a1890000a860000519841d01c1c202e0422015645254010842e9600780004c01c100e550004d542c2d0001c00807001e20025040005010b0700d402081c0c1d034405043e01103045d040141c1a14003180d02030007190801c14001c400600581c7c01e0300c03140c0c041600c0c0d1a48942d14070076585500c0c480e01e804034402e40d90202c104041c2070034280008094800c250b901e6186601e00c061866515185400002d0105981c800c5036440070b802040074011098005121003041082a110141059520781010080540010780c0d80b40e141081c2c402012589000d4540c06d141c107140060054890140747c14500400110f4003d100c401d0b03200308088a449040140001c5160000030b00c083c4d0b07a0703428a00222034a01801002031005880380c4100c074407281e0091b00480c80d0031031260001480f803110400300001c1c400c4020b8003c4403601d0304120701c06151041603400c001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 686283579 1250 686282329 686282341
    0x409030507020321161e0b0a060f06050f03150d0c0914040f14010b060f0702130b1807020a050304030c1809050d140412030e15120106080406090501060e 67
    0x1400c44c44107240c4814a00c1c0c9440c40c4100c071981007101c60131010522001001c00701890140150070241109200c18004100c1c0041809208108903005600d1000c0c200503040c0d4039070108521401c01d2099101103982070055003d6880200021503105030750480084080140100290881440d40000e0700d664100203000e001000b81071040c01000d00c42020704143c1890143c0d180741c04280480f10080041c0451100066000340c00d4000c220001c200900407a101c0c45000603580054200e00420780c4610104681080a40c01b1031086800303052004c0d140e12000c00340b200317018040d00e101410785030843c420f40c0045004207030180058000703184100d803460f003c80d1410002507030500d100d0102010940c904105200041c03c00644000c491402e130030320341070981000d2a01f10460246501440140001080407000c06900c1039a030214130b101211250a0140380c01c06030326140c010b904441d8501c0c8a40c00050111a00803800300354058841c03040800d1040481d9101030035104154809000d0050789003d000c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 686284829 1250 686283579 686283583
    0x30d0207030908012d0209150904060e010f17100e03073305070306170a02040c0c08070201080a1b0f020f0318090711060103080d060f050d12030b04090305070203 71
    0x50a5200c002d002003200d180294001040058075042c82170f14400f0070016043c0c0e0340e0150f446c1480010020247c40500442041055105603a0741d031080d8580309012031103101d0708a066058950084003c00b409003031000b00c2d959124589032a0096100f56035020020a80c940104030300c2c0d94586010311344454044c0b0b4207102d612220410003001d504200144050000d200514000300701e0310000100e030a80752940240d00404080d04603a0380c1c1c0650f180f501907006800550a142c5078402d503400c000d009003840c01248c90061404008010340c070100100d00140d03100d80c0102e50054070302c0d500010b07201d8170001e00a034500c3c0c0380812400031a0620303003142c98594040c0891001e28040c88003840c5480007070340b01b20100000e4481821310411540d404602100e100b40010800304203c6003c075262940c407410071010035040360b50300303040040c1042400700e0068084500d041c115100984100c503252869601d08141d01000f608150070107564a44950196845015480ca1907019846095840115005043c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 686286079 1250 686284829 686284847
    0x6090613050a15021507090f030b090607081e07030f14060a050301020f071e0804231806010c03030e0d0e1f1b05070b1201180504050601060c080c030d020703 69
    0x40403981201c5420f03240d01e034011914528003da801d0700740c2d240b03680c1c41c442500c039440790b40c00242010002000200c00c0010306160319008400e50b2080b0303030b101e84e100d040450784188204c8088031601415401d80d01e02010200040d030700704409080100c0d0300c00a07100c0180031600a510b140c9a140783c80380030700081c0c0c148292004043e103800e6000703500d449906010300c0179620a07144002c0c001441440d1180c191820030402e00203050b805803040c0d40d603e654209601c0c030030900185044516840c4403106416240c00032184010703002002000390141d65113001501c20031206482a0181501d90300e003140c1505090188880249460b20351118070750721038003031125001400440c0e010841e0140119018150000302c64981c503030100e03020740c2514440e8604181451065840040303501030100d00c141d9044018610981694203043d201c80284072005200300c203a54059401a1564100c440103125191180410400407405404428504003a126400d80341d036008800001c040c1d03501003540c4080560240000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 686287329 1250 686286079 686286089
    0x50f0c1605040b0102302106031612060507030e0d0302130609030b01030807081b0c0f091603230f061f080703180605090c010f0306080a08070206090613050a 69
    0x10300203d81d5100c200b1b24102986070358103501003e40c01c69240700d6141c0c80115081085900310380b40105d180828607200180e41940c8031071290203040c0801e09080070401e104021201100b4035203603020351984480c802017502030003202c10945c0b03c02101c9201e150411402001c1186a50010307a030b800c40042031010b8903190340010042150b1017504102207450b001c4001d05580d00400410f940314010321b4403e600748958040711101c8100010030001e030050105180c416003006403502c0c1c40601001d820864425001c40b0a071102c5210510803101c910f100e5848080785040040540503106440501c0c03081d08482141c000c020021a0401c00485050102140080002e403000d45240c80b50341c0c0307001500c526001084c0b002055039416008460306604107800403241d8000c0f01c100708604120220607143e00c8440c0b145404200e245a028402034400d00c0b44d03408584008020781121242c035034030981131354460b283c1668808070500400c5081c2d510080181901c008079400c4c54410b9140c0000d02c00d10700c08550003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 686288579 1250 686287329 686287333
    0x31406010e0703021e130e090a06060501050a0203190203091305060f0d05060103030807030f02070302030c010c0e0a030f020a03080a0915031505061309180302070905130201050f0c1605040b0102 85
    0x2d1042050100e1034041c00c5c00c526200c3c419152410b990045401119a521581020100c01c05018071042c001c20240e00c2c00740115000e000e10f5882d203006407914400c001e51840160300800950600c00041030304c0a8032a000c1d48141d9107407451180c0003c80340800344c0501800036640d002406240c0c500303000d414903c0e04007070301c51107980181c82d2112034a41d20141310140a1040480000d0403640c400d502429808615240c2103464080c103043c02941ea13000101001465840c2006901a080c003455821038815001865141c007a8150781e202010340d40036240c200c3c0c024604007800701c001115180501086030040e0f448401d028075220402c0040c6e017a0308260b40030b0610742001445c88040d0010250259071007900e049a0703542110703000e080348958a5002c40704143c0382c4003885a070781c250207030300c218401d0007903080303510303ea0f01d52840e8002c4803c00d56024071400d007015000c2c030055002e41d02a104090540d102d150404414804041c02c10303400481058041e1503546007402286018401c07078201c504c080c40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 686289829 1250 686288579 686288587
    0x12050612011b27060f051e04030b0a110301060e040e030a020c09010b13141801030818090c160f0b100501090602010209150f040b130e160e010f09031406010e070302 72
    0x100d05505146401404100080100014a05d80c0138804446d020b0016131805c40d41480c9900810320035811900003140d1801000c4045030b14541e26018603004010305000c0180356928016003600c80b140803141554000382caa080c11402d8a4017440600b0800103280c016100c000180030811080d50016040020707444418031114030300c140b243d000407042d0f900d00e820070300112070396400090b941490328103041c00300c1500000220800c4699000b40441400b1b580c8410121165072040041180b4121040001507600b4006900c0141c83e20808112075070140b40d41c0062a422034441107030300e8004540c4880ba110b0322500820095a0050b4218000d00a41c0300840c14003031548005404054030003d42c510b80000030403400c0c070340982c1c082120003c0400c6d120087c0e49400003503a843e03500c951885500c1c81040d0b00c50000700c640c23458107040c403d00307240350362541c508400000064440341d02040e00c800c2040b84144000c00025482103d0a441d00d030854001c000c59071401c203120702107280c000d10300c10400d40148 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 686291079 1250 686289829 686289887
    0x19090f0c140c07060f120207030306050a060c031d0111030c0a050c040c0c0f150e060604060b0a020601030b1012050c0909070803121905240307030312050612011b 71
    0x204030b40c030a4030781d01d2510141140d03017940c0444105502e00d80f2040118400601c64007099091703031095046900944101c03e40d181d40d06001c1d034051004400c040d011401c4e00000245e1509003c40600e181981410b0003c1880c40c81d1040910b90380050386550401d51020440170180035040003205415042200d0510603c001c40e680100300f0408104000c051595500401d03080041c04908400c0218043c24204400251a048180e036014140d0308280558074201c00070442402000803a400754000f900144416480c685d076400843d1001801142181c6004101044401401c0000120240614024008403510404000d030147c400784c12a2010761140310108060b40b00801a43e01900c030101e82c204584e5102d084040740d480c81c403090045c070345140c00100030300344144071600400701d25042c50140c000d81c801c0c000e041e41c1d424140000707004a9000000c00641b0290361300303c1c0394000340140c140c0505005024800c2c1c03d441e80720300d0101e031069000e0000e8a20940c0045150102e070301d40c0201c607000b44842 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 686292329 1250 686291079 686291083
    0x1e010f1e0b010324030b0c07030203031617070503041a07021c020114250302030c030a1a040f0b0f0117070e011e020d09061d19090f0c140c 61
    0x10180014805407541c045007a10782c002e0b44002c1980c51615564005400030000c500e400d124180001c5908000d60008a1a901814401d40320b00943c140c00452540e1a440c00225040704610a50010400603005d0900700006600b80c0d1801030300262501034981c107241c60704803440050301007010101c9201c00100003445500007507100c1101c0c0c28401003448030b096028100d01500c02c11460903a410382c001c0501900e220141114200b0313200e000340041743d18049040880980c40300755104100183e091000c00d050506c00d50041d580072094064038090040400049810703118031075102c1c03403502e40d16401c02401d810308011313070b0100317100074030b480c0e0700d40c20482c01c95161280003d801c00d006c0100d008181d2503242d003e509201c6402d042c62180c5180c500850380000c0d600c40b2120440e1000881c5444001a00c0d400380c440e9050300300c203054800e1a42410b0006000c8100c0300180e101740303000314030300000810003401d11907110070380040a40892300882045007e020b0304030612180d04101d10030040d4002200c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 686293579 1250 686292329 686292371
    0xc010f050c060408161e1e031707030212190c0c0201140d060503070905060a0e0114010804050705040f1a03280606031a15010503090d11030403051e010f 67
    0x1100c80001d84410307220558401340300100740e000304603280c448002d090a2503201c61294246100e0418444030701f4049540304d0741d0313440200c0010049101d800720282c250514130005640720005160040c00d003009440b000980040c00d0b85c44102c045101540f20320324661070b00407080d41d8804e40c00c0c14003185000382d000170101406004038940c8140080344c64014440b55400080c01081c0081c101c0380d000341c0f24a9048020201500c026104d00d882d9500055100304120710035048800c0003440c0c1000f49840300c01954105c0c0c000b0000c49680c081c41c01c01065650320b500c58548260380e05600090030400320203101c1e1020201030241c512030750201324030045650600b20102903691a901c103002d406401841c0c030701c0141801d5000200301d80c0b0305070440c01c11191a103c00922619240501c0480300178054010f480e544425200d10880b508552101079449009551414031071580c041120b00d050383c0da80b911800c0191049114400000e01d101d0600d024009009034402c0c202c600404005840307083c0001c0d100008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 686294829 1250 686293579 686293583
    0x1e05090312040807080f0406080f1009020a090801051602011d0c1011071409100b090103090f080705010203010e0108120d0b01170a0203180604081204051e0c010f050c0604 75
    0x90302000182004070700c4044d13407541c540c080c0c1d201d43c44a4003541c4003074241d002402900700280038080041c4a42ca1402c0180c0d0054102d00000300610b030911300d800002e540001381c01800e100000c50002040b5101348503982c0f01c4c0115a81400f8004074540d8000e0079030308120708040c5251140301d11080c0c032142c04034a14400c0700301192018141d400407032040d541082c0354101000d03980107000000800c0003200c0341c5000301c11010ee545990a41e01c41624010303071812805800c0b003110080c000d088080d4025402012098010200c1003901504c82d512800d00d640581411103903030750040010440144035060490140606001505a41d42c03c06050400707405510102c090300c58030780e07907070342d5250f4041c01600010614440702c9201ca840e114203108040d5009841c05c1d0b05424038041d01542e4000c011817a10300803a0300244c000e2810224064150798404090019545d602840d006004007a041200b090020301c284000b0703001600f020300024106002c1480844d0500c00c0c00c010004140101040582d4000c1d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 686296079 1250 686294829 686294857
    0xf0e12070b03180316030314090c04050a06211412030c070c05030609010e100204031a100b07111504051f02011d0715050c2a0901091e050903 62
    0x41c0d035488801e822420003c007a04054040065001d0810355035541040116009807002d001c4401005e0314882c0a550858042c90603400c40003210035a13141c16007110380c004500e400d0128000e603c8081703090002940f030940c4c817608120000d18038201f20690010403103102812014008040a401c40e00341107101c01001c011100e0b0700028000c040240005d0698084d02010b4220761051500d403400e24024042e584409140d44941e10b0318010300c040d1b81c000c5806a03580080c1c2070300c0110702500c1c0c0b001065005003c40301810380585012400d0b0250b000a424114001d035041011812110107000726071841400c01d40d4040010003040c001511414075940d140c4141101400b101400356108900521014004020050f042c0d03082c6122088002810030a41e405005010030140d400401980c60340b060344075071415900180300296019084031012a5140701001c009203030065101d0004040b0300c0c00b6040514016030304c6003500c455000d80c1001c50844504d4980030800c80c100192019a03130b000b99a8846409 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 686297329 1250 686296079 686296081
    0x2060706090609061109090117030d0e190c030b010e1b03040302010e070b0d0b0405060d02240301030804081c1b03020c030318100914040f0b0901060f0e12070b03 71
    0x2200301d6102c030031081d40000042100d58445c09031504644d021600c0248640c90b048000f1560014003c0d001b480819000001c52600900d50b41c00009803074101c01d040094060a103c0d100240c10240e40000300c030780f10b0740300f24500c681145012001140f040e04080c1001444508100a540c0c0c418808101c1080f0320300c030303252a580c591900f21b001d0030300d0700b042d010a80107200c2c0000e5210000400780c0310000c0d40071800d001c450034400c244070031035400f225810f500c220580c9040300075060030001c0303401c4607050707039200c9403e944101c50510300c1d03500a910840741a400000c0c10050070320700340181c080e405200d400d2944032041c8001c00801d09140090340c0420384c2c00d2070b0b070740008050080203450480701d00038054a45030100c480402440310310000308580515800c80004030501c1c81814044140e540c2c0c041c0400640310420f0601c0000e1800c0b6040c0a035441d9680d007420420b68070030349124001c24240e41c07030207200d2051444c020a488040844203014408500012103c2c00000c1524015034840010f1191a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 686298579 1250 686297329 686297333
    0x61c021308010b0102070e090606061c0216020103050f1003082b020307020106050111100b060d09060e070506040308030c070813060801050315090613051f09020f0307030206070609 79
    0xd208208829140942842001400d032030190003444204109800359545541d480ca06861481800c89255255403c10340005006242ca403001e0322110125007100b466001800005c0ca00700c3c2e100884a903244948080428119a0b06018050b0300000540480080c0c0c01d0401c26200050410b002c028400080480c0c00f10000851813404804582000c0c0d0350b202c641c000b8140341d4029030040e40d01800550801c900812a54041c0000e44c04440d00103004000b21040c0340030711401003180b0484154060400c1000700c10760681802030441c0e450203548001140400c0e500f0702e41c54440c2c10761245004650510007000800c480c0e0054071b500c41c0594011580e24001450414814400c0b260f20b070380c03c403001c58804a8510790142006060b15002d0f03049031003100c0c01c1d03502c0ea0360b0f140046903101405d511480c000384042c00f0b6140c048000901c14012100c020051000710360000302035015100e201d541e622602415882c0051001c040c0d014103401510300507040d1340100703502c3e2007a0000a010580c41e00d2543c01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 686299829 1250 686298579 686298581
    0x190509070c26162906030c010306180c0c0b071106070f140f1b0d030e0a08030402040e0c03070b1312110d11030a0b0402090906160c020303070b0c0406020f010209061c 73
    0x4030501303d050344070360900c001e01c0e03140150360343c291801d40c0a80308014440d0f0203940681301d030100b65004000d402c501d00803070001140103440e10303494110810900b14860800210340110060154545440302824204102e441d94a0b000c4000c15100420108d0341000c0c230110b420040c59200042400d807620758448e403040303099105205035103410b00405000740d00d035184081d01040054a01415907828400030300e07821a015501d1010650142c00e00800b00007260061401e41c2c4841c65616000e400d0301c501d0802400060300f01221030748001c01221000400380742400c8000c41c140c000e0040e440b240c0d540700f00551128100f604e24180420301a80e2490080303030a01c030a062424010140c000e040b26940240c61504811111094504038090400e0501060002502244580c4548407a905681e901d128800c2d003202d410840700700c00d030b8240c002000848042001410443d20078018041c10a80c1c65103002c00003442d1400d451007400301c9901c184039446d1246e40b51801c4880500d602c0081d03030380114407041808 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 686301079 1250 686299829 686299853
    0x314250e030604030c05160b12040609140606010e0a08030a03020a090308070501090b0a090f0b070c06240b0703020c090a020405090a0b010311090906190509070c2616 73
    0x303641845014200800c0552040c8040501841941075030030203110030742101992030711805401d61600c3c0070300c03010f62103a0a4072031641d400b0f40242030114103021140c4070000503456902003e0815006001080b019581040c681005d0050540759501d5043c6040b150581780d0140e009008101900050b40c80407451040381001d002e503400c0b000b02559020246440740c000c182400c0201d51804444000900c5020305114001655800071001000361415684004007070748001d1040e414405180303039040108181d40b1a110110440d84001c98101103203d01021000c291a840003a03441b01c05c02184000a070b01182b010030221042d0f8403201c0c2c0c0e03103400354480c001c0d00483d00a01d410a011508001f41d280d034070381104240b14402c0e00d041241c0307030103002c003c5058030030107401c1b50f045104c0d540800c0c00d905042c1035910940340328140149115440e100082c81241059075000002219450307041d0900800228201c2c0380508002c0c030600c020180c0320488921701545400890052485240005101140c501e032 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 686302329 1250 686301079 686301107
    0x50a0c14190c020616150c0210090516090603061a0109060f0c1a0601140f0f0d0209120d0e0906010c1509060f0c0e030109080912030903030f070201031425 68
    0x21910340c03841703da00751080c0d14240707010b440000031402007210341d03030207803003071a04600c0a039029103d00c0d010b81418001a00c3c003d1412070341482900501101103602c2000c80d0094842002d0104800303185041100a5405d032045610000f00d04107055822070781c004214038211080f500740303414031640c02c0601352041200b2500290001c42c01706000440340b440704080d00e1107100d0903292091094141c0341c04501c54001c40e20f0314951a8410088401c101e030111001c1d1111616003400075203010711502c0850310100d0700c03a030740032115407051910703032069500051840b085940503900d401580c540140001c00020311141d0150241c1c2001d00ca1030100312081e0842d04000741c01c16400d00c40e85050094400007040d0080701d0b18000b44500034010214035040c040c10881c15080741440c0e00b800c4241003044004240d030102600749210400c0600850f031001e001405051241d00e1070a52a400c560002405a4143c003915088400c003900030085581810f0f101c001581c105552000c540701c64060090325904405908 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 686303579 1250 686302329 686302339
    0x130314070806330109140402071a2e26070f06020d020304080d030507110109060c080108030712031a030601080703051c02030403030e010e04050a050a0c14190c02 71
    0x800608800c060101c4909407144041e5000401404035801c1c0030041c8050f5007400104000c40400c02d6880115541000c1200140010b2070308c24070b036480c912802c0c14800103080e1041200e0421008580c010409519590121007402c81841c613815004c03400d41a44c0190490410811055550364200c4851021680c12602c200d0340426111005a00980524440c080051140d040b144418034401f001303480c1100c01c2c0d0f02c0244500214000290081c0030028032030020000c1103050140692400d00841800c14080e540004050146840c002d2000340e05030095102a4000c1100030000368200000740301050741880c00141301c210590000b2001611000a1f1b98140310b02000421010030129401040340c0c4944c0c100d82c40081940c0c034500342c40e10b607901c514015800910042000c00e00545480c0303051041490090040c00391500080c0496500760b41201da03980d951002c04c0510000762213400d9813001c403420040d400650034508100c0d80d103d0541103803051171010507800c900d0740c001c8040701e0a842e80104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 686304829 1250 686303579 686303581
    0xc060507030905041503150c121802090a02090f010c050d140f0a11061003200409080c0a05160b04180e0303041b05100e01050c070e0c0a1202130314070806 68
    0x117658550301d02c24001550780014000001a0400ca20312882d058022030b074440d11007003844d09000c100282203028403010f01c040074980d4400180c0c1c1d11015a07100b140e42c0c110068980c800343c014084445400100b4030f044c0540012440007060000032000201903135840d010b00860511000b0400c580198121300c8008500802c80c2c0341c410b9005104108050701c078108507000e41d13542d80a50000d65400744809024411011001140c0c80c90300141800c41590207000880c55002c00d903181d0146511500c51141c1d650421254a0104403050241d040311501c0e83c40c03603880040c1800140b45140c81144100d0b102c410344009414805a1207820441c0d481c0082801d40c1e440f86440c0c10540394605902c08010a01580414003040500e0300c0100c0c081e1044084c0d032105038420b60305005548503800414884054071926400141c103080c200002c5105d100c02c1a00103444418a01d0040c283c900b11448800e4003600500c0060214056500140122500a01d00c81c8445005d8052507040c11a16000312072a401103034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 686306079 1250 686304829 686304851
    0x120907050402270f09013609020f0109060912110604030b01031a070c020108090a060507090807090501050d060903180e010314032b11070b0709050d0c06050703090504 73
    0x280d108000d024a29041c0300c002030400400c42e4503500c4d018016400744020005100c4082e42c1d12021442d80c800c2c041130311220398101d41c000529401044020040d42e00d5540c1c41d070840c02d02240911741d402080c02c064031000d082101c0a42000030501405012801e0480c4000c148480c00000c0c10400b90040d0902d03648940783d00380041170710000d00050700c0000f000c044003030204034686c0c00144260b09950f143d848040f9242d00469240d035014211aa4601c201c8150101040c440d1080714002c400329150106c0c100e00e04441e940c01c00307440760310144d031a5244c9001045551240d900c1400c1860b401000025035401c02e1030181ca03103449518500c00c051000035800b1410201c410812410b8038041c90140e02c1101010000c541d40e4803030713902216801005d0355001d9998203080001c1010804900c540841e40425910f9609101d40140a0507540b0446940512020503002200038000c0c10041d40c0d41d11492125440300912448544650b070300f008400100c00d014540709016120103818014010302c900c085030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 686307329 1250 686306079 686306107
    0x40e09030c0d090308040e131211010f0204030b011401050f0a03020a09050a082104090e06060f0405010e070c0302012a090915050d11040c02100e060408120907050402 73
    0xd48510740e20340c4200c0d1088848540035040b101c0803290f002c02001e182c2800c00c5660400c00c03002506111103500907940220005020340e012030000ca5180d40d404280d4a20258410309507039620000400c0288100001d002040b4070022160640d25054070f40b1104d0320400c3c004840b140f2580882580400d00840d165801640c51380040600101d0b5503121182d09841d442040001c2e0030b18803600802d035009a00303030086100003680a80d0000c80c03a0704110b0615550320040b4055564500020304240c000f04208061440e2055800c540c80c0c6050781c0030002d941c1000111407107603102424000034130003580e41400030140f003504085540d1500c0021340759409140d03c204420b00c0e0907100e2040200301c441d031000c2501c921500c9003440ba03e05458a8402540c90a41401221402c099040d642e49868410a8486440d01e0051030304203030942d8000d1000d01680c81c1c1c200201c42548048001541044040c0408203e000341902c1c841c00720305504000d1500e40c102051300c0c14030194000d0350454000b00b0f4078031106c108 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 686308579 1250 686307329 686307337
    0x5240c0a02120f0705040501141315081f020309030a11100c09180c02031b07030c0e0412090315052205011d012003280522020102060402040b0105040e0903 68
    0x80f190840341e2083d1074208020907184240581488003404015000c00c51510301800c2031409403002000945213511700144140c21402c0d040034610764000100344d425604844614a0780780e0a08100b18118100110195140e100da440c0c124100002140170719003241d8103114002c001c0c20789010401400c881404080c01c3c000e01c40c4110749801072940380b42d0507003c0c030f2805442490010341e07000d580b40c1012a42c019120350000c84600c0c0142c400d41d400440011041e411520140c00c201c0103409aa18042c98061118580b504260040005c01881040001c400d03064110007032140724030104080e03035690481b8004001e4090144086195113103090148401940080c40c02487d50017a0400030150340c40312400c0e82c031103100c0a11850240448009504014006190000741c0d041e0707001900c0c140c210700013014501c411086400180d0f1003050202041d0300ca1400c849034215290394000115051300041e445420052020307016a0300c5104841c8987e06c20012500605030075448030000c0d00700141d001d5540d0304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 686309829 1250 686308579 686308603
    0xe01050a1407080402090a061e17031620040222060f090e071403010807140108072102090d03090e010e040c0314100c0e0a05240c0a0212 60
    0x2140201c0c0c5903040a80e01c02140c854403068544951648032035080c4030310345900070038940c10a40d44030008155407000d165084090803081801d030000504001481c1200081115182200e44c001c10603c9580400d488102c051250048241c040d000c0c401c945150f0004030780301c03c2560144c40081d0f030341d600c210080859102c1c24030303086010582c1904c1d4041581d4484c0410610804101c0c1a10b040140c6406100e515078004541c6c6020595000115205415070b00281c000207920313000700301c0610201b503880d00f0800500000b40303841905420b000401400400c1400556040c0000b0030b451040240020b8045510154016007612000100360800402260f614017441015091074400080d400805c03004031401140c00c00254076070303a49156221182c100400c55a41114040c000d103c1f02400000d118207001030b1060744070113081e24800010400741c03840f6604824481d420350b0100800e01c900c001d94100003c40d0301110700e580c801c1c0c0b11495529100030048020b502c500c1c2503400c030b0203070900402c181d08920 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 686311079 1250 686309829 686309831
    0x1e0602030a062c040c0f03081c021303030e0a05270a05071b17030414010c0f05091302090402030c04030302210304032703050124181e0e01050a 63
    0xe071508101c24541e071003440308100d002162403d4422100c0d00c1549560024403c10707501c0c800e40d0307846680710361202055000761400034022404481840b04080f03680450408080114a03000345000f45080507101c5010107010408840d05a5085441d0b12000d1006404002c141c010515100030420401c00c0f0500b4081034078020a0f80420316620450007500e00406054541c10b0701d03101c04407024400600300d00c505603211400003124041158620000758002d81c0101401c1410403960700001703080d90000320710342e010054141098090745034031000791081c0d04400c03158040708444120940700a4010003544950251002042c044c508514100800c103d0b4465000c4d40c8030b1911098440000c81020030049480180400c00140020720070300032008190342d607912a542c04200040101a45442900116002c0e0341d00d16060140313100c002c05401c1c1006803141606009428a02400710a942a46450600f1174031440f8100001007150080c000e2091a0341e4100248a210b2111601034002515040c03425 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 686312329 1250 686311079 686311091
    0x10f0801180f0201050c0319031a030a0b0f100807080114100f050d020109091b030e0327030a0215040f06141209120c061006020d1b1e0602030a 63
    0x60107296411280700c81d0400d0a101400101d5001901c06a00c0854110101d0000f0800000207510044060f441d580b4581d4002820100190081c98405402031011b4825401042c01c240058210a001c641c8a4000b031150451511038040d0f0340304080c0150484001e5000742100407803d00d40552003180c0d0031703260984000f51a1104020f41000c11070b00d00856070081001c0a0030310190070f0007201d40720342c14418500110382d00d5484400b0340807038407920025600b9883d9100c503e03991940c0f50040c20f40b108090401f8600c0c0180e50910900b84401c9070014141c0017528400a1001c0d507814004d046001e81c020b0654000032480c003071100040d80c403501640c1010a0003540100d880c51140c00e5008c1d80c00c80c3c0d07440352850304d000c1910345006000c000305010501e10401c1c80641040360078401038170210041000030070050410460002104102d90071450440d8404405a0040c1d98003900d018000c041d0700c50160a441c119090031420030710006550026026032956902c00c0003142e500443c843e07103d4810401c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 686313579 1250 686312329 686312351
    0x1090b0f0f1306020711090c07060e030408031b0a051603030906030203010f060804051f1e2a02030c0312010806180d0f0e0a0e060112020a0f05070201021005010f0801 73
    0x4640d001d4840500780340d4210781c03502c0090f010340d0060118902910000040180241c00141c400c102107581c20300c0201d01260103001c06c40390b03006040104c6c0c4d9440c040d40c10030b030034010b0240e0f070380c000c0491200302c1e6291161038410170741091005010703040e086400d58901c42c041b0714140320000c0e414801200000e041c1d14001407194424030969068554400e0203180003458580c2c0ac46901c14080d0003558a401340101d2202012241180e02242c219030580c082924003540718011030b5103440306010035100d400d20fa10701ea5111142c000306000c00c282050034007162004104101e1440c000c0d1200c0c401640720000d0f400421207200030b54103040790410001c0380e5150361000d642e8080c20b0307082c00e44e000141d400f5030000b44170103005680d2104520320f00e10705a642c3c3c0c400d9000107a0903d103150f01c00030050017401705000d240e5174400d080d1107501030f10010a5240500c1180000c00307084038807518108010700480c40804580c420300841c5a84d19040f9401e00c0f0319611903008503551601c51042a841e0340c600b1140c400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 686314829 1250 686313579 686313601
    0x160501020a2a260910020c040b0604241403090106050406080a120e1207030f030206010605040815042916110606090406060f080a03080f04150c09050301090b0f 70
    0x1010a5026140782c00c140404450f4560441c07402404003550002400003500640301c19030501c00300381c0700750f00802c0c0804a01050000726001a846940151410071091100031a00c0c8541070f580602d9450302c400215015400721803003001d204c84403080d10000010700ca00204150014002d80d201181c040200580c1d4188440d6540301080c1c0c0100240040704000c1c0a07240503860320300720980054888541d147c0d61900250401090380c1088034a10241141841450350410580303000d0085410860319007401c2c400000c0c0c1d0fa407000c80e001c54014220300000b8003004900011038a00030180d43d02c0c0c11108020f0050a5548003049400200c0038054440b00540c252058a1305076007111044050852a160715090000325000200700b03544a0b45c481e800054a1201d910040000300054400303044040514030340105407510240a0013090f400040038030000c00c00149214030555403029001070780e0364002e20140c1c5d04110700c7d44000da140d481c04500300280101403a920344210080d503c131900c55507404400300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 686316079 1250 686314829 686314907
    0x60f01091a03190212070b042103120522060504020f030d121d0a05060a061a04090c09090c09170f0a140102070804141f0206060105160501020a 63
    0x60782c580d002080703c02002000c0c15030700440c1ca0014044007003c52444a08920f000c00580c00383c0d41c41d80b0000303820004112001585c2d8070900c00c011011421071403a440081c80055403441c00035400c0e03650f00205031140c20783e107400c240140700081c0c40e225032505401d14a008040440c1c0076801184807402c00300040c030f00420380e201c01c802140c44070583c040040b2140002846080542241c0800c20404262180000c0181d0340e0a0341c400c00007050f0600d025801c00080d6411580034200880d0745861407100c00404074141d0b02a60203640000039846034800d4101c0740c00748a544003100403450500c03038400560344001ea020070784419181946088502c0b181807a601e0110b4144183c25422101c901c07000203049082801000202c10009410a44151201802540700750b1001541070030341542c031a0b0504240d010030381511a4900352000c4841201e1002c0c2d01c40304010503c504000001414107003a1011300110100f00340c0080003107403208072022024050000e003500121044141c0008101201c4405c1841c1c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 686317329 1250 686316079 686316131
    0x51f050c010b15252012060901050105010f0f051b0307170c0c090c030106030b010203070501020c150a0e150604020706060f0f1703040b0a0507050d02060f09160b0906070203060f0109 80
    0x10303111050b035440d2610340b21280060025484910805541b010010400c0032a000c2c10200000007030652400001400c00e542000301581800455001d00c101690008140c5140c0d0044034140030010756803540d824294030900c00020003c0d0307003000c4a814003200940180149000c05130031901540c1c1c0c2c0c401005050038080f152200c55000810060103860301c243c00c1030301c1020040c0101ea04011503552402e003a6005204000650b511580e0814a041103007c1040d401460045003044001d0f400c6220300c2d1150340d14507140015403441700c0403a802d502d941e411943c0c142e0f04001c08104942d11214212031180c840d00c00c45c01702000c035140200b81421929000c05247e41000000d6103030601c2c01240e581150045100c50060003424800200842c405000c000188103490340600914600b80700036a41920018007403174901c0d441040410001b80d1a52480d009492500741581c0d01d41c03030104005a6075110b0000004d40501590b414040010b84440034a4165180304a00340941c04102100003040c40c090005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 686318579 1250 686317329 686317343
    0x50919020f1003060b0708130501030b060a270314010f0204050109120f2003060c0a020c0f131107060b040902060409090c030501020f090109051f050c010b1525 70
    0x81c101901e0203036001c0000b01c40e14203002c104141d031509410459000140152079004000455072100030012100c84080c080900b000c200701d0703030b071440402c00d00d00074182d010051150700340c0d292140b840c60010401d84a80c1c40001040200c1d168500905a503104400e150030070347c03e020710280f0a400d1402590103544069580a510a1511184500d042041c403001e889282d000782c508408038030410080c148100d91907803900780400b00f0300213144c54208020150040303a00706010f00b82e05940d01142ca5140540c08480d400d00c80c1004000242e2030f260540380c0d08072410718040403401182207403409841c02500604040100051400a101c00d8a401460081d48031743d08000520a802c078130f920061945003d0f0f20b00c0d840140d100c0e43d8284c06c80e800003001180c035003004a0102c0c2c656a000302c004002d49410f444219032152548250381104941c05101000d1200200308005e241c4001d5001c0c802c5410020440c0d1400a445821031000c3d5001d41c101d031b1482411705928a482a0304405d40041c910b501240c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 686319829 1250 686318579 686318599
    0x31009110306040f032715020c090603030a120f0903080402010f050304050606060d02071a191107141c050d0608160603020c0a02030111180d03080708040c0e07020105091902 76
    0x28044480003d01154596074501b180c21210803024102c4107070000d00740b40c1085801810440d18007900e00383d941004a40b10b9034800782000b42e1070b00c0210590300040309600b04200c4a20042070854050302801d6101c00342e0030716000c00e0b03409050b84404864013a500031307241c004100300e5100045405200c119000303482da60100d030115005040c1a402000c42e1121140014207000180e505c1e41c02c080301c9400880c0f01003003200300b48103c901d0300c034181b181030481040d4100300300e002d038010388a594022a507002c0c08840c0c0c8020300002203401800080042c409504103030020036080303039000c1c0071600b04403000341ca07070752501802107090701d40000d0b020082008199520501482d0200440c003940c05650034001c1401490700183c01a1001d00400d00488203440d10300303444040702441d1400c071038050303542d041c17254080e084240040782d005040f941d0000020303d0030058980d50390070302c0d07911111a503210702268044103007001380d0703a035065102c1ca000c5c407000c8003907541011182240151030808100d02a60000f1403070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 686321079 1250 686319829 686319833
    0x91b0d020d0e0f0c0910080f0f0706020a020904020f04090212100b09090a0f020a09140a0c050a0503010e06180c07060c1e031d07060224012103090302031009110306040f 74
    0x1049441d84004410450311b1900d03242c4500d00d080002c2003954000f01e034420316907201e880b8400c1c40050040c14a40c401030201c51695000106840b00140001e4000c03001410b0180154582d9005011490707005030004884d65500c494896941c16130b0803031391922514000d191642460200c112070b01800030180100909856501e50414458452104a074060300c680d00000e0140046e0058000c252a6036080b0751b042c3c9800442c007420f0350350b05840340302081020020380f401c00b42c000c41a00d040d54180043d80b051a6100b101083d00d03000c00c08842c1140a10b141c0c10041c4001c2d02d440103241052250b04240315044a170101992640c80031210305424074500114101400c1c800e130702441640503844248186600ca0013a0941003400325005040140c20011041d6081c0f6114410000c0490340070040a0311503160029030468030079407a0602001c04084070440003414800e001520165400030181d92051134849669030003408818070450b4007c2c11a4003078180c9140c080740061040307030001740c0500140c0c156 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 686322329 1250 686321079 686321089
    0x27320604050f040912020a0302070906031703180a0f200105041203020109020a1d010f0f050d0303022101150503090303040305130b070f03080603061302091b0d020d0e0f0c 75
    0x102d80c10394015655000e024082040309205400446464000c0c086003501e40c20001e0a0500681220710a141071900400000790301602c1504640704094600741c4a40310f0340c1ea241158117807045807541c1803240c18018000d2007401e410b5864480c2c852084039006500c241e4000400000280c801800704500f80420001c0c42820100030741054460710000031061525070004480c2841500802400990781640d250700d5903910740707182d000d4140d0140d0305100c0c8d031410b05034015102c400d02502d0b002d111802e82030400c050003501614a8235404021544c0180017400c4401c4000f4000d209056590722240201c03000d082c0a01c013101d005d411030201840c82c50b81c607510144c400b81c2c07018040c4c0d02c45401407030780010300202500290034034600c01c83c0c0740d0052516070304004200ea28090541c0744079800840c244522030320319030200c813800b03981640d506407030796100e0503900c1ea140c071138120420380c8060000e09000103424942c0148003041c0b41c400108421010f84400c0c03503a4040b02c0c0701194081d07000030341c0c800880c500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 686323579 1250 686322329 686322349
    0x60e040b01033803101b0804052503080a181403030904050615040b0c0105060108090a0204110c1e01050108032d0d020c060603060105150a2732060405 66
    0x120034500f040c941c10007001c20314107941c0c880d4505000b41e07034410300291088030f958000402e030210316103000745003040d464040e15084100d00300310340d0004d00c622003010300f41003004110066400c000041d445013044807001e003988114058202d803150403848c0100d5081c82d03400c00100d21500140045003000c8401e824000144800b8140c1a80f001c540301e020748014a03844000d0014000c62806103407208403804541d402e403040902894140550201000b06082d030004060354900d030100c0b80403c50b408100c8100c117262052916007080350095003800e0004520b01c0f15a100c51042d54402040182e0707075546d040d0b44900801c4a01c1c94109201004001e111114081210b40001420b115a1034032000d6501078089a10004641c50b9030f40203c0100180740c54180003007801048151a500b014201010424000384903100c40c60040c81502111089103030b51400004418070f052070701d21020305e41c840c43c0711002b0448000600554001058103944e669a080c1044d180c02900038021720300b080c0c1450208004020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 686324829 1250 686323579 686323661
    0x1090b01080102341e150b01080f040303290a09020a02030702010507030909060f170106060509040c1e03200a050405040c1704080307030b0105030c040909051204060e040b0103 77
    0x85035610214410714131700c01c1448082c0007900a0100d0601d0201c501d42c4450742c409076080e1501ca8070001998110050070ba03c00c582d0403040b4055a5945425001030001075410b82d04131700c0c164241d043d10540c020301c65500200441d05400150780ea501d188090b84908607103000140c005010342401940650081c0400520908100c0502c0d03450ba0781c04000c03121a075010040c0c1010001c02008003d648041a810700160b0360700902c041c0341008006004c80c41441c2140f40a29601c40a151007180301d10000b03484003008009405582e910b41000030301400c4910103681c124a060504070714980c032160220303000940b080e104c5a0801d8502000c1000401c40c00d50003500340002486641050f2880d000e18a124a12030342d0201d03180e003081440181107502c44070b84241802802c10501031000705520645d0102d0f03440307800114400d525403400e0b41c01c0034018403001c1d2083c00040340116800da04980c007421002d400340d078100001d101c5800118203540c4034041d10110500786604c0201d5145000c021085111 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 686326079 1250 686324829 686324917
    0x100207050d08040212100207060b121b030304030b0a020307030b030a0c0b1c0e0a0c0602010b0604261f180b150312070809130204051c03030908030901090b01080102 72
    0x4070521165070400c82d2007846c042003198000350b002e040002034412101580380581d070500411210342c10060307031400d800803001050310228600b800d91307aa080007120065680017504c4a140c0c20044501e034040d401c255142000310b403c1044652041c180024400d940d2500002092030b46031906441c102964024804210001d2940320641c3c1d0100b480c1c080c03114014500e0300203248111035810140017454040d00074004590401c00300c0320290f44e4201c00c0d10180d0f44030500b40312404240701003403a2520f0701c0c0c160b56403450160340b0440d00c840d180d04495075000e079440b800078001c0c03400381c0c0340c0480b175030041480040170142030340b001c900c000360b00300001c80404c40d02804443d161020200da082c020341201008850042000034201d09506040541000b40791414505604244c02c20001641d03001c40b1003044401104009901401d0511139005445115044080c1c155a070500202c0d0f14041c00010005948400b0800000200c0c0c036414401c5840f0040c100320311000800c403150010f80c00142c1428541400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 686327329 1250 686326079 686326099
    0xf1315020d090f050d271707081510061b0b0402010e03060c1b030a051b0c04060b030403172502100501090c1407020108010302130f0c0809100207050d080402 69
    0x1d80070f140881c1d1420700910013001170304007822000f41000007401c2c20002c0344d03024451130b0451442c800e648805407151100100130080000701034514041d0903038800061482010750840e00001c042c2c40d8980113601d5a40b04540076925424113881200c015090000303e05001c40320000410362240030990028030502d0080c042e130440d403000902c0d1480c1651005034401c000074600280000081d801c011188010015605104e04500b01429a0040b10910340c5003500d424a100030300c802c28851415600001081002901d03110b0340012410b4000302c0b0b0071404176020466140c82104070055661040a000f00e4428000c0360804101010704251411803056209500b21142b844410307008241c0070b01030b00c442c00501514140c1008041440c0440400c4a1030810040c00f40542d82c060308403815641c041d5096451564080300c003400800c580c44c1c1880b0658604900701018a40c09400039010794102d40480c0c001014804c0c04c18203d2042c400020115400400e8070070300d89001d0039040d94801e00050012401c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 686328579 1250 686327329 686327333
    0x6070b06040b0d060f0f090503070813080703080d0c02032805160f0b070c050a0b18030c07030b070509060712170f1006050f090409050f0a0602030f1315020d09 70
    0x1c80b100b9100304a410345d17120390308490306600c1c80c0302e2800d80e5419071105102c460810b0301d40136124403603104003912201c0d0001d00c03031022030200c440400060404000311004c560b687d0818007200d030002049061200e00b00044001e210b4400070996850b410b001c81b060300941700c507000b030700c0806440900000c14030105011110203c3c00200e404980a0b0180501c11a03035001c81c9096502202c000b8460010b0200c08000c080110350006042816a03600215508060710303507079a9205945612141003070f45100024140e602e0000c045401d808880c400c40f21011a43c0701c0c80d0086e18680a1034444940180080c400d0354089818100f1703003440064241451141d1080a400f00c418945044a45c00c0e030700f49003801441000349510125000800310ba00d045810296104414144c1c1e04c01c0940d0a44210307100e000e104140300c0e051040404070468502101e021f04403610f00308000c0d40048a81d252038010740800501b44040c1005000c12496000c0e4051541501422005009401280504a0751551089041c0c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 686329829 1250 686328579 686328589
    0x51804180f0c050916030b01021e0d0e0102010b010f030519050c07050d3e010507020c131103011a040803040b070203060601180b070206070602040b041d040206070b06040b 75
    0x103240c5014902200d0850140c1c1000700c240d40559000b54000c036181350070401424410130310500541628500824140c690000403447c001d03100302010081c1c01a103901010042e000070300c0c9054251f42c2d454001541008500590883d0480c040007804500c0340f00d001040140310364070043c1d0010300d40910701880c0e13251308220b83c21600d08880824200000107000d00c1805020840440c00100600e06860400507900c030314a07a4003841405c0c0d10921050f10141c1c0e4510440055014182d541040204282c4c54050f10007903550509005042c09030041d01e83d00e501c1120300e80620300951301c1d150700032071669280c8440343c3c101c90f40c903c240e1000b1440c24080824010800d1000744010603010151980f1202c00740100340c100000985454140510900000201c500103036201007110348003a9041c1c0c4491b51800031800600c181d040c002d101910011303000ca9813603030010240054130f0b10f0741d000c0b001c402c0c5040e21071004a82c0599019500000600c4001d00052020726025840b04010303001144c00303040f40740461 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 686330935 1106 686329829 686329871
    0x6090307150e0c0d12090f05030304060e01111b010306170a081c230105030a0c0504020306040e01091a0c091503090109020d05030d110a051804 63
    0x5940048184050543c816010b40766809000091501000030105e13015854003085800601181003400d0090300020f0300c3c4041e005503d01410444261010103044942c1c504211415108e4040c3c24002d108407070b0303c070f40303840110103480000d01c0016003955040d42041c42c91403042c3d00525040341c03000900080d42030700702035051750f14403119000b84070400301603c01104007801e1001107060404100c42a5028101c19507200c0f01c540d88400c100340d16545e01040182000c122101c080c0005c2c501035000b95048440140005508400750b503155080d41e0301c0d10003e48400700c48580c050310301c8035042403441d404480003903170302d00e00032140c40000c80b03845010020318003008022000824000c02580301e800f016070010980c25802d443c5203403565503640301700f4030f05d46043c0c1490181c40c2c040d81c903c005c0d41d5140215880340c5082a1003d6465022198000c9840d940961248124003107031300d40704041 = true := by decide +kernel

theorem cover : BRFrame.Cov 686151079 686330935 := by
  have h0 := BRFrame.cov_init 686151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 686151079 ≤ n) (h2 : n < 686330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
