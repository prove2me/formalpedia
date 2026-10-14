-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1262
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:03:23.421228+00:00
-- url     : https://prove2.me/submissions/eb15a3d1-1e94-4b1b-bed8-401cd85cf55a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 226798561 ≤ n < 226978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 226799811 1250 226798561 226798577
    0x120f010509060d11060714100507020c030a03090b030606090d08040f0617040f050c040f020301180605010c1b03170903060a0b150c01090c0b181801060509030a12 71
    0x6850401d0100c0d8010800b5140e00420b100a5a99010403a01082101d0b115200c00314004080141d0124000b549a201c0e034241c41c04650b0410240000d40010369114000d030045140c0f860b45814006541d50b031240c0c040d0345551005260600c40d0300594005020960404002c022a148644462841c2c108052050858582d02d03071800e8038503c5500b00a1308a9030800c0049003441c01c41e0500d0306d14141d001500309000c08100c006500c2c125103801c11000040f60000e0400c01c8000c641500c55011b98100c43d06401d029055080c042c80000485155004181c082005d5001e9040801c40d22480002c904011801c0319543d1600c9403240c2e1035224034041d048400040000781000b150409020440c1c101e143c0034404c1c0900391280d40011108400301a441c682006c0100301c071740c20312000750045112945c00c0218040019212206d0648031350140340d14220f0901a002014003600b40352815403014440014025402d0b400c000701194140e00c4031140950520601d0806000b01c0ca96014020200e1166201d80300d07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 226801061 1250 226799811 226799819
    0x40b0703030b030304060c021c0b09012003060d1b080a08040302241902120c0d0f110d122904060909050705060a0c1e020405090c0f04020c03120f01 65
    0x2030b03901650115000c1e400500080081c3d60304041c5031030050ba0b04440d0302410140801c941d16141c40400005000780b500e40e000c0c4041c90606600c00751103000501e40340c888040b100322440382944030907521660808000802903004c80da5581d0b9003890325080c070107503800003951080304510744001d450055509040001d000c000314079000e01c8141c7c0c11a030307081020048055a800030340c2c4030301581514900850400b88a06074081c8203000c0e0001400416540341d407603101d1102c170196940c803540e1020010403a0361040840c11802500d1445e040b18110004180301c00000303008440800d800c80031006601e40301c1c1a100e08804008005410700315005c0f9410701000540400c02080d1192030340020348007440d080d001070210b01c0114980701aa0702c10f85001381d441085003400c80e5588221000074102c01d0b20301d00c0c09501e003200c00b803066120340d008031303820f115540b1a5220f19460712000305071306600078001d4241401c14145900a4460145010250b0382044100300600f8100802202c0c40080c1c81680c100600c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 226802311 1250 226801061 226801067
    0xa12080a08010504050405070605180a030b040b06120a1b0b030403020d080a02070b270712110f092e091e09020109210f11090108010b03030a030e07050402040b0703 72
    0x1e80101801c580c1885113042945500b0f803207a071240164030420000103501d010044586526110204c0084c22200c001503403030800c02c0c1c0244046e01d01b22405405503020400700e1524004058200c1c0000000e8036642c0313440c0da1081ea10b984540d0707030441041e100400019210140b10041d40c841c82c0a90080c04000003440801481b0030790042030308598a10500c020004903095644080e4800340340c0c0054103a944460381c4451601070380905000c0c03944a82103002c00d40804141204130304034881c00d82c4060041c4004e0422503200a65882d42e41c010000c4030015907212001c00050006d02d10440100030043c00620180c2c0314149039810903148251150350b11a640c50b10644900c005040005040224103666170008025425600c92848070070902d2803203400080180281c44001d0394820386d02c591140e900c0c90000030a10b40c0800a82c4615007013000012044410701902c01d1208008001d94036000c03640360242d0007400d5201c0e00c1c0031188100040812107403641d10060015040303601180b41c841c80140340003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 226803561 1250 226802311 226802327
    0xc06050108030a0c03030209030c100507051b0d0f02040f022101090614060706061d010302010e120c0d03020c120c101803060906140106030203060406050103020f180a12080a 76
    0x12065503000b089030f0010540c2c84100c8440395a4140303030240e40ca555210001f03281501c0300991070341c44a049048a41000e810100912805202e50113544403d000e100f01002c100c00004501c0390002480c0d12400000340d94051818586440104001030b001d50780321040c0101d810040100218410030000010039490f00a4420b0040c010220203009035810003651044d1015032001550041d0740c003041083c00c10046420820180100300c0e60035540003100040104103c10038030069000c5200750314202c90070f003013004219000240c0b680050403042c242c1d105011540045010a604500901032540e585075101d2001d01e0241c403101c0000e050030098441000800032003104000d09200c883e1400c01070884514050100710703500640d0000c1d8841260804102400c880f0006050213500c03600042555a05a80075500442d420f0750100109a15400154101c1c0306a800c032154443c814000e111400075042d031440d003201c40c0540009a00d95449101c646203081c002d0003210101e1001c1440401c00380d100c0760b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 226804811 1250 226803561 226803569
    0x2030706062702070206093c0a05060c07050f04110c010507030b1206071206090203070906020705031203040f0c08060106030b0f010806180a0219020a12020109020108191b0c060501 79
    0x840c9000304542c0019401e10580c81e80d907010f20a0b104103000b40300c20044031003000314084010500c0d0f003041c911400c10911640008c9a01c290030000d8003141c18240b90b0b09440400c0700c004003d0099900b003c1c01c005046c1c0b07686229030350250300e8400114001c1c092070050565054124004509030801040141c2607504131400c1c2401041d00103189030707003003074002103690b08580036003440244042400801d0340507045580103240800d000100b0b06c0702081c0c1c01140d4500712440c84c0c6c01d03201c1700b54554041649856502c0ca03103032002c56052005c81e01181e40f11580d01c0f95144a0791901100b41d81d101c44260078030034241e022070b010994039900c868140c1011851000344040901c1e000d0100d240c80000940c00c14070f2600c058441c0c9028400240c40d120780369044a420710752510030054600d8900350000e5481c0c80d40d0208403507400144c0d101c031620f036005000e00c1400540c140c581c180550703101d100c0c01021491040c560391644e070329a880c1e54444862000c120150704c240d90344082003c61241480402e589060748 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 226806061 1250 226804811 226804889
    0x3040318050a1d180a030e01140c0c2e030f060305010e030d06050406050108010b030711011a040e0309060306120c0a1211010c0b1504140a0c1805130c0203070606 71
    0x32104000d003e020510b640c5482c0c3c14100f81102c040310000482741c0070100035806403194800608096040d10002e00601d403248211582c200080c04809901c0140071004480b6401180301288812024001d40290604c9610741000203081546d9490382402d407040001c482280b9000003c210007008407902400024060a41d0306003c10742c5070074002408080d0500c10401440d03400300100320018810140ca00b00115078400074000803800900c9014551081d0b030500c3d115916000310343c801c4c1d007400702c01d0300d40f0504000c00c41c90a554403142803154484001010100c9400385448018050366500c0c1440041d01501c95a0458040103281c140301c1c1c0310242c11341c14184000380c45001c0014055410340c80c2d0201407110349205c0160340c100400d000c1e00440c07044c0d51203140b0305010000c0e41c400aa00c610040f100f10f5941440380c21080461403c08203181c059540c2000002d1000000c0d101b25410408050b041441201c0c80c00d41d10741c6031102201d80a401c040d42c00c0c0b0b0340b1540e03d440a0460b41c030702c04550101d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 226807311 1250 226806061 226806091
    0x3120d060503102009010c05060705042102180403050d05240d02150906160501050601021c0906050703091e0501030b0301150905040503041701061d0106020303040318050a1d 76
    0x1360030112000c0f01c81d0f500c81031002001420f05020f034898444454900d070700c00c04aa560741084403020307006400500840040b40080942550030081550f0390700b0b40645c0207404140c000f0081e0035296a030400c014070036410b10208100c03007021241d1510039148900d11103128914501051000d1f03804510f20f12401f80c3c4210003407010f00d00035030742e40d684416405000800c060b036644030160100b40036020310045140c1c0c02079110941414030030103400039440b0f00400d070300340d034800880c1c1a0b44010b8417081d00380010014031404c105100c0c1034003c40003003032498003e04000c04415514001d5000c03407244004c0b89809041002c900b0403003542c0501400381102c40890090013100c85404402690402034450b0f400e407071380c41e20080307403d000b0184200c402411050400650205680101c40c0c043c00307840c0704070315500c508940708605084262040074103803651540990310355282c0c1e89003110302140e2020310406003000b5080000d190354600c415a03004201c48901c000e845070520640c0c44100c40c0080c000d40400c0c901c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 226808561 1250 226807311 226807331
    0x507080604020a050636120304032303030a02030408041208091002030f0702010e0406090c110705040b0d03030b04240618120308070c021314070f021b03120d06050310 73
    0x2600d40e910a118251211ba220b503030386820061030001540ca1058015016007214884040c000c0004d100b92805061f07040a084c15100110b0801e08840e00d010140f0b40090000c180300c0480e5030000c40d0028091040141003544500309207a42d00c2000f281142d5a010004859105084c01c101d5512140e0480c00a503080c0406011031030304034441c610009041005030311300b00ca00c582c0c80d40d122402400b00d4440811601300c54000262201000007010200d030f10480b94002007603d01806600c6400344043c22080341013030140d50580103442d000c40d20b254081e8132042e03c8600e050869440090300f035244500302c1803461034081c000d8003503003442400414240e120007040c003801020040022409074145001907081c0d4554034126201035007024000e51000d4159144080e62040750031020418071034060084064817942e800350340c4510703134005c2c00b00035802010480041c51010f0740d207110940c4010303080c0c2c1c0081900103d00700707456004a0103000219900c034014442824200001400c00101190804c02c2c4021 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 226809811 1250 226808561 226808587
    0x70210060812090d080c030304140307020a0506090d171902060402060f0c0709020708091806180c120a0219090b04140d051506040b0411091003090507080604020a0506 73
    0x1110b66069501e0302c0c0060107000c5078035503a606254150300215055224005200390545960050720140c50701c01036503e100c102d030310303001c8102e501003903000700f40c00032a510341405c2c405136801c015140303a07005145000c0c40340031a260302e80013031105001d614010f544440804218a0303280c0480b8402c421540700f5410000143c5030702048030401c030111480d031503d0380d001100340d0b854054103030030065481e800824a182000000b034041c0103541411581540d40700406d0390800c85191080340c2182c4e1103d0080b021403000000d80c98015003005038082c7c01441d01c400000303a4145048161216140700b5800601310003c5800c0500881a400d928a80311840034681520700140f40102d0080000205402c1001001c2d40d0b611990a500f41c0c2d400310648107903a9450450b1005264200c0d1098022070825071190003038913141c4150300c40368940700d070618203100080042c09024080c03100340d18241a0390b01054808600100051402082c20b00c0080030540b82c14030500080340d0b19648943d005030800d211000342d8940d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 226811061 1250 226809811 226809823
    0x90c0b090a030b0405033a02030903181f1d0303190809070f030f0302011a01020d050717040b03070306050d0b070c0c090c03020d0e03182809050702100608 68
    0x1d000501c9a585407a1800c0943c1148210b444150101c87c1e0080040780300d0740e01403158a166030f09917552245c40002424088280d02c802c0344c1e1b6200c2d9030020400c0003000110034503290f50012014010487d0301c2c4101e83c2c0000c07003100c010740400c003054100d0124280d02811038004814160154041d50404c401d42c1251010b1429a01700541486901d900242205100300081c03402080060240200195070f410001c0441d0200c0106500550034520354000038408015415043c00e010382c01082e041107102c01c01c880942003d401240d032020b003071310000c06480003d0080d2003e400301a0f21030ba9682803441028084603610b502481c0a102e003102c055000c601e080004940c01540c5003401c42440c1594a460121000c10307030401d035912480c0562440c00d056056015020444c240b040402200d40811881e40c3e036806038000841d2210300303101c2195650b080c00c2c20034102010001250501004820f407440b0000803480e0040b18401b69100308009082e0b6040107200b50ba40c0300785008101c2203041c100003540f511 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 226812311 1250 226811061 226811063
    0x2070c052403040f0206070f0311070602120f040803040303110f07180507030e011401090c0e0a06031d030a050d0c1704063b070e10050d060905060a090c0b090a03 71
    0x1507000c40050140200c00c3c1c0340d03181c4030341d00a100e103a48100a1920140d490111a41540003c0e01005c010f00750031000510301c416500160000d181141400ca414181a40b0030b80440b44003036824040003d40740c00c02c2025001451003600d4200c0f5030141c4108407441c040c04004900542d13072080204100c2e160b050314032082990424000800c081c3d42e0b5020075030283c6110b8a42c100b0725072822808035200744d070814107541a038080c02d8051242c1a815041159072000c4810195400181c0107020040329010b540040d43c4e08100084400288401080050850300a01c0080f40440e2000928240303da5444c41780e0000c506060400c4011000c1d4a04036040103500200f00030a002d580b0300038080140038100c000c882c80665141000c80d0440740e010388952813503264030113602500c1051004070b251032107042c12601c201c94104403820388030301c0e03c401c01c59821446c0340c080d12100c0c0c1e034a141e08081003061062130b1003a44560000708040f5110316145a14416582c81903981c401c05101050259943c8c0d0781c840100e03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 226813561 1250 226812311 226812379
    0x1090524070906083c060f030a110d02030c0604060c0308010614070212070b040f031104050f07030b13020c0c1302090105040504272105091c0303090c0902070c05 71
    0x200c110031140c2405007a552100f80d145c0c2d41d02507980803043d03400c0b65120310b205540600c000c0b1401028990b443c070825000400802c840140c2007064100f44c0350f8401203038001400c030f54001c100107010881075802500008001111403011000703054001d4a818010482d925142080e00c21424071038609014040000344101c082c0403040c0714a0004100d0b20015180d484066941c40d50b81d9010420044440d02c800c8a004211100c40f441780e1600d489110321500340d01c0d00c0088142d4a1840850040002141060b4842c0882d019064600290b1014000400300c40d801002001c0c510345c10006640100e41c0b0b02c5001d40e00400c201100369a10106945c2182d20965020913610042c1641c210b000c5414900045995640100541480310710125192224540350350340440081e41d100c100c80c3ca00c1000c0703584d908000010340142d0611008100508900d00919001940d84950b59441000c103110f0750140c49a80d0b00800c8410074400d003c07150348010b041c112140344123098000a2040d81c099820b8003802c1c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 226814811 1250 226813561 226813591
    0x8030115090f08030a0e3307050a0b0f06030c01020d140405060a08010303080123150d050f0105150319020307110a03020312011d0f090109052407090608 67
    0x18003030051101d00080c02a12445031259070721800c403940e81e90002604403000440b01c008843d074908240c42c0c0300c85103000307842405800e0b08400700d00f0604040a40a042030710a000c00401e400f2510911404513003034840d00c40d100b99030030541c064402e803102c060485842a049504001001d82e00005d070404083d0f064103224114400703115280c1d441c1e0040380c0c01560845000030310f411405600c40d03e6903050364071032b440c1c1c0c0031a6602c81e00c003051140741f92074103400d00340581c1652031464a01411000000d0340100206490008449038100954409450078442480404018400c9160406401e01101040c200c228250300d0403480c084812800c891411007000d5000000c2480755115030b1303265020480c0c40b4200c401009951600039981c0c0c2c070401c0000c0510b4000000441c0001612035207102400021008406d580c850680402e8040d42c0a81209019903840100200090b02489000c2e0100c170104003019052528180380710310850003c1c5024200902510107004c1250407003402500880210380c04a2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 226816061 1250 226814811 226814849
    0x1b0102010605031207140a030525150902010f0c020108130521030901061233090602030406152105073305130501080c0412030507030219080301 63
    0x40184410b07081941c141c002c0d03880d240c8074020042c00030084a03214184c103c10510b240d40215803500e005140c0240010801c1201b651820700b10058800400d0307510101403030389507240e901c841d003020621801c1001103482d0300c820029980c10030701c0091b40c603215041c03404101c4502e50009003000c1006010a040c0301460700720009102d420411082c0079110681f61498440d4503000e80c0a0075042191510f650f5030a101c00401e0b40080d95041c03030782a5501c44a564030b04a000d000c10408815a140d20034040c003600c081990382d00c0c00c28001c817000d880c05a01d00580e00d041504001042d6101600c040e441c1d030581c201c0c05c1042803147c003003e00700071500902c940200c00030780c640242001d115074007043c1d00c01000201d071000c42c4400c3c810b6072101c0b06020038418030341084031400c0c3c540e07020ba0079242d40c050306c00c44001c1140c0d50180005a80c00000054076514281e210064102e00c107002d0740c400d400241004c00c00c00c0c00c0503010000720700c200c2244d0355401d03594480d0f50fa69400741e06c014051010391082c00e11b43c2203 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 226817311 1250 226816061 226816063
    0xd0e1e0106210804210516030f140c0a061d040e0606091306090b1f08030904020c0102040b04062f030702010c0f14030c150603100903020715052a1b0102 67
    0x54090111170700c6500f51000c5c8241d14228109598201b03903000c1c0950994581d4001c03ea01c1c2d42000c4032782c4002050680106a26800301261040381c029a02d4040c15540000c5942c2c0c0c0d0358400040c0c000344c0c0740d00403411282034881007416043e031280342c0118a400701c00c000201e000600d26611002c201c40d0781c0b0b000e9858014540e4051000c55004060508080c10f010421540d01790445c03003032500c4894046154559200c07544440000c0c440c0a000b50010840d40020382415002803240c078000c5d034005440c00d56980e132065099403069000740c0018058120501c1c2c02d001514450903041c0c1e00031061551402034100c125142d03c00c0ea6402814003500e40c002c40f04100440c0d03204200b485d041200001c0f041107202181e900c903441000030181c80c0c02240340646400141c96042400b404010340144840ba44404400700282180c54099080d0f100e90300c40040c0a0300070303600d01c41b41076010359904c2d902c984040c02110900920403100c50006440b08580740080600000c0001a000c5803444411081c0318010050b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 226818561 1250 226817311 226817317
    0x40b0102030706090f0b060405061f1103030109020408010501051206070e0406080303040606030605090d0912020409150209011202071a0402060d020721020a05150901020d0e1e01062108 81
    0xa0040742480d13860300c103120400d10750026840c010740c41e2515591314036040000f12441202ca02e5840340d1941513034051590240d5000700c403405c01d400c142d01481c504114191071504241d1102d806d10390001010f1028503020302a1030b00508058516400395100700221940b51140140b202040201f13103602c3c1d090664582e00480c3c014054081600e0352410b241c1041c0d0003810480c0800d5410f94108000300348a0b12000809014400240e510440d190742488403c40383d81c4d440440070307680103440306900004109032030680c0d80c5280c140c510041c1d1315244d8800141000b09450040e042841c418001c0c0c1e0085803044d4041c40c0d845001c802c9101c600e0b03a80e407000480c1400780300000311905202103440130400102d402d0b000552440c0000740ca13030074201c911040340d841030f1120004105070004e1017150304861803030445940107401000091300700642c1e4244102161170740803440d0441d5001000041d5000c003811070560b05140d64200038441a414080850341040006404060070480c40303180206012554040d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 226819811 1250 226818561 226818563
    0x30d05060a0906060f0212041d09010902060c0609060f010b180d060501180f0219080709050312092403130201020a0b0f1b030f06040b03011506020f01110c0a02040b01020307 76
    0x81040f0031911214020700a54890391030002510a83c51003803403600922082c0c904999000c100d2000f4a0040b460a104905000e40010840d43d03c58400000681d035040203884040c50b00710061120780350000e410381c64010084c02141d0790b8032514006100c402c00c11411912035048801010103084080c0c00414a010303241079010700014900b00c0046101c5040c0c00c00008007000540703091220300c400d4201c1008070702c1006020483c0c0000c40c1003440c03503e400307815020392008207418140d1880365282c0120303040c032407805040c55440400280c06142ca180603503114003040d40b2840c041c9041c441d0300c04440701a2002030142c00c41e6100408002085a108000c17152095034800703002030860410440041c04d0000c29144c41505062601202540c030140c407080d01d1241e088010180810340741c440c00d00000b00803240c4255019501c036180c010041030404500e2004122aa0040109242040c9103508490b1034200030741c608041002b0480d6184400036400380c2680d01220300280006c1400700513460b522800030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 226821061 1250 226819811 226819829
    0x70504090206130b1c0b0603040b180d02030a030c1b031803050708060106020d18090209130e1005090a02090a0e0313060c1e031e02010e03070f060b060301050102030d05060a 76
    0x440451030114110240c41c3c0d940c400e1117444071241804101c0410b07a941d044d502034002206100240c0414000d540c190b4214078030141210f0300c6810342d44c03140e050014404040700540c2c0006108008a60305120740c1c4107aa400d403422023480841400c2002c90303145c07002c0c006000c1050420321440b0905501c40400c004503488000c40c6c00c1c841e921210261198001d00c43c8002501507114407031312940c02000c030104449680c0c6400c40c0b40c2410012410002e4014000c46500700b03a002c41ca80303c00d900350b407040c00e841c5040740c8010314407042c1d00e04140f4241c407030080003a6500d0b0444550100140c403502403050700103141d01000300e024142d28503000d00d035000b20058011546113541001441d2038002c4c4003034426500814040d180c0711282041140360319980007000300000d43c26441c80b8116060200a50519030141c130000c900c9841e004407840c9103070032134001583c0903060000c0110820446104500c494902610341c14190b40c90310001075200e0052003000e8140c02c6d1078800190701550341000c020090a1841 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 226822311 1250 226821061 226821097
    0x603040b07110f1905061305030301061110050405030702090123040203060609040c170106050301060507030e010e1e03060114221404030f121e0c02070504050405010b01021c02070504090206 83
    0x40c2e03840d184540410300941d8103001b040701140d0110030382c004d00d420107908030000318510307441e10308200c030340c04c941c488ca410890190042203020b480c41802241d0146000703038019522150240100b092404040c1c1c082d03043d01c01e130b10480c0c00c400c502504104180e407504a4006031280d88480114065201d40443d4650062070300b20041c0b00581c00131112140c8240800300c00d151686c9031401070319988000e018400206805110136400244281413110368480b0624000703241d50044808510009803a104285804011200c103100303c0c10100306150040c0381c14154403002c003020a001c02c6812400004441c204c5c00790004d01c01c107504058204142000c5081440d548074a45170800410070081001c1c440700050020401c94024403480c0202d104020055810010000c2202c94060040071101c2c4400b042d070045000c002900c2da101d05c20b85204a0141c400440c2404146d8002030504101e46c410208032a442e403217001c8140c4c0c1c00a03052064a00a440010300f4a542c1e00018186000703140d000c6617090038103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 226823561 1250 226822311 226822333
    0xb18040c02070305150108060103020d02120601090204170304301a070e010e0a0b1c0504050c031203010608190605120d0809030c0a080919030b060f0603040b07110f 72
    0x90100c0c1100c1c050000ea50041585c3c5080701008a07081c4181c120541c08400180050301d001e01c503e4611610040402c09070f4460318560600f031020076400551540d0340803d04101110a404c10340c04c0c02081c032405185058240304000708888400921400c05120b4120004a20005103100c12442d41d0800c41e80082e400044054080e00e07401107071040300040301c02403005203550045030300800c0c51a00900400409090498212064002d88118020711a200c000f048d085404c034441c0ca8000e0f4041c0014101c5903441e2414146000202541c850540744100010040700d90300501c3c540d0000e00c0c004883c0e4041c201540e101d4040c00c0d881e04081d42c0203249003880f608070703807001500004412071511a035900d0350321040c45c50780344d020ba0008100a500405000c40024012400500c01d480f4020311424415000b0f085101904501d03030011a000982e503804d02c42e20340703001c1144400942d400c03298549585002e9850028081001d0555801d00411800d41e0755001010300002000c003040e4001c450000041c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 226824811 1250 226823561 226823563
    0x2e0e01060c1e0203010e03030f1b070f03080703290a08070b031f051804050105070206070507030315030f050a06110703170402150310051c0c030314191707020a03090b18040c02 77
    0x81520403d1b0b050085002c212040cae009036051f100003030b41010544da001500c5403426500030000410b02c2c010103664074001700e8900c0c0c05d0b44100c00600c103c1034880320441c2990042c0140041640c02142556000c2041085034140b040212035114100140c1c04540c511010031a024058007a041207074404042418840d981071042ca10340d2140b40030784000d004540720188141d84809081c0e800701c0c0015801c021800c08a13000f9001520840f100134041d0034002d54940380c0c07040d0b002e0740310403c9800f50441e50105045c854280a1001c407020349145d15403800c1c5055402410035120040500c40384600d180004c0c043d903581020410a410343ca2a44954914101100302085029406040e01c1015190080e005142980580024141d400540001d40c20b056403025260042c2103800058407007810081241850400a245070481407980c0300c41104500000101010210060109086500452002d80880d17800b05901c41107135142d0007180d50312a03c100383d0407000e402c50080030342c109003880c4030b2404251b4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 226826061 1250 226824811 226824841
    0x70b0306100c08040603020f09130c02100c02030715140a0609110f0306040e0304080a1a07020d120b1207120b011208030f2e0e01060c1e0203010e0303 66
    0x1c85501e442801c956800761a0034503180d902829203441031100380302140c0264000c00390400118111418050418000750401d071064110110b01e0b0380300c04440d8004e0ba0104034500000308250010b01006005840080daa4062054043d081034021000180301c6c26059100720180500c40c0c0419032540b8101040c0805000710388501a18246406980c42010320341d203065607100b541003002e283c503580b14041000003a0421110380c2d501400304100008030040200071a524251040b0300d07030041c903100e060720b12400510080407241075420050f10140d040307500c030705d0105055a01e60400105030f180c04c000b19201005640c0f041020b441030950110740c0d02e82107011412001e1082005c46150b81c0c8070300c01d01030711400548004018a80a1011840e08180d0314169980100010350b417400b05584910f02c40e40e0741c0d249411200d1000315075403080c081c0e00c40464105024002034204010740c6c1361b251b070312240b040100ca000c2001014022020ba011541d0a401101c212086d074000c981c0c0300c1c1840e20007122104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 226827311 1250 226826061 226826071
    0xe0a03020d02010b0a030204090204141906060806180a3207030905030f03090c04110c0d050901022d070e2a19090510090806060307051c03050c070b03 66
    0x201c40d48080c10022881405606041c4801418440341c2d04d10b55400e010280c070a8482c200e0b8466102c0b650506290409000c00d0f03c40d006440d200e600001040c180c080c01ca489a8001c481003104c0d40b02000019120820703d189200210b00d0380078034a03602c00c10100700030400d0340102c0034001d00d45034034648403085a1054016107410f060740051951180a4103408a42400300d008285030411f202050040d004080903540c481c405d513042c0c6092170381c1c80e8000741c11070b085172103182d0741000d0100e515070309201e08000c1700708c20310040c0c14042e16140e0b240c4002b075030f9032205009002c0311205415600b41e02c10407007c0f01d10500e2a01004443c2500c0d00d03180501c00c01d941c1101c02d1580c011010030a00c50780040c400e6aaa8111050642145044150400e071040701020082600503c9846580003035607032101c070b2041c2e05051855403690785184c1014200d03414402e022384028800d0340114020f000d0b82d5992030113074495062103081072555441d50725060b141fa0059044084440c080d010700014104108402948070f1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 226828561 1250 226827311 226827313
    0xb0901020705041b11010b04060f03050c0d031407021c0506040512070b07050c03160c1a0309030904020307110d0f080c030906150604090204080a06050108030415080a020408010e0a0302 81
    0x2071500c840500c021540109200350854040a51000540b4025903a0042c128440000418040401c031b01080c02e807026640841c2100310601c0302001840014400400082d00882e030400201c1c0d110b0310002c00c1d6900740c90180610200009034442159100b41d5064110001306010b81544e8805040c410344810044406940c1c9007e80c2c1a0f24103035401d168100da841c1c9511031030090b801e440e400c104a0300b035080030180990303d100420001a450001e80d1500c46200d226003100841c060528800000b82007240e0710302e0344c00040034010f00141180c0801600c0c00e03540309960040c0c403582c03a408210303071080f1003080c040c0041c000d11280702180307503012120b01c40510481e00e80b0401600c519580044070300c01201d642c5010782190300400c2151030209140504100c004125500381519004104100d078002d5200190304d90280d602441002050701940d401000c0010146040c01d20b480c01820032030500143c480101700d186030010700c2603140390f0b05a401034250700b4020400001e8025466a03140002e41064000d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 226829811 1250 226828561 226828573
    0x1b0115061d1c170715020304030c151505040b06090f0402090a1206110703080a0c05091e1c05030322060c030c18050120030714060106111204180b0a0b090102 69
    0x1c8500074040f40d0b0900da100070701e1021442445c020600940003d0b0048041001064440002ca45400300044006030034010000f00098040030041480c54180d2149015505080c1c9800303540d50b0324010f0701e0100f0403c0d6401001c14104d503001a0081c401c08126643c083c004100100f44442018002640d152056500f005042e014451500d403501452a001f40010044000102120119000040484660f09100781851a200c4c00901040c1d00300c400000f204400f000e00702000c0c0f170840143c600c0d281c2c0c00044c903074116086407a599242c3c030009044a86a0403140107816101f04008422041150004001c11014440601c010051b04041c03081500041c024411f816074007108060b0202200c0c8161a401d03070709104207400030422050400c143c0c086000511140012944079440d110605000001524840d030428001a00703202c2d0300a03454001d544500211446c18208a0448050703840d003800c01e204107503480c5541d0b0043c05248010392b4006030241c40c00a142001980504020340090b025207003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 226831061 1250 226829811 226829843
    0x9090c091109150c010e12071e030801030b15030109060e010c03060f090903020a080307080907170706050309190503031801020f1801050c0f031b0115061d1c 69
    0x80c842c064841c2d0a40d010701550440d2010002d00001031680c110a00b0000c0313600700d00070702d009003850700c80c0046440003200011804c00b001040542d041c282e60000d04910394002081c5c500070480401400010401c10307811020480d44552002c0c0f14400903c000d00900c1145c1c0c1d40e140c41406845152038a0074690b0910843c1a02c180c007d014820a0712488514900c0c0c03035181c460848003500e103404059065000315041e50010805406c003c6109000d1900c4180041c00d0443d0b00c0e40c9462a16408040200070a0f40d0904c9030341c80124085084911524082da202d071074000307505007045020407040c0781150400004604110011025610030464004800380c50036440108a0a0340f20701d050428040100f00207181082d0301c049035038643d0200c10b240c1103082c01a1003185616002e010581a909a13001142c100303058650321352519006a204e20080c0103030201c143ea4145511094000c403020f12104070244099a4101c000005a41000804030444900900d0008121098104080d2a009020300c0303280 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 226832311 1250 226831061 226831091
    0x8010c0e010c0201120f060b03130507170307120e061b060105031b1003020f04030321180b09240a0606020d020d0c020a030f0303020a0e030619021309090c09 69
    0x301e0026010784504045c4080300000342e00803d48030715950b021598030440031a600c810700300958801e000b40c01c0c08a10000143c2445403034151554000e06441c58000e1420301d85020120580c3e80716075000340520314500102034107440c081c100c503070300e5900682e002c110301081d404041071221801142d0010b40300c0c1a42c80b40103240e01c6084c40c060b0b80031100c03000c1c01c1042c41c90811314501c0070082420710b0014185108529200c0b19075200d035100307800180350255119621010b004c030805160b01c0c0a20108800500031211880724528500f001d080020020000740c400c40d014414031114420250040c42540f144407401d82000328207a03a000343c401d2401101145880c00004d5001100312917800500007918040300c22601031a00c3c0a049800600c60400000055174019940034618132a071005078980300c074031030000d04180e0401107483c4a68044024070690381032224440840e090407031809651040450056034181d41580e000c0314400d03141940240500500c0344158043d075404001c2070141c450600419 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 226833561 1250 226832311 226832327
    0x201091a0406140c1903030c0507020d0303050703110c0106032f060d0204080303070306140a030b0106031a030a0c06080106030605030d1d0d060e010b0414070e011808010c0e01 77
    0xa600c842001c000500009000c0e02c1c000e440680c01108040c5807058481599080004542000d400d04c2030070340c100c208141d054050f2101e03c1d0038500d44507003000f00c25000116002000080601419529070114034420720039000740b00c2c0c410782c400d45143e441b0140c804ca50b000340060b00c01510005910301e20015004042d1207881001d012800014402c80b54803020402283e1241e05000042582004001440581070015510696141d100003c01501d0040d91052100f52140301074850168a8010b000280c440b80703807181521a640340020701685002a26404e143d440d50911354180316450340301003040090650780c01542c90075601c01c005640e07107441c00e8042c0d80480c083d103070b855080f00c2e42c421400b601c101220f200785100340e951020310b803225801041214040341c00c160750050b258501a032020800b4000c144503c3c0d03040e030703082045c03064540c4200c1c0307801c8004c1c2941d4100040000360129581c4204448031881c0074100c216203030300f84e0b201030740c034002e040000c0c10f2008100c9003588824207601a80013 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 226834811 1250 226833561 226833599
    0xc010e0409020306010e0c19020102031b0702130c0909020301090b0f030f0d050f0d020c0a0203120703080109090c081f06090e0a020118080a0305090a0e060a03290a020304020109 78
    0x40620783d00b44044c0c146c8a1100500c40210814140031558112082e0840c0300201103164000507603031b08007807490b0720700e8118144240320a01001c021400060302da21440c101e500400b8640012641d8002e0b108503001039040d400800c4040c008000400e0700d03182680410340c421000c441001d01000c8070300906131a02d04081c00303203110f60080582e0381c000902410080505910401c45185002080f082031022a080a00c00f40700e0b9902200707036502181010010811102e420558a5040038036540c1e0061507803105002d10038803513850380c0400b81000a21032040c800f4201d00d10a0325480307403009044071031214003800b0401c00d050a0500000d0050424818200c2022660b8017074074004d5641d0b0010f646c440c141110a048007000b100c4006070403003062060f11301c40c41c441e940d40b80d0313142000c0701000025140d81c0c0003241c4003603481c02801034a603500541e000807294828940150800303850b102042410034104200104030f030707407810002e50310b4041e40150301ca24400d80740e400f0a03c0d2130f40612010b0700c000c00d071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 226836061 1250 226834811 226834813
    0x4020c0312060109080d0507050c0907020f101506030b0607021c0308060411070f0c050307080d020105090303070f121e0b041b2708030d0c1202031e06031e0c010e04090203 75
    0x421031b62041c2c4548014040c4501030001c80d1115000c00d400300c0c0220380704a41400040e001440c900562901c18000b1446030f84500c80c00340b141100e081d507070b4900b0303001600c42c150915903108800d42158071188190385840350010b01c5400c40030300321455105902a01c01c0304800140880c00050210311300742c4195010f400c03181200c94100403d41da1400e00d811030900080ea038124411780d0010702541d0070081200038001c0d0001a01986240b404041c0c00e5540207080b01541c1d07001401000307542c03036115120880815091900045904401c1c4000c0001c1452100c004884201c0f00400044410150415040c1c44002c0d0b078100300d428200c3e900d05240d51190509403000403c1d02280d0006c020340c490300d80388c005c80c200303100741440c0f55140c9140c1d05e15417090444442e419113030300c0320a0038542c10401c030403c2c1c0c083e040b5003540744d4a094400d0250042404031080c5881e0840b4011401c141c50070840310710304012440211980348004510a0b9071140c105444900064405407489400d09240c010b02c28a01d80c094 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 226837311 1250 226836061 226836073
    0x111030a0905040906020702030615011202180d08040801051f0501020a050604140f03070506040614040305030105062b060e070e06041514030a05040204150e04060c090504020c031206010908 83
    0x142c20003028041241d0107072030841e0244044e0000d65024845a8014071070000c0c460080c1041c400050305002c940030901c0d00c0c0d00d1050004c28080f602e1562001545141140c5001c42070049240080b41400382c3c1d001082150f290000300090302c2c0700701d049489042920304805000c1e070780d81d80c012682c50105800080c010f81001c004900020640c0040014110428055442003542850300c1450364000c070109031210744c4188207020a009081c400c2c2c001c845400092007459181c00d4801038024403040c40b42038041c1c04001100c24030512001140060300d200400358201c400d07120410381c0c002d0106805a000e500b000c410105110b0760051510740795455018003c0d40c1054640210300c00440d140d03004000c18000c4c0824404508545400218455a1500000100350a00b130050000b2103840303114030008900000c0050244402e0807440039131180d840b500205480000290489880c0199800290454000301d0031540d5500c001c0090f10480300441c5401050307998480044500c0c0c02e49128905e4150844 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 226838561 1250 226837311 226837319
    0xf0405070f030e0c03100b1903020a121506150815010212210f1e0c1c060302030708010207060f1b0c031809020909070e010516020109050d060b0111030a09 68
    0x3e8004104009071401510016000000032a0409101a860146071603076040c1d5600280340c04441400030448102c60044904d003198045020500d00c4d0050086c2c03282d40040e80d000b040302c01c5d110ba1559192803001480a90f42c0c4101d9000702d81707828222407010174a0300d4000380d00301c045402c41e288140340c164020850001441070042c03003a40803034081d08007070381d0032080f410720030003181e00c030600442401510320320502d07003040e4500314582002c80507032072282080d0a0003042c840b82415582d0101c00119155140c042c45030040c001010319500080d054051a04c00050401065000d070078218018042030107141d40d00140a0102c07248280110301003506a86c180745d90380c0c82040e1800e14103100342801280c41181101e4490054001e1344500d086640000d44c0b1411030400340041e68000c845401d0025142d6042d80018019006140b805860703070340088040c3c01568442d0386c60200416002d00011113040082c240800030b40f200d00c4840c0e000c11600c09800c10100303400001c0707a201e21901e58400c80c4407410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 226839811 1250 226838561 226838567
    0x41401110322051c110105091e03040608180f072c04081603050f070f0614060a03060f060b0c0303010501031503050d030f020d15050301060f18020304030c0516050f0405070f 76
    0x4d10405403041200c00306041240500902c03400b0f01a940c80303401820f2214500c3d5428103000041d009140340c03a00144001c000c52604851700a41080784200480b8081030525070321071074640b01d915443c00d188a8100002488141d00e10f1a0400410020b2812200094200c00c400150310681c0d004040306020080c0345a5502101c0b1081421442441e02c985001c91600a580c05500b05241c251509401050900c0c1088103910502940c0038280702000703514904070002070f640c43c0003444090b15003500c48da00c039202043d403540701e0005400f1070740882d92550950b50945580360170034014540440d00c0c01b0718510005a013100343d40c0c11641d0000007030042141400f400c401800e400030186d89440e8084c088580c964607113008007040070718004074480b02145420100750075501c0c0c03603008803903803030b20700f07009103c500282c030503035588556035400141e42c81c1c41d140b408854800c450301d00506240038070f440000e42c00814540200c103d5408480d24401e104840b8200300494100360742050125506021010030640 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 226841061 1250 226839811 226839853
    0x40807050a12021f11090d061b080103140304030503030a020732060a0612020105130b040b0729070e0a030c06050408070b0f090904140111032205 64
    0x12056040e16810880740c0d46207203200e84148605809030308800391544482c3c0352070402040c28a0404802e01800381070540d0000c06101e00c045080c0039403030015015042c850641c01000841c892001003c0780518180700080030301200b808101d0b40ba500d074001d13030741000030000181c500785c070f4200018505c2e544465801200940c400b00040791081c1130544034403041521142d2600006c3d50b16205820022113280110703080001c001e0202035010b1410070113102032210a004a00e0140d420b0130b01d541d0341d90300f500500c0110350850307000d650034403070005011650000c2d51001d400020300c140d02c6001142099881c41482100e40300714403400507001c4c80040d4282c1c1c40340d03031a00e17000700c009806240704688035201c51a262000390400c03408a00b0000302002801000c011030b20007881d54a5401e4189001c4e90a4103d0910070000f806100c1d036070050100d424000f151111300c09001d0740f5402004601030b0400d072405241c1048030b080240000e041a29580e2403001d249400e001135002c8050704060843c0e41c1d088211305 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 226842311 1250 226841061 226841063
    0x40b0603040b0c070f060204090506090a050106140714070f0602060903090d0f0807020405151207080d0302030c0c0a0c03031b0c061101091a10060c0c0506070602070204090303150b0f03040807 84
    0x138405c16004404034003188004c001070888480041110b103440001c1c40300d14071002c1c028040c0b6070700d0140100040c0b40d200b801c40500d01c02c0c0820060361440981080307a000100c18182001501940f800015403940c407039118021a500f98003600c030199a901e503295103c0c040d030000e09030484115840100011102c000f2140d0880c0318040040c01d102054011800302c40d000c0f11074542d130b041802181c9040c0d01d030404000000180c80e1700202812800c14001c40c0d100c50040303d1f100241900880403c0007200c9680940e80443c02040c100c40144070182010200b0310501d10040d001714034040d555001c0203c1242c5100c1030550002c081d000d116140c2502211418110345100b8555588c0304241400101e0181c11060084416100000a17050502c2c485000401551001040c001d4103c950000190364071100d6040310411502640c982140b818540302901c03410b80020760140c90041181c04150305070f441100240360049020780300d2520340c81006030510481100c13000000060001600207103203580141541 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 226843561 1250 226842311 226842323
    0x706050a0e01030f0212040c080c060d02160b0901020a120506010f0804022d031905060a09020a09020f1e0a020a06051b0a11150f04020105090117010b09040b0603040b0c07 75
    0x30007103130743e00200d030030500c40300808101d1a4180814841522044405010450060084402d107070001500f00e2144203454001e280c0c01203203005041d6a181d4060180c41d0b0841e824101515120701214001d41c030007010080461036100c1e66103000100d034412184100c20603128103000030744600c815a5611402070040b60300c40310002d0070000d80544415640f190341c81090709a0180d240110803d07080c00c1d03c520707030304004200b20501c2c68085480016031b90380280d0308040c009004101c60001c100c115204e17400c038981c103c1c00010201c03001e4030588000e00010424a0742161300801811070311030306226100320304e0f005074050384084000c650700d58402904641070420280341e4140040e1f01c07007415001130052130b0205a0414418268141c248541003000030f0100710484c0320328282c1e140600908020b0300190400101040211060b4002c0c3c03140e4900c605244210f4503250307507440b444042b6a02c07841d44180100c1c2440c04842c440e08080041c1c03402140d11150108044e82e94010030030042c0c1114100b40c6903 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 226844811 1250 226843561 226843571
    0x5090c04020406051e0909040210030b09040b060102160f0b0d02220f09090203030307260103120906360e0c04030b01080318010e0102070801050115110706050a0e0103 73
    0x390365900c002d00003801c0d5503c0302d42c1c80758404d074104241003807110104484101c00f000350500550747c0710ba401d54840d074100d07410302c03502c00c00840480091000c26001604900b0b60030070720040c860210f02c5030b88a1a0240d080361000402220021200c040f41e22981d06c1c4200d4803403040c0610901e10300644205800010b005081495a60b02c20604442d14011040510710000f0180450480100032501814100710213120140e07003035000c0307540c2e848000d090100b003140035a0540c2c84620866074820212021004c00c0049503128100710100b503034004c0b220008250427000c0050b42e18003e0901c04040480e503803981c00784030001104010224004014441108503005000c580310361030700d8050b405494030001e0a03480301e0a40c17074000c0790380206801c080300c00d51050161041c030f91011030030950840c40a00e084071b518115400180e2078031300d09400981d299400d12001243d02811a132005442c0b426640d81c0c081142e82611b1607640b00e0300315014903c0050420444090058000ea0303e072a603462040c500064 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 226846061 1250 226844811 226844833
    0xe0c010816110312041133040306021308010f0e06040605060307080f06010602060a0603110f0f040c2a020907050307090b030a05041101080105010509120c090414070909020f040509 79
    0x82561300c034002c4282040100e40070300c0b050007105819246070700e0003070b50400d44145038515001030001d00c120009032a00d01501103811340c890000c05a50080d50700400239074441d01c600c2089081c600c0c0707a000c1d090142d0700c0d00002211182841c0140008101d92170046c180c3c58441da107806002d800300410180d0548282c400000c1c80343c0c07040000106046000c005030009505080c0000d013803131005454101514100174007800840c404000125a10204448800915001801103804966082d074169031080c68016404c0100b074028245590980d0741141c40070403494541d4040e240746c043c1c1b5101030740000c0715800091206004230001c60b0003007080e09101034038554920326004603030310865a024803561588184410007200c403a102c4101402400c01003900c0d0705002c0002c11502445000c03600c5608100000e1502000c2403150310f4880e40e000e4801d0701b091605041c00035811848041e0303c00c02e4400d070407001444030980d20074072040c598011f1411400300c0c20030003000054100509411b9981c000d55049038 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 226847311 1250 226846061 226846063
    0xf090b0705031b070f1e06230a09080c040203090706080a090609030c0b0a11030a0f150305010606090e07090e0916030b060103060f050607032109030801090e0c01081611 74
    0xc2d1a840074040103104d41d50030150050321100d410f0b03101c0020322000c40035941c1c2e207030000e550a0064507a42e2800c0e002c8003100c030102d900347c80d08500c3e05c0220500e00285d090410f503400000c00c010b41e500c203001c581040034040b092000302c0c402100c5008094000b0a001c1c480326229104594018100380030105000d80b2030703102c1804661165204038080f0f185d1001c98001c02a0020340568002c0441c04200301441d002041100c843c40014881d00a0f55170351703001c0320030444440d484624140351844004c801c09450b8070f0802c1c0281820f00440000c41c0307900700c0004600b10b1070b40000d07208000319075901aa240c94900b0034444518098450300c02400350200100d0399944c100c807488020760140c1c1512106040010026044500796006861101c1841c10140425101c40c8100d40803998580f0f800b0304000c07952030105510007050f00f039148181c2d0404074a0014140e04c022241d0585030306040400442c5d85c1c80420035a80d45100400c603021442d103800181002d0561044c480303074841c06080c0144c00d4940400d901d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 226848561 1250 226847311 226847347
    0x1305071403090102031006050309100e030c06090106080618030703080a0f090f1205040807030206070f0c06020703020f0a270204090e0604060b03060408030c031512011b0f090b070503 80
    0x2c00240d039804410004090100c10103040100140e0034a1495400c004007803a884690b8402d1241030103072245011032070a20704004840b48016250181e0342d96003002540340d8081c05080c45480b64074441c550200e0401d03100900040f019921000c0150700d0004156816107041c6002000d0b83e0700c1507030b100068a111540d50050104007446190649404826880c0006c03048a04605000c1044800d0205110ba2600000d03024140d80e01102c1180d242c00f46840c01c0c0a03502d0400a0083c400709200400140f000d40014440302505e00c21507104114803410001e0102512042c0302d0791241c40d59200c0010030400e0310710380385041016002c0e400f40ca859141e02402c0706403034000b10071000b1684000108010701406200d10400c0d44421006041c0504103501c4281e110300020b8640e4540750300000c0030404503081800c0c0111125005000e5600c1d604134003c180703009120740c4d6015442003003040302da244418800c00305190181030070b460b021119030a06c1c44042c440d4010000c04c807100d1008000381c001e480070800030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 226849811 1250 226848561 226848571
    0xa030b01121806060b13170a0f050d0816051804150b0a0933090e0408030f0708090d0315030206040b1c0204080d0f020a1a0114010e1305071403 63
    0x1c15030725050300f450000704662031a0b10050342100148052a041d80210030a0011100da0000702c03003240208500141c00d003000714900804039007402c6210f2040110114211022910b2a1603406c1c083e55184504040c02c4091074101001036001c012403111102c070030a9240700b1001c05400000e001410301c1d20708040c43d1950b004005c0300c050210303002c0c8806601051800203807a100d9142c80c40c211525100c45158849007905090041c14424142c01d010300c5640100d0003460018801d00c0c0d04d041504000e007103a40142d41d0320360060751440c002203415006a9109024810640040003410384440b4224000c120348480086540900c140020243e541c41014201070300a640c141940c80408003400041c00081620070010349006200810108002041c0c8402e4881c0d1418402020100124101c0c2800c011403001402c2240109001a0903400c24040b241038075500c0ca15400600108001500c2c005194400964420031881002401107076913007109030402500d08010955104c80c1905000365002243c2d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 226851061 1250 226849811 226849841
    0x40e0a0203120409110f0412031806080708060303070209040221010f0f0c09210c030f030c0615051f1403070224070519021c0903050f0d02030a030b0112 67
    0xe020300c0a40032621900101e109041d007051b25040d9100d0302c281140c0103034400c204c0816480203da0090501070110946c1c017003040c038045010513480b01406001e03102c040d84d60f44001889580011f2490400004580c42203400a161081941d220380c01c00000b03442501503d04000c208240039903901009006501c44002c0c0b1031000701c0c842141d01c10580480f07041440d03180411411813410840d480307031001c4218500d01150400105a85a070428901440315640010400c855a2500c80c0c289070707200300000a041d1082c0c0040c881c4400c420800b51840069000d40d40c0c0c00841680c1c040302c031034850f0f00b84040e101d13214100120308031446000c0c641f041e00126010400341e00020345404c0c10312082041540a1000c104504e00c0600b040307400104540191001c00c0e200d078590104c4844507074008c021100c0400040d9110101494400e00010141400340c03004465922036588002c2501d200414480c021031110790045040040003d000c0340601009454103042c890303903921004100303c02d03005207811440014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 226852311 1250 226851061 226851067
    0x7120213140103050f0a02030c07080d0203042f0f03010f06030302060a0e01181e050304090e01180f0b100b0301030804150e1320120103030906030b030c040e0a020312 73
    0x808580501d998000815040524050800410360310b00454242c001c010030300c00586030780c1c480b1100c49041c071a418010340451008649100300e00c555030021849548a6190349005403127a10190100c4d204a500c006000141c10307010001900b0400e002c40030441004001048030700784c60710801d0844584c1e800540050700300004200d000b41440c05001d4145e10b4038002048081d458045680000c4420400180050240041d400182d07003009012000c01e5000303001c0c0d0390740d61f0b5200b010b8401060b50100d07031200b81d4204040c4102c1d020342200259900d80d084030030381400c2500c0c9e5441746001e00c8010001c03000049a0314004c03030030107841d8001e107010310720403102195141c0c1410205002009981d107e50104203481445000c0c81e200c0341310b111201c0e40c80c0c1201080c025100206100305031408107421080e010045042407425400c4107540303040781d0003506d070000c11503182c23001141960304c000c5416401d41d000a80304400b908066010640042e1041c3c1520000301040d0300003400c14100c640e443e0950b035404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 226853561 1250 226852311 226852319
    0x5070b0c0c19030e0603040303021e031b03010f05040b030a05010e0a030e040c0906120b1c030306050603010b091c06091109100302030a080309070302060412060b04060b0306040507120213 82
    0x10440c2c2000c11034a04407040c8490129540140910001c01c01180140d5000c400b10b000c041c020f4041d20101d07841492461a01e142484085090b03800071181003040c011100390780c1102d50343c4034044030b059641120b20020680d0400080c003000d040b010b0394045d0144119258440840c90a00c1421080902107020b0440c42c049400c008005100e1f5121181c803661410324200c2005400c840406c04403201406c04101d0b41c2d038044003d40003001113180301600801d040f00c43c00b0043d500140e04809152083e00d04001041d15041071100a000074054400341903410026800140380140180305502d84002da403410851640ea103031004c4d42c5500c0c00894003015003a400c0412440e105851990105080844010b03007032460300007907501c0103001c0010b44904800002300f240b030134007800038802958000c1e00f090368586e0307290f000c541e54a546120580303000d03181c41407000e410b140c036015010894041004250864589000f003000502c4060610028455000380540d60b05220703002916020354980c442c0c031070a07854 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 226854811 1250 226853561 226853563
    0x621040b0604060f050607060e010605030a0510110a2a1520030606160f051603052503080c010b13060503010e0d0206130c0b070c08100b011e05070b0c0c 67
    0xf58111414100c00c81c1020720440d00d4003001d440e542c90708004e01203211100c0e41c1c4028014500b80d0040c80d01801215240000d0100004040e2039030210707a40d04014080c4da905c4401114041c000752a000904118126103c1c0300c509150759403000b41280781c2100302c5107a41d60350000741071540003201c0d2943e26892095084110486940001d1540c0a40b1601d0361a00100007603907807044041c0d01191154002c681c1d000d03c000c800d06006042e61200c1100e02d030341c04015100750103403003500c0708441e41d110340342c49040041c0c0310135000800f400002852448541c03c0da690041660001c008142c0c0a650320380342404c00c1c0d5142c8584045444c480d2900244050920342414251051001590403980c800700b44420740c294002680303030303028000442c441800f10783c45c900014140050f0707120040301000030441c0824042808400c0c000c45444004585001420300b100d42c0139030f90003000340c9001c500e1501d50030403400d41d1200c0207250300c0b49a1030104d140909907699040c040d40b040da0441543c0402003000114924 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 226856061 1250 226854811 226854821
    0x15080106030c0c0320070e0a05040c1202010e01030e010e06040c081006050a0b2d12010e040b0c0c070f030809012006011401200c100507050601050621040b0604 70
    0x4820326100e065510303203480140813000c1001752101600c2d000e10050003c03400610a000140c6144400f018860400c903c0c581d024140036901a19480f041180c0095000440300c19038920b143d043e1558000a800c8a00640080c040394085044071b54a61140240d428000d005241c452484bc4c4411101503051403103803442e00706014124100c0d20300c2d00100b40460355500d86280704450b072400390f19603103406c0001e40c4480014011080360040c104070940d100f80050318000b41200303151510071840c01b80e0381c0d0a095510003a007500c001e40482c615a022800e200f046000824000c041c0000b00c07521150307a4501e5070403003403d9900c03d4508a00208401e8a40d6910100b0034142021060180c07031144041c86107662515810310072103030001d42406039140e0036406400c03824000401300510007500d12007120802d44407082401c40074030079103103607035005a02c90244c015921f205402070028807090b800e1070300303001040e880340c1e86940e2044d0240c03452102320f10302e41851a01c109d20540d6420700f942051000c0c801610 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 226857311 1250 226856061 226856081
    0x40e1507120b060702040b121e0d080106120506120d0903051902130b190306021b01021603081005060406020d0201050c0f0d09030903050105070f020c09011505030c041508010603 78
    0x3801c051100206660700400e4603804c940454001854401c0c0d040040d074640d09440810b0b01901a02e40c000300e4203c0506034032a298285401503031a140e01c030f040b0803134009409028800c017080c080c1080c41c480c44455400168030800c01b41102900380d00080900e85405004c42040303000840001050040080a1103084681208240b6042c00c8103540e9000602c0300b2222900207030074a23078800903d90140c1d01c08020300c50700007441d0f2040e186c258172820a04060f50010142c0080d4614070451000100014401c44059810b050441440c0304880ea5040711180b03000f03031056162076801400841c103556403a0041c8000c0031036800400d403a4038011400307420f4400052001d82c030503005001061400b51200102c980004201c140050716075054a001e0710312421036000501198a80300c20001402d42206040e5010f4110360211203500900604004c180340302405524800110401218400c0d80034001954000441c50052814a0b840750705010f02098917030200800108403c00400c840c40e0944254013602c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 226858561 1250 226857311 226857347
    0x10204090f1b090e041703010b090117010b1605030c160509130206030c0904021c020309070506031e0c070f0b061203070507051908030301030503040509011502070902030402040e1507 80
    0x20062031101401ca00030340d100390740c01d448200000904020385207000d01050803486c03001903200d5071619202c08154001c5030800703001c20000703500c000c0c120400c482348904031044210b1041c5841c000e50200d0b0304000b2810070031502d41c401404001003010060002c3d0782e0818032041c000d8001c6142c20108201043d001d00901d42202c1c1d0040b0390400741c0c486000300c9600c1003800012581d107420030008500244910325034002c000000c4070002590342815002180126442c6088a1f407458894041014a1100751507204402041c2920102d801001c030f0300d100e601c1200420581d0605015880710302111340c402c1e100300d90b4129290104407203031400e48410014115034500650409945981d1507a0340e00260040c280324900300c40c41c060100e40c0d440070540c083d200c2c40082e40c0d12544d5a2402982c0c94000e401118402c0103e000046100204003c0320640514141d005054651808894500950002c0c20580e042500c901981804001c01c0105803c0c1103803403090314980e4a0002e0300146503209082d014544 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 226859811 1250 226858561 226858601
    0x60314011d0a0308061c211110111209030720091b2a07060302090a1203030b040903120c0e03070618030b130606050108010b03010323010204090f 64
    0x250280004512501d039506082c1030404d41c41e0724001800000c1008204130002c5181c4541c001041603181d46e604400c46040480f40c2d82c48980b00c001d940b440d2443c41940f007503512101a0401c09409504890042c00030f110040786000e10301c80041c2c1a0301070480c1c504d0070070340c400508a13080020610b54840001d0b000146a2142006180010603440010300102c02c071709a4081c4007840e803014001110071100020401460941c0544041c0d1880080900722110030b000d241c0000840500034002c45101d0040103040b40c03074140c1000440007800307512680c10f508142e0707030b1010044d15850702d20230540c6840c0039446404401c9400003241060b210590450f00c00c0044442d20014580c4002503060203451090a05030040307003039800b440c014004554030140c509120102484508282d12042042642c09040305005198a900c01510100b40070f10481526420030070040011070203002e480400d6003000f003814105030513444122800d81e00a03800c141c0b0740a607900b51000d81c500e09482041258110b480103640 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 226861061 1250 226859811 226859861
    0xc08011404060b040b090901060501080c1908090f100b10140f18030303070915020303090705040b030c040c0201270f0b04020303040f06020703023d050d06031401 71
    0x1005000140340079190f124410183da1140c001800c0382c0d01c040d003032a100f413070701c15003d50207007070148180750228038540302160600c083c031380c200d034018841054140e5803215904412104410014410740701b034007818030301180c52a014004008080d110300c0703010800c0c502000070894140d40480000007480a00102c03095010000c105580c03000d91010300890302d9041d42041040b20724011010281e06020000400552942004209007a17070328240c0c0c16501d1221806060303a0ba03110540d540b40855219590401c01842e05c2e400c041d01054014060b6159001e10b4004038094400c68a00320300580d441da201e480400550f08000b404003400c0100901d07031601c2d0f0752101c2c01c503540001c10140c41c01038400300040543d10200200c03801001e00143e810f8401e0350f1010025107900349800b08a00c280b0540ca80ca826540107038425050310f07105280d9603500e00d05410f110b409090403100407401441020300c03c0403684100c1d407054200941c01817880100a0f01d04110032800c4a101d503601680c0c1100c42c030f0006c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 226862311 1250 226861061 226861091
    0x303040807030f020c0112020a0e0a0305060403031b1b03051204240212040204050402010c081201051504051e0102010609020f070c082d150c0c0c0f1804110a06020a0c0801 75
    0x80c1c130f2807c8207000140d603841213030011105e85c070000542c160400120f0300008100000050300a10450190b0f0b8100181400c203480800c4a4881640050000380f204515601c0c65109003c481f508501c00e0500d1850601081c0c0740c011204001c80c2c0585440e0f10220702921892411f80040c03207051082ca404514280700c248000c00e01a81c0508064003139603550300060110390103810001c817841c1d00109040c1d200c0b9503d91011010090901946000b40007100031301c5880c44407070095606540d401065080c107920480030302500110312a00c00d504564a4003000a00e480c1c203031008220341d03130740112650f42d2181d0b94140042500d126038020946079100d0300703803801b280c0c0c11048082c10018014000740c42502d21a56a50724145c000240383c00c00901043c140200100340b0001000042442e0058808040048080000d681c0103440381540160891a62600d200c4000300c019902c81d200e001e0380f68101d084803010a0301442c407500958003580c0044401400c2c05030450811000f40b00d00d070024000c01408030008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 226863561 1250 226862311 226862327
    0x414010810020c03090315042a030206070f0204290303210702070801050a02071a090d0f1206080708070905071d01020a0f1b06090e060603060a080303040807030f020c01 74
    0x3500740c80d804142c1041e98070040c012190b000030020115501710001350210500c02006403001c031f0703568944180e0024902980c90080c580400c8c2d40d005034202c3c6203950244040d681c8020800c407880454a0b84080c01030380c881c4602c04405001c031600c0040352140c00c00c0700c24000c07905007626200750710501461120091a0502e2601108400c40140058583c854140d1404e4003940280880d0b5007010104131f035074000c55000d014594040d07500210807089500b024072045009803420390441c0c2200b40c2854240e40900d140030b07079a0b0b03b41d18220501140f4803a81c9030440304290403c5c0340da81c1120608101505003000158003810b141002005581040307440070f05031400c2051301180b030384401903030038030280e0003881004100b68000b17049924400c503625200481d0141c00c23a101c41c00f40e89510010411502c1180c00030281e860507100e2441070b07114007080040a420081041e94024542400440c441600b400510f00451082c02529141e900628000e842005550f4220b01194440501c3c4a0311340c1e1302600c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 226864811 1250 226863561 226863583
    0xd061a0301150507050616080115121802030604050a02121b0d020d0605180d0903050c04050c160f0309050907080601080411040204060908010e0604080f09030a020d06050604140108 79
    0x8902c480c0b220754002e55040c010100c02416a0098108024110b040703810742d0f00550503990380f018256030300d500b08828014060281840002e00080000c4d144010303e0780840b0300104007104010314810700384d0000b443d1001c2100d085510390090387d20041141484440d40c1608801240905218805543c00070203000d01616038a1080018400307000940d00c40c0b43d905000160040b8050020303107016000c0c40c030300f40d51010894103588124002040c120b40b2170003c1400741c81c2d03c00060204000080c0401028040103071246004010420403400b1038020000754804603441418902804411400c01406001480d4010f0740103210240805c04d1040e0700856540e4000c2090804070641e4543e401c22a00b00490024055002440020f01160030340d00410400300b01e4040400a100038040d07003844039120441910024650007042c001c40000008010190090b40c001504940e8030407002c0e00041d10080304100d0a98a1a541d4021b0105600340f030f014404028400c3c0351241d1031945003940c49076580741c0c3d54039 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 226866061 1250 226864811 226864829
    0x1030f03050711040606080f0a0510090b061902100e0606090a020705010914031e090306071128060e0703030807050904150602010606080a0902130e0307060905030d061a0301 76
    0x400d201002102c03901c14590f4507024004100b040d0321150f000d01201015202c040d04101c000300083c0c0601c00034000c2c944107021215202000d00d2900054002808190501542c0100240214550400401c00e0821b0440180e4002c16000103a9660101290b20554910446070004e41c204090344e1503c4004540001501000503660100ba06140d40142a81c810040c0f000c61168044440164000041c150010100202043d10b0b505448800340303e100d101d00c0260160001c07000119030078060300200d105000d08e00305032403840b0800c11041e48030b48001c03180c411b005140d01e12908280701061003101002d07070120780180115810740d28041c00000d001442c038070402200058a40d1175440d03607009950601d0424217040d200315260000a806040d03540103110000c1c03244000100041214001c0405654001d09031040c4100c00d04a410007902003200c0e072a0051004000000c0054020710500c003205010b4400380d520381c4018007200050319625031041d201040c10504198514040c00c08590444401c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 226867311 1250 226866061 226866067
    0x120b0c0a03020c010e06160302030912210c071a06010c060e0a0614040b070c03090504050a110a0207051c0317070c23060c030106020d0807021c090807090501030f0305 73
    0x46040740a845410307951811542020f00220500c2d000280342c6020303011801080c0e41c0050400310071000c81c00b0032110841d10341e000b060030300219040034005060300d07200300c034400e00003920381081c4802141090f91102044000002c3d01414000105055101d5804408010400f800c101c00000c0142202c17100140509075225040c5682d031078100150440c2581c460800d010b0342c24007109554188104590540d03080303240c00c000034a5207215100503500070782e146e140c0010b558141030a0000070b100080c21921401c2d5954909541c40403510040c1403402e045d5401000030328201421301540b0003c2c40450001079005514900010f60410058580407001d07000303404540c2e58642045460103148900680050303090030180c00040c44180620b030310742c0d00c128110f600c0e50b21651080f9080744030034480c4100603005001e03d15440741c4038001c25908800035104032820500c01ea0000c49440411146540c040f41000f07008206000046c030146000b0082c120007000a507146440d200203a200d02c0d080181001000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 226868561 1250 226867311 226867327
    0x1c080702031b010e0f060a06050603060603010b030703060e011212020d050a0509190612180b040f030e060310080c0402070807080f0d020d050901051312031d0607020115120b0c 77
    0x35880304c428640c2c40022030b59a500e019001d1030b00c84409580d01c0e01001d0800f1781c082100c0c00e0500c201c03406a07a010304010705c2c2d61b00c0e0003e00100358002030800020107489031000201002d41940180c06000d0180380308014228500e0b14802c0d180b404000c1d030f02950080343c4a07184558002d0150713804a8002d040c0180e440241314001401201175031580c0d18000b0034200003162455001d0a014031441a03807000300a280d40c010742803840116840b10003096010110005400102980ba62091403403180c241100c2d003043c10000590150001c60300584190703c00902000359000401198043d075205480440c501107041e00e0f10546440b400384003400c800c0000403d00010350700c2004407186c0320310b03040e41151120351903010200900ac0640c2e5038680c560034031011400074040c03801c03000642948252805e00c0c41017030043c194060800c428078280c0034000445240b0102c0010702030148541c005900001b088504105c03030b0300d0b2422140d0441d8a909003c5044800003406451902c0d40100f00700c04040e03110900 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 226869811 1250 226868561 226868563
    0x50607061103070e010f020705090103021e0a0e06010e120303010b03040c0e09011a01020105070818070e04080a020f0a080706152409091e0c0201090c081c080702031b 73
    0xc40100c410030300700c0020422100710307070141103404251000d903110001d180d04220103e0b6120050302a00d940807015000410062404100352240b074880c1c2d800c012400e80c03036800051b0801c0703000d6000d8102800f0300e0782000fa03250382c468074400e0080c01c1180c094840d0803c40148039560701050041000c00ba00c0040810180304003860301000500c610300507940e03240741c41500203000c1c00c0c20039003001211440d00c0c3e2600081d801802001d20824140c4d4a080e001d40e03640741103443d14100460f440055010300c800214200010030280d501c990300a0a01c0c50b645c54404200901d04030395000c3c5400c0c950405081c80c000209010201c0721179540080c000300704400b80f00d0b01e000a020307595000c8a810503100460000d500000901c400341001d1030745800d030085c1c1c0d858480405030748002d40090352100c1207036008040c440d030702e0740440e2122065200010700d0680a580704051504c00f0b0b0001c0686502002e1103002110307404469450070140da00d031190303c504000601070364a00902810b00c80020b135400950b032031090 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 226871061 1250 226869811 226869821
    0x8151302190603050a02030121080c010c05031009090302100c1806020f0105060909100203092e050601051314010c0b070e0306060a0b19091215051501020705060706 72
    0xe0000c1440010302501000301040e4081485010003003030074140025400900d600c01d40381282c07021004010f84841c042a2003180345aa610100d901e9003090002c904841c0c0244681d044100094469603500e0401520b840c9002c01e00781d0100b100380d81010340d1320001941c0403400c107285400c030010120743c0b10b040310070980d445100100e030032601080d00c510000e0b40c01e038001040460000c6e020004c0001d03031650018040e20302c0044964120f65840310140398001c00e810750045601915500568401d0348070500084090108000360304001e11445000e4880c401440c4034158004200742021032501d0004000c40c543c807241c0b440b6003a03a8819041c070400840e4020441100f000358400741842a500e00200044c0c0300c41082824a03010f40f040340c0000740c40b03041c150180c00907946841c04482c02e0be007507002c0c4503042d08814141030b02004a00ca1000070f420804408440c00e4900c201e14014400c0500b001e001d04850b00244555844985020751080701e9030041401c9050710015074034982c1d9031a43c1d00300301000d0300f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 226872311 1250 226871061 226871063
    0x3040605130513090b0906010b22051201060e1e010e0601110604060e010c0206010f1505040b0c07140117040206031513150b040b09060a09050d0501050109060b04081513 74
    0x20001c22500f900c803032500c0c1d00120803180b280f034030502662250084175980c0c440900403405801b40c100803a034140c000000c1000034094070750306501d4400362502c01052a6070908081e41d0001c0c2c1d1201401e101c54443c0505070796000320340c0c2c8144180213242500d00c0c00f0220040c490f81c100c9800d081c0106070310364850340d80038640c400580100c0e00c013814a40391030f4000b44a0354122078459403809008500070752000c5503080c1203a444075618403425050034400480b403c0180d2050382480320410000851a520602511806040383c0280c14018580183d00401c00c84012100b8100714a0000c4080d01c1c0003540c124640084d019600785449560311b41d000c0500c6a48250503680c4154407413032440a1f480d5036040a0916282c80000040c5c640e038a50ba41021802107000b01c100130305051007043e0340f03424103001401c1e45039600e15244a226682e84085040c0c10b800080580d41c603511500180000380b542d0142e03000805000c02074074541480c0030381d040c1e1a400c02444000c1c1c502a241e004c1000d03644140c0030041c0c51 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 226873561 1250 226872311 226872319
    0x1030204210203010506010302070b0a0209030a15020d050f041a220f0203070e04020102060a05041109150a0f0605041a09060c03071202061501050c0a0b010b0901030b0d05030406051305 81
    0x20520303615034090507018450480c03013582414009801544640251400642c0c840c5014105440d88101d13800030750030803410340b50580320300d8000070041942c2c492951800100c0781c000607518941a8250307425210000c16088025141c0c030144000514290780c1041d21a030b204550403041c4e110b42c1416100c00301d4205401e2030500055100f00c0c140103100c421505414400c40465103000ea6402d000e48288a04542c0640540c20101c0080c19a52481d00210303801071052401045410100380020304581c1c0680307480c00d100c20180310104940c10b0180c42103001d01640240089014034250008005100d075009124440d40e0b440840513082c0e80342c1c0700303858600e0b90007072103643c82d094035010260b507075006604191680c0302094990046180003081a90040b5500b07140076005010704801900c207a4040311198441d442003190301c07404a169800a0760280600709a17066882c51142c0004041e219641c100d00d1080d80e00042070400500f002040b602184e80c0d0b41055034465404912500d41146c82c0d611032504 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 226874811 1250 226873561 226873589
    0x15050a0b0a0314070f0f06090e04020a03240c0822020a06030c0e0d030503040506010b040b07080309030d090b07020c0303040b0306041e0f0c120b0f010806120703050f0f0607020606010e01030204 85
    0x1000306c1501c4c00f2040d503285903a40c0000c160303126444400e5480554010b034001000690074004507141aa6507000c0006460607034201800e1402450116402031911400003002300d42801140c00040750b00307071000300c40b90f0403144400300707a0740000355a460f95100742010b05a68401c44074082d4080d609643c46101c0007408110145030500340906a6841100d040b40c0c00d006400004c1001d64240003500d0036102221489400c0088654800050f98400342c09035240d484144000e0705043d816004d101012407003101407210a06103a000030307240417550710600e80f0941080c8010f000385801402500da1002c8102c5020a940812444000807002d10741000101c007401c000c1c080000c41516004100c0442c1181d41d800c0c8c0d4a0702c0c0d40142011104090f00301030384080490b042004941c480da40340d42d0031a00040c006c010a04a01d448246014039aa00484090b04406665a01c0303000602050b00c081c4d90010242040b403821400c02500c0e504010030b814140100700300d034103039a07910035415500038000403c030101e8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 226876061 1250 226874811 226874819
    0x90a0c020d0e030120040e07080106050a120b12150601360b0a0207051e06030a1505030106090e010e0c03061305070f0602160512030f1602090415050a0b0a0314070f 72
    0x705d950040c024014500d64480110300151304c1380098034100c44c0b850340c569003000200341c021104024a40085000704d5259502c00c0c1d140c0e5a41c10b000820030611100512204890724015aa01e40c0002d06c603605202c985092605a03041e51803201451a0045400e030000100c00594403030405c2007a0000f041060300440c8070500035800181c80c01c140c990855200504005219564113860076004580b900b0290038070125a00403225080b18280900145d9002d2840d40c454022070f084442c15440313402d00070744400c0c060b040c54000307105004100c08000c02030900d02408201107551500081c18041c0c0341710115a0100600c0f81c140b00400142900c00b4150500302d40e105002903030b03040401000d042e043c401400c0001c03d403070030284814998071f5480c0510301300010070907001029040000b0491107089805c0c81540180d03030f81e8a91030300c2144a02c0350300d00c00e604002c18040803a130340100f5522030545051070820b140e03511400c0030b00c22a503004c0b2800c00c00b45060303410b06040080c542d126a03607209419501007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 226877311 1250 226876061 226876121
    0x6030a060306090803075c0a110a05030601060c110925020106140f0d080415090e010302010509041107051204060f03200c03040308030f0402090a0c020d0e0301 70
    0x58060007540d1340d903041c0c0d44900c84084000b80356580d45280c0c1d000000c243c40980c7d40360380901d1070461440c51900c8241400c014541c05000a034a112004543c2014001100304103c243d0100018641941c3c802d000c58240300200e65911011f000f500c0510000e02200801c001d2900403010310309030007401d40012801c01c0e440c10700d03014409410048007040a00c0301d00d0191341c8144101000c1322480c210600d0189148418440d1100e0111015900304c00743d42e00d00008520590002c10050000d05043c03220501740000c0284541303030640200040340100070042001d030781c0c01410786105440c111400104d0802c12075100c10b80e44106403008109000340000800c1e284c0691000e4000c81d94580c03150000404011001c4044542d41880c1e5000c607020000c1e0402c01d4048200a807065124101c200c1e80381c603480b40c40314407040c0c104890b03000a0103050400c1004506254444a4101c2804a41030041a4050101948504d410840c0300200404a40490b815540035002080110401748200c18a0285c8503c41 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 226878561 1250 226877311 226877317
    0x2120405221e060501030504050a02010807020f01061701050108190b06011e0801050118030215070620090f09160309321603030207030303110909090109020a2306030a0603060908 78
    0x1102d02454288005070300e50190041d684900e6200000d0825166a03500540d11480040d290000714400c541500d41402c01c03d1155101915001e208100c5008480c2e480364290344d016046003840340c02070701c4000d1048982240801640354010b0307900744141e4407d00100d401030307914200c076080d0242c03940c0b01940d0381c1e070041c0345a41611001c0c2d03a2821000a02d036810020080b1500c80250071042d0300403540e00924100002d86401881058082211004000410303443c43c02009450707200d0400103000112807806040300906102d0036200000240380954580302840908090700040c1600c6107810405c01c030009105244165185003c4000d004500042c2000d092100d01010302a01c50b00611282a5039500802400c0329030550003400da0508568084010f004140d00081d03a5420a1001900954a10702800e00c100221400000e500481f801000458810341d44280070000444011140300d03001401a5100e9260581d05541e80781c54000706100241744943c405018545024070410801c4241d1000f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 226879811 1250 226878561 226878611
    0x70309020a03081c0501050607081c0929010f12020f150403060b0f03030301120606080111030603011406030d110a12030b1302040b030703240f0807060212040522 71
    0x107803030410a54000f188100d170300a00503558040024804000004d2005005141094944100f0f06103905070107000f1040e140c00080807079210031900d040f40c8074442210200c0c4028488071031085429490001d842c9800801805000241e1001001100c15511050300d04403021201404190041c001049003610940060108a9180741040780140d11031030161401204010018091841d41c1d00c1d08459500005030b203e02200c05a07210a0300182030312003842207040c03504407422110360b603161900400d800c541801c49400600d00e200b4003800f00c0b60301d0014641116910030306040346039910b8080e0f803034609105108000c2c1801a019005d004103036058114001040c03058418400c1050310704c00b04001c2e800745000b040c0c203070030060000031240c5101b508800c044a400984600301c00101c150038a040c28030720f40103004800c1c0002000c0103aa48200103400040600b44003600f521500540180c4442c4602d109451150800b1485004030b540c1c520081403000c1d58680b820820b4040d050030310b42c801c40000b80d0b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 226881061 1250 226879811 226879837
    0x60108070503030c060c1303050307051507080708060907050d050901091106030f07031a0d03030b01180302210c0907030c030506040c0c060c12020f070c050d0c0b03070309020a0308 79
    0x2800101410000113407100014000701512056403511281402c0d40c10400030391b100f940004a0000110700c003880103148450140380500381c91071030070503544650300024248000304003a020801a01c1c603800f1081d69042201150350111686982c3d0048460303010301c0b4101d1040070314000501001d0241540060200c074404c10204030445024410010380d40000c0740c441c8100c48100c40000c070700a210f0b6121030b58009984121044440c004408500c8400002c00210042a42c580e28078036030b50f0700050030b851888000c0c001100079a04560104170801c0c8466003240024017507011800c0b0b41e9030144640410420040e100d502c480c9016000100074114200111001c00d10300000b155181c2014020391300140303482d8a0b00e20342a9450742c0c5180007066902c0c108020424014944080d400140c0000c1c13244664008a08c1e48540a5040054041c42a640040d100c0c41140103100300040c007504030030301115020403503182c80e073780c42507801c1c0c024002c00e002c02540108141804000c02090201902c0140c005407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 226882311 1250 226881061 226881073
    0xf031101020607050f0304050a12120f0c020a0303021b060408190e0108160e0604090605040e1c050c12070f110301060f0b1305040f020309060901050c0901030e16030302060108 77
    0x400590701d0300c0041e03d6581c0021010070000035031101c80001590010f20540480720310501d1500c0301c040c0c88500c105c0b913100140d0b58007069500c10800380180320400140d084100413801305410048d40d40c080c142d0b40142410780108061004402071034012110111002c2507402e00e18043ca040d80c0e02c4d90008030044561044400c014007101c1c41001200048c1c601a1038606c2c076a103502503503100d11104401e8207420800c04088465044c0ca41501410080c46812408144241450104000d885400c1e80c08500e541c02085443c1c9203102c10449044406894100180e0702c104008a1600300780840c00480204000081c0d08010001403404401e58680505c45101e61503240d41d0401d420307121144074404420150003820300590742c441000b41109080781c4007a04c043d07940e4030701143c2a200701403241a081e6030701008000020701c050050640c40203081c0c0081042d8a40407030269a24003c1185450406954540003092101c0030008418400070035080d048501350340c0d1900966450b024010111a4007540e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 226883561 1250 226882311 226882343
    0x90312050402030c12031b0d0f11030304140304030602070b04061a0102061f051512010f1206050601030f05040f060c0512040803090718020d11210912040f03 69
    0x5441124001c66006001d8448034188600b04007005601c450710840c14002004802c0c0c88a40d000f5660003800080c0001d050990441000545601700814603802400001c0004030014035000c000c990340f10342d2000e103420303040c1020961729207140150b820003001603200103942d0307041c8400e102819203e180701e680300740300742402403010800d1412490300181c050390054010480c24160070881051072440080c03d0303c192a03854002918908103503075007541c41c10340015000ba02e02c1c1d10348441409001c020114040036031800040c1c005200851102030601a580d0002c01c0c075507803285c4c10480506e10001c4051286080604040300c183c495260201d84103031030240c0e040b1903107016a050340d6036584e03040d407000110f41d82d079181c1c42c0081d400188001804d000714480402e01d99510240e01e04286040b890040c2c071001c04100740c4040f07800e135016000d682c103800e00001240400003580c030341c80790b180410980229201c1e00007031464482150401c6201030300c0442d0201300480200c1048085030f014504641ca4bc00c44 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 226884811 1250 226883561 226883597
    0x10030b0a06030b1509040f060f110415020f060103140106030f140c1f1b0215070507141509010c0c17100c0e100207080a0b091015050f0d05010f0903 65
    0x2482909400500751400103010941f00c11403a6072003402070340b0101303407024150310034070031201700380301020544d080440c040c03003a8040310200c0030103040e850006100400302c10340c4040c1d13281c00510005144092035165504512003e4024000039039000690000e035004a182404170f0781040400b0403024807540801742000d103800d103403695281035200380b01c001050650004543d40001c0e1840002ea0354000280b140050b19480d9031002000e80c0f0441c150f845515910303015040680c15400b80c08080c0c1044c9400c800c42c0c1e43c8116120303840c401d0384030f03ca40c0c80c050f480041e528001e244001801c18190260001070007052601180b1000180c00160341848504070100d000311200e00180000051000c003082e80d050030201c64000300c0074850b00484600365a940c640520f0044510011605400482e007404203c06013000030400003811701b18244801c00001d00b8400b0784900070b100d104c0c49440d40a20301429929a00b0041040c150090020f010fa2064000e584010740030609040b4005003c040300c010001c04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 226886061 1250 226884811 226884841
    0x3010b06030703090215040e060108010e06130504031209061b02011802060c190c0504060b0a081611010e0a03180f030204020d230609010f0609090510030b0a06030b 72
    0x800400440c11900e82d0301c001c4000f050f80340d0b0103e0700b10319a00c0100c4040d0b141600070740010144013428400e14500900010030f0f0f6903045e8441140340d0540c0c4144070450755607015403000d001144400241540e00c038101200c08403029081260aa4030344802c0710107022258000d001528610f098000c010700045d4422401c0300c0d00c140360322408100d00c010b25001494502d0062801c0110384084907041000a103240c1130f01c421214040760131600482c020082401d0600a0310300400e03200f60b2060802c010401e0241000c0c200502c046241c0030749100c941081070003016000110000c041c000c01007180200700300d0340c0d12451100160045030318172541c1e4954040750302c0303800107550681c0c2407003880d03501d15030900011750000d0105440320b60f195400c480f8607580b402d440051040588240304064107240d000d2242000701a0081ca50503100340c007080c4055508001b02c40d046403085940062283c0c1c4140071003130b2440707050300000c00c180d807000280f002c02102c0342c01c4442036030b00540140038a0740700c9400a1003020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 226887311 1250 226886061 226886081
    0x507060e1513050901060306030c1d06190b1b01050c0403050a0b060301112206020d0903230d05040608130b060405040204060b1306410c0d050702030c0301 68
    0x500300c501e80c461000340c1c0e48042d1150318034800c14142c182d510b640005100d20000d0300b051001030f0361283d08100303004881400c40010680940448260580814100e460280090215010305420301c4c0c0400b0840e500040440184040703160703d903c6005000030b040a0700e0300300c1410074656080038080348900d204101160b0803258040c00038048e05000750f9810300807201c000d00c000ea041d56600705503007032400d0300d00080c0b418400004038447c101d9403041000c10071156a40004003150b2220b005121190b4010b5504000e40b03400c1258404036070818107144035000c91200c211140e41c0203034100c1c155503540104c0540107442c80764946d6038255440220744200c1030901d805c080e141400340008584142041c0e8010f40d0030a0000d000420941e45400309520f155002480e1141100b11482003000301d194800000c01342d10f504c004500d440c8814072000440c50107411184407001310103145a20094548410481d8015422241540e40969848001600c5608840416806070050b144003145500e011301c01c8407005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 226888561 1250 226887311 226887319
    0xd0b0414010b030f090f070b0405010f140315130f06170c010525061103060a050904080703050f1303060915020715020c0c0607050d030e031810090302100c0507060e 72
    0x142d520120210084c2138080d010080b1406849038907031894005120b8440078103d00341e2015500c902c0c00b800100003aa8070810035003007245c841d110304031280142d41207a030880c2101d01c4001c0c2c0100e8410004030455004000d05035010301d04145010060701a80000040b25007550082040516a408a40d01d40340d070703c15181d000420400c018408201010000b18007840000510079560b0400da072070394201ca03040984005149000300800007a80380410b00b80d0b018050544409100d42030940c3da0814901440328014207000c4081088075070200807200341e8003c415941e100f4000b040d82c3c2c1c103005000b8001c4503015540141821000521301440e402102d2455510841072004004400c40c4400203400c40580c150240c081d144a09109643d0440641307002806a80a46001441030721b015080b1658043d42c0092078100303000034800f01e2685050380c00f000d6019210240380c1020000308913283d0a05400003980410088016960244e20100d05811980b0540880340b089450b144281c40441d040b908840d44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 226889811 1250 226888561 226888567
    0x14060903070b22060609060803040b04030b0403180e01050a170303070c14010c080a0b100906030b01030b0603090d020609030405030703030c02040207060e0a11041109041e020d0b0414010b 82
    0x8a00c90000390703200a44144540d40105400680c10302094261000e8031400d8032904244915595481050020230090005500d010324000706000c0c00d0217075200c0580786100b1600010107250240c40f10b80c84c2d0003040390103040c0b11501c43c3e00d044122070b02800f0309030003200c2180c00403584e00c1100c400c8a607240e08010040d0308569507008220751400c15000c084948001110190b243c04000740950300c055000c0307840d0303486030f032500042e140200e8103235614103849020001e00c1c501201d6000600441641c03224640820805034001c0140c0180c10100301698201200204010030000040b0b461041c4c0481503080d5401900c480d00215660701503070182030b5064010a204000181c0205064003c082c8003030400741c01c1001c07c1c1c4403041114100034407030000381c011600030410032154041505071800100c1d81000248c03410081d044013401001c020a008543e102000560300c03030700c005080ea1118801c40155514643c5140f4100580b0082c5803280c0103905000c0040c0a864299066078140c42c8030b07103c1182 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 226891061 1250 226889811 226889813
    0x90e070b0714010618021e120f0c0f130603140415180203160501020f01050f0c0304030c1704050a14090c1b12040e0a020a120e0309031005041406090307 67
    0x4007401c021010352446650322403001922146074144030f032030003c04000050f2034006409185503031040f04501f0190850b02040314052858007403030031581003454881084062b0761ba82d075240d48107203d03204e9848103030b10340800c400340c180e000300f00048140c4020b41e506100c0d04140450144481a05803001441c00403507540b1103107a0b013010f5110041030800e40406039401c06060300400d0401c0449143c1c0c10088410303000a12444d60100301e40c40c00240b624000f0843c078500155103428864001d4101d00303d5410001c08513003803522440c600c08005030401c0040c4208010131051028a601034810240202c0740c103000051034414084000c000404054103104c0306581d4070b210030f0702c0d81c0d00019400c000030048803102c00d14000104041100a40840c0c0030030b40d25030520000081a204c01042d681c0b03418010441d0b80381ea598441e52000358100e42c8030001c14010704031000300b400c1d80140c5441c40e4052040306c581b120039440681105010300d00509010200c08410f400c40fa03100c0c1c104481002c410307030081054038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 226892311 1250 226891061 226891073
    0x3070c170a0204020c07060e031c0e0f09150909010905030403170f0301080f100b0d02130204090e0c1314040b06040b04050108060a050708010501020d2f07090e070b07 73
    0x2000c02803845054814180080d800038081342c1020400490903800540207104160304200b99800c04001200140f0040501c0e50b079400303040c0c021000e61410010703002000d9080d5241d81000b5884898010052400e501d4a2070130b096003c0c0c0c40300f81c0103204110003404624107001c188a038401035500312020350300e01419511075005818040088100503602000440c00c4443c0c0d07000698041c0032120b028100c15044902964542842c811120340054580000081260348826002c400302c1d9054403414020764081e1035031002401240d0201221310305100c00c00300081404145000c00301011910403c00b2440c0c078154000b110404003081026000420100b00442c1c260346a055005030000c1003c240c1041400105060b504c00303030b201808a40c4814107000c580005405219070298107071900302003a61401000039a100c0421800300c1c14007920030b20b0040118800c44111079101d03224091a402068400702050741c582d11846840b110602e42200c406500c2d0300414a1400c440c90941e203541012115181c038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 226893561 1250 226892311 226892339
    0x10f0609140d05190501060504110a0e04090501180201020f061b03040c0308040609050f0f010905010c0204060e0c19020105060a090b01031806151403060a020a200601090e03070c 78
    0x5650002401010034000f41040150350b00644400803e4844010180b812601351141500900d120341d0070241c9800100c08408103444001110f441e000c1090120310021900078514010064004d5003455201c200800380c80811025541c400e0f400c8522010070480380ba521040182d80c1461070303040e440340030450030b05801c01464200307000b0240800e08030b50340e580d801c500e581300354494004686203400801c068070b040d000c0c100260074117903600c0b2181c5103a080001c011024601a0302e041c800c60b03401c03580075505e86910590107840c646c6000c51090520001c5502650420b82e0180c071400121600303040c8092040c0501342c0201806402c0300021418880e108014160464149041583d50070500e10b00c7c0c121580302110f058000d150004030b01030768003010722006020390010349606101c03040d909000e4400280b820340c48600045c005032543c10100040311550541b1040026010615402140c818000714580e0304031408a0001c020b03c2c2a0340030040d4490148040c042c20300302415104100c0c8110070b810b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 226894811 1250 226893561 226893599
    0xd0804151d09040c0f0f0504051503120a03093207080c06072d0201020c01050406020721050604030f0e0f0319050102160507150203070c18060e070f08010f0609 70
    0x11510704c540340c400c0c14000445990000c0b0000c020700408100c582424851141c0140340d040300d807902c400c101c00100e076483e0040c0d80ca480c808503000458800140c840d0707201002a541c8441c10a01e443d002a45001e08165182d10758194805440f000a11108001a60a0446102d98040c0c40c46000303000400406401c41c0d402615298215082c0b449003186080342c4100801d200b401580e020b110a000084c03a003284640e21a05000c03081005010a5400062100031610010304c1c444500e0094400d4003090703d4101401415403044000340700816411580c000300c1c900581e590049814062010015816041c0d80341035055007004480e204030072140a19006400e0051001610b01603440d410101900d01296041d583c50300165828045640f1244bd62924110781d48011801d104aa07211b0020355641441100301d880030302d401076442c28200d81c002e0b000812a0080c414003920f080140035200b00301e0310072400000341990001141001d02c096401c07043d1401c954840840c5410300d21042100311304a11 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 226896061 1250 226894811 226894823
    0x90a060221040b07020f070b12060301060906031a060616030807020c0a080703021e03070b1305060703050301140d0b070f0c0f03030c020d020705030c010c02010e0d0804151d0904 78
    0x10801200c06480c0c0e009030b005510404000480d454040d070000d09003803152645080326080301c1810003e0141c11415580690840150352040352917450010313005085c00d030311408205043c51400024400d4060412601c201240351003101551800200700c040d01c9001c081040c00c00e80500508042881240d0281d40144180101c40311020705a0024000034407651002207642d2040b5420700450504481da6039030084034600c0c1d1500b01c44030300002030301d911060040d18540c820126035030440030365141401c4d0040402034a030540c1e4003110300340100654000d0003001100134600e0442411811b001c81300600c07498111008903842c0d10340f007000f180c0c0d8054030300c1c0807010031158020040c0031810b801da008c800144261400500c0340070041c0042c2c1040b40a02c608010364004007410031043e2404902010592800d2800390b81c45801d0713100584040c00c1e8590216000b05610140d1000c11681500500c151002c03010709a001c0c5a4200d801c441c0f05500080540651034019072510050414540c005e4000d44104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 226897311 1250 226896061 226896097
    0xd0207061b0c080124030f020f010522050f06030f04030302031506190201050108071514161b141c03050c030f07030e270c041505030105030601050108090a0602 70
    0x240300c070024004107401c00c003000e943d070300e51285182c2098030907400c60032048040600342c82d11b5900c40b247c25001800019019089109502216038455011103070200801c015641903140d41d4001d1151000301800b4581c0200261a02e0f407040b80303040c0c0f041c0c902c182c452100c40ca00d01e50f181c1da000c80180d04054448126030740013003003801c0c41d980c6940c041c18140340c140c50002007811200c00c009081d05c506910201054001100a203c1403c400b000a10901c4050a00e15038556450300020310034450b6099800703482848d50340c444100b100c803c0d07092240070840c601c820f46154480301d10781c0c1d040c2b1051804592006485144491040484070800d03a098028107200341000d105033401811341c0d00405080c2c010f4840001c072101016000700e100000088103480e520030320146c03907610440401c2007a507500e645001e032000003454001407030308403009800b5016000c841c0000d0700c040945290028004c080c400d024034400400d03654840c981c1280302c3c0008000600301c0c0d500392b4a550000f5800000260b400310548 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 226898561 1250 226897311 226897313
    0xd0203010b040212060f0906030d11160e060109060305101707030209041a0901020405060f0702040b03030a020a05010e1c05030a020403020406031101030c0f02030d0c020a020301050406050f090d0207061b 89
    0x3610250213152030071044400685814004c2008444203545010b01c19400b907010b02c07000e61800500401d00c91400e0501c0740c0c180070f10345600c7d40340568030f0307041c60500301e20500c0200740b8464604402d070007150280c0307440c04a9521180141d081d504201d4017404641241c08041008544009000392520702007419500340c0c1d91203801203040783c0022501510f080100b48082c001e9070707401c0341c0c80c1039104901400031030400d410000059080e200348180e14001402c046107001c150b642d01c1d80500003081009003129916901a60065115408843c040e6038039440d221898990346400b141041e001650a1424001c000842e84c080c1d401d0b81010700020000c43e828000480141c4891140a0140d402154680d002c000c264000405844a12440404001c030506034a42e1094000058400c0307051000030218900c0700c0a4000ca03c2c04e080010065855828041803005010480e40510f00401002400900b00d82e0f5518003255281e06c1c4141210069000c40310030040c25204501504c64544000c01c0300d40c02c4e1400b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 226899811 1250 226898561 226898569
    0x80a0c141b0316020316031101030b040b1e010e09060a031209090c0c0c08150109050c0c12181f05090409080c0607030606110318010315030b0403080112050c0d0203010b 74
    0x820700300c05800d0f80840c1106625040101911615441b00c3c503200325410344c3d1b984030100603c04680d074145031701d4010741d202a6071650040d06401c180a807100403500c41c91030503103483c00c451040c81c601042100d07640d01f0711420122916841108098004004540382d40d6800c8154401080030004001d03080c2008580c040c05400781200380c007016541da68107201f060802200000e103591044007280d00132070745c046003650403104a904603207149100040f96038440030011258450f1862104550040d030407040b840109c54005004050443d003520b0858424844c1804444c0f50407025264000058071654030301e142c0310310300500c240c01015001050900349503903900c0c0690491241c0b601c194118000300210140d040c0718080090400d8600040b043c1280140d4a81300e10031408041032560080d005034036640d0194018030110002170f0405640d60340c0d28241821986000d58040f400078009000000314008030708000c1c000607030018064040001c454003005646034910700100d03015500c40e6000100c0c0e42ea = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 226901061 1250 226899811 226899817
    0x11b02010201020408121c0b031e070f09060807060309051906093005090a0612022a0c04330e0106021b0301110a0c1b090b01080a0c141b03 61
    0x1e44078450079144d48281d8207103401c5000c44480541800d1900a23003030401c1c1d80006594811a2404406414071044200c0703031400d01e0707060780100c00003806801c0002514910b0b40c0c8800c04844101c41a61041c2e40c407448100c0940344081070240c0f481d8401ca11107282c440c800201c2128a0b440b403400060021003a50300c15142e00c0680780902c0c3c001894071f021445c042c0303105580401000061600754038040d00300e030003d90711041d280a03901c104001058050300c07800d000e43c110f4550309019540c407905040280044003082c40b4681558a450190100c2145141401e016404200031802e86250031141603078608103068001d050410790322000102c001405c0d11002030341502070704050740904003c410240101102c030300744150150090b0714003044800442c11040942e042c184591400441c1d8202c1410040410b140000300380c0001318400d40e000803051000c0d03005000800702030302d03a8012959212a030341c040341e52844134640410b10420901610000001c01054804c0410829181d8100d0200800345160 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 226902311 1250 226901061 226901083
    0x1803050d030e10140703092a08120a05070f060b0d030806030f211c020408010506090f040f0204180f060e070b040303050f1803010509150a0b011b02010201020408 71
    0x103a607401c55880c00a0b824804405408440c54051110325a40c0030011802c907001011103040507542c048000811900c0040058450b003490584401e1820b026001100f50a10b8030031004c031480740003945a100c51203402680d0100700a134a07450304200a41c1c644445079840024110340a9076180174460456448031104c0c82d401d8002d0742c610210707140c1481414030b82700d803280f4411065444a0400c01081100c10100003000c10300103402601c510f040b945844410344c4019217034480c14000700d4045003d40b015070290384101d004503105c410310f0700c50314040980468151000790141040080076030160402d90492060b8080700000c0841c4004503458140c00740c090a00c0480c1d42c0350b1641800c189201003008104080d180c04a0002d2406c3e02e140e5021300303035100c0c030104100c56550105500b00304141d401084582014003500070310881c60007109050b1601200075a542400d004540030912a000c01d00c201c10001c1c106850f245581642e0394003501c3c421990341340c1281159020407002c03c0c9aa402d2142140b08 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 226903561 1250 226902311 226902317
    0x318050303070c150e030a1203110a02010e01060b041404090206091504030c08030306060a030509100c020d02060a02040803090906120703120e0105090906062206180f0e0103031803050d 81
    0x10700d040c5084c2d00d00e0743c9407820301c1004006000d41403a84540e804a001c2c480381e944510800e01c1850003035000c3e006000181080140000040741d06105160103402c15150202c1020080084540b01d52030700042e40241e00a8403446940c51050b0400385c10a98012031020f40010519030a000c1024000b4141036940101508002c402050400420050441c1c0b00094420007018506600e00728020a142c1c0c05010061810143ca95002c11040c1c01c0c10302170706400c11101141400f901c10a02c001a50305d041038844000103204090000e034840c3c0c4548207a030140e0704071101541c64984035804204d8100c0c03020300015030083d03400c0034095a10750200300b40001176129036240f0f00e811515100103052030003001141410303c40c040140c83e8095865030001c030340c49101181c6107900c1e2490300b80a2030541901c4510360384100c1c6079402c0468050f07082100194580018049821181d0722b42c100c11621301510300c02c0081c061070450040c40060f004440310300e002208003140110031070f030702d840b007510b4640b1032516103002c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 226904811 1250 226903561 226903583
    0xc09170f0706020d03150608060d0f20190323030c07060804150209060301030b0c0c01140105240d0509032b060503010e12030901020c150a0c08070507031805030307 72
    0x11909405004410010b020008000305d20f44070008e00b407030800800580c4170b400c0040151017007081010030350b81566080210300329850062244507440c1d40300132040034401c00b84a9961180420300d00780041c2541c2c0d1110008480401c0e070045040b2a620340702c00c0d03000d503000901c06000700c07403820089280181019510320f100381c01c1c035041100707888000c1004a1856401002100c4054440030122811250b00c408040007d0356201c200e001c16004486c4045440e50802c91120b24299090100905030303002214100340b4841005150015000c403001d100200000500001c0305440a641c025a030000c210800d60b490a035101c0300c00081e000180c0c1c24003400e600b0442c0d039920950018410100030b410150002c00880c48a80355556480c80c0281e4003600780203000001443e11301c0290151000c2034402c20454004031380f508000700c074144003140c4200c0c5035490003025000c1c0034412038030740d8001c50041d00da041c900400c9443c00c40d001a05090144104680a200040d642d00d0403c024085603003c0c08003a40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 226906061 1250 226904811 226904833
    0xc030a03050c0c0a082b06030201020c0301090b0604110c0703050106080601090207030e042007150e0a0209070c05150106020606010311040605040e0a0b03030a0513090c09170f070602 80
    0x104440700035021082d0102c0c02e20001d000d039040015681459a000b642c02c0b0f44904080b0040111400c1707060802e1205441080766141e000d4140d006107058a10076001d6801b0060842c0a15003294a00742000c0c001540708408070701d10741000d5001c1c840c840300d2000c50328607146402d600c991800d002a44100c40c00d80d52000108100c0000f07102150141c03264190035850059035132002004c540c1c03000e030a02d100d543d0ba113858440003040c40e86007410414100745000e84403505420944403914101d0700020440d4100b2040208071840482da031420302d0390081c085900758591500c12585000d0015081394184036060800450800e001c0c1305500900d01c43c1e005200700e00d044000103040d6171b100101782088800501040c00b2698001003134030180d07002c210480306c5030b41c0d810804102030004c4140c9160103000004400141541c4480181503e406400f01801c4590351490070031b0807126443c13150000114580c0080c89641d80502d10480c481c44104100e07405500e00702c02d4103080c1400c41c1d110740c0143e840031034041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 226907311 1250 226906061 226906067
    0x902060a110d021c03020a021c0507020310060b0f0705100f09020f1816020115031b0f06140c0c03070e090d0306290403050106121a090d180302060c030a 67
    0x402507411440501407403d1002c2c8512004c0ca640f10310301040c590049031000e01c05201f080491034090300070000e5078114448620141060340518001ea001e40110f16400072000302d07601544040303812901c002c1e4500a048661580d068110807422225405052075084180f081d902802ca90902200790014240f80c03a4410041c036551510110b0740034464801005803c520b500b20907e6110040d1404d40d854411064022801416a901c086050050308103001c010303c86580d095812440004a001040036191302801500c0099172240200143c1e031061748500400400c1d0241034108100001c81d040901c0f007000003414028103400c182c0400c50844108680c5075030801c61200000994103040141c241080d00390083e49580e25440c0300000b4040c1c0f0502c2440c45007200300e40065030408003c1003039036140c0c031502659984105081c0d9000758820705a019080c2550801405004003d00908901c580c103802a10180c5815080181c83c1d401010004017580fa010010301e8010004000780d0b03640c2c00151005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 226908561 1250 226907311 226907323
    0x130f05040b030f1507090302090411041808030402010c11061602010f0e03060402060903150f0702010f0203070507110a09020f07060e070f0303111e0a03080c0306010c060f0902060a11 80
    0x1203210341c0c08050102c43c02032001c80d4841000a008024160b81d41c1ca401050b01d0311411760380000d4118001c6000c010a108224410306224071085030207104121030b45000300108645190b001e0203603074041011500540c0902c3c9080249803180c061080d80541501c0041c9103038110070080d020101415000a00715a8014400000c4816a0501174050169200420342e60400284021702440c400504c1740030700c0c1d50800100c0075144280c120381d4940d10300010400c81007441646c0c1c3d10b015600f440d21814062801d80245c038840e0010340c0d1103a0400c41d054503a1400074212036240c98200000c5880451021500d0004010030f0399500300a558480381490040111a1140099078058200c0c920074007044030510400f0040729058a000d01461040c48959800c001684a85501075041030386c440301820320100310000e450b0f02944904505942c2e0341c009101600c011030b08140080c400800b01000190284c1c001141c0e0803240000245401d050784c0403681d680c0c00f01c10300750040703080d00ea1003460341d00c010448 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 226909811 1250 226908561 226908581
    0xa03030b01140904091106070c0f0b07110103050703140123040e0303010e0414060f0402030d09050901090c23040509070e01020303191e020d0609270305130f0504 71
    0x8566400342d41c40042003240d000358050140305540301c5440400b407000e0211026200d2a0040456680704004d10b89a00b40c529a4030880480400010703002550007000d4007587c4140750808a0001c110304c0100044009150041071320082c0b55580542c1c0541e0031900c172185010b42034220200c4038201a080354840d0214000803c6803040e401c00b400d1595011010040e2070444108034011702d050b4a4600d000884c01c640c030740004000c1d10500301001059002c644006004034001d805440c40d070030041c0d10480c0c0041c4a8041c03640c009441c4401005035450561005103034104030b00d0702d018407844610071b40d03000791100c560050f82108041814485441d15101a940000450030110103403807800300040d46a020003440c42e08034020191036038000c080c00380c100401055003216400d5010300300c4010200250010046030207001e18161b000305440081d4440c200540030004503000900d805c000c055800d41e400316408500300801401408182c0401181d5040504900260034844034200000e1200b02c0e070518007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 226911061 1250 226909811 226909817
    0x108011a0402090a030816050d0207060e1f1b1a04110102032d04090e060907050a0f030209041103060a02041802070b0a0b03031605060108010e150703021810020a03030b01 75
    0x308038515542c1c0c91091341100e03803003c0d01c2902c98419a2032049800f40d0f41c58040d010b4002c0d0300340400c0c40350303001c11a882580c1141e110b07103082170114418000c1d00c0c90f80b0030141c2403000c5c16040220781c01d4010b4003688401c42d044951100b4070182640c03a2603041800514a40b07141c1014800e020030000d42c0701c409491340c1c40c288011410a10084007181d038400e0702e040001036002c9500c981010301f940450864000d41823603d810300c51110285480b0b541c80804032031480c22801f401d00003141d01d1608840600842e1160032100380118207507000c00070600c0e80544203d9a00c00d81002944c1c2c10346060083d9031095010000058450f45010000e0b038004179507481c00864640304100c010006480110300c240c100d500a100004c991a0407004203107507100380c6580341d4030f0144048851042100002f022810707505400002d0050240342080309944079850306221089a03005000580654801c2d03018003c2483c800716080b6041c1868004203920aa001d500e0a0060300310030801014144c25002d41840c00304286 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 226912311 1250 226911061 226911067
    0x3160203150405060c031e010605130e01080c040203130f03080a0e0303010b0313142d1b12011b09032a06030b131107120c0c0306110d050108011a0402 66
    0x10340c0721515542d0090611380c45005c00320124200c81c842d144103a04d1142e11402445407944c4824014045400500d051181041c41c40d4000c5000c04941d0002812120a24020004842a42d042201942000b070500002760700004840005c1001d000c41c018045000b80c403010044c0c1000c074606020344036009441081d0754000c100411514101c00c085035030002d824144482440e90a00d80002142c5130700d82508034038450f09010b019003502095a8030015021481040001c11040c1f81d4551230f42d43c094034800b5604854600d200c090b04040071900010102d004c00000c02800314188213410703040b1031b134a030782c00038003641c00520401510701059903503003c0100440340246003c2c20707180001d52880c000c640406444611021003900d511a003c0890440c030b480a01403101781c892109450381082109035904003000180140441c010500d4500468020000115181c10740d103c040140c248000025441d69040010380401010b9108203800381c08080008a5624038001c4601076100468995601c03880c410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 226913561 1250 226912311 226912313
    0x308090a0b011703070b090d0f0216060c1505130309081507030e071214070e010e0609040c08010203070207081b03030706050a0b030a080901080c07020607021e03031602031504 77
    0x5244a034115241c1000c148003c240036051103045021701a0001d24070410101070140c0d030700c0003040300d60000200c0d81c0e4030500000c034018100d0f40c0c2c0003502c202c401603940d0b9800034032100e44600150030740980650f00b680c03a003005808240c002c450b012940622103a03010942d40d000c01d50301000325030080c1040300040c1820031000ba210107102001030048400d05541d0a4451404001400408001c03c0100c0b100e0350446158203010301c02d180f003808440b01c1400361007004141d0f6440d0b0b40c00e540c1a510182c0004001c0c1d0342d00010b00c00094000360056030302c01400900011f10302e80c2400114802c0300e2580c003401e041d87c17a0444c2c0718a0703c0c002080d001c405c20f00d0707642d032900ca13618001709880c02c1c03581142d40401c198450407500f500070006045400d4160050085220900c0303041d100901c249002aa02d400007640c40000c031641a0003540c1c0001c4d80148200904800362a2008144440000424040b10481b44400000c1c0c51a4040700820360503d420f40c80010540c68144940c0b03c0c6001e54002061291800d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 226914811 1250 226913561 226913573
    0x17040b030a090c1e0509010807060c08070302031c0b0f010e01020a0204050402040e0604030504030312150b18040221090d080115050f1201140414010b1b1203040308090a 74
    0x80107181e240d00941e01e040c15000c0c86203c290f0700c0001e058825440c48980111440c0d441040e005000f4079015880c500f000050840c0006002001c40706199121400010076a07203c40c072a40c000a0b0903402c6200902060012164032204041d10214543d0001000380a0300c040c07040600300c168540781441040280680d541e43c011070500302481e4100e90008950b592807000800512506015088510409003080b0406070000d0050081d42d029448414042041041c00b0701590030101c284100c0c0b100300401088000312150140400991340d180d407403802029000403404a070007000701810076000c0c99441c8541011002002900071180c90b018007551b10300b00714050000101842225046088980f40c2c141007845602640d20003101d8003204c1b0f95a949189290030108428043c200c48070301c070040c42408501e018881e1155084c690082058141c0c40e200003459247c100b089400e1200c410381c512000c180c0d42c1801440c18000c211541c050b102e050a050091071140b000f00264480d6216480410100704 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 226916061 1250 226914811 226914817
    0x9030f010b1c060615050307180b1c0f110d0b2713050a0b0a050c0a08040308090a0c080102030708011d15060c0303070903050c03030a05180a03050d080417040b 70
    0x18115880040c1c902d182d1904074000c109135402460302080e40842540526800002503004160a40e2584003104d648501c0758a141058890106504810403001100e02420400010000c80340c0400094900c00d41d1541c105039510820001c1640800040100c445015440362140d140001d442d90000b00c143d4a020841c80c02caa07a034102508200740000400070b0429080c0194007a0b80801a6081903400e0b05d8001159070013550940c1e032450415000428440c00c0c00151081440d040d07a5405094031151415a18203101600148050203101c51074004109000c2c90343e00100101d000041e62860142c0008107104010703008001139542c000102640b400d00d01c034203540c10850030806c100c0440c900c5000942107229010382c100c42400040704000c0015001500181103900900aa64504a0020415489100c1c0c256400003042003840640520710b00d071010341e02d02d42c1016000a6402d80c59868051070b001d8101040d00014110108010030004007003950416041c280c1c0d051418282080204800d41c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 226917311 1250 226916061 226916089
    0x6011d060409080c070308030a0b061c05070e0a030c0e06030606010f051602040525020f030403033c0e0d0b070c06060b0f0405031905060c0c071a09030f010b 69
    0x281e2140c2c103860a0001c404125004040c11004a541440c0e80745821395194008036041c060399441c040151650382400c80c12a11212120000c0001c2c969082900750002c0401901d1075081080360250741d885511003500480c042c5009417545030489291440c10b8a80072801410b15010b41c1265040c0f0040766000042034060a100c1d0034000e44134007402518054900790503901039403103030074003042c000300c040c409516152503c8646a20b407881554441c040e40c1d51803203108407800c2d0703610402042000c24801e45c0c001048041c940c0f218944401c03080c1041400800c040341202207941840d10184c40c60303070072004100d10307030f802035401c81c1807003100e41c4443d80b60300302c000c021a06110800c2c03e09400c00c80a030303015001607d00c0c07000b003035282c040800401c01c05400600615000b8420340b003c1102000607000e89802e1b0951160051030340c0e40d40c45c071220f07a268008610082e030504c81c1c200085200c41e03c0880c240301da039409001954954054908251400100c20b0b10682c1f10391605941ea015a100c010f6100104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 226918561 1250 226917311 226917319
    0x312090c030712060b0324060306040c05040b010905060a09061e051e070f050c01031404020f010509120109060b010909023c0d021b0d02060a0903050706091406011d06 73
    0x900c100c0e0904e1405081a01c003460390600a54000800389290500c50741004180c0310034044140c0e0f01c8a050650340e13803003914080c0c994071400e03004001c030b440e00360006000d608061402200c825501e0010900c150488000d04000c606601c2080c1706032603000e45620040103c00110903008540a04e0140480c0b0990410f125440550302d1000d4401d98080c0440b50465408945400f500240e810b01d583c5400511480b0760019003403c14100c84034004425141c092030b0000d080a002ca0810001134030300398030601c0c100e81c0180d03450311041412034080c0b044100c81c2d40541800301310134001ca0001400003540d500640e007440d1062049212444070005802580d00101c0c2c251503070600b03040c4022420883c40d280c4506070400018485511501a4006e040c600f840341e900c000010044000c003d0b203a07031104600ca401a400f110014141000b1500203510303ca0103402c085180a1094448001303480882509075400d41003c003200e01007240400005d80180202180c00e4001d01e01840a07000920340981b1075441 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 226919811 1250 226918561 226918589
    0x4030b190e0604030210110a02030414041d01090201080c0f070f080c010204091d030f250b0408190f0c1b091b1d0a0603021c0501080312090c0307 64
    0x405800341c1c403403030760140754404550892401d0700c0d00964030582001801401401c081c2c3e0100a1402882074a40c40c030580c0c1c001d1410542002d909101c03a05500991550041d101e40112031b08403074500c406144081d0380380011410000d2400050540074003d8580003642030200301c0300ca4000110b009075500c8070381c401d1508014007024201900c15014461400c10039502c0001c000078135001c268071144d4651a4040c0d10484151540801d540300c0c0140b5280e5654003004000c1414010824440c003c40200e071074690001490050b118210340810443e012a441913000440402001c0f001e4001400b1030309500d0174a281c100c009800809089886400030003018001080e520342d040310400082c054140c0140030004080201400b58000840c802c0c110042810260792401c51010000702c501c810070007605c400003103890400704400a501c00c0e003100c10136448003106030301c4003c400d0007058000c2141034010b58640702e05d40c0507012128005131401c00298444140c0001c641c07400306012085905000344021 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 226921061 1250 226919811 226919851
    0x180e060402010905090a0b10030902030c0a03082b090c06080609090d1409090709180203010608010b071a04030509190503100b0a0807470901030609110c010c0504030b 73
    0x4081c0403500c0340030b680040b0406000540d189c2c0f40e401800003e0089044031613482140e018001d0b00c444600015003001d10070040c002c220400d03000c81e0a84200c000142007408a400c01c28101155103406c1c1c1110a2402c1800c100406a40190306c540c02110840b1003100074103202d48a59542d0707241e20240307420301c00c1e4081442c01105c1401c00b501c100060240405445c0c0c90408001440d4001a00036899405450410100f100c02503100b40c9040c0e030515280c0c03c999034201010011142c1000c4000c6a00c40101d00301048000322422070780d0f01684c800d4840d66140c40d00c02d0204030441442d02400703407130a26650000c21041da0700140a2880040f0b5401c002840207150380850031640680d007000042d07100e4140e0000d10308000d8280c8101100070540108910b980c000604d4030641400d410b19074040d05803c00c6011b44510781c8000308642c0905040c0014240d82e20041c03442510b0651400c0f40c0b036401c01045454580c1c1003030086e1103072803650b0300d4180c6c9080d06503035820301c00c007202620307600000b00c1c1441e0b001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 226922311 1250 226921061 226921081
    0x905060f15122d0f0a0506060702180601020609030c03030c070317040503090108180d0e221506020a050307080c03040906090b04060510050a0804050313180e06040201090509 76
    0x1800d1181c001448079400e1400e440f900c1480000d5101030804051410f5003129541c2645070018000c1d0764102c4800ea41e500d4800003030010381806880b559000c0c0d400c0241c01c00607520100b19015109801c070a09010349000070000e400e0640c002c1030a5401d4008110041c85100080100d0b075004803505002e03502c441c0c5a040031150312320741031000900700c03d1002c10b1006011000001e0700103610241e850301d600e6520480c00510052601065107242e034040d00b02c11f024a40915028220103074054034001030140103164100c0fa201400214403019550364014030b00700750100c0e421401030301c014001049881c07003507a11943d4071f108903500540302072800b1694440e030982c00d03c2250014080900c0a002180d1101e801c00d00802d03003852924800c92a0580000d81c9080240454201c031805440d801d0600e103506400761451080100700311000d01003001442c00070010408014003034808070904800c0f01d2088480c4100b00c03901c0301340241842d880394042100603a131140010007901c006680c1c01420b0b881d880d5100c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 226923561 1250 226922311 226922317
    0x309050f071206050910090308011a071104050901110409150e070203040608070201060e160e030c2d03160510030608030904090f2a0504051e0601110a050d03060905060f15 75
    0x9028243c11f10002005043d404422a41600c02e441c4400102c01742d0120604454800c03c98000c1a80070f100307030f1078015403802d980800d50001844c0c0001c00d48042141c5c900b90f8907440b540004902c2c035560070811001e030203404403000180141e4801c5e0021800d115402940c0c80c051781c89400c0070000c9074400540c0d000d10030b400c031500420341401c080080703051507090120244072074200000001c0a60b1a220f08070310b000228504001409094003911112200c010500030b00b00b040075000301c405000c036000703698a081000303c0c040300641000880c05810201000068a03030740045070101400d1120901c00700340080700315603072000200c400141c0501c03c0c2c54002d24042070010090460f0006088000d081189000d11541d5244140c00030b00045498078100011250290354100b10030703400314a42295100b0b2250950781200d0141400c0031500341c80c0d4041440d03c07901c00d8003195560005180c80c40c089426003d004042d0425041c00e020602d41900810000d100a490031445840d548561002d00301c2c0078000c07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 226924811 1250 226923561 226923583
    0x3210603070e01060207090b0d0218060f190501080603060124110f0105041403070f081b0f030901030b04050903090910050d060b090702030f040b09040f020a0309050f0712060509 78
    0x641100b40d83d440340d0107512040c0c03520910f1b101c44e00746501e4003802e1501d070304a0340e0820f6000f0214844094004d203111000580181010782200002e4030b0b075800c03a5071352000354065807400d1101025003420040010945900508001d00a13480b420040c440e507841d0100c9010403006140d840307410356040c00000c950040c0024105d180900550001e81d060f6107041d0030440c41507004018203100e0142c3c901c01e159492240c0e00000d090702c3d00b00c1c0b000000185180000384000d9802e64004000b0000540b079036802c209011196031210351000601d1045540c05001d070110040d0110341c10040361500844043d05d0b0b200e08010300c0c1c0300c0ca140c9030004404500a1807048050800902486106a55403401d000184903440c034080c4913040c41c100240714244004101c3c0e440e100c00e09003450a00d0300c0c101c1102d1158000d4211540d001e900c1d2015481c0c1110301d4400b410400207581d40219943c4200c5c2425420b02c1c00240da04442038001c50b40901c140c092030000010126405000010155200154182000a5040c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 226926061 1250 226924811 226924829
    0xd0509130504050d180819150e0304091404080910030f051807080f0304060c08040308030c070b0a06150f0207030c0303080405100207030c060c17010e090d020321060307 74
    0x42c002441000660700745034061940301c90f069083d1083d034043c1031a201d88941800303540002d801c29000c001401d6800941c5110303503161000aa03580d40c0d0350003612441ca45c071761610342c4046420000790ba028003900303c410440c40054103e41c181500c0300e50451142220280c003406c00300695040042c4258407442e8000d23110082003103030b410318114210641ea05440c00b400b5902c1034200100e0801c40119014107005200401980703440e03d040302c283c850b104040015a103401d000e0000201298100000390320510003103003051355420040c42d1a8854040140081840340e1030020107002c5020f55402c00344141102d814000356400110008074504051500010a0303d0300b8803400004068010503810300891140068400800e03041d14844220b01400f01e0140003d044480c0070000301719160f0269005015924001c241d20000954510540e5000e9101d803503520300d41d0f4204003a0000038006a1211003051024515003a07181c05001a0740d00000044103011400501091440d54100007403401070003155 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 226927311 1250 226926061 226926071
    0xf080c012a2409031e0e0307050906030f060702060615030603070504021c0f05091c17100e04051f0b060f090a0815150f01020d110106090603140706050c0d050913 71
    0x81340007805800070303440c052241ca40000405504a025000081100030064002c220403232030003041013811200642f0050b09805020002c0030499000c0c00004d110315025001000581090b40601140d860303410885a50b000041c418841507590200300c00080300c00494000d0b80382c1d41e09011403016003c036603c80f028901c0c9426505000840e040d04280c1c07080312400c00740c3d1624045031a20707541d46020341c03461100003618000340718641c030950004907800c1041041910b040720b4855549002a6000f1b0310280d0303140c1c0c821180c8078540d04500040c11030b8200094018040040c501010030300f0b6000b01c10f04850b150002140f0307804540c0b50244107030010030251040701c0208030381002e80550800306507040c0b5040c0401d00d95216481c01d1884816030441c3d0103030300601210285620403a88010f0082007140555250080055240c41500138040503500400320b1000c1c06414100891070840154081d206001090050710f080000c0855420360034181400c11690322200840041c00d000d4041416004051401d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 226928561 1250 226927311 226927313
    0x7030b040b030709150b0307020715300c092102040f06062d050d090318080f0106050d0c12081317010b01140406180f080c012a2409 58
    0x194010014071816070344020585516800c600c02c4c2444112108c0d800350b071101f001000308425400b81c1c070a00c01c0d82440e004245440c0c925030409031210354241c2d80000e00404900624203100741c400ca03100c500341c9082c9520700d24600041400f10394851079224131920b000401a13825501e0300d4008a00850710000c04118850b00d501025001c1a034155801038410300b10034080d20b95401034903c0107149005600d403107041401010483d006443d1a0100720100400340340c417102002e40500c0c40340098070694010700741c44441001d442c1d0840780c407a030020f4865101419020041610810943d040d24441800b1041c4003803d070074819414415130343c45100011030348100085160318502c62001c40004d190003030000e410010300440e103d4180010710035406c1c0d0304000801419001c0c014244925682c09003401c00145c1c6c40c0780c00d02000205900030601500304110040f020769100342d04590300b80c01100e2441c0c982901c50510700382c1c0310640c280204038000071240f00744200742c8403510b40c030040200350052010b40c0103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 226929811 1250 226928561 226928579
    0x80d020a110a210201061a03040c0608040b0a090807050f06070f0806090402100908100c030b0402070c0e0601090302220b0619030c120e070303080105121b120a0f1208040b07030b040b0307 82
    0x108270b8065501d20200c10000c10300c0392096512502958101000c1410307038a90008502c020045001c04480000003045200300040c014000480c0c1c9101e80d0700030b4256450703c11800340c5070401c0a2085810482041c0030003116562390ba049640060301940d0070001c0000000081c2e88561854201e0b0241d48100035000307801e0f90349908500b104007213903a01070280101ca0310511042c1d002d000801466036014003001c0c004610f0483e0f0390303940184140b4107440450b40d6500070131010f03518030701e601544484a03410281140118002d03010006801c2c1c0c0c4051506080404491000601c000c905003019218040342c00000c1c41402040080e560841f000c02c4071310042010180e0b500c54a200403000300740564000a42c610300f07814000310f14440c500140030341071044c04040c01020017040310123a02081440b00c04400340820414481032900c907841d0501c03400000d0800c0c011020113038400308204101c600070440020003800403582c002c56107007400b040010905d000030300901a0386840fa505445000700000b000070b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 226931061 1250 226929811 226929817
    0x4150806010302031002090619030f0903053c0a02070f060c15050c18030102160506011a0910230f09040b03030a17070c080d020a110a210201061a 64
    0x1200310201c17503080c010310311000305078040e20080c264400000d0122950000e242c2c22003a103220b07280d140c0010706540394031400d0120341883c04240d002610101d0070070b059036201440301c020855a0b5288281c1c540d071a400a034031910281001c1d0101c0c0c400440d1400c1944d00810130140946034030450058001e444940003001000c0504050b200703e10084d90000c10b040321807160a0240c90f46103951442d00340751440c2d010380d00710740103e03041e01f540d4200010b100c070380303107460031102d55030710035030140a41c1c2d450010b0965a0720f0050360b80d10008801003001081c0e980d1038243c208469015824007030038039660400d11010b11168007c0403420305000285086480308800e00078964284115800c000b82d203031380c0092580d41d000380c00d080030100b0361801144841c0c65002030300981c007400d58a00003442215507600c21003103403c03d07011612001d030046100700e0703100c3e006842c2c0000d05800c540100711500e0039455107011040300c1402d012103c603004080c1e0000c0c034402e40103800074210081a12404000040c2c400030340e58 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 226932311 1250 226931061 226931063
    0xb0307081603050408030610020309091e07020111090d21030b03070602031306051e040605030a051302130c030908070c030302060705040311011b020d06140c0a02030711041508060103 80
    0x641c1c1c03050402140307402845810302868101c03840034190fa48080a0006140c5034518140030740c071003800f100c01d043d41c444103514820300007130039407143c903003102c1c41501c10380034000d0880c02c2075905240c0c0320240c00c0780036015581c8442d0112007505001e00c517030514034200b83d050000881c81d0992510302c1e01126403d50442c244640040d000c175084180d03584412626405107a0800300c1030400c02004001081c8100b0141543c255901c0c2c0b0407111140360385404c0d066621990241e4003248011040001c00d1506201e40c2c3d41c40001c00120400300001030b070000e10844107604c00310074030a50b6100411000e9200350301c00101160300a403855940c1415007000e540d41e61340c0d48001c40051203444000342145100b070050750300b02c951291100c103c103040a030040d10850b00c046054a500c07440c580070301004d0380d900706452103546e0041c42c00180389609084000c414550080c00f0300c020711020444601130540c000100c0c0c815903003018a5032580c00d402c40c0014080d140c12a05142d50300f1440c0e60114032103101003485412a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 226933561 1250 226932311 226932331
    0xd0f050105130c052d1605060601030c050a081009060e060a08030a09150507081b0c04020c0a0605060a09020c0d0201180b040201120e060c091e030706050f040b030708 73
    0x107582c0c4051075000d41d0000b5042c0c1d0b0000303806002d0828880c03240c00d41c0d094421440481c504c00d0003150010a01d1640110a80c0304a10f0303144649030341840410b00000741c228000780380502c15044000e50241c01d901c05ca0810600b04035800e00059640c4003c0003108028003038510007400302c103030b541500010401040c0c4025204001d8160005010f94001040324840c004a403208014240340c00b000a0a25003004044800d00000b0480040041c403041e004007010820401c1401404071082d210901d4905451241d80c055403040250061451000071000304803035008101054075520540410f6000741ca5501034001c0da8000700b00443c0114000c00c0f08064180254001c00c015000400c4540d40c0b0117006801900b0b541028021401551042d0980c1c07402140181c000324250805208140c6003c00c12504000708840104038100d0358503156108040302001955144007010744e100c00203403030703d600e442002c0521100149007503401d84040c09950081180054280d1a46080700024102203011200d150328 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 226934811 1250 226933561 226933579
    0x813230f060f0f0105061c050f012102150f040f030c060206070903020a0302010e0f2115040510180f0305040603140702060c091201050c070b160e0d02060d0f050105 72
    0xd80314540c1080c800c041c49440b900743e59180400384602a4001e03102d4030703007440101030305c90003454403802818010409083c0c015810340c503019010352202044002c083c2000400d64050016a0302c480ea42480b40560030311040d6111f00b15a00e0b0340051045500941800100c3d10000041c0400c803c4c9402c102d841507000c0e680c0302c0c0c1d0f41c15404c81d2040180d00000354440580301041c07002d94820f01070954040c8000e000e414140407010000313182c220041b80c04848040021814002c40a070512120242c089803008200c2e0034101959916101c10703202c0030114040c1d541b1030801100e100141001004260004014040400c650400400c1d590041c0203940219090039280000160303ca43c0c002c6c030404460f8080c18554482c44540320256001001c901c0d8030201200381c40c10095801e00c0394500070756040c1d0f055503582460b0700d00715803006c00090401c02500b0118080807205600042c460300521411604600c1362079151002078103500558035501034a0b840c1c20b810342c0407881d507648858181e030412181460 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 226936061 1250 226934811 226934821
    0xb0403031106090a17091216060c050a0f0c150e0901060e0f100504090204061d010c02030607051e0f0307230d09080403060c08040311010c0813230f06 66
    0x140d6458190f452280ca80d00c10190100414480a5428009001e05100d646042d15180006018144518034864076800407002e00c1080210056040014141e609203110040e200b03480315070729080032540103000342c01e04c404004200f04560000c24090061049504d00f048440391009140352002200c01c0c0c0100046400030a400e03005603042d400e0004010903400e80e641c50f0b102030001081c645181442482014400881c400d4040c0c0041e0025144507078820305d1080b4030400b87d0710008449100036040c054075010b040c0c00344e107001c0ba006520024500701710b039035050591560100364190242e0300c40040c001080043c0803146030002140103813010b1381c80a9040c0c107906030014840b94101c07100a035601041102c10710300302c05c6070000c050660149520608040d130300d40341c4e402035440d541d5940d4002041c0324108001c050f003105004d6001c110b154001c01c03032084010005044204044c0002100b8409a0300e003d0400070f80306080c110524441d010035030b20019261a05503592141103044100e4043c501c0010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 226937311 1250 226936061 226936063
    0x403111206041b06020c06040918060f09031d0616080d0203010617060a060f0e0d05010608010207140703020f01031d070b043f050a0812010e06060909160e0306010b04030311 76
    0x1304e0010306c000c04031454107107040d14100090501d0555501c00138040d00c1441c0200f501441040000c282440011503005503500c0d000f04054441110740e0744e14400c42180d080c09446480650f5201c0c000105542804940c2c0e04044009006d0310100c031413002d0001001003111507100340b44440c85c0f040742200380b603691500b10401c40340259500400001840c046010710b4410b01c0785442d2022084043c3c45030714080400d44a450940e06150000301d110780d00022140100300c0c0e10700c1b80405500a00c009842160700b15030001e0062032920345014101074a070b4860700c040300a00c04107a0100c1c4003900891751b12603900d022400041d005441000305d194019a40c08458400b2810b40081452030804c4111564035460304400340444516025642e40c810703007000d003000400f19001481041c881031480c1526614000083c0003102006240e540604d00611440e0529200d18400030740002c00e1411289070440b00d044100d41e5981441c881e9a07240c880c0c1400000d03581c48940090013641d0181c1d544d02008440342d40c1803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 226938561 1250 226937311 226937323
    0x30d0c0f08150a080703122d0e040609020703120c0c170a090b12150f01021b130212040501060909050307060207030302160302010b09100b0403111206041b0602 70
    0x4041048000010502c00c1590342e0b00000b084020400d03010b46071030b154038600e00b1440d40c0007107800010558068908982022a840586044e050340c44c55101603070706400c2c00080016650350074032503805420509507445801c42c4001d02501d0000b15207811243c20014600c80c2c050340302e03941003887d000150351203601c1085511007082c0c0142c0c15810a0181d80c0040f400c0e030f80f000140c0010002c0d800408500450980020709900b03c11030740c05031070340c10b0100406001c5007030ba01c425403040054030b0028620341d07004904200c1c43c04622100c20400b45010f0b011810203291540f540c0d4a07644005810700c1d041c204414038600440c0204003c009960b01e5148140032030b08041c40c0a81150f10500401e00050714070340050051a2103441c015003042c00098828501e5900c020307048001d81d440da440c2d1900d5040400c04d280e8003d0b144a400f1010b80e1502031058014803480c00040c0c10400106480c4170300d0307200c1c18400d80ca4200300008031519451700d42405003602c0e203001d004030301b21404218000340d190300c00610 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 226939811 1250 226938561 226938587
    0x1b1314040b0105040e0c12010e0102160506060907120216120f080a05101707081c110d0905010e04060e04060e1203060915030f0f010c09050910150210020705030d0c 72
    0xc29400e006c04040045001284401c000f043d901c0b013a001c0ca00310f000703002419203180294015012604541790041c200070000308041e000e0031010040001306a030200b00c4074007600403c100140d490300b00400210740624841c502810889082003400038181d4081c0702c52110315407a43c0c5407291601c6080806090b50b0080e03c41040e42c000d41030061100c00a0035084903021504c52040341c03a9550349101c40390811550740908004e0390004002201c440d908403200c0301c00040c904019007640780c0102d00151203c00540601c904001415407055010307101e80e0320041c00b03429400740d05419864030780f0f0040e000d0f0104100c02d00a6000c1c05e4000f0740f41c5626441640e0082400412400465817404d20040f8031060208103280d1500c01d03000c090348031070350900115420401c0b8074008200c08415081c0a08111015403090713004d10601e504000f56000041d80c80015944d41d102252418980d01008a02c0c3c0015400c0c000c9115200182c2002040380000c000c1c00b601d800540107225201341c011056800103100c242c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 226941061 1250 226939811 226939813
    0x7060315031112010e0303070e04022d040905011202010315033f02101508030904020a02120d0c03140c03040609020a080f06091501081b1314040b0105040e 68
    0x420720000e190039980450440010784001000c01c2d05590a6080d902c1003030040701560000024045841e071b11a01003001c17040103036015480c245040c400501002140160078540c8101e0b464240c200301000d00c12a4010301c0007120510181d6144c0703040381035050100404a01080c0f81c402361550800c4028884002c40b6002008400d440d0108481840d4106118a965240200f0f50103032440a4407802000c0d81e20b2500c076401000003449102074a02160b06007148050400b502440801100100004407168228195405a103840c0d52040c141c0c0307404040081c0740e1240001052b544560000c0d6409050f0052890358188940e84042c810340b8040a000e851000c0d0042c0c0400c0014040340c0d950b0421034000c0d1024040721030b001c2c1d031021000e062003092402000540c1106050200d108020424405c803011154a40109549040110b41d030710042049180e01c4034900c2c91600c04550754400c18103d40701c00e841403d108018000000002c00c02046a08031004117010300082000d0500d80700d120035144100c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 226942311 1250 226941061 226941101
    0xc0d08090c03150f04030e0d0f0b09010e030406030b0d020a030f0b0a1803030902030c040614031e0303270706050415020f0c0618130504021c0317040f0b090c0102070603 74
    0x72410f2030b604c490080040e0148101c0580d03909240d12803040034140103008412a40710038a10f032a0404c52410040e02c01c071003a0381010083c3c500c41c03c01108640c00c41f00c41c2d060004080c05d1600118102c10b860000c06503100d00da8140000501100c03140c141e01140c0f10300100c80c0aa40c410701c0c50400c44030b00400c1c80800c1840204c1000000c1d000740d00160301c1c5030008084584903140c800000f01996104d410620302440d100c0101e400034201000034407080450031840908c4081c040180076130300d01004040080b500b065402a03011064100c1102011182010503102c3e00d41e280e14001d0a60340c014451181500c01101011300d1440c0b020508012806032070010f85500084030040060541014003201103080b0389030b2415103d952038011a5040010412020900b440d250040001e61900e40e112907149624400c6190002588501c0c50000520140b1403503010752110305220244803158240109081d0355201400741c8401c0c00655183c103698242d086541140c2c1b1030030203e0607103181e50302030904030440f1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 226943561 1250 226942311 226942321
    0x1219060f032405150f010207030519080d0204060302072102062e0f170303151003060e1504060501090639031706010504030203190204020c0d08090c0315 67
    0xb45500034901207150750304100401000e01d95004955040d00d10314410050541c1c01c00301403c007254000d1000c1e0b000d002900340680303541c0312141c46036120310200c0681d00304003101c0f604105245003035031044518810215112500d4040140007507100b804185c0c2e0300103c588c84072407482ca4407510040c0c05c89440d4003510254413002c840305110340c14958910440b4001e40350144d16141d884008000829402e485c2103102841c00c03000d2400c00d00d046450b070710180c108000704080c003001c2d1001194170100580c2c083d000d06003541400c80061000350400c4000c1c940b61000d00c111034128240300a64140112802c200041d0744400540310f40c4d20a20611010429010312039440210400c0c24a400402c0b558400e2075a54011030100da0440c0e0012007100407a06c0003028441001b03000004a6100800b0f0030058503007820b5800090365401c045070034103007011074006007508544494045d991081000001c8400c1c1000340000078003c2842258441520301c030b003004102e41e500d00011801c55100541d004a42d064a82d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 226944811 1250 226943561 226943573
    0x6030108031e160503090a080313180b04090b060406060801061b170a0207060e01020a1509030e09100303021009020d02010f0509090a021c1416141219060f03 69
    0x308151000e901d07038207011014491242e040010003c2d445038000d0f50f07450006d001000307010812900b1280c0c09900610000100d030074940441c2041e29011021000c0c3d800054010348044e08422440c0e54000d0b09000c3c8203810404036890315801104100c6080c01119292030046034010030911440c00007501c00d5035a40b107100e07507801444040e14014168401e80f60044e0003107036002d520070304940d0010ba1180c0c03c10002142c0c030980c020020b8500340302810300348003a604e0307210380b2503031088081c60040d40d901026010180120088107030401c019040039401d1414840030f030b42c440032612007a405030003904e0700c0d680110014411004c0d05640140500480c010070b400448100000418110501c0700421000c2c49603503d06881c00d1090100c14005652180c03000c180c240b4803840490084c607014149095031601e226021901507201c203002030881c078241e000500440d54940742590340c00d11890300054082070102120313001c2d031040c0c3e00a983c4207012030f00031016801b01e8203a4419003000c182403000600000d98 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 226946061 1250 226944811 226944847
    0xe0313052e051b03070f050708011803051b2a030105130b2a280c1e06140601080106050c03030a020918180601090908030c0c070e0c180603010803 64
    0x1288a03200003c00748100081d403940d803200701c043e03840680f62111034041040811500340540302d190001d0140c1010740991101000080000a0501c0000300386201c2220290074008071003a090400c0f1505158441d51005040000743e200120540c0c2c8985514a5030405001d418083d18043c000124084140e49442c041c1d140003403c030041c3c5078074001040103c50301e41004400340b003080a04141c1d480707020003940c2003070700d03220783c8400000d4000d09841600c0c190009985200b49400040040161030110300b060010100ca40c0b00a041900d031440c800c00103511003012600c1201c00b030321401d18a0b40c036078205030750500414070064116801040020429107807078010323100d03034200034000c81010329520f00005802e5104551500081600900255541004000e441c0c01404078000030000485075072914601303448010000c2c064028005810222058104181802030408040743e024a05051103070f90348941c020070801d9000c3c50034101c6c601d0702c0d280c28012039049070700302c000441c640001b500310030324032031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 226947311 1250 226946061 226946077
    0x10209061b07030c0605040905010509070c0303331e15050a0309060905010e0d030b06070308090f0a050f060115120513020406090606140a09050105030a0e0313052e05 73
    0x101603014004006042d140c07113a40a000c19403503d40d125814041120b04460b4141d000e184664130440520540f645c00828040c030785a010326000c07843e00c403c2e112580035a2a0951540068021207403aa505079000d0041071094941c00000406004c614010440303d9072424000d030a00700600d18407481e1ba50740111700070308151001d400c1c0420184155192801254400042691547d440d90600c4003201024040380405190350b0604200c1104504c0209e42c95000e101001802c0c860769401103440754900300440260f6142d1102265440c6e4198500680c94140020700c16506100e143c0c000304001c0610344004021104590381d4040707060319911030340003600d000f62400342c0148100c28900c0246c1c442d4003610014100e07440011580914048004141038201c1100b0744400300140b100012407175105100342d0449000f460000d4803070311504402d00050120303011800c01413000148490204000c10000c9040307038070444810351040e05002099001c84241d074800c001710498802c00480b80b50249000e45004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 226948561 1250 226947311 226947313
    0x11060c2704020706270b0615040e0c0c06010b0c0d1b02031519061a1c02030708040c0e0f0106050c03071a01030606050303040b0d02030c070614010512010209061b 71
    0x1460103100030408982c000001a203481d0745481d007903508100d000560560034440790404405280650721a101d0081028101c648148000c540c0c03071915490442c141c40c080c0684501081d01410a0032010704a41d0044003200c81e01d0240100001d4400340c14000d5449000da20300c0a0020180000303002c95503100510049103d41c0072080c01d080c09070301c0c03c00c41c1fa0003000f08455400385074140804851020b440055076000d46906102c41402844071070a843c0281c16011012251034002c040d00250040070709444104c182c1d4404401c000c0780590058845c0d005901503120100b203a9120079542c6110f000450321212102480780041148911940080c48921001e07070989040544503a038020020748070004680020320640c00500c00c0c054544520002450210011071900389030000000301801845400d0880a5000c0006181d140b0704000f11003d43e588110704000b20903444115074100c5c1828004d5034000d100100d4600c1e070701032051084035515040200050705000c0661078004031411540c40352951 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 226949811 1250 226948561 226948627
    0x30c03160c08030c0a0609141606081303090509060d020d0602040e010e0705090d0816050309090a020c21160f060f020315090402030a08040608070f0318060b0411030106030c11060c 79
    0x16500049c00409051140e0064410a107440c2c10002494031030007400c1425648840441200081d800540c0b280491f041500e0f0313403c07603903518000940300d040300344d001940265001c0201d100300700040e4010404c0e94031400300203851b640c8078042c0034441e240c21641c6401098040100255070328104260822030352240c6106403500d0080020040c007e442410200c0741c5500c04541c61801780340078050954410f580000442c1000b5143c0c0d58030b0303610300102d040e00150a002801c0060b00e01002000c42e40f10000400f100304840703000d480e00c65081150108140c030700603d442c10108009845000301c0e4080e00440038171550941e0804208517826601400883e4148500c0200d50006000d04025000801083d12544485d2500b01d41c0500f80d41c10b8100c0b071000301890103100c200c00b01045809118140e8004100040c0c982440300400d00504040d402841050800b0000281141c0d05802c01c3c4003403a816076422000d8400b103203c4550740c003c10b54285c40100c074240901c401d10305d070081c2e12107260300718540c039092 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 226951061 1250 226949811 226949843
    0x7210f0203120912191401061a0a02010c09141002030c060702060106020f01020304051e01240504061409010b0307020313030308011d0609040303020c030c03160c08030c0a0609 77
    0x840c2c50000ca802c025001e5001c100c00711689001c02c0300e20308070340100c0e0141003002c401a141036500002c280f0000c00b4081480d000481d15602540010094581c98190500744a40e810704600d294019244010056087c00007400f2114410680d41c012120820302021100e003484040101010f0f000c0d10a2045200074065696004010840d02c0d01035801d9402415065040000013424190300c101100e000380c1c01042440009500000c9000c4814860501003401044580310140034000d2003420b07914101c44c1d4112286090120352b2102e0807a40c04840801c0450340c0c551182070026912441294003500344001040a11900801194041500c6c41502d01e402544040f448280c1070981041c2c6c0001d0801c40140b043c0e01501c41e02ca0880284920b82034a580f410400052130b14100400090415801040d43c907200c0b8030030010354090100b89815a62107205013a560705800640300f0051b40c1844078100d0006001401000f200c0f8a0070307140c8060b007188511a00da11000c3c0140840844001e0820501c000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 226952311 1250 226951061 226951063
    0x7140301030f030215040f110f03150f1003171e0a020709142214070801021315120b1816030b010806011209060f0e0f0105010807210f0203 61
    0x14081d42c40b0305940900455141002407800050a0400900c143c0c45c100b440040740b2100c2c4201d04847d801683e1006c204480404540070fa13818070042d0b9018070a03405041e071202c1c00c0c41e107000e02c543d404010581e20765848102c1c1c4d0a03107001912002e401000e549011074062100307600100f082c80b6501080d0041c180709a943d065a6038842c407041d10060b009040c00b444018000c0c044c3c01800b0318400d8040a82d402c0a0107000002e07100002c0313108014082c1c00c400340c00c01c00c2c0c203412110f649e030850050b21041507482a00d117000c0e60045c25a80c4240d0614500451407015001e0700d04182c540550340c4200c00c070301c99900b280041140740c441030792000c0507a89062810740da100038a4843e4440610f0305402c00c01d5a1005410780341c90140050611542c80d00b000b1082e42e02c0b1135901001071082102284164041c20520010b0041c421900240e0f401e024a02032070f9030f00065030758181c070000f0707008222980e0b941440b1911654035010750010450002c01400400e500300d400e072070000d80544850091460290300003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 226953561 1250 226952311 226952317
    0x6040b06030c01050d20120a060605031e0405100f09020a1509050907020c0a060c03080a1406060708210105010f0201050c030402010509030c0a0303030b0f060405030309040e1f090c06030c09030b0714 87
    0x600c071f060b103e9030b0420900d2546030103000d004242a007001400e500b030100c40d0803002040d641e20a000c003440340b0001014840208400420300744046410004090790310100130181010100c164002d1400000018158811100c0038241c030351595a608003140c180401c10110f0403000c3d003103004501c100c00244a103030b55802003000003071401d901d4180120040e86400303021414018071102840d03107019912282c00c1101503250307902000c2291080c1d92100c1a1415074200d006500881010301c0e90079808040c0e000714200c415050302c50980f2451440501c0c15030407030988000301c413140008030f0140003090041d400750000d080740741c1005056071840c0103e507020486a050940c400e600090702c0342c2c460503590510704028091900b054411518040c10000441ea80c0d01ca20300c501d6000300d81c1c072900020001030038003032240210030710300c60780d600d080d1000007141c05800da050068a60180c840c0c0b00140c114000e1150b40040d5460b52a62207032070f03146468490211100030800002e02070b400e41485005001e00b401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 226954811 1250 226953561 226953577
    0x604061107032001080606070308060f061b0a0605060a030c1512020d05070e040903081302030309030d050703090e090d0809030d02040f091a010c060b0303041706040b06030c01050d20 80
    0x2100c4403c040f041c000601c0c0c0341003d400702c0e0040808112440c0402d41c007290841e841401510705142c454131b01000b02c0d00300e10403801c0d8807640c07070f080c0704010b0350b14040442c0c40f039540790061070240416254102007110780c541c1c130f100041c411146580104550b54a4000006411105041c001ca00742d4602e5104410380e8414030204507001d80ea032040100d00c41e000744902d4252101075400700011a81139401414404001d428081c800301d0f0882076401b15076042080b0b503203210000e4144c1d4200c282801c0c0c05001c0f50010801180462000c0f040410080c08000019200300c98100042520070200b000581e81420060030034075040c00100031010019030b85000070801008141c4580c0e842e64030340240c1034102c0b040f91000c000c003c5007482800140d0b81e402500882d4150304507100041079448040002e00c2d42c8155442031440c004244408e040501010034054031490003011480d80c00c0e6034410815072954070413000c4601290342400001009901c41e8080c0d00c0103044203072448020102e02c205d1206a03084413031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 226956061 1250 226954811 226954853
    0x20f040e1008010e1e01060b0708070c0e040b0408072604030b10121502040e0f0f1b03130507050a0801051b070302070b03040201120906020a031a060406110703 70
    0x18071810036192268400180362900003081840900007201c0e031158a2500c1200209030941c040b6180350380d0030340c0114002c1510b050720558542007480e06002d243c000d8042941c4c01d81c000000007658414018000b4412640250b06050756a510340c0e0720840b0707410100007600d644411442c1c60340d0210060790001c280310914000e040e1142e1452511041740300009242d4050100740040401c4002c0a0100300784450740c0c40224140b01100c2d8170111402405960311041c507150307a000901901d158148001c138041c4180044010840d43c2c0c103044500310225403002d0540c054010030008003074484200c64050000d10590540e812903550308001091600160090380e120b954910500104044410100c2c1c0050602e00b03280d030400001d610042e444003218441c814207040300100040031607110340c00c100002c81e804030f8100b105152904020000f901f00c407040030042440c00c07010041c00d400c0c0d0003a00301203502c0206034500c2e0500f094000c030754401c0c1c3c60140250034030400501100107104100381d03400002100b4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 226957311 1250 226956061 226956089
    0x90507030b060f06070507060c0312050c1306030903090302010e1305040b07090f0303021009080d0207030216050402090d1419061b0c0807060c091d040203010f060e01060c0204020f04 80
    0x2c410000401c1540b6a014850f52080080c0400900042011800c548503418201c580302c07038504003a14007020392010a00001d148c4000c0041901e0440040c00c40003e0364103403212281e803140301c203504071342100a01502084c0120750420041d846020202c80a2001801c083c07487d09010a04105980040d5400c5801e01d1582c0b08001c0d00e01d900211032401082030010580420786162000703034440100c0d00045003640d441c0d00c2c40c003061110260444075a0291b2807030440d6a6100b904000b5290220340110f0186c640c4646000683d03403070240240e5021541c0281081c03400c0c0c407190b03240605450781c0d5041e0103143c060001d10700502031a0329180c40e1a80e0248401041c3d00318040000901407140546000610141085d00303004103854000743c5001030b0b4000e4002607000700c071074019251036045034401c1611014102d01c058051844646250043d032080d402840022000040c0070240c602500400045000b882c004002c00740c403425081a8040c00644014a8001800c40051143d07110707410400c4006041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 226958561 1250 226957311 226957321
    0x4020c070806190504030512090a020a0315060b03060f04150302060f1305010f0c060902030f0d050c0c0d0809131e020408061e060d080408060106021f0209030718090507030b 76
    0x400f0345100c80c40c0344035200b0401490103a802501d140030395900140507a21041c0000c400841c100503038034410360000c04880445076a4a8580e040710b00c1000c41c10540380c20604005403032207410069078002d0900605d0f00f2101c6550400780300c010a10b140b0003022002c3d4107070b80000543c940d0345c000d0001c0d985500c40141d50b4070070400d100240c0511a44a80d04001451145802495014583e05680c079800380700801d06003001d000113460700341d10146088079401507003124038a20390013400501c0041040b42c02c0d45c1c1403200c05020804450704d80d0002614070311003040145101e240094164003926003140d00015001d5000031440c004040c05410380b1030480e800078051010300d070300700207140c1d20840d080050728103140d510090034500d102c0680014001c410f0854100c0810044106032405440761504030b46556940c2d0300000d5660250b0400c515030300c5070b400043c2141c03401c180200d40760000080c7c0200710b07070b528041c001950706079030031092200580e4800000340091018044440158000c9071480340305d0800c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 226959811 1250 226958561 226958581
    0xb010e090d02060702060f1e01060239040c05040b030a14090a1112010b040212010e0f0c07110112090b0a0c091a0a030e0f01151703090f04020c070806 66
    0x80704104001e5500120810081d5540010b0056000d20303001a00d0740c80341c507020f0000035051400c03181c01108810910000c5240e940c009940da011451900803070090504a03030070a925070003142c5815221120070325021419041c00d401c01d515900c203624000340350541c1c0d406182c2e01038200b03440a03c6000d80f21245d001600040014058210f00c044001e030030300050030f0303a80781001c49001a4580c015000c0c640c0712010700e502940141407440e0301034415035455880c8802500350344005d004510440309d80c1000b26540e0030407032030200e22030123070101c03030314a0000300e03480e031b2000c6e00b0201000d11704002c404042c040b1034449600034240501d100700c030003d00f1405c0c11013030001692000000f40c0200300020900700840282c2c0160f16080c0c50a40419554600452000301c000c0c5c240c1c42ea0390380316841805a12041000154010300e02a0119440c8030361107a190400503c0da0449180b150725154414440c0400b5460b00c9034641d2000f031402030005203001142d894513801e24506a1240005030064401c0111080e2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 226961061 1250 226959811 226959823
    0x601030809030d03050f0a090302010b0307090b120c0102030f0304051204170105010603050c0d050604020d060b0307080106051612020a120e03010e150106081819031b1707030203070b010e09 83
    0xb07404d00341440103251505141c0e903005001070086c968180c44041c007000740350003940310124108010f400d50310500d41380c0310b81c08060b100c007600c501c0c0201c41542e900d1080c0000810348180c0c158050740a1803070300d82031024180d540d4002400903981800340e01e12081e41e48801100510052100300d04402c01c1260232103c0340d003101c0c0140d110005043c00c0204100e0400848821140d040300051000144c58940d400881c2c024090000c40310705051802c2d00106418858002640c4034a1250f0307640c000d1a030321424125003502031407000640460501c400e400015107500120804800d003031044440381d44454468289060000741c1403800300700c1440c264015400c0038000c5980c1d801c0002e0003051005030603820035014840510a0364100400e0402060090f84036410355540c4280c3d42c0c00b154100708040c649100c044134100022004a48455880101500580702016100d5088141d1407260b9881302d0702c80c0c80a80c0107500480450000b08644400038405142c0c00d8046c0040400111041c0380544469107418 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 226962311 1250 226961061 226961083
    0x3020a0e0a18111309020a050d03050f04090209120a2607021005091207080a060c021002070c09054b0a06030308010b0f04121104050442020307020708060103080903 72
    0x317418070220030056182c41148508413041070700c40c844209164203088420380180c42e0a140e04950024000400031442e8000c0c0c80614022901138802e41c1508a10655441e00b00130000c0050801030103800754203102e10f441d200c1da021902c4813146450f5460b40025200511111884081440031445141c1810b01003000380da410041401054002c0c10407800940d9250f50400c01000a0b03181d8100800207442030140041028007020103540b5084076140100b1400c00501581c5440c502d04030014482209000045084800c00c420202c01043d42e03015180c2e1072009031310360301617618840407652014140b9409841c802c1c00c1640c00069603504502d0018460b40040e808641050742c10b100d030000c10f5194004076411a0300d0303110034580c00748052070a9030550a1045596501c00c2ca01030401c4107210068031864040140600340c840074549000c0000d1200112940d0200f600c9614000d05100070311030307030003940c120915004440d240303651500d42c1171804800342c1086442c201c2c00b01780e20140d0b05013080104505 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 226963561 1250 226962311 226962349
    0x12030906050c040303050d150510030501030501050a0603021e0301020417060f090f060f1003080a080601020d1b0807060e010903090e060901150804060908040f050307090603020a0e0a1811 82
    0x4185136413002800c901070b000d05d010640d50740e6218040d40b100246900001828090490240c0c10381c0600042c000b00b031b0034803007074500d035007040001100f51307000d80b01c3e0f403041da03500504810f00c1c41c0a01ca100d2142110501000d44c040d90308002c04243c800d191400988c40350044002007480b440c1868503924060400f8090540303903409020952260540803c0059208803d111400c1e000ea07203800c02d090f210704166101500c00d040c00161408503640c0403452602c905001c1e0220b0b101c1e4008204119000d00b0030060312a40c80c2852001480060300100c010800180500404184580000c4041d800c640f8182c40880200c2c0c0c1d01c2900b0042c030504420056444401215807041940c035190140341d2100341c40e26100100802e44002800300304d282c0d444a60b4042d0001052519143c4840a07030b07055903201d00a4601c40c1c800c501001901c0f205501514081d80c0d40074187c02c50369450030f55000c29288001d00320541280c0c4804286041514540b48071b00d030240500c2d9100c01c4e0640c040180b120b1003400ca402c0441c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 226964811 1250 226963561 226963567
    0x1a0406050901030206071e0c0303080f060102030307270617070e0a0611010e0601060801050a08030c1c09080607020a0204050108150403120f090503040503250302010c0201050712030906050c 83
    0xc26590450264116a01611100d545160618081a004c4980d80c1800c00c503002c0802140e00340039001010a0503603100c2d44070803401e5111800c81802c1407600303d61490059008100141c003491040042511203020482c8100d0759150480c944080000f081c3c001400258003124000052162102c003d60064580c2c2400c2090070710b800c0101d48c90104078041e03030003841119006508490000d50048109000103002d03036803696141c480041c80c403030302841034900c0fa81c004140882c4540b03010044849401580c001071880801481212101a5805401c04117002c000c1100080036107050000e03910440a5034040c1c08042e1051041000329441a0441c900a0b032020030842c450904620005401c1a0141040c1501d281e1210512000e010700c2035448910300c0c10308108600b041000800303002500c208509844510031701d13070f2044545022824a0082d071a0b5584000c0001d075019040100289006242261070406103807602c900000e81540d100001a41c0c9030a81c0341480301c03a1086642041e031641020386 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 226966061 1250 226964811 226964819
    0x9160201140903040b1c09050a0b01081b04151a0408010c030c080604090c05030f0a1203020702180603030f030c19030c14131a031f06053a1a0406 64
    0x150741d0244c0d0040320303a02d0000264000820851b4802090040480c3d8020720003040c2d0391510380d4070b80a45030070071514688910b002103010300000c20702c1d0030007400341d008090181d5192400c00026120040060031204068100869078251405c200c4900c5250015120756a83c030b0000120b08484551032441d082518004642c0303c3c4c590b0020403da00410115404070b18000203090800b4200051341c07107541c0c54030400400d41038012010420064150196201c228480c80004e001c0e801e80c03180080081d13008501c0c0c0c0c41403036114081c0c0d2000da04034801804490030701f01c229680034956030080c3c40d900f0740407030040340714540600b0050340020900900d10b0b05000348801d4a50141081e01e16410b88103140e480402c00c4034203052150072540052050041001c80d440c10b41800344070755807058400c4117502039000d040034645c01232002100d044880c581e880504d80002c4091001c00701d80740c51004010000c440b424140d00b1041c4900745460f05050b080005080840540f00b0b0b0107030405400300303038066414010104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 226967311 1250 226966061 226966063
    0xf02120306010906080912130801150e0708090a1208011502070e01051c0f110109150e040506060706090b0126030304110a03060f051501030b0f0103020c0c091602011409 74
    0xc3c044841d1403c0002980e00c502d20300c2400c01d0384045416480f44030104041048803114040c3c0c03821102850020011014a030f41e403040440703075600070420304a540c1d40104007520710030b05030302d584640c45009444200009136034114042d105a80d4141c0060488001408008500c0c1e001c0903560449000400c0b06510300305902006500500c1803506c01d082500700d10010090544e0507001c0254400300000c1d02e58894034045880c201400b13425070009032200c0f40412072544428071060031801035110300450385152400c0002500c1c2c020401ca030840310a0040d01e001030264040d10b04a5841001d43c0e1120790f04201400f80740f02c070b500d429086880001c295a40c07000e00040704513a08941c120880c101d903c007041011903040d000c0d51740001c7c162803620034000c1a6225540c480d83c040d07000e09000c1000d004d0311400442c2551804104254403c1d00140e1070308071980030ba4000c200c5100c01c1000c0ea4802c00e95580001d00c800c40449010b401c41e0301d40300b0f501640c2da6082c13042015121007000c143d01c290604e602c0d42 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 226968561 1250 226967311 226967327
    0x14150403080f0a1d0a05040c14120f09160302040c050405030303090f1621080408100c030605010c02060306040509100207080d050105010c08040308031f09090203060603060106120203060607060c0f0212030601 91
    0x4031f004655806030708100510441c0403444019541e0b20940d503c400a0000b400d190364111031445a101d04140803500300c61001c02c60545041003a0300e0f2200b07440c215000c1000410111b4988011f01004000004e45e546050020351b205040d0a4003610b0242c030079401e42420190514459484490300c0c1c2002e201244030803028043c48560903940c0d03900c4051628100b0403910494102c12664410050003a1a10b036142e0440070040c18140c0c3c0c280460341d6034000645034400c0c042e400a40c802000d200081060a013548070703540c4030203054211002000046194022a80300150a480200001480841c05a4103000359801040280782c0000050190b80354452503008501000385003c0c0700001180544680c0ac0a01e0b540c0c011101500340c8241e5a140240b0040480d42412402030041d180014035a16002c108a8100c0d402d0340c6560700302003090450000298002000c02d90b0100c014810b08010410910401800d080c0e96240c0400240e248640070740b91201c05541c0f0248450104100089a6400444 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 226969811 1250 226968561 226968569
    0x615050d060e0313030506010611011512022d011d0607170705070f17010c02030d0f0f141902030c0a110a2109080714150403080f0a1d0a 60
    0x904140c42c0b0400034154441c1c030604124514011002106111011442070304130740c01d07511032121030f0254844550989072104280005007070740d043c0800034a95910300c02d07040f43e480203014a9007065031003035440c0c9a8800d4000844500d1090468000355604403038400e00e1000c1c99048000ca5544040008010b48074074040104070021003000322180d00b502d0b200703642c00b8a9008090354000303500c82c925145100303410310411044c0e50342800c0e480c184071818440c40700c00192a502441c03a004410400c0310140c0181001003681c00d90341c82c3c2011900b100d5201e11441d00c0c2d40000d102083c1e0800c0050b0f2a80b0403240e040c05040240b0402c01c1c001480420f81c22951b8511650400e840720004080e00315080c1202a640a820b040c143e10910007000c0d048a441680d0303681d00c2e242c03108420f0329200703110b43d03c40b6140200401e03000d5691841060303281001a000308040e420100914040e1a580d031a002da030004400c00102d541c000c40d1528541d0303008413605005000140c0d6904000d03400900003607060004d485 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 226971061 1250 226969811 226969823
    0x20010e010c0c0b04081e0301090b1302190807021f0209030705060309030421140d03051003020105030a20040303030b09010506070330020a080609091f020306010e0d0501090615050d 79
    0x40d817820700745448030b1140303a603e4000d0320746e6102d6a6440c10300d0081c100c000d00d1503204140d0048600c0c441c01c0c80d8030980311192443c0b8002c6510000b60780d400d4036a010060402c3c0203511a44e0070105445c45189025030703982c4c58840016031223803c404141454201c2903001b4512811041c420098460000000e6808071050b2401d04c414800f034404500010305044000501100c0d080b0503801001c1c04001044208141349650402692b03951100e050081d0802c0e000090016808001048241c240b0b86c01c038103c001c1414580142c140b41c80344080559901a07401100420b44800c891802c901c1d0030401e11b8010101a9622840e103552640e004007070148180219071040c1c240a8a03481340c10401903403802c0d40400c4841156a10390903103000c4d1030b5445c12249907101d5242c50000420700000420502c203061420003001c001d00240041c408040e40008118604000000704405802d81c0e5403401c0840f05070050f00001218541e80c06d1250a50350445a080d01d41450350b40b04000300c2c0c51721460078813500e030400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 226972311 1250 226971061 226971067
    0x60507051c0e06030c1c0b0d140c041b090801060b07080a09090501060504030204051006082e06032304020f10050f030f0105100c0309120320010e010c0c0b0408 70
    0x1002d4072200104081150401c00110400c50320036400b8000303011910349000e400c14070041c0301d000c030070942d44841040b03a04074429040800c002000c08011101402e2a001556240c450080204007141e540749202c04042800801d154960307504a01c0b0355019142400c0240545410090300c17081a104090000741030700c0001440354401417250b491a009081d070f40c4000e20507969950320041c22a002400143e1050303240074049040e41c120340c20960b040f103810b6264a84541d4412891444050300c840100c2801041c0c072445010340701e420b130005000350582c0e8400086602011f0a149140c117200707511074101900b03c2060101513500c1e48807000c4071860486520b40b10103004607040310b1500448000c1d40e0140d01c080240302c0d10002c00041c00341a2403007540c60fa4204021a00121000c410302c4070003a0100f40f0a00c03081c842c40400543c030425160080c00d002c0c1400050140c0009034a80070b445422007a551040d804030112001e014805800840385003c5400703078a40e85500c00103000c003600040c4152400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 226973561 1250 226972311 226972363
    0x20712060e151e19050402060d09060c030e0f1f0b0904061b050a08130206070503070b04020a0503030408030f0d060506070c060206130b15061b1606050705 68
    0x5a040301c44401c40745001d80342d01c80b4500c1824501ca11003500c050058041410501080405000b0324600c60b07010761600003109031408a00c1c0e40141800360060780c100e9030400142e4400002405170443c0356100340c0c80015001c0c400c0d9001002c035043c00d0504403550300215240c000000740042d0403030035442c10500400420b1911000c1a0041144180d915004400700003000107100c195400f03100c06a403000d29a130783c0340800303510849507882550305e90400b058000c1c0c04564508910b0003c040002d101400d1145004001c0d2606440c54028040407501c0360520b400b04000c60515005d41c4000b001e041d4011411b0500b0800100d80300e008485500400d0040800c00100d41b0060b600040014a00274000307941c0c50601b81040444405c20f40509005441444042461024104801e80402d07401040c0101076840f280c002c2e0f40d06862004446034024028400c403905c83c1c0110000100b002d4401005100c070841904071240c03101c2d4a03611041c18007600744095000700f10045540c05090302c0d440030001845043d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 226974811 1250 226973561 226973573
    0x30a030f09171006060503061c080f0304080304060f020405060d020915070813080703030f0f09180207061107030c03082211011d0f060d140901060321020712 69
    0x580e41c00801001849a08042c1032400851020350021000c0410700c501c548480e8151001d04c0151001900842c541d21a07403035003481c1e180400b4030b00d4400c01540385041c0104000c40410741003610180e030880400400e01003000a28800c010090b200400190300b07040c586400515240511441400e006800141c100110796130105a2810002e800c821117460f010a800c01c91200e822103160881881c00c51030003c03ea51b840054403a08880d45542c3d8101001348449080704c1c210303034800f0b0050034003d4034100829064400c8480044896202e500141c031128103003403540c240d030004098201d4030b0f0010811480843d0f4082c1c18910001e400d400d0030006610394550320241c218007490383c517200601c00a80394040048480040817181000d80c3c442e50304480a5114102c9090b0701c2ca0706591009400c010170181d030408901818441d00c503228000b800c2d2800701c900044410003287e6100c4141d551300d10a004100300405800a04424060119410f41c2c407450081d41e5806940280800205c000300c0300341c10004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 226976061 1250 226974811 226974827
    0xe06060d0908161a0108100207050c2e052d0c0604030302030105180603150a06030807060606080f1e0430020f0f060f060a080723040b030a030f 63
    0x16011050030354030742c41c080320240016003c480448010340c604014034141e400380d11001e03042c2c4012101510401102c000800000c1d031000c00115032074002d0054002c2a03541c2c160301d15801c1d2440c84018a004450700100d00101c41582001101380701c024030950900440341d41c40368a030460000d5550300c940c5200c140c1c3c5078141c054000c420840303101e180c081004255241e0007542c101c6200b5a0101d4944031403042201c0400800c50f9074682541c000c0c030f81820705028902c500c41d0006034460000400944a4860341081d5004a01c00e41c2d20b00d03142c00080100c1a4072841081e84182411245a040e04003001a40490380700c0403c0041a1086e840201d41880f400d405035800d80c0d00301d06000d40003c98405da2954862404248100250040461f40c0c039081c1130200c0d0300400000314030041c0006540341c0381204d1f0750040103000550005400400850000303003c201c11005400b82c044c81c106011500d403ca442f20650002c0c9a9000f10306082c1c00b510146c1b800641612803507894207100035055805141222005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 226977311 1250 226976061 226976063
    0x6120c020f07170706091805070e1809060c0307050406121104030b06010807110a021c0215190f050403120c020303030a020403021201050f010513091704140405010e06060d09 76
    0x1c02a42c0d4000b45603410318035664030810f4288183c0300d0069403240161050380e254880c0a540303c0304d04290080601807a8000d5600c0b0809040c00003841120101040d00d40658410f141520703010403050096009080103145d42c40407000b0700b4a880c1d45040304c3d00600c0c03401903104101c00d1004072001400000125084070151021900742c003501d540e502c0c00c2c0751146200a80d1114007240503100860000e9200b100c120356440940d6000701100030315030b800d11000c014010346c1a603d1b043c06aa60314010380d255581030b21070f2100c00c004a91100030f030103100141481441e46039030600000078a8600642c3d0420300392400c59401208410380305101d050251104105454000e615010010801c101c2c80010307070207041070300e0090342d001d841040243c5c5414200c560a4034080c048041060041100703180c04204101414001a03010078020703081d6482d4170058111098143d41d441d07004c6001c0c884210440205440e1040840e020302c90f03949414100280c498014080500925002409030800916604044545 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 226978417 1106 226977311 226977313
    0xf1c06140607050f0a1b0f12060209060c120c0c0a050901030809060f04060201140a0207120311040512030a110318040b0f10020703050d050406120c020f 67
    0x79002250125035611600500300e101d503c1c00d0091850b17051041401188039a00308414042070f241c160055081501044001c000543c0d940040440c0d094212800580d244151070204009108030f600408a13841380b00900c00d10076080c03000520000c1c40d42403c0e200c030301c10842d003040524400e82c4185980b1a02840041c00414003850003040c0070320008011601c0d0602098400304550055402040581d40d550a0a00240480c2da041c0c1c0d4810031603401145400b21907070b41c01c0b00a52100c0014010540c7d03442000c94040490811280a404001c180c0c400b441075985403e6074079030140301c884000400c83c0f0440303d0548800800c0d1454060311425500c11151036205100040100e00750f0a42d200e0907041c40080c440c2c0f9568080321505407180d0207000c826066046c41d501e00030300d01c0550406c220042000304802c0da40541c800000c8920b00e0f801158206000780c0403480d14420b10f0a00c13285e = true := by decide +kernel

theorem cover : BRFrame.Cov 226798561 226978417 := by
  have h0 := BRFrame.cov_init 226798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 226798561 ≤ n) (h2 : n < 226978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
