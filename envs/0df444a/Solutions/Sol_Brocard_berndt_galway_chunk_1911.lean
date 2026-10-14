-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1911
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:07:43.713512+00:00
-- url     : https://prove2.me/submissions/80ccff14-4303-44f7-9ffb-bc5864bd81cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 343525179 ≤ n < 343705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 343526429 1250 343525179 343525207
    0x1611040908160b07090b070b0a06080f100c021b041524140735040e0a050610080a09080909070c061a0a060e0a030605090d0f0203031014030a0602 64
    0x40741d40c0300f240c4880343c0f502c8803242100c2c03130300e000c1c0500c0c00ca03007104208581c045422182115401529107001107160341e04c03112a541004003400c40a8140c0c0c2c004d00345140e8021075405045200e03005407004000018056500d0a0314402d0382c0350300d901496980384808161a80313030017250082c1413210b6114a20100e9030310448840211900740100007a14507042c1c200a1600b601180d4203140c20000ca404030070f0300303007041c02142440307580300d141d1011501c00c0101b40c81d40501c000c6d0000300205100c25946107414000603054401c0103140e14800c00000c41c24040090700030f4419500040f141000003000095850401128841c042d03520f0780c803504e10030400c40890341c00110308210501c500d50502c1410034072109400d802d00c0040302e083d40071100e482d080c0115071082c2c10480c09a41d0041c5516452030b525120b80040358019502c040050700100d181091454019201c8208000705100443c03451610040a401c080024090004005080304885440b42c0e010088103a4454001000b1507585401113a000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 343527679 1250 343526429 343526467
    0x310609110607290708060618040c0e030c03030301030201020703150b0604090b210c0f010c0602070606031406040512030702010b040e0102130515070209040f1a0106090b1611040908 79
    0x148001c8401c0d070f401803840c00c41a114000d0078140c40d0b2a0040e00d86208100607a000403c030541095803252034002680d4850050495807001ea466040f034096801c0c1c18075052034541e03149540254000c200400041c0d90004044044135000b00b040b080c02e20046500c075001e041c1130b14400ba071055001c2400b05e0303a40000c2e44450101c0070200d1301800d07001005c0c60303100c04120103d04042b0060300302c040c002c0303c14240800f07810388550301450a40c803542515580c3d8022a00081d9007a103a040d0380f964207000b0030080300030701250210f84000401503860300c0d66446a4030251403510f00007201c40400451078160003500b10603100e89000f0412700400310302d000c6d424001d4200d0820000c100c100c0c480300180a041c51244510300101c61042c0a14110454081c046072040180085a5034113203954400040386048070314900003c110400307898a94034002c0c0003860f000141d00010014642041180d190800c1542c0c01d09100381d202400c0ea40c039020280c0010000c02503c40d0142c000000040c0114002601103444 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 343528929 1250 343527679 343527713
    0x50a050106030b0a060f0306051215061c17090907120c140909060121060501030c1b0b040303110a03020301080f06060d0b06030c04020a08310609110607 67
    0x1002180e03640c003002c5050f9080d900481d03030000029103007800182c0c8100c501544071409401d0201e542a541d01c0030070840c00d000e020a0031185c00c2010482c07419044000d0594021908407460708404903144c80d8500c4414034000c00400480c041c40a003000e00c180c0c2d4082c0d070b50550b00144120501e1510300f00150019422800403a47c0f2450a00361211090050300304c03a208990884006080107504c4c0103100d40c0c282c0c0a000d140c1070200690b00200c50301010312008104000810011070503901d044009001d0754000e001050034490350170345114100001040c01c4ca0705680001203074a540c0c80390304094004080c03030b40301302003075003030014000c400190142c004504854040c0c00712072032000306c0d400084d00d9a078190358042e40904a000c400000c901658032044d004480181515843c00c0100002422a80000444404600c8000410001900584580c0c2491411103040d07005400022404010101005401080c03c0e40da40345840c28032030a00440c0480c0a03007c1c00aa582e01c800c0d0803d044864452841 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 343530179 1250 343528929 343528931
    0xb0a0806030607110706112e0f1806021803030307020706020c090403020c010f051306080106081305120f041a030609070e0303090607050f072402011a120f0d03050a 72
    0x210f2801e500c2811369001e6214080040c003819410400101d030102c0000103030a046104422035203606030603800c3e0900c8815119246041c00209a011300010745513020801c4800901d0154094029905805201c144551204d801030350f801d00c542d007021103e0b0040000343c0c0c142c8000300400c040c0507000140354042d42e00c642c080b0307034002441c8000c10519420032540140140c1100c00440130a50040484801081ca581840c900b0303d0322844925800030185d0b40304100003a07060004004a5030040986a041800d982610820720150703187d5550f61121209030f11113101c400141d4191021900d42550041e10071000c0c41d0141c040c0e020802403031908240c030005d108001003804500b440e8020001000e02e210302034041d42c01d00f448002040300c0c58200e1a0189c1d0203002e0584500b25400d000d10444002d0700c00403d02d1007654072a110382c0b141250784004001c0c150780c54100c011500c01c050f400c02c08034008084640c90000300a03407120314102401403e00398158424090198119501504018401c07000c144c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 343531429 1250 343530179 343530181
    0xc0807051c200d0807150513050a02100c0b2509120206030c3703180206090307080a08090117040b0f0405070807140310020328060b0a08060306 63
    0x62803854100688034000c00403000c1c030034110484030070030b000c0600002005020520241c4251500c1840368400c01e0101e0ba203040c40200c0024510907842502d4125880042650b00a8110354600340e4603411a103010b4030982d040700e141d00c46036210f13008490340d481d449002c80880b410902c6131341841d80080d52690403592044441c00c92424414031ba28002c0701c080c0b0341c003450080020740a0200a0f4000781616001d100708000c2c414910704110b902c6080380304516800c0c0c5414440b0b803001c5514000b00d01802040504040c2d41464010b1626440c80700c440c0c0403140c06503124042c0700081c0c41d00001e41e0000040d40201c0b0f115205008001c1c0190a0412081c2c8810b92100310919100024a00845000b0400000c078030215203610b94026905920074414000c941055494258503403400440794091048944074206080240c1418070480c101912400002c0d421418030101d240c211542c42c880180da060f00b903444100c0e52042070740004000348410b4110a83d42c0f103090358020943c03003003241c0319402845184 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 343532679 1250 343531429 343531459
    0x51e04051201320f09151602060109020415140706050106020a0b0f060105030403081005030f0a05010f0209030604030c050102130b04050301051003170a021e01091403030103030f0e010302070c080705 87
    0x102d0600c1c3c03080d25011243c10315a8407008208110040500520098400c250304602e101c6000507100d8000d291500041d0300500d601d1900038500f010580002e155280140810841c440c072001480329644410b0074011a0400140003040844c02504c2003e400c1d01c2c00c01d000003d6941d000f0505c460001c0c01403107003201c960380302810804504c5058543d20b001030800c00c00100401d20980040390442c0300c00e1160340c0032540e030b1000a860032519890204032500403c070300700304000c02403060841c10141d400c815802c2085000010783c6810b401400030b828404030b41c87c0401005030079070454010076000b140140e03d05460307141501890700280a054001c1d840d04010820301a1035041810440c5e90041505c07009001048020045400036a8140203502c01c4100c82401142c0390603000d465210120000110806035040c540c403100d00c0ca10041c103031034200b0070050021a5000744020304106941c04c0507010041d00d900101c00a12864001400c0000448000704003001e006ca54001200c03c1240e08410381405a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 343533929 1250 343532679 343532741
    0x70f060b0a060f050307031a03060408030612010501050a05010f120c020a12031529040902030907170304050405041518052112060d05150a11030403051e04051201 71
    0x100c2e0910020813418800a0483e0380b107034020184880d0621b1129417044911300110745003075020390307003100c07881c401104004a50030000c20580c51303051364000034880c80d40340c40701040284c001c50244c24108400580c121150901030340d4013030600e5903400b20030001071090300c2c0300a440e0280f21200321180d400907603213044800c0c843c1c040d00003482c850000c064201c41ca04051091411420a19289000f403006070194000000704054002880e00700360269580c5041c0d0082410409190408402403504203103041e401140003080c3e4003618070640e00025240c43d607045c280481035900c2640c102c120304040180328014100011600401e200380100c030f10400340850021f9051004408102000509001d544202200c00c0d44503500510007134441e441c8502c90351949401d2206840d00303e00010400d1003401030640840c450700740300c03001c2c4960300c43c11400d0036980204135116035a40c801341604225401000d05521204640040030003c09403142b1035180e074040c9005c2c4c00d000d114214821101e4403000002c13540 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 343535179 1250 343533929 343533947
    0x105010303020d0c03121a0604060c0611041508070903062406080112020402160506072d0e060c01141006110106060215090109081206130b0a0501030c0203070f060b0a06 74
    0x8580c40d2021442aa038070100001c104d004951818200c0c8220300382008e40703803840100040e05040d602e286050a2a04103141035601c41101e440c0c41030b05c204002c02010350307014410700c644003580c13400211075202c0c17040c00c41d0150504c0c0c002406e02d6142c00c1240c0390f403d18000407a50851100e40e41c040200744d5403141943d6251091060100c206002c040c084014545a402009081c451301984004420076841e080e2030301d07000f185c1b07450106001d001c0b40100500301480f48030700d05131402e00c114245006003800801c04480120341038018600030400b01d000c680d080d00080704001140061070bc2d1460700460b0700307009940b03520801021808055000703000070b5043c004d00d020707208141c00800e0400b5003c0b00e4044150401018102c86542c1c3c2c42e2418002031811000f000c299200c8031400d0340c9820b2900800045407801401c011200b0b241c43c40581d4a501d518002c44201c0b1400d080000d12400b40c54030680c10b41c458004010600c2045125003000c1140c5070780144007030784060b2150114940c07550401da801400c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 343536429 1250 343535179 343535183
    0x1206030a030219050a0618260901031d060f0a0b09130227070c0c211101020a020d0507060e030a0503070b0604020405030109030e090c0711121204080105010303020d0c 73
    0x3c2e50000740340c090302520b5454151090b0201c0d00840041e44070070045a004d242d91001d80b2039001c03990028000d240604545100e42c01d043c108110307001c480414068422400014145038031003d0404004450b507200c104046100070603101d2501c0c1c0341c80e00607c6410308480b490072440c07030188425643e05202c00b4140c4541e4019210341401d45454003005148201d6000355854240108002c10400b00f141045078020102a2250b0310f1091191410500c6140301d0f4104800c03003402d090b01612030000884460524032b4024072906140000000100d0421468900194100300703180b584e8000c21030001482c4e401c4a1181d501e40d1103840c000001c141c0c0300d108010001d411507100f4402440814040c0d10490380080d00184010f180c182e031400440c0c04d46c3c100b95402e0300403034089855031615041c0400c1060f80141c0300f8000310321340380256586481110501d0846401900140104490040100101c800040151803919110341d0707078407d064060079090000301c0040c007941101d580c40600664010000907 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 343537679 1250 343536429 343536433
    0x2030c060903010204081b091b1909090903170a09020918011515020615011b060204031a090f0a03080112030905060a050c060c0406020607050f040902030a021206030a0302 75
    0x91541003002040d41005a070785601d5503003000005185c410030452458000917421301c05d01442882000c02002c400020a4240980740142c142d0056142e040210354075004100c00c02d0108074503ca20032100c41c141c0e50000450300d8a401c56503c180340e0842001c00c020550b408410f83c9076501c50140a0035151a15802134002214401203901c150b140380020000b44c81d60800040c0000c11103842c58886119a8059543c0040c0030010001c0c0c1a814801c0369071050242d40c1034640510f4540000b0b100011174180c58449a000b400114104000d1303070101d4009503001040701c0f03240b41c41c07248011031140b000d4461898501c101c40303441c0032001d40441c40712011030301074541c1c80c0c00d80e180c03c501c0030600300740c40404c4040002900d40895607640d1034000c0d1121110651383c081d119181e05000703920301b0070041c00700d405042c801c0c8020400c4607800030780a94000c2280c43d115440719040c081c2032205026581001c2101400031081002030600d40d4094185070200c000c0101302500c0741e00504bd1510100c0070003600603 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 343538929 1250 343537679 343537693
    0x6050c0705060a0207051201140c0910021b010309031e02070806010905130210020f1b01030b0105030103081912090501020a03050a09020306040b130f11031c05040e0705040815060a09090203 83
    0x40c0c87d141e4410101d01140720008551840000c660340c400c11400c442c1c4a120090101c1d802c0e2190502c1d140104134002140001c0400080348800f400c0d075081588050360405455003414000c243c4210300c2c4614102c40309004400581d14481c002c1c0d100c0810740100d0b5006e100c0e04c4000144403000b4040c40f801102c0c200c0c62001042c8440d020702c4080204144071105500c180b03420b00301001000c00c403010149032401e0700d254603200d21900050503981d5030141a410400d0600c0140301141030041112111070014141c1401c16600310704c162001c180255001c1c0d512442c247c003601c240281034005141c803038920741d01007005a171881e0218003112400f483c040c4d05544104005000070b80d6072502d440e005a007801c01207c1003280d44c0e40d03080c00780641e80800c076103441003002100b407541070030400c101304413681490221484461320001001801130f482103000c0300c4001000b00306c2c41c9024400b01c1e80a0300010080e1081080d488400c005440f1080c5c454034096500a08005140e0305a4496100c1180e4014043d10b81 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 343540179 1250 343538929 343538939
    0x60712090c03150902090601030603080927010803190f0203070609061d0109021329010507151e0209060f030a0e0a030c0302010513030c0f05010609050106050c0705060a0207 76
    0x1402145801c9038640c00040010012660b0803410307600c0c0f01d03900303140400d04a4840c41801040303840606083c1c14941490418070006005c9000e50b0060201642c0324082d1102070184500c83c1c402410700700442000400002c04d20507004401407103811840014a502001107560441c0d48404030f84004006070010b00c818070000301c040d004000c40f41d0282202003895048131521284488440300c24601980d540d40000c011401c00003890307d43c501085908220030f4250b1381a0842500701c68615403050001d12080040c103078002e00a56094640124281501e5900144110010440d100340d0132401e081101c104000500d090089884002003e41380500313006800b000417040d030700041c048154494448003d052299004c00c502c0f00e2940c0280d072232040004081c140a4211344001e4603e840e0704440303000d01d5000c0f1342c101410165107507201d84503404820050905d2401420743d90000f05240d824980002411540320f00a01550034881082d500740680e10303403c1100a1040d0101c510260704040d1003000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 343541429 1250 343540179 343540181
    0x6050105030c36090703021c0206160303091e051c020d050a0c0f03020c130506090103120201150e071205090c04110f0d020703090e0411040c0215011412060712 70
    0xa100310070350034001112256010f0000180d5044410900d540e000718020000e500d0300c00d107080102c0b90828030664101d07281c4d801040d100d1069024046100410f01d61050405109030b10506103a60440449400200700d5a40c000803003100500684030380c401c04083c913100d0907408056451090560b00100300342e03000c2590903141c0785c1101c00990b041c003415021000c00314030600108594503201c3ea024001180b40d04007001508a01072180c001660b09c0c010401c48a42c456580c4203041d40e800008441030b28642c000102d014020440443c691400f000000045040344141064000c503c69103407444d140154205d24411150221a64042d0794414401800a4203042d445000b81d0b0f441c0880061500d01c50804510300c584c00807007003000055002a1b040305141d40b0001c050302510310303554040d041e400c0c0380c1c0751584000801e40000d882079540d10001c114542c002c10202d181c1408412031443c996940301021403c0c02d504200321400350f01207003030b0760441c0c10021440901c07030a104e458080c01c50a411110700 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 343542679 1250 343541429 343541479
    0x4020306011706120a08030f101202040b2d090106110a0f0816110f0607021e1f120c170f0618270d020d05130e0c0706050105030c 57
    0xd81082c4d0702c41c0e040300d5505060040750032950041c48a540d590911824009080b9001818440020001c3c0002d020001c450f05440b1031681d01160042103441602c00012520520080c4020410055142c0a40d42c85280b8020070105041290a1100784ea80c0d10002e890050181d10031041e40c0e00691032000004410020007003401c0c2c05006054203200010403020811404a901629113016260403c0c01c1e5141c07040105076a124140d43c9031b420f06405501045043c1c1c01b0384885142c01c1301460040e001c80d120040807000d05801844441000b03881018090705d203184690010a03010301302a443c001c0c05000303400001240000f941a20110343d25500038040e910009001c80f50302ca0304002031060036055007441a0302558171400122401c1c000301028140c54007a003001109a60080c0d170840384032030b40104202041182c103041980e0385100340c0506c000c21a00030340140d882040c0b072a09008200d07042e50081c20980b8400c090402045c0d884204240c0c0d0b503100b03120031941c025403000408610948005043c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 343543929 1250 343542679 343542691
    0x12030b042007061b020322030b0a021806190e06070803011a0d02211305030405120106080d030b011706031e0f01050408130f0f06050c0304120b0a0605040203060117 72
    0xf800b03d66000c50305020b62060740c692001a8004903140c0701d0312007804920b1604030087c0505041d220b01c1c554420501e00c9006088410785035000c5101000c0c4244405814000040146003e40d41c84869442c00c0d18000d90400b6800080c00c4505200d00f83e0400504440550b0b404c111440d041d43e103040300e001d00ca90004505404141d40a100702e0304000c00500141181d050b400111b103078800300c0c07031807510512030009040842d107c2c00c507924140800c0f0044100c5041e500181d8820310b403881c0900b00039003d000c40740d00c51403851041c1d1010710240d41d4560b22004c4508802d0303070768007440c00c0e503110240b0415400343c0d1340c1c0360301d40c03c204c0c900551186242c00080402d5003100a0354000302080d280076003190700850b001c0d5001c003000201c12940c2d0035003400400140007100340c60796200b410320050880200c242e020782800d000000a4660481c001001a20001c00a10a801c0ca42120601c0e01c12030701c01055507040f036501c1c20618040341a14150003500e206d030106941d000c0f00f42200d13074045c1a441d58081c003e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 343545179 1250 343543929 343543931
    0x10022505010e0f070f031b1205070e070f0806153001050d030e01030f0e0f0c030c040c020a0219081f0f020405030303040221030c060411040b090c0307030b0603010312030b04200706 79
    0x641a2403108e40c03011482d028a02501e8503510308401d402070031400820302000c0080744005112034580114050350025403d488456041501c00014007051142c6044401c0608403d158071481d070214004a284031800380c10a40c165036a15820301400c080c842c68020007007610405c01c0b02c03440d4401d42c800c0401c0e00c005040400e803404880b401a0070b01840c2101302d5101d0f0016001c030f41040c03e0403c0f480d584c0070b20694042085a5425000a4840b071b14054000e00c6210710745c86540700700c6440e1411901420700e035020b4a1101c035240c12403012160458542c08013807800d010000b0741003800b40c802e980444201601440ca0760f5210313420407035100e40000c1000401d01c034251031a25800010006800910303840f50090403103042504048600500111402e84900d0408444c00320039183c40c500381d40c10807080b2b1010381e01ca8964a60603030207462804a065000f010100c000010701c40c403511980403a04081d102080298501c80a00050b240b14402110b503d01100f41d220744110083ca0081140e9402104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 343546429 1250 343545179 343545233
    0x1305060118030b040302280609060b0a1e0519050d03020f03030a090219150c080c0d091d07050307230703050405090106050a0210022505010e0f070f03 66
    0x801c0c04140c1c0e040d0400d0350f1031200c0c0c4040000b056010003400786500074030740302c600305400c0f0451214060003001400504041e1103101400c10003615030007900407041c0040c507491207242c40390f0701074000c90b02ca40d1112994503406000012a4203006000740c020340d0407248241c070f104e030a017801c3c0092070503030000c220b0441c42460462010940c0034405580a02c4854502040000f040d0040020078808402c10b43c545030881c1d40200f00c01800078101c00305c04684c509084225600c14100b020030350044d00c159005d5401408a281030f6141e2010700030054403180250207101700c551081007504210200c0d00c0d4800300d4410030100711120701614000d0658150a001c4490b00110b0700340404140d00140c2d0110082480810b00b809185080c0c2c0c0c55070301400071890860b040001c00b00b002503840110020050742305500180690801c1b884417290100c0040200c0f40d0450b00742c1c05c0c94100c0c02010001d0465840d401442131041400301d010850750704448a1144030100d242c255225400c42100060203c00c824034104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 343547679 1250 343546429 343546457
    0xb160206040b130b070809010f02120f0705070609030c02150307020c01050c03040801180614160c021302030906090c0a0506120907050312040810181407230a0b040513050601 76
    0x13000a03482406180c1e038660b82810010105825a0300740e1400320355417801446010208503450f41080e60104500081c03041c69100d00b00192400d02c51660003800490030410298141a0000703804004940b0940d50b42942019084d0140310a000035102c500c016006003c2a0045603c60000b4002c0714070640300fa249000e54480c03911b4210350414100e41d0030f14407050b440009100640c450741b4280d9010300c0c1c209166280c0655003d0140b40052520414060400c0354002503443e441c1001800101801d0f04664904000e1041503603a2003c40342910280f14000446000382000004402117500c042c090a04103000e103100700124180080003010103105a42000480d0b80d410495501c44103490015103685a01340b003c03039030403c0340c5020700c010410704242120301100101161030b00425000840304024032101c0d0001030601e40c0c2d552042c800440155982c3c180c0c80140300c03c0328042c0e03008694a840056031880364400342e0080d03100d01c82d40f04003202001e20441240b50070040d400030051410840340340040f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 343548929 1250 343547679 343547693
    0x51303060e1203010303050a030218090406140105060c070b0f070c030f0b0114010518040e0115143c060415030e0703020a0b0711060f070b160206040b13 67
    0x5500944595855615440103104148440040c444005242c2072640d811910040e08034840c0c2050501019800580c580002801003005295400001c00702001401d282c00c02c14064201c141074010808030403000040c1c1442c00008a0b044180700e2005843d41e940703000007210085c3c0041c0f00300c0154420411410f00064070121a01000d944151503905151009081c0240348000507040405040010440c03480941e030050107658043d5140040c8082c803480c608049005420941320711a015070814680e80401000c00d1004020f542600c002c039000d1860001c20013950700b1a80710145100c02030300581e4040e4989011900340034450315107201061101ca00b02107401588541c2c0501048114902c06804040e854010001c01c404500000e241441c110f400003072000e0020302c6044d040000002c0c40300c0400c07190000c251030b84040203012a445a1003007501aa1580c0026012502c5d059607000181213160b0749000180310030040e50003000c0d036542d1651201107500029103a81401c0440080c80d0b4000340c1760f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 343550179 1250 343548929 343548967
    0x50c010905070e07090501021c030e16050f2b050a0b0f0f0a09051e07120507050102010e0a0c0510030209030a03111606050d1a120a050709020f0a03090305 68
    0x41000180b10407441c0210414240801070446801c01000302c10411a0382c0c0d0010f03c1020b154002e044a00041d64200402d5005004150111120380120007005070440b5042250f081103070408c0c2d03846512100c1c410304003c800050b000003051305007501184a2010380750944000300b030728420821940002441e8950ba021804100d45015003a03404108100b1200b601402c03481d000048058144150722896a031152602000c170118880e080d40c101782222030120800c001801801c1031840b882c20b140075810700da500e6040a0080502660801070020070f1002d002600c645800d03000314141001608040410156000c00f00d09081010340078051078115642c14480c6500301803081d141c00315206001d0491a08101c0f81c0242100c040d901c03000c0400546801004460070082c0c1c0070800142010705081c1054422001e442040c0c00414884034900c45410004041300102e025204840c0d1282d1707608003030020f91003102408500314001748180c0400e1402a089041254400e050550070000101c000c2038142c61 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 343551429 1250 343550179 343550183
    0x2010e06040e04020f060c100b01120603050606040e030307120f15061101051b07020d020319050307140303010b0f07020a210308011d060d030519090905060a0302090c070201050c0109 80
    0x803000041c8070440c9007085d01d2505481090f41c006062422400030185c44142140e9100e146036110314110744a6889491f210b0480342c5c6c080402c202c4281c5a0414030395405040f583c440c060f034500090014403e0001090301d00c01c0040c0d03541c0007800960b9038100b82c00390034082a030020007922000c00900318080d104040b0050240c69555004070560980c0307250a64101400c00d00c02001b490128946060300c03102154041501239400d00800308141c40400e03c0c00d44103100440310b1110f90715601040040100003080d4042c040c6618414038a608039901e500d0740320a01c142d00c0b00c850100800e403c40c00e02c04010749805400200401c10041d914035109556102c500070410b0841c000c11000c604060300314070824054442411960422001c01c20300f0040700202524540c4140e80c5a42c083d010180300d5011154600c03042c0a002c06444002ca401408000860048490003801c1c403001412505004820408176074006100401c151507a40d500c40e40d0740d1084405074100f0604020680c0c4008007401401c20040c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 343552679 1250 343551429 343551449
    0xf040807060f020d08010806060118120303091a071b151b0f02011107060e1207050606012007090c02011d060105040b090c0901032c0708070f030c0e0402010e0604 71
    0x8003480e0b4000b8242040031100e030091150620050041035000101540d100400703090103c071002c4080c880000c602c2503544412800075aa034116030415070b041d04200b100300e00c01d07131040340c0801500d2460301540704100d603034900240744004244040114040041e080501480618040304030344c40310b600c00e0702c03000d50f21440d4020342e07070030510759140c0c1c081d011401d8041d540c13008010200880704041602d2203020f20240c0000e0301c59502803c03410080c012218a034200700089566021203181c0305c0e8440c81d04507505800310b080e4000010686582511000d600c18407074018206250400c00100b009180f40541002150758401d4104c03040341090700c441a40500c114002e00103507142004010644000403000c82c05800a4028011010034003011394480d40003d00340403540540c50401030501d0854030645601101c04000c05400c4007070b0218580e000d45003a603066a42c40c540700c185e5410b5400091100400e0070111103000c01030b941c0c202003000d4106105240c49800c1507d1301c80011115002a0080c1c0111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 343553929 1250 343552679 343552697
    0xf0f1d0a150503061e0903090915060c0303041511030622110a1d1203040605090409081b0106170a0f0533010f06120906150b0a0216031101050f04080706 67
    0xa00c0d41103d4171684010208010361620703800a0109041c500080c0c004645140c1c1d09005480341c0c5d403054142c4a45601901c11030340c0303038a081d0429038202a1007405040050b13103014410b0342260800700c2220f2080d03101403c0203104600f043c0d004c0d000f005070000f0650000b581c1d85640c3d0746800c4a5001840e15a5460359200c0941071900c40418018030001069881115030801e41c1070352050200c1507070115102c5007011a00c0e980d022000c500904031421006104107000608003e8030760380d000000382160094002007000d141c40d41301d00000c1c08500c00003100c80754003080f2010300003441c00cc00358031424404d00681d100f000042034048071900d42c00c2034200360f1a040480c200141400d0504c010300500d40b40302c1d100805450b0000250900916103210807810b42c80300650f03024481e581c1c01280139840c0359440d00b2815552002049402e40003410b004d001030040d9002c1c014088a505526401d5a41000454005444250064500d50b100c6129114001c00900c030010748094180442801042e894071510b0340 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 343555179 1250 343553929 343553971
    0x6070b0907030501050711010e01060807060507140601150305090615062b0506120c0a09020c012004060e0105190807020a0c030f1a0907090b030111040f0f1d0a15050306 74
    0x1d43e098540701051623854402e03308052000014164216201d07070800340e681c1d90301e41c100301201d03101c00b0040503514420036000180d107242650500c01e40d24102d903010001919410b410b40e03142c08083e550f5043c60a0307084852200c61400b04020040e01d00c0201010446040000502d0742a20400c2c84040d20140c5d2079080203039505200e40040b003904200000b0746642d150031000100a0140d500a0328241030703000c1030341d00003038000750f00000031403103007020303a8070408500000689075520a0088800261420300011555402107041c0c0341003000115a1408003441c0000803281c1e04001000d21086100b900401008078462000b050080c42c010012908100c0a40c1031252024030000d5604411038900401c101c0843c002095200039106500d0011405124003030002c2d015004140640000d12030020300042c41d101c90b05140c4c03044a1600c19600c1d103180e81d409203c50303410f041c0000034086040241c001841010f00e94001c1d0100c441110403440b0460300c900100f031400000f01c54801c2c000000550001e1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 343556429 1250 343555179 343555181
    0xc13140408040f052704061d06100906030c090509031c09170f1b10022a0109030503070521010603090b0609011401051308250f0506070b090703050105071101 69
    0x40031304002d0301c100c5d805400b88203901c40303039542c41180141002684404581040304540100110514146811000c03c036400815a1142800c0d500f00c800346001d602c00150400e030302d0103100202da03003050020981c01c0c40e140000020303000040109480340400c03c58225444040404802c03940500e10001408008500d080780c210131580180c0303021860700788407491601079648112800400038000c0c0c045e0310380e0043d400501e030041d040681c50b841c900101c1c0710480c20b0144240d20500354503218600100040c1041d21310308950f0781d82006000034108000080d0000d000310010841d0107440003a4042007003040110705000a02030300000700098441031450300b48414500d2240e0044000c076440b19565241442c07075105030007074040d05414081d0105141c412602c90406440040c6600c409a802a15510603070210503070343c21241c0c503c03031042d030b80c00402c00c1c00380545a40c05440000d8491440d1803a95100d907000a040101600c2d42e901c82c4080100029078280a0749014040540b11403007503071000315040c0c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 343557679 1250 343556429 343556459
    0xf060201180b060f12030309010b031b03060c03100306020406120518030d0c030209060d05010305060a1116080903010912110a080403110102030d0903020309090f07020c1314040804 79
    0x101c0410700c020344a020420030076085800400c121006414030360444c0100304a550b030111082020301011040000c425410741101c081c241c021010350b0035001c000602700d1140100b85500c0f50305940300c400001d00c598100710096800c081c0a60b00b102c420350745ca47e230700402d0703a0098220000180e510300f20130088201d00d0080c50b80010034000e0030311100080840140d0340b4004c684030164000e4603a04440b01441c060360445100e490060100303907840c85254000c1020306028071080f0b680348595800684501c0307051244040c80b00e03541000310310380300b46c0c1520b4181000c001c0c0020b860380802000301400c1554240314814000748640a448000d09041102410321803e103aa002299080000c2c24400910030100301c905485d80400c80d407500e60740b82c00041745180280c96100d86010f02d448503100c28150000050702c1090021144440580e4030ba0007074805a03102a55107034007503070014404000f035180041d500000301034491000035a00310b00000001d82001e0982d8142c4200f00002028403100322140c3ca00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 343558929 1250 343557679 343557701
    0xd0b010806031f020702060403050706020708030a0806090709080a060b03060a06030305070b0c070b090a15230406020d060e0121051504020406050405250e1507110402040f060201 78
    0x21000d14001000c41d4031540d00c1c000d04025001d450103070407009181541950f05d40d0790068843d80d1180e8592400d240d5400da00e010300390140c803038030b00c0000e50014008215110241c0c185e0f0b030140140c450030180888900090b004400b0701100540200c0c0c0850f00300008094980125400320711084d1040516003481000b40c6036894213800d0850500210750450100c91840c2e030300000c009402e5031683c0b80003040d400380b0b00f0010881114541480040f540001d60b0780070a500848884503038903d44006002202c0c0301040c174043c019240c1407807401100202d004ea95000c0c2c041c5401624108981000604840c020f402241000c850300703005000d000c000d112641d60300031045c1406020030500340c82d0140d9843d9808000ca81d80156000000e085403182c0d00084020100070b0014825400c4c15281c02c116500c41c030381c1c000740c1100010110011248500316a10381c0000c00303401c10043e078113060120038940e4400301e000c2d00d00d071801c40d100c1005602d032840200001c040c40c618100c030035428050005d0a40302c101d019 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 343560179 1250 343558929 343558937
    0x30a05010519031709100504030314030f040201030207051f0903170103081912050c0301060e0d08030c0d0b090405160603061a09120114061c050604120c080d020d0b01 73
    0x64403600181e500d00e043d607402c8030140705500c000452142541c86003000190300522058111400e01b0742001c058415603100e0b0310364600c0210074141103091400308984c0d01003803103202c0020a000d54000d40c020860075008a05580958081d080e02210001251a0150310166142503000034568450f0b2035420b11000c2007080c02c4154515100e0300d035075004400102d80710b004a04294504107000366000740e030602c0584014012403900c8992060301d50000d11510000c19004001c2c3c40852601d260201c5103a0360100501d4115110014004880d4100314580220075a8503096580d590340c0f070300c5125125512920041030881503001410244014913400754041c0760419900b80a0f140c0c124402d2a8500f0380e0700d02c1c0c0c1c2d855165850000745003622140c20001503518240a9003040362900d012180300352000c6e14114007584201018000c035403c501400380c81500828085070006407041040b19100d8145d180218a8040f0340e00d4008066010741560303c4002e6000071038400c18101801140202e410900b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 343561429 1250 343560179 343560199
    0x301020906030721050f071407050706080c09091006030b1801052e0c030e30031c09020f0f011704150c030b031507051b120c03030a050105 61
    0x201049282c00060418030500994a5591152a042030803c040c0e42200410901c050b0514400a14800805898420025040e4002400440b280c941100d00b004c0d4413400401d5424070340f62084030030250150000a03040c07001c006e84a00c2e03640d68141240103100d2281140e081a01d00702c0e010381206c1d2094083c9002d0030754440c41c002540c001c18501811641c0944500340c0e51000850140c81e426030222000071911220214030402035408609201001d210352030b841c4009144004000c071802850030915408600c4005036501c00e10715081034032000d80380e4000c490402d40340300200320500ca03d5080350790691340d440c0c10a8040d03140c00e40c1d13000a818010340303a011b58540340c6c2c00024a00400c0080c140344034100d5001180801c40401c50022203d0f18850007004080c154800040c050241750b0b401c80d121344030790109807405500c0c50007001d02521540d158a8600820045403800741f51030034580761203900401044441c180c9180380201000140e0360059540c902d001e8004034100e403010380005010300c031600 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 343562679 1250 343561429 343561447
    0x150801021809010f3003020a0c170706050c0307050d120f05070912020a090e0d0306170a170d0c080a0c09030b0c070c030f05160b0910112406040605030102 68
    0x300c0305200351030140d84000005c424151070803485c0004403407110003140340b8141c610241036010640407000703403040815a20035952091340d0b440d150681d041000d46900511410800c0d00c1c040c1d00186020044001034905181482d19064204260030003050045400000440c040c08180d200b40844503220381010010760900da0002000341c40c0600508442c141126443c3c4190354851a80c4030080400c1042400b0012404034415140d48900250401103400c4c0440440c1101c0d84903585400c03001030000030596070a1a882d50400c18040070681d100c11102003000e80034400d01401a801ca2400548546400f0b00705070380e100301220b105445203010440d40540500000d10182c640c00d411661030312000340c4030b03131540c202804005215480144440700c510303d001c04003c030128070b0001c4031481d045104140f655400c0008181e00c95912269807280c03210200c550640d0085088000448038a004c07034080200000e1448156500021070484504400c41040f41610381400f03001d0180c0003d60095082078005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 343563929 1250 343562679 343562699
    0x106020a110d060e0d0f0314040f0308040314040f0f0e070e01050f090a140405060a03080a03050c0d0e010b0405070e0d020909150c070308010b0901050a030b030115080102180901 78
    0x3152141d84201c40b07591140c0e003403022035000581d41c0c51a000c140c5500710392175400500260212030b60b86000c01e0a01199078403080da22154144503981000040b1410041c0303580844074010000c10031014046440c2244503442a40b00c00707400905100315140c51241e0814804466080507940041104c58022040184041d845064401e8590081c2441501d50b44100c44801c428090024204c0d0008641103000034860400c002040010034291420003141c3c866205001b2209041d0002410001d800c020b2035620380e1080c0e00140d4090700100102d0708005c0760003522003e440c04403031032000d1a03460f40c04481c0545010701c42c190304410b8904015261008407008110181c625032008ac0c8144d508500181d0105010720034615803001e04082c210003413400f4080e060b10307600a54800d1b40000c10900005c24256142c904541038500305031540d81c00d00d0750442c000c07006050200d50843c1c00d9502c4443c1180750b1070040c60f4001c05015440c00251301e41003030428042c60402c41d110483d100e0030b0309000410602042d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 343565179 1250 343563929 343563953
    0x602070e0c120403020c040f06030b060d020127030b010b1902061603180203030a0908070506040b0304020405041a0106050a1103030c120901180b040303050a0c121a0a031a0106020a 79
    0x111400010460303443d400c081c0d080131318005005400c40c0c180f038100700301002e07a903001d9015241301e04210b90141d11500180b04100e000560000e01145034204400c05045100c01c2c1c80e0098400300c441642d040f0344036960404242070030b0b0f01000f41c02c00c0201e84c00c1c0111400c0c10440d01c002400c0d100030401e07460613030208103501c200592843d0505560340b071a0300d07914200d124080c0c00d2640150031255282e132001c1c0010f2a0003c0780c441d40000380201400810603140c040116030840300d07101504c6085031150740801c001801d011b0000c407039030f04401e01c0b03401078544d814024600801e01e540f1101e4555a0390103000d0b052074071020408000390010020001e03408200001d80720701d1010024050881e80d1a011011300511100e0790140b82c0c80c4410740c1040401180708050381c03003a4400d5505220720385030f143d00902502d500ca0050703c0803039902c0d00846001d9491b68420104c18a5619404008241d00c60208100d14016001a030307410b080d00240384010f1082e40f404034010728082c40107042d010103688803402c1d0010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 343566429 1250 343565179 343565197
    0x201021b0a0b0c070b120402030f010c05271e13060806010b0c0f0703210206040b01140a0b0309060a050609040506370507021905121b070602070602070e0c 68
    0x180214128004580810160000c5e00a40b44e0440e56000099410300c1c075500100c500300d00c00d205481d020740040074103001d0564001820744416003401c0305465082a00c40e43c0d401d0b104041052154210005c1e41c411440322603c51200d0b56005503010143c2c02c1c451040f0622071054005030421004200c0c01600140702d604540f11040150b23100d0441100781e5080c060700004926843c440c058012081c00761400610320342c4a000080d40381181d0200c0c800b80d80700c0500700c0d006403041b481c0704010840800300310303070411030503400800065019458005d646101d401c10384140442c0c0d800303201001030061403841629001107048805900c10701c0c05544082e9211002401003003440c141d19095902c0c500004a90034000243c1a468591b008007104c261004110460f5030740010311850b07400702c404040070741c03c0e64012034120340500081c0001000045c2d03030354400e104003114420300710310000d001442842500e000e8a00ca41c00740640d03503d4010020f1030046984c0001001e207841005202c1d140c5030710030855081403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 343567679 1250 343566429 343566449
    0x30e0f030717070b040c051003060b070210090503100b0307080a050a12030b09040302010e1b06251a010e07020303130209131b05011d06030606130b0a09030201021b0a 73
    0x44030003200c00101d4024104004c00c1c000114090004024100b040b281c15208150b1383c1038000f0020b03002c01c50030368607684205003400d07104110110140c240180ca20412803144c2c1070803c0141e40c1c1e81c01080c90540e1076020b9661603590b862a42a9624061040714014000c24000300750070710305601e0321a150144580f0041c9142ca070020710131041360007908000940307600100308070218940350a010303010b0418821101c545001d904da14000c2c00455507800b04440101074141070030120740509510000418281c0d4900d54001d1440c60b800160854166201c00c0c100d0540d40e1401c0d500d071041300010300030050310284c00d54005108004424401702d940c044915012143c1684a46400441c400d40848114000d03007da00c8004005003008007030840322084035000c1e614000b03a4912224000e460452440d0459480801000850358030300d01000030742000035195001c80b2030207039510b44550179607019010600c003140c0340802c01c0003590307014044856080b441c0340300007500c0303074a540005a29030258091680c9070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 343568929 1250 343567679 343567703
    0x1407020a0501051b0604120206060d030e15090a0b0a0801080703170d021218070b1201090b01111519090b0106030f091415060a0b0a0c060207080a080601030e0f0307 72
    0x1c0203000034084c51021030b0415030349241080d043c46840c038001034140001602c141c401080072414100d4643d485d098065450b140301400410411851030500341c4581301034107052040c1100d640c2c4107021403008010b000c1d00142e6450441c90302400c1910305a11254464000050030004104044081c001100342c45807605d80c0c600762070440078028050b9518101d42c500c4044104a4881880752010000846100c00c4441c00d90352816854820303c50406807600644070000101308030040c036042003010000c141000314402511800c001d01e002003492100280d1420041405210510b80810f9001d05034110740520812409496140c00610107118074820950f0b146d00303120503840c0702d0b40445007855100070003840e4590140310090b5140f0200c12511400c0d00c21401103180f83c40d0101500d02140d10080a41d42401c1c4403950584007010041419206a42c0800401c00028101c0700140210501034070f03644110b06041000500709c4680c2070403a01c642d40410200750b00e01a000040d91000355101041c50300c0c0f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 343570179 1250 343568929 343568947
    0xb0906010623070213061509140301020c10020a093c0b1b10020c0f250303140409060305011d1218310c0906090b0a03090b01080309011407020a050105 66
    0x102410b9202c903c15001c11000c0c00c7e8101e0740604120216034940707120b0401500a64101804c0784541c140da14600da00c50341d0f034980400059006480c01101d24107020611a958640e40c801c01c40300c0002c20780c03000c28940868141000b00302030044800009132401c1940c0760818100e40b0044c4107080c18250b00d0071043c007107c200301000704600202a803400000750745456200b00350603650103282550355803501480d514034042c5403403070502c20040540800c0c0e5848480c03454078151095110f403c1c5800030484c007000f000c103030300e8500e0007000010b510402c0002400d00700c0500c1c010526480c01c06540a603040305055006a8013604161201c4907110401d1416058140c7c0000d0301035400d440404003080c2110720135404103180c0b24558031014609071400d1201a0120500703c94401d0702e4014500400d8411303c003804404000e001424400100341000190280c01d07469031458590240c0c0050610b40c000110400c00d0b5a01519000420749401c240e9810301d90184e000802010603401054100300c1c0202d26022 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 343571429 1250 343570179 343570181
    0x50f01030b0406060f140312070f170702060313030e01090b0a030b19030303020309070e0610050705030c060f0108070f0b04050922030302030402090c0307080606160b0906010623070213 81
    0x10013446800c12240159941b0f503095010b012100160034441d025200e0300103000e0004900310f61026900c041001c0c01001d1030ba5850a0351200d40700060b20004042c0300c03850060311110300440c0600038a40001d55064000e240c002e003070b26448001c0138100101c215041000216000030f480e6840410306010403010030703c0010503850110000020b100701481080003040c1030305680158064802401618255a110b00351251203000c19140503030003802c0700c455030201c40d204070050300c080da01c2007043d43d16081c070120038070b840c058054070135108400d40100108040300302003141000408040200072135261402010740e19501480c4200c82c0240c070352400058a600150300c1c041042c20047c441c0c1346c030b10241400d008009401c1164104d0203030100c0c0001c118503804503810382c0d101c1c4025070380c1d4032500d907030f03075824010560084a41c8120380d2402d04159400900c000ca40107100b81c001400900c0d8561520400406080003030340c000c1e0080e2815801d09a941d07465034221680c5c150140d80c0e9406031050708081c44 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 343572679 1250 343571429 343571441
    0x10c12020a1103070b01140604031e15090c05030c0d030813020316090c0909060b1c02040803040801020d1a10140d020c030d0f05131506090608160801050f01030b0406 73
    0x1002c030f40400200071081040400500303040c1c036000c90400e2035480031901482a80d00c6140805007a00c4d0650150080c2c00b50070300403c0d00071764415800c10220400b046400d2040d44d40c40c000c00c6600400501d0280f0103801d00f0040c03020500f40c102c0d01001d125203240c40241c80e0450241000d44000c0e0242840c00c02c1d5142045404408000000300c420503583c2c3d84400c10080251050080024901b00c0d800101d500342e901400d0156803411107018505090180f40c40410100340128016460302440000303103286061019200900c10704001580c0c6d24122081001110344407210b100b03400d20042e10482041c1c0b202c08800580c04000e0519607a58000d24034408607a004100300d405205000060742f2400000102c00381c000c0789100d48052141003c1010450162441203e003054680d9403142e80070080b5003041140c503060140c0102c0001d103a80ca400c105000c1c1c490980102c103440d40300702c81441040c401da1460720002c00c132400080125040801030300c48441410b1001901501031600840c09110a40d4400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 343573929 1250 343572679 343572707
    0x2030412230d090b090a1e0602061e07081005060c0304090609140403050d0e01050103110108060315060105160203030c031c0e03030c1c050103140d031505060a0c0f1112010c12020a 79
    0x1019a81f41c004901d001c260503500540340180905404180256810300240c08540c2800c010b00e5456039400104850300c1900512509424401a20010791900d0740c4006207840e00c203c102540d9604e0811682c40d050304c44590107403031101c8c034010300841d4601d40b11400c60740095040c035003150389840003515400601120343c1459074a5280000010030025800407620a00740b0a0300c034444c4503603484040584a0100070301c041d14601d40680021040c0d0f100302e0050440d10b900c06454000301c89941c01091458010f031b80b1105541e800003030b1500c00554030700c11003143c00c401142d0501106400001164407400040e0074079100346004950380281205000300d420940d1595001001742d581d41b820004107813030b015078031100d0b940140b030b00c400d103503622170b02400307031144000c01041a40c40e240c40c007030003040d40c00b0800e0101084018100741c40000d01e0000e61000c00c0e409030881c11001640d0310104945441e04007009801350b0b1600f18044d03009500031108403034a4040d07440060b00d4601800094500075203400030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 343575179 1250 343573929 343573949
    0x90f09020c100608010c030c02010b130c0912061401051c02060702060403150603140102161511030a020a0e1c0204050402150c03070507051005030c0a02030412230d090b090a 76
    0x30109101340d0541c0442e5a041c5160b1b13051042e00c11000099007261004940740e0780103c02d1b44115030700a441c940240f1224a1549014036031960b4810701d02c0407030040100101c41c06602c0e800d207100211051402c40b0b016040031200311411344581d1050001c8500c3d040300c024043e5070f010840c4c000b5035481c0800c0da00119040511980301e504000c01d0b4800400c01400100c1c1c00800b46402034080010510030764801141c54041007458410503295003d030f419101050295403601c945d0403503040540300020b50300400f5049409a10361000100c05040ca0706101001030251402c08040c4506641e00c01540c0200c2d50181d4000685072110300200b80006007169107402c84400000f01801a000c00000030084240200203a0398181d480e001000500300480e0080c40000703138180042007840c00c0040003800c4610a90040740c1c034140d0f0700d02d0b200300c007401048403d4a010031000401c07108d8001c0400d030601003c011001410801c03140d42c03c09400918240584002d01d80003040b08400e5071240c20f07180c030241c55000c2c2c07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 343576429 1250 343575179 343575191
    0x14070b06040b120307030f05130504110903161d0f130606050a080307020f0306040803041218121208071407030306050405130c0602030a2a021201051006090f09020c10 73
    0x1c546035130fa0b202d01001c60008440034004000380f44035000f6101740b4034031002441c03501f524000410002d018001003201044a0402113040315a804000b05400400a003000010311442d107009a58a07a1580054242201c5c0010402151841c03104a05a112042e03400c0c41d201d203000d81c28607100509481d003240342c008101e48030120320701c60004040d01c481c51080300c09480f01110340c1c4c1851f40700d400c00d440040611000b4000f080000340c00303500e5200b0400705131510b04007000200103504250001075000710341600c880307003450050103900742441c0322030b5511341020400d070f0800c15001040e03ca003411000d4541d081c04243c2c0b0040500c80e0700000300804000304244078034144040c48154180e2018001c403001c031811100007034528004001d0315070000054075520285003607010100c0c0f2444036100003031036034a4090789880060340d841501000030038494000140750328101101d04208904c40c1c0015060228040781040350080701540c030801c1d5000d600015843c0c1641c2125145420030030081e007401d04e81404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 343577679 1250 343576429 343576459
    0x705010e100e0109050a170c070b0406030f0e070e060d0c0801020316091401051c0f0c08090a0b0c0c03090d060b0405010b030f060904020f030f061614070b06040b 71
    0x44409445649200402248040c0c02c9030908885005000610940050250002040482101c4c1c0c440103441030707035035140c1041700b00d00c1070030031246802010100201141c10301804e41d05114140003110b02010811900c4a00ba115a0341c8102c02e110f0fa4541c0380400c00041c4094840480208842d035105101201c0c0c2c940f2036038a18040d420484a030100b404510080e03101941c8640040412508000c10701d1035940c110030011034150740005400d41e01c80f00c1d8107842c40140840361080020705519550001100a6410002404100c0284c00710f10503601031800d01001c2620751103899045892403a05036984c0a00e561006d065001f100c100c564405102d1035030714140200754002e1100d002d400c440801841e80c0359407501805004c00e4034884040c042c000009921414000e60950708140002c080c1100181c0603c0060700e04481106c0d116200d030015401c0c042740c80140101803c90940e2410040300480d11515481e03903e01032510007501e035081030300c042652a1640d0344584125100a800300348618002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 343578929 1250 343577679 343577683
    0x12d050c0c010f20190e0d120c260a1812050601030302010f2009030a050d0c02120303070e0622030614091605040c170a050118091203110705010e 64
    0x107814248420070302e09401c070500107214411204a41c90003500140031742c0c1030307134802c50300c050712001e00d20b400c09003091400010038068444450580d1140d40c031101c01100e2440c04c0484400c0020040750f010310b0300b564060a6000300420741d803e410b21450311121400e4000391140c15000300341c1c07080c1c82d802c0a4504020900c00007180c00b070f06a03400394000340400010400a01c044480a440000d01a041c50618050a41000008010369440202140c003029402d865080c1040b13070709526000480c03095092241142000e00c07500c034200385440c01075401c40c40e03d50030140c034000841c1c20046c8210b200088021680113035200c451304c405440150b4040d92500ca00d03103100108140d1600d025420620000210500000950b00e0064118900113220b4036103403c1c144000f40c60091900001e11804084428000b483c00b0300480c400e0f00d01c0100407805515107904540d252000407028910720b8107015100011607118038901040704100d20300020103400da02902d4800d40a030100080c22942011903230349a681c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 343580179 1250 343578929 343578941
    0x6060d02060d0204090b1906080402090a150801020a0f030b0d0f081215041d10051909050319020307110904020a1d0f0601050405010c060c0905060a0f02012d050c0c010f 74
    0x1507e45440710303844408084880300030341c4601e01c0055a043c0000740142805000703c0d2f002900b100340419442101c1c0c5200c0310a841a812503c00d980d40400c604081951000800d4000c1c400d40c201006142030303038804606e6400020202030300781454841500100302601080360003c854920450003542030070310b81c151079a00c903107011600c242e050125854800c40414082c50707a1107141e5000f429025a4100300c1e201411004100381045002000e80c100404400d0165601492154014565070186408100701c1ea4400454403c02c55105200d0040010041c1440002e20070045401902d80d946510000360800b109420420050102500404000340414520f07401a09039110f2101c2c20754416004645501a500c01c00740091940d0400c400410040d03440300716103084910345500542e84450224580d40d20030840c6c00009003038410034610701d583c28405c030b252002c480c0c948000d944100b240d80c3e104183c4840e510b0032403656250302054001d0f10b003108551741c00103000300a004100f2541c00710801000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 343581429 1250 343580179 343580201
    0x40906030201090b030610080c1318060605030108061305240a0b0411090418021c03020610062a06061d060d121803051b030c0d030206060d02060d020409 67
    0x80f0328100803039a4204242603034813411002e002c4400d00c0e007003004116189000640510384110041056404034029201c000004d8000f0049180d4030401003d15001287c80542c8001d00700107081c401802400301c04181c182e04038080541c82090031201b82841317403d0038551103a000101d9484054041c4060302c80d112076116401c492410000e00030100180016980c4080f842840c0300020400d643c072a1402d64401441c5442095010342c0081c0180d0114400c22100407144001200b400000c5040650410005034809201c07184241c625152050151074503e841b5600c3c40c2144504100d80d60184040300f4008405810840901119030748036101c5806415002c00701d5840f9100400042c0f1600700181030610a542c018888900c0e1002340e2003c41d188104c0401448040b8a41a030020100c3e00411040071201d5000c40303601d5210302c2500170103150404445076140204550107030b140210342c0200b100c5510920030f4541d81444192403001808500c504000300010b94804a80828450015408601028 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 343582679 1250 343581429 343581437
    0x1e0c020d030b0a090f0e0a0f0b1b04051002031317010f2a022410051801140307030503040308030f0c0705030406030915020c010e0606120705120c06040906030201 71
    0x24110404070207480c2400c403400c2d0010549002000710b0442c40d0f010f0070744607132403000c00203200c201004614142036944070107991141c0185d1002041c000c880d00090340280042011a1080d8081601e90f005030145124240c803070400740d0590000b8074024011106c5030594420700240e043d484100720740080742405000c01e600d42c42d108050310040300c1c62107501c1c00c2011b500d6080300265094103001c1c134211090105801140620a40b581030078081c40b6169102e00110095030255181150308101c8400c8594040386c46500403d08202c1005a107401544c15111184032140d0880d00c02d00120b89004000d500050992000107000400c2c480180041e50040071640c403074242641707850041d01e589011f8900090265001003008122440c042d134010000e2511941c41c0e0060301c5c0c5d18603e290101c0e040b14031a400310fa511a03229100b040800d0100300c0d44900704407460359035581c880715015075408050040501488101003600022402040b0081411314010710184c0d6440d1520720340300141c00e09100032030200d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 343583929 1250 343582679 343582693
    0x30a05060f180715030b1005210610120b0a180c030905031603030605060d1e0c050417030403140d080c09010c030804030905130606080906060d020d03031e0c02 70
    0x200c0c1c65041c0300d54200c42220000d00d90f4a04007420100380c2c1d8415582c100502d070b500c41e00c140b031507107604082480d40345442c0c46160315658090407074001400032480c84541c111054013002042e540d00a851011941355103000020f0380c804c051100003e02c152a43d49910850380c140029a50150302056a2200030b000c8061041307403d2014140e05640c181c100080244c1c100340540c00302d81d00c0d60302c162070b0194002e15020500c5036036003000c1130341a44140c901000c015101e07400004c4251100808040c2a600c083c010890202c0050000b4054099130080440c0310761207803a01e4a40d030004000b558065504080111501510410541d603140746024000010400f10300c00130382003c4416065444518040c0c40301c100070750f005d030384c00c503880d140c0244205d05100c18068080303140c0d1074204e15590082501d2000196050a00340c01400703c1e4001008401386030b10060030412241c481008044825505541c9842d03d85041d2800790b01030700304000d0080d00c4a10080000748514500d0700300c28030303a0420b502070311f542d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 343585179 1250 343583929 343583941
    0xf05181002031608150402300114280b09030f121903060306110702090f1006050c0a0f0606061803020f01110307081314040207051b060f03100e0f010305060601140405030a05060f 78
    0x1030102445001400182164040e107241041030401c01ea2f1141d007030403c2e41140c1500499020707446250002d0810b500003056150950071301300405181c040d19200281000341c5008000e56151041c5008081100620965449158000e40148015580c000d9091111100b9400c6040d865040b00d03c00340e20641a01011403e000c24031105140240c4201c91101015414814240d90540c0980800e5510b481485010400f04020701205140d4900c2048086211850f0076001001807848018040e9a91003c400030001640c501003030000803e001e080210700c44d51000191030441c003c0d014083d00700340c0005014101449a21040300039202280113070640340703a007801404100c4c0240007006106502c03651840360000041ea1441c0340100c0003c2c40c003454003446105007080394005541c0c24220b0b0030084001d00c24082c1205940e540b00a984103550b60940c910b450b0180d440c0800382ca0b40303040c000c0c0d0034003c5004003286401c48010300701c0502140c10603100d40c90001d0b5030f940701703e44034044500c941011a01d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 343586429 1250 343585179 343585267
    0x130606050907020d0e01171807090b0604030f030306031401020406080a05040b040f0c090222080d0804030315030b16120b030703030e040f05181002031608150402 71
    0x100458240c1c2c02080701c1d48441340d06540c0f404894040e541031001002501500ea4401d8000c1e5128680c0e0a5007a0816054002d07658503100b000d800011200b400c1800303040e6181ca405041d14101ea41145038030b00191500d0800b5001018640c0024100700e114550903000e42e603054005000316015941c17403100030f5407a0040d40c8103c0d10255402040c203181c0c900801c02107210301e249a280b290281220042ea5075907a10329004980c0400504d0040c81d0124201000a0800201040040c0080d02c00350181c8010108000c01d841e5000b0401014161b58003c1e40c01160300b030120900145078800f06905050a06410b510301c4042d131910104002000a01803072a540094082d88e0071101c005401400c480d800c50340c090b02c0f4100011003280e0130550f122210b204960380d038051103001e10304030706204003848911040d0700d003402c503045603e11100b40104203000e00544207c9040086e00a07519000040d40c481103d00c2140c403800402c20340e032244c008581030790440e4a84044109045600c0e25105840020500c218 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 343587679 1250 343586429 343586431
    0xa0501030f020405040302010b040203090a06060b0301081c03020c030a03020c16030c06120f050a0e0f0706090e040206160b012102060409020a0c0b010e160e0904120e03061306060509 80
    0x81468112220407401400c0907080035030424440d0001103200705802e00428120703041146c1800e02640107071042024090300f0f20900000d04076002d0380514660505044541e00c520b032031814008803455548006181e44640d041d102d503200c12409484e03031100015070080180d000400d00712214043d09110407042c40040354100c04590303001c150742078458a060350031341d00141c00702c04551071030381c603944181203d580500c01c0038400e281550300000c1c50038001c01034604c0c141c80079000b258164001d14040c04180e030064142c20440f24015054200380c0c0d1148081056401800300035050442e084006004010090302054107860000b03401500f100c0e10002220740c110002e00780139421200401c4280321110781a00144005601818a25044a0f0560303079082d030580268000a41e900b561020f000c040540320340710454202c1e0030720340100340310291000504c00386009407008003911900f507944000c0600030341811408102c0201502c025107400b0721074011450035440c0807141c0902e041804135491400310409 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 343588929 1250 343587679 343587683
    0x207110f100305060a0515071106030f0609041401020304050f120702060d021308070b04030302100911121606081506030c0d0e0705090103032705130203190606020a05060a050103 78
    0x24000041501c20180d000300006060b1641240840b8404a900e40714440150b40d9a000c5000d6182d07680c0c1e00b810482100525001003a1152000b041888519a25010b5180d0040f40c2100c104c0429142d83c5405103c02d00383d0320b0b41034410b5002004100500001050600030a5140f00582e070764007a10f443c01d05112b04c02d500e0700035400340741880701901100c0031b5400f80030343c47c8080712100ea6103615042c202c3e01d0454a41e0044004a80c0090180708056060101ea851381c480b03103005025015481e41d41d021341c5078206403114020102d41003042c0c0c40c04c0e010425003e10030b50404040e55180d4035040010540c4500b229100c9500b18005107003c01c5040460032070b8400d5803000c0406040000078044000588400b241011140c070030f07401e0100352941ca03c00c07628000c510030384031240e400c0700212103180c45240e0000b0001104800c01d104101e02e0b1a0b61204042031040c4090059599664009200c002c0d0000c00604000c2e525010b00032402075000119143d8003806013080b649965228510081a0f490034000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 343590179 1250 343588929 343588939
    0x4030320330f1b0904110705030301090f0207110409030210020d0603030e1f080903090603102d090f021306020d0206090c061c2d060e040f03050310030f060207110f 72
    0x40e0b50b00b00f002c0018007509100240003040b40d050004040065420a81c0161140d40000004015178043c904c105081002100d4096040c903000380c0310030007818207540c80f25020359100c550820402d807082c00550070324a41c50303500f15101c0802917403200080590740801c4010900703600c9407952625180c001001545110f00800c5c1000041d00012a1205009080040d440c03005001004440d40c508c0e0185104501c0c8040c4001528502602000041c0b101c6a2007081090740442840d505040c140424096844614021404452a0111000a00c1681092100409102d1000c1a0741e5804115410001c0660b800c507070b619100c1020003501c0340810f4451552080c4d0411005107164203216407001038180400b40000e03082100a203044204403c03030000d18203a100320072038a0a002943c41a000500f00c00f03107144185280c642c0da02c09411100c0c01002d024080c012000a6000c5e942d4807107200610f40c0100d0b007185030801454010069007000c0802c99540380c014043d1a15400c2007814007113078241c0244 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 343591429 1250 343590179 343590211
    0x303060118030b0a0b1003090c14060c03070606080c09131502070503120108190c121b030302030a090e0c2d070507090b01030204030320330f 62
    0x55485031007281c00c0108100596900101007a40105030600c00c00d41d03030b400072802c805010204025909444140000d0501e03203c4020082400c0c40c0305001a2103070032207822040181c00f000101103000b50541d080c0c603480300040c0700d401c2082c5504203004a8400404441407500c505003003040c03410381210001203c0d41c4204046001c1000071070b22400c062401c0e24011701e48070042e20b5060030b560100161309030208002004204c0010f0030801030000d868046024000d5100c50796580382c40006601c6140100c01841400000b4402d0501c104504c9584009003c0842c2d0354030b24010b0b49a030000c071040000310798048000681e900c1015401380c4030304020301c4800d240a281600764240780320804a441c0e15800d00344114115010060300420504c5e015000810380c0501d80101c103400e0701d161300041d50415005000030000640c015400c0d1a081300703541074442601005c0c250041c985081d82c4082050500180741e801c01002500e16010054070000300e00d41da840e60782d66440c002e0070005072030096107420000703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 343592679 1250 343591429 343591441
    0x1e04111c050a09061d0c030706020c0f040608030a18050f010c030f0c0b09030706050c1e0d1e091a01030b07030911090c0307200a08030a15090209040e0109050303 71
    0x540460b07404410800002040300c0d040d00c0d02d50032581140c0d11a00400ca01d850521a01d035010010014000c504500a2a40b40d0903d10002e46810781040d070a401a0359540145002d43c4d17481e0060000340941404494442e0300911004203442d0781d261800401c004481400705890030960003100441c041a1540110300c5d00b03c0d40c08443c188003240c480c00802020030b60500c0060000c00c40c050240901f440116154840c60400104644e40a0070003589000308001400f0780c02e00c03035802e4000d078104424a45407195510030031040074000107002d00c0303051049aa00c0c40c900ca59294400141d442c029810001800c10344020603901c54028000504075401d0f500015011f240320340c2085060703d10500d06640100f0110300810001075040d41d400c0b130f68400200800580c0355110342800e07100c2201c55240242090f04e6060581ca4450954014001100000004840c000c13035811603080d24884030f0b001c824261755800808001c3d0400c5480601c2641020342d0544001814043d00301d0594001300076500e151508 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 343593929 1250 343592679 343592681
    0x140706152309130501050117010c02010207051504051612110613034d01021b0112020c0a03031d070e1f08030705070e0606040b03070806010e1e04111c 66
    0x30711040783c0350f6010b0f41140025000303000301e40c0205441070350003031503000f0390081070b082d00e5892415800316032041c0300c103030301082001801c3c00c40e0340422a0205500d480f541007450915001840c1d8003405082400c1c0000c2034000d8030604a0814050034595a0701c00101c0204056441a61407a1041442c060320910100d04100d0001521608054034003064400c21525121000407044000342c02562020205007032003c0241d00802000302440600844602200c01c10802e403030000004c4d0400001c201600042565641200c0000c1846011610700b00480e107001000703413594480c40780032081410340c0b020074030500062000a5903a0404a201c10f40d039040b00143d4400d07010001140d140e0041303000041c9240040c002804000d0003800030700015800c150b060f42d0108005441039015010412041010414120a0f0380d08103d01c1d25011101c0d496040041b22030015a00c0c0c0c16511608100050134154520300005800120641e810300080b0701044120000e4051036508241406031903010309500c1d011 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 343595179 1250 343593929 343593931
    0xa1b030b04180c140a030201080103060b0315093004050f0d0209040b01030521030606030601170a020c120301050d03050a03091a040b0901090c050f01140706152309 72
    0x7030700014100000003103610301c041c1000d0041c2e4425090361018000954810294110f92200380c4095262131325544c002030100d481444041c0c01941da8912003045550207202c2c0c622800642405080700d8205852029100e000422101114459010080800680341c8001c0100b00c03a05030002401d00d840c00003480b9000303803030100c0582d101186003030040050b650880e0071381c0954010050000c03d03604500d005842c0200d00ca114903811060049030340400c202080c00c4a600400940e035080c1c40782c0307440b0b00503189601c04010001c5040e090b442000041090340e8050030101209a045403050706d26505a410141b0081c012207401480312030504000c01d0003003001304800c0c5190300e40014404900e848101c0b021343c44a5402542c480984c043c0810f20207400b201c0354001036034000030000303d055551003007904089072092030b00074002504134000c9a80101c0d04a40c00c0041034117443d6850f5001c1c41d05000908224400200740c1520382800724000e0544162503c0546410900b507841080280c01c000c001c01c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 343596429 1250 343595179 343595201
    0x30c080c0f0f03090c0a0602010213050103090519060506040c080c041a161a0c13090b060c060f060301180b040b0c360103090c032a14090a1b03 63
    0x207010001100381d611680000d51180102901030140c0200300c500f000540c01240d0b124134110380c0141f04081c140340000800c8012600c09090000b200c40342854100d0812603081001c00036400306844180038001c990304420b11a08045408000c0007400c2902510a2002541d4506d1840703400e0009010285a80c82d83c01d10301481403010724105020b00c0703803400703007060030150464486080d00c41203410001403800b200d40103a1010342c076031f060482824a0100c44450740c0305400842c0d448043c26001502c44104a41001d00d00c0020ba40091416242c02030300005d0658540b0301075803900c22090b102c42e0502e8000240b0652002c10346075192550307140c940c182030000d080c142c20740c0020840318840414070048035051101e054140050603060309030a004904110032a00d043c0340c2495240c07400207010020040c03da82d0f1062184d00070220780101d601c09d1102144500080520064000c2510345801104018202c42110030701160769400300d140c4140e81031007441103454005c20740355810903030103500301c009024 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 343597679 1250 343596429 343596457
    0x907030b0108130c0306050c09030d05040501170106020c100908010207110a06020c030307060c03060b041212030507121e05090f10020702060405040902030c030d03020a12060506030415020f190f030c080c 89
    0x8070340002800c1020bd2424500407401c0001e0400065070000705528084e8880100c0205541c07405e10040c2d12040b880d144075109091032281580000d0003200d80704042e1909000031500e810316407034101c8007588a07902491003240c900b640068400e100080c08521080050051414803070107644003000703001071000d64000e141e1183d02c0450800b00400c09803004014020032100341e818241011201240901400b00406d424801040b800c42e0700140c02072452295040001984103600d030f07410700148540390444218138200004c0c0100303c0e0340000c20716240c03010302060ba1403116621004200300d20130400020340111052104105038649980031021823800601580e0140c071100d000642410309054800c80071036404603d1182c0341d9801000c078030901c0c0c6410010440c0c0e80c1001c0000d619408001c10003484200d03039822003141c032122901030360300702c0f50442d11154989404680880c031590f6250070b19400100e4004612860610900944c80c1c030421340d4886440395141c001440d8855800313482006004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 343598929 1250 343597679 343597687
    0x603030219150504030f03050f0708061e04020304050d02160e0a020d0f09140c090405032d0a0509040b0409020901050622030b06010f0c0515040606050907030b0108130c0306050c 78
    0x1459010f5284141d2084d680d10343e10f600c41440140444001600740301c120000581080300c4a40c12451450b0014000c4550f41c0c0c0d0380500120318000710076100845504540003100b44000c120001841c00781c001c0c801d4003680c070084002405026640d2081c8034400942d8a0400821101d01803a8010f003208100c40402107128440e00c107080e0107a80700307180112016120303098aa8031043c828841d00e032401d4006c036a685154101601d4655580c02242072400c4001149452003116010403680303092000708200d49542c07101040840035140d6003142c0d0201d40201e04000c3c40c0c407101d1901340301e0500c44580c001c10000f92030f402c2c0b10a001241d0000030a120840d142c10212002c000361a0700e01000a41c450041908549000d900061680d03402c5072004040c02413448080000480c0030481c0b10308410360642c800c0040e5103908111015142c6944001c1d00100c80d1028021504c0d41500942d030015000c1c0c0b0b0701081c58907140141181589a443d002d8141502d18105000103651500019040302c80e00203c0e50078 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 343600179 1250 343598929 343598963
    0x30e040c120b0109060c1b0302100801090f110703110709020d0b040b0409150b01140703020d0206070906020703030818070b04031a01030309050906040908040807030212010603030219 80
    0x85421520186012800c1804550021401c0c1c2c0a80c030a214020b1030a00303140c61805001804969405000910301c000b508501100034010203014001150000c007407160380c500825024009140a000b404501030400322141c110b4160350140c0100c0d00030040c800780c03420206840443e41c1c0310094011030340c80d0188140000715002280054080c03c206054002400503003070342000200c4210b0120503004a00b45078948006c20080b05280048160b0204003045240f100f5004842000070000b0460b1805400715805091603800546808000c00036001c82c1d8564a45280948190380a0700c12100144d018081c2800024400e91a15801c0707034807400a400c40c0702140c2c0416090080942200700c4080c0701050410500102c641c0c1003804106d009500c102950450300c00034921107071800b845028415070360202d041ea441d00d0348401d1005030855030351915152910443c4d80c960080b44010f0740b10700001c50a60040e00c2041c800d100480c0d6140d0010301400c4480601c042588441140560381c26010515280d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 343601429 1250 343600179 343600181
    0xf01052d0a0206061005030c0714060a09030f0c0b070f020705280b0910030e1005041214131401091a130b1306030b030a060e160602030322030e04 64
    0xe4030320a103420580d01c540140704020315054004001911450300007881c035581c2a004001c5a030010448801d881c3d40f450700b41085000c000081c82c2011051080e00204800c1d1b80d00d644c0703c1952140b0030b42c0c0c1e103a40019105000c0310000c2a066020380440800c0307002c40c1020707024003191029281d0b24019100700981c0c0d4000180c142e502c000c51031011601e503068074640085c42051402c0940144105a03044c09410030200d8002501034154506044d40c90040702d00c485400c01c402c0c501105045000c1c0600c2c82d1500d082d0f03c01002e1618040c0108504510700003100380080140c1d2681403252407286621032074082c95283c00c80b02c0000460500c401840003003445c500301d400c04c98003c080d548001d40e85450821903102c080385564002c0101e010b0510000c01219448a441d200b144d060303103404506404007100080c141281c0c2500104244e161401c1c0740d81460300801e21017280d0301000b40c0310100d9681da2030141c3c2c407071008071002051490f05441680840d6900341c0c000d0311040c064900b804125260138080f078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 343602679 1250 343601429 343601497
    0x303031d060610120b130c03060503061501051c090c0305010c05120a0b060f030106050306030c0d1121030403050616030501031a0c0f030c0309070b041206091505040b0f09010b0f0105 80
    0x740703aa01c030100240f1f55138060280c10000c200a400400345440c081d00d1508283d58a4000141001303c00102c281011003030202c620080c0030914000c020b40140e07031038000845200d9100840c0d240d4200001d0a81c803a000c3d4043c0c03500c4041e03100d03010000790f03200d6490b400240110609154040710604c000e0707211000d0000598040e02482e01c0c0c0f50340d6800e00e00c02f01490b107071424030383c01e100381e490010b040006a10f01503241d01c420000d581903041080041c0180c40800c0807403140d03072068803020074000240600010380902441c2102820659200a040304a00f615803d00000e40140c00c540c2c0301c0401c0000f169040c0307600c000c4e03031f01d08542802d4040d40b010700d40d40d10a0701c9401d881407020090148028042c4100002441e1400e2014540748c98030840d48032098260318060016a5620362043c18030105185001022114507810072440c0b0b031500d808000c41906940015000d039000307000401d0368070305200316078881d0300c0181006000c0c40740c180115084c1d070101c1080c21420410052500310b45511018230 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 343603929 1250 343602679 343602709
    0x510080607021501050307030c06051c020a17010e060907110a0b070e181012030201020c06010e0117010e0a0605190e0c040c02060112060e160303031d060610120b 71
    0xa480f015401c030505240240045e08814425004072108200080c64885810100e032007a062950307c07042d8a101a80040000c8691828686d00020700d00084691004801c087c130080c01e0440841a49c0301c10024000c54001ca8002e41c0240d003910100712200c1c09400007492024000c0c00f01d07115105e032507850740c50791082a500c50005c0f030000d0301f03440380320300d01400580da10340400141182c2c240b524480c9115025118031a1800288c1240c0103e400d1600c01e404440b840d0045a00300d65265a40d00201c010090f403d00c901945820404555010264103000d00021440288004e20030010241c4034a0300400014100b000070022120160044060310301075615103101c050050140454403106001c240d40210031b841c01107420200042c4881c19544403d01d0115400260000701e010980003840c8c902a0890310401c00f402010800008040c0d15401609040035012a50304403650540901c0782c0e100000d80f1401d9100034885003075410544a210391036803804501d10701003042e50121001c61542c040c1c1c6445 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 343605179 1250 343603929 343603933
    0xf0d020a17210307171b03091608030a02280b090604060b01030204050a1503020c0f07030201090605070503070201080613090f020a050d0b180c04062403060501050409051008060702 79
    0x300d003890b00d0480d02c1504038a80655581d8550b10f03202c10010300d400030103a038110086816201041c5d4a10800701170078022982c80d8500e9640381480a40343d55295400c0b1a00d40400d07036040004074010001001360745035265290020b08240c0030b071803101c06603054102c818001d10304180030100041022000201d00a444410141c003450900d410190300342c91844001070706150040000300950b0b101c60031b41000715281d01680100c0090a15405c40c00b0703202d419060f4049205202c40301509940100b03046080300e100f40c8414a000781e0390081a205401815009840c640040c0510800f5500031407425501010043c15400e01c06176008400088800360607080d6204400d00c05000110305060258170b0140104680c00b46003038045590f034101c00304000f00341c0038100700041c0d007914400d00300300158002000014401d111642c0c0303401050304e81c04803182500c56050710714007803000c00c2e6009120700c0e8251141a0f44080c54142801d0084002c2d00c009000b1504030405580c00007084001442454064459540 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 343606429 1250 343605179 343605193
    0x213020306090105040b18091002070b090c0307060e0d0311010c0306050f06120103030c060212070807300b0105070c0f05031b01050d2a0201020c1009020f0d020a17 72
    0x1051120b0004140c010718011450500000e10540d43d000c0d40c9410401e080d490801c40d9565940f9050078405d150082c812424004070b070410421844040c0f05102e8012003084500c08501c520825660700c20600c2004089100d850f8408001e00f84110070003415400390412480c0310344c1100c021070840300560224400030b81d0f200740a202c40c1c6003548040344034480c00c540003824495003524500d000c042c10710000b030070b201030280810100007068046e2010300c112549503c089141107d809000241c00302c4401002820304588407812040c200036000c5400c0d00c203107810030260840c000040086c10382c1d04400f4117001e402e00c5000001030384000d40740d000d4032149036403050091510003490f20304804403061200d100c244d45007d4245903400010744203600c4036004049068601c8c2c59004002d0b95680d951030100c814034803d152002901500140030b110344041c215400c01e28408410401c9804022000b9408020074032910050301d45001c03580b0071540001c120036201a90b070803140c0302641200710f29100c142c005403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 343607679 1250 343606429 343606441
    0x31902030a0207080f060a20030c04030201030c02190206160b0c070c050a06120f06080d0c030e0f180c040f0f0e010605160b0702010b12030417191e02130203 69
    0x40803400c01000c6043c010321101d2810940141c0312a4018142403030140e031101f4000ca0342c04040000401723200814030007562420080c80900d05039009000903801f080c21310384028082c52000401605007030b001d0400c2e1920142070707400c002c2a0f901c00104602c10380120300e40302c40417458000c59903008440f038a0740c1e641e68204c145010400f0121641c840c03842203812501c03c01c078154120450f1401d180400000041ca04800c7e55034500401a5400ca00158442c034825280a5a0051003100707042e0301070b4607003042c58029101000010450b0b50460358204510310040d0a01c400c8076100360782c10120401209092a032501a4500700d00707200d510a1840303503c482c10401401903802601350140c010741c5005481d0480411a60582c5a003440008101c02130b031900241d4071074801e5209640f8010001e092a1288003105039a036900d4106001e07034003074034034201d80c903480940d0005128103844d0480300060451000c0e94482884001c15101006a40c4486505450042c0e4800c2020741d07282803c041c2c0181c4a08002c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 343608929 1250 343607679 343607683
    0x5091309020f010c0305030c160b04060f0f1109060304060f14070906080c271003060302120c011b03030905031306030b040b1c050102070b010e040b1b0a11031902030a02 74
    0xd42003543c144080b042114012070341c80021664006014902c0700d950307039035000d0001d604134030110014200164903c01e010401180303400148041c55005814854104405104400c50b0b50904443c00414400c10200006040203009503510500802c03000401360b005800c1303030007501d424020000018540500700203040f40c0000314600a8021890580c4c02483c0003650000729101360002070043e10700c502c000544002029004007105100a03191802020600002070003425170750004911810244900c1054181c00081041ea004816075030001c544d115650307103030500040d2500680c209621030040e200031030010001000510b8502851055141c54010000c00b101c80d08402144624100144002d20365110030f85031800c40e07960004902038451502e021802480303002e10050880c06800c00014046540c804014032542c010224899581d8171340c41c0780d11003030601d00780301d08101c1001d02610301c041d1b00c030701d680816038030b66030007120f10744940344201100c20b40c81e40010600680c00000d148a4040c0c2c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 343610179 1250 343608929 343608949
    0x1009260a020d02060405060f06190605270a0504020c030706060303080a0608060421020708071412060f01030611040e1609140102060c0a03090f050c1801050d030f0509130902 76
    0x30701c0a0701c130500707007a5501070b100c1c24040c010302403030304104000ca10290780d12201c061070070008021000446507030702c7c1c0142c4103030071500310041c1c003030030000c1d10030701d8541e8082d240d4601f550003c0082d9680c0303050808000003908210025040c912080c465000000c010f1310680d00554000d403a4002c0300e16100e11a402581e901d03801061140d0050424071001521b910070780c0301c02c01007003854110016001e0000701d182001a5000015600c04c0e168009101030a0914420a80030300b680d00155080c00450742d0740da40c070000c2d107400c084141c255004002080041d44130b4022500400203003843c159460600c041c8141058549016642403940902c0d940e50300007030f41030001c1002031a000c04113500040041d48480f401807510621040c0091132180080c80781d401000810740c4180803440980050070032035540c00002c2502405451707484284070111410b660700504950300100b0380e00013040c05a40460b0302c150059400001d01109000c401c0466031494806400500d00300400101140180100900842 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 343611429 1250 343610179 343610203
    0x304030c0b041401210c08041b0b072607110f120a06020c070b0c07140f0604090f09020a1403100c02030304030807021c0503090c121009260a02 63
    0x1a04000802801c46030f0300b9034908800d02401c0104850301401046900a510341e001c6080381e030300d81640850b4064110035101e00850168070352490a81c0000041140e400300d5019004c0e03908010301924000602d0309884602012803000b606201e403c60441c122011703040800101c03010a030204000031710342017a030100340c492141118400310030322503000d4058440030f07000d80143c0000d4002400e180105800c1204100500c0c8500c9010303a100540e0000f07d407108914013400c2c4480042d840d80c1d0140b0b2803d16191880c100300289140d01d058503240b840402000280001303c4030715180d0090b003000d82d842d00c40f2440100f81680041100e41412410035080009640407118010324008004d44025400002c2d00e0f03005615081001e12902c640b10281d250940c03d00760980c0109403605010411940180070354002d000d10707070031505c1550012041200700a0050003050845e8000701d00d41200c01c440da0080b41e40c080c0038080e06420b0035070715102c811551000039190703180d01c82c00007001c03400154101f1203545020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 343612679 1250 343611429 343611449
    0x608041202010506150903010b06040801050f010f083307030c0306081203060d030c062405121203130812040203120f0405060a0509060a1107050d24021b0304030c 71
    0x490613100259492216052420b4150b0001c5801c11560710254010340c24004000d11198a0313aa0701c2d4981c501802d0304450803c0f007110540000203069281c0700050003602c003900090500481800d011a03c000d61001010b052410070041e9020201c0b1040c030a10701136803080c0d8010a003661400c0d0080e080c0c9990f41c0c42042c050b8040809200707da0003aa090ba608600111982c400c03609041c04d08451101e0503000280c8100c3c0b0b0a0380b40b02d01c09031b18103941c01254149040c16000644d0b280104100c04444001100054208061031417804441314000c0d64040c10110f0100c03107409054803051010341003c2c3c5000001c0440c40148415840c2c1000f1510804012101c00ca00e84600c00d00004200d00440c03055900440000c82c128030321500540941d4944440030744136030780755202030100510503811016015110300600c01c000c101400e102030001d555540084008885440c0c9070603c001c4c4d07085e107460001c01c440c1c0c24400c441c41c040c07240d10710402c54203583e130040d91074031f056050805503040540c0c4000c0e103030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 343613929 1250 343612679 343612681
    0x370c0e010207090f1407050c0105060f010c12020f0d020a050606040203040f060b01030209041b031103070912020a050301060806240904030e0d0804090f051303080c030a0f0606080412020105 83
    0x90381e000806009a8081820206507200c0c5242e5101c040c3c40c004800300040d0304100100301203158070a0244c104035400c02c009102e25214201440400b051003640c550010707407000500da000ca140800c0c440c1c040301251049414015040e43e44078100703690f0340b94000068005130003000c18490100300440d0441402ca40852460030141d5598100e0f01e44500300a05168680301a40d501d60300941c140c4014503000b800c14003200301041540400550010550700100c3d1401c2c2e581c0c80c03012a0502a40d21404190311031080442c2400f40940744042280800c9038065065400800c058030203024200c000c02040d0001c4c80281400d0381002c5141c0c1020011800c0b03520140540440c030340c3e0310015103802c150541060312442a0310408143c0d0204000806070a410000500080e103a40c0e542c000504411042000c00c010b45074801c00325100d25408030301030001035006e0040354550440b58011034204940250005180844000142c1921040c1d0310078000b04400d40d04120038441c400050702c1040c846807008001d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 343615179 1250 343613929 343613957
    0x110f0c0c10050d0e120a231819030c1205030f0d06031205030f0403030b040e150702010605010905090a2a020c0a0501050a0801090c0507140706030e06040c03020603370c 74
    0x81b405140300b21420010188a0100c00c4403015a05110202d001c4821641d03450600b003090040c0142510002d004600c86003c204070420031500b08003d0721b5003e0030074925140f41c0010342c020500c42000c10f4070079000070025064450701d802c00034002a06c8115010030100d06e5400d104481c5a011103159083c42030410070031900040f0340e031255030f11030f07818100011900545404078008101447c0013000520070040356405258100c054035209514690080c49100c1d12240111140c04441c4902a00084c6000c0400c0d030340d400d00d070440311840901040821902034924405100c0e511640c1c17200c0050f820840115030941044280e4901400e0213082c058a480c92945c0c00074018101485291480c690394648582d089100d41c04549840340c010401e103e08a1249003503d4868500e48a030802192402c80300c0c054400d004601c1038807032508401051016450b540a02440358401400305928072840744003000034440110550120080700140e00940c2000b204c2030f10b041322a041100d100b0700c80034407406a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 343616429 1250 343615179 343615213
    0x16142508070b04140112091b030506100605120a1401030f3809070b0d0213060e0a06080403140d0507031d0c06070c030c0e1603110f0c0c10050d0e 64
    0x80884d007840c20241203045c82550500a1500041c000c2100c0301901e8821440000f1310344031000d59015900783c41031a1282000032015070040d12607580440c1d81031100031a03007100da00029500010a038400319500f00c000c031105000c0303442600b0844139806185501801d001811020a81145480e200010048103e90001c0019442e642c6202103400c6d406000a2264009100030002000b501d039415440e034070089603100180d002881c0c42803c1d01140640001d025200f00d000348011840900a030843ea81040300807110594014000e60030700202801c02c0c1e090034140401800c24000048000039035050040c002001d85005c62503841900300b610352000b50110020414403032048040b603661350303034114501e01444c02540907400940f01c14907440c40010140cec079000989204804050300c00006244400046e812075142d95038076106c20000340448082151014000c000740e45440080311009000c00e800110511640c44a0000050f0041202d89040f5a24050a013000103810f014081e03000c2c60303a454031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 343617679 1250 343616429 343616459
    0x110724050714031312030f05090604080f0a1b0807021e031c1b11010207121a070201090609150e030403050d08060a08060f0601080c16142508070b04 65
    0x103050703000070105400c41500c1020202c0150f111204100e402079020014008142c087c49a84200d4101400210002000b09031207210341d500800d42800c148091450810a40005400809000d03d881031801c0b00100d509014880034407600106036114150f0bc1446030444000c840b038101c80d64041580c0c6910ba4000c2115042541e504200f800d03107950f2004111600700c4280040d014004a00d5078a005100413a480d0240180080e021280c0a40d600c8000c9120a080351201078000005082860305201c1709030b5100f03410141c20f10001c0707440300c00c50f1194000c44000040c21540e01645503102080e10781d4070301480303c143c004800a5800c00b0300d0b5413141621864981130600400c5440e400103800b40e42c41954201c05001002c003140c900d0714003030307011501c5010300351503880c0454000f4001031070381d0602004070343d01d40f1030202c1d400565060030341d1050489170044000700c056015440e0301e44844003002c0f00d0b04003422146006012803600d846140703414602d65410140b50310301704010900c0954004100c0c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 343618929 1250 343617679 343617707
    0x203090a052b0507030b090a0809100509060d06060e010207050a090b0414190b060306011d0301060801020a1805010305010806130224090906030d02100f1107240507 72
    0x301040090030b00484000400c20180d0300300711a0000d140c418020f0004101c01034074812001010152140ca0700749944089a040040c0303000d008001c418018240344084115100b694146203007400704240004040e034011001280c4035540d214800c0090a50040809001c0740080c00030b0b0072001d013814007140d10b40241c1d000ea004800d4603034247c080d0603142e5074404024110960130400300f5082c0032010884001d0740d00000e481c010f0070034154030891316010342228060344050f19010041042c142001c000d83c0300d200c0c001035065680c0c410000741454280007d100008881c0e46043c10700c070051400d850320178501e4111604040c98a4014010b0031000150f00da04086901c2c48000c1908041c80044e010101c6071241d107021442c84024a0880007005000d4140c00c44100d40822450b80c405081c10765400044200e140160f00c0b0003212002105140d0040e10036184030b0102050710b504143e803032a85603202450403219081c60b103041006540f448403079420162400f10060086080200300109000440090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 343620179 1250 343618929 343618939
    0xc07061b06020408151015030c0c1b0f090905060f0a020c190204050f070806010c020d0c0f17070609060e120106030809030708120d0203100803190f0203090a05 70
    0x11081140118103000e890290311140c15940c4544490140e522a50510010080c00d0080b1000c14403050100d006002a114602c9070140702070704580040f4060040d104000c000e100d40c0c46030240209a4464048003103040307600c004044c481c0342008050003102e259002c0c1111600d000d000600041c4042003264104d00c1c80141d11103952280d04042000303109544503801c0f248590304800c002c40d18941e52043c40e05008944c20030841c1d86407102040b00701411076008000031501f9000883c258081e0f400d8100c60760015019039880a002d698110100800e0b070800e42c10070522a03810000b03c2001e41c410b1020304504c00107000003902e82100501f04800380d0040d0014400181280409030312210004401c00c88000300911081e076580c02e140c0c406074000c4e201c090180c0a1030002066019000800810103800070300d80b50b280140c00043c0c0e00003904060a145621140f81600141d03442c0e0800250805124a03a1031002042d91030300090440d4600749903840c1590030501c202050b0382e40d6001000c044402c2a00d07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 343621429 1250 343620179 343620197
    0x90a0803190f090807030506060906030c030c04020a03060906180507020a03021506270a0e0c030601050603040602190f1b0812070e0301020406030b0f19030f150c02010b150c0706 78
    0x20648043c86284c00080c40f40c0b00d042d60000c00e020f40020803502507003058805c42200e48901d010f050320361949002c3d05800d03601c242c0075420f0354148bc0d4003e10180d80c6600d0001200c0d500e40140388141d41c0d03654001c80c00c00e00044035140c0e070035a580c03151a80058190004208110050f90301a44684100c07404800030ba10c0a000281940c50b0072880441c011603801d002076041c07103000040e082004090b910403030f01c14a00406c8c48031041000034505c802c064010b0090105038a04400c0100c16400203104542c03060702800742688101c0098209540c1701d40c1910f4400760b50014410062081400f00403d62010340940c42d5080481ca190040762407103042034080c0e100e0350b0ba4482050b01c0301240c02c940c1e240c1542c8001000210a42e01d6070054a504004450000540b1802010005105500c600301c1044181c99581000099500c2c2420013009200e10070110740340c5002152601280e00485004015035100c000c4110300f490680c0201240c006210a85818403041e00803e0780d4625050054005015001c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 343622679 1250 343621429 343621457
    0x405030604171603022103090c04020d0b031504061505010e040203040f141e010204050120010f06090509060702070303080a090f02060a0f0f030204030f2d08090a080319 74
    0x600f1150000070081c2c0710810b014036441c0095941c82007214010340496041aa0184040441d044901070a0040002c042c03030030502081100075402007899402da80c0e030b00c02c101e0300d040c0c41c00c2c840300555052400030405075240c582084010ba482e81600c0704d0030096110030901540e030b040030040410360002d641c01030b202d54540c507143d40c0c00e6001110142216000c0034110035081e0000480403000541c2400100ca000d20301001d00e03090340686d0260b50301107804140310301c900e00495a1401c3c0c1c0e4050b44000821070060301050b003411110703243c1110380400c0e01d4504102014008000b01c5420130103500c003d005084c40c54800401c5180080e18105402c1c0d00d030050b03141800300314400b030340205800a01090745d5581000029207900c003498601404610200f03199483c040c000d1003a10100d03500035142ca080e00c9695607841c00d01c410310000e5081000072511480e00c0300320040c1108001a48111002ea0b92140001e00f048840e020300d50006880398820400c4480024421051004030416814003040d40c00c042 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 343623929 1250 343622679 343622723
    0x304060504080c07090e0f0309090c0c07031202030403030f0c030f080604020f0d050f060a0b031303110115080616090314030405030307030f14030c19030b060406030f060501050405030604 82
    0xf100035a0303258456400080342d40400c90340300a035094039400860f4060b500d032890316a140d004640b080e81c0d01c440c0ca28005501d110711100184001e501e0741c01a6183c860716035079140720303c0384080411320040c0e0012070140100340c0c110401c0c2e081e0f4110740c2070030030740c000451340d008020081003c040010040104c01180d40758449405556140d4800a001600c0310410f0340c400008000407a2030300030a1039024003150351420f00318055000e4a4900c0c0b202c5140d503464880d521001d86ca070002c00c500300b0403505869a10703c8000e2041c0d0708101407080000407810300d8094150b180c108081c00180d181c0307040141888823590881040307011030b54005807400940c0e80d80780d40030381907020355804181c05000010702e0750304240c1e01c4550303c500310450340c0b50000d034a15102c52170310481c0130484070f440e4411410403010b94002e200303c25151385000c15141c00b240c0d0880310b8002c42d00c2038106074031080200380c56840070f50014003d4010f03440078050a00c1c0090078585801e00003030741c1c1c80c0080c0c00a80384496010440c0701071104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 343625179 1250 343623929 343623937
    0x315040902060412050a0c0b0a02100504020a050901120b010b0f1b010204081e0105010b0a0e06030624040f1205150903090d08090f3307060608010617070308030406050408 75
    0x3981844e034550406820681c4d00c4183c1d03902d00f02d4440c20100c401107080210300d01030b0750040419500408021144ac1280030081c0b0000c2c01c180d034400110302c400201a6501c040350b5020700710b0103541554020045c03416501040040c3c0052080000902007035620000060581e405c4001c1030000d003800890000e01c1500912942d0030a10300b9000350000d0364240c0380c146d42c520142e064050001c010b00d03030b69019503a03100d0017401d240400241c0601e040c814a403401901454022030000d1006400c00c0301e1500210704200c1c00c00c010400c07114045004c00c003408542c0142c6009140310210f480018050f551420307183e00402a260380c0702110403000c1303409c1c103c0030025117100e16400b4040340c03c5240c480c01d1070072844d0408440a44203041c3d4100480c403038103105880b03950780c4411f0030801071040c030040e1105022062220000301900e9050020002080d041e010f80e038000e003d21301c0009205070601b2444074071907403070303000e245036580c4100b004200083c1d00e5422260f03c66040200014182c50302d18282d50300b885 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 343626429 1250 343625179 343625189
    0x9011e020c0d1a071e050403020901091112040b060307090b09060d080d020a021605030a03120b03010b0301050f01090b10020a03030b0a0824011703030103060f0b0d0c050a0b03150409020604 83
    0x4101c420020005e400c8840066000c4810440c01e500c2d04140604132168441c1740402900032485200410400001d0781240304082d000c002c080742000c0b16154901d0983d0030444054a00103030b11405d20401c3d080034443c00003e0203640c4401e2100c94158400b140c085200503208034040d8482500902c00d000c003013030542e401072110705415551140208002503644114081401d000d20b9090000106841c0025076560141d6040e150411551450f5006034000d140348498036405540b03508000d91190f03420700c01c0c540706411401d580344803541002d5080084070b04e161201030007020901e1264003e560009200c541c2c203540351178081102c20084000c00d45051555021200501c40d007000031101421103240710b10404441c42d01e61071941e0340c4640480c56401000d0070490369400400050012691f00d41100651310811078004c64034400c1500800d80c00303060b808003500d82c1c02d4121414082454071f240d01c480105410f141050440c00c0240d030000160234002846c40c81103a841c40c0d1041151500d1050380c0c0200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 343627679 1250 343626429 343626473
    0x1b0a0503010b09222406060908060612070f0e09010509010528060f090504060b041a0105031003081201030b0603060c0909090c04060b1e07080f0315130209011e020c0d 73
    0x10b10f00c850011140d044545c1500b003a410b008001c20210b104101c603800f200c0381b00e0700419440e2261806e000b0000c813181316080603805201c0d0049006405000d0b1100103045045820020345002400c15086401c090b02120942c0d0400d801d20000482c0e000b01e4004900d24181d1403420140a0001c80c0024402a840130356140120900003e580000d948694441c501400041c0b0104048c441008121241c6081c001d014099444407044175512a10245901c014403142101d101b40e2a506d9001070b540126202048001c881d10040c003c03c01c89800107900020305070b00808250074405000480343c01501c506030b000c1c00c480c200046041c4030400103040403800c0a00100081525010501400d42c040407601002c813100702e0024500741c8420301120580b17600008498103045403d004107503998000380020b07050500d50380440c5a260f641c2d0404105407091a100180e803011140005040701400b808899410007003040a4080190040b90b01d66400000b211800f0200340a803800341d00d072002804046442d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 343628929 1250 343627679 343627703
    0x5120703020d110f0a08030a0f09120f030207080105010506070f06021606060815040c0303030e0f010c0f0305060105190f17010815090a050c011407051b0a0503010b0922 74
    0x881128150548070410a490300d440c0c00a410051000c101c2a1303105901d419401000782031481c521079030276120803d00901c2c04444540c2d640420580f404207080f0b00780c0c0d0600e040724600040513010001003004103e0a4000d0013658035202c0040c02034090050041c00700d002c11000c1104005d803d6040b2901180c01428110710800340d82480c1004040328001c02d01e01d403282200007844031400c500c41504c0359501c400040c000e503085a50407406003c41100e90316080c4039007980c04110b80401c0c024010344180d60782d1008110781c03d07141c00500b40d07100a031040d41030140401021130301280c04005040340303504070b05004040d401d005104641c0346543d49000c0c2040f225034000820104808507804000b00901071041c500380d250f2850700ca8031081959001002070f8040110303002d040d40100a050000c10000088908041042c0c51701c03802d10340b81c03101c50058141c541d03d20140528181c40100302600040c2e00030000b8960100110300f8a4401401c9501d206444000f0f11b0404140c000e420382081e940034440c3c5d001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 343630179 1250 343628929 343628933
    0x7020a03240f0e060c09030f030c010e1902010e0f0f04060308040f05010206090d0f090b030c0319060b0f0706180804090506030102270414181b060405120703020d 71
    0x103075110141a1518500303081c2200003228460040e9041e949400c1c000e0461a211844c07002c030981c0c4440c02d11070b0140182d001060140e5030034405000710096000c000b10344040c090780b410381080d91098043c0141581e182180b00580d91002080c200d941c019512003000018600008007030404900140d075101c0d040c000048200003aa2000c3c0089520805042e060b40d5218001a600c50034119040d2940341e01a9103048002407042c240b403940040b542c1003071602292a40f50000302d69000300c80312408054000140728140c82c512900404c91040107408001321400c04402c0f0b1a54031485074072140c000c01c08922403003480095400303440210042146512103050300d251205c0540c0091103400c00c0e2501e0840090000e04041c02182c0d511010905101c080000d200307550b040c030030172501e0286e4020369141b01d1a00b41d40d841e00c80f15400b848261485c00880200490460710303200f030f4001c95203200600c082d180080c3d80c49034070035242920700c11105800094081503100745480a140e01c040c0d4800a05880482 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 343631429 1250 343630179 343630223
    0x10b090109021e041a071410020408060f0903040b0a02030d0905010603030212070c030209040602090a0e222001020f1006050109080c0a0b0d0f093206060607020a03 72
    0x55900c01007100340c604040700d6003c6800e40558071483c280c2d06240c148268941c44d034803004021440c8103030308903900300205038429440d0040b400b6504150a5000906100a04041103c240c0c013103001002e525a610703006410940b64015442280d0031f5000c049001150f584c0240141c83c00307a02c203102c04000165081c180140a42031500c42035026005554500c101403580c070007101c5036503402006042c0c45ca445c0da803d0104040005000365001942802001c05d40e6690710000c1001f000040ca51042a0400c9001c2c48140f010500c000318101520003000ca0005802da80011450283c1d0b008604100c40c000c801030b1b0411203111514100b600415140301d080d401a41d014005481083c1e0365501c202d80c41e01d2025070b45d0305c6588621584440c650b00208241003405004007201c8083c200003149085400409106a5042d80401c807889181501040e54020b4004140300a9066101c03a83d0100d03021003240c03588840c0c01402d1107028200016550040d511605030040086602481c043d11200c04000181 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 343632679 1250 343631429 343631437
    0x61e1818040c060206040f030c08091c0c230d020a1a040801060506281812060c03150e0702030f04060305040309140f0405040c0510080405060105010903111002010b09010902 76
    0x103941c50039501c07020403c2c601c00100a88120340c450801c2c0007032403440e14246c803d92010201190410010001c81e0321603103401605050b814211205010510114074200ca402d0700303d900701e00d40b02c0d44004000e000900d0304101c820b118410a035003100c02c80040e0300100700a1b070600c0c0c0101064000c454000905492505c0c000d00884030910020050f803a25402000f0b0b691041d2402ea18031072101041440b402e40801c034004602d0081c0b410318042c100411070b5690441502680440641e002d003205810600c40c10b8002e0710000050b41c5030070810203041c2c000c2214040e45030b000b882020305100c00000c00707540c020800c603402d1000d0700782b1040e19240d031540002c01529040300c0031000207420680008907141c40014070345081c6801807004205548003803c2c000200740040007510301d018008000207003a212101038020005c000c0e60b07480e070a0b2419080c001e25104041e0b02560400241440410105407105041d41103960111000c0242182c0c20703208901414002e50160f922500071000060170700b460794010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 343633929 1250 343632679 343632683
    0x1012080d05010b0301030c090b03010917120117070303050a0c02040501141807050d020d06050a03050303180c0603010e1e010b0904110909151201020409090b06061e181804 75
    0x5001da60f80358106036607240020312000f80035099165060141801d40d0708400541000a8000a071342d250b03544a143c60110100d10500c0d62210000b032036500750304481010782c090004001e020034120541003034946d40d405544030113030401802048021299103c0d40000da4070b560011300501c030740e584820011007a548180f84441c828803440480c1e041e088440a00c642c8101306603107919041c4034080741d858000c1d5005840700c58003c1c0d0b4a03400455245e5920a410740176500503001141c49107001c050400c4441514000d40c1c555621400c5000c0c056074030042183e040d66a021448690707910350143e80ca89500c0b25000581c211070007031001040e5400e124002c4c0082940c101e80034000220407058420700d92040044c169000540c060004041100c803020b0528003800c090680c0041401c856151405c90b001a04501c02071341d1141f00c44000d0000c14078400c3c1d009042195414600070046084c003025034801d200512070700f60b020400f20880321a0804020005001414142d6203040360340c00d01902010403101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 343635179 1250 343633929 343633931
    0x2030f0a060e10050909030c01021b0f1c0e010e12060f07050403110d08070b0109020711010503060f010c021c0302150106030606020d050f0d0219080601140f031012080d 74
    0x440b00d40303503a000c070300458206400c41e50880c1050180840418000e02c07661092100700306040101c00d091004100b0100006914082480008000c030305080090052132071070362101c0300c1e14176014001c2c44005040d0000341010742c9040600c01c0180d90800048100e5540518a0540d048500d01c0100e0514070070712f041c3c180b01010795220030054581b40124040a80140000029803c00742046005000c00c580a50205400c044807607464a8900302c0c2604000c00ca642c0100b440d02c100940004038000300c98003400e202c0c0c10740c1307044004103140c800342401c4941006440903a02003507481d2a690150100c20808160041f0f0a00d800c01a6841e0041001030b6203d080b482c00000f44188a4801d110590b5a254041d008045034544201c45c113402c514940200c110703041110041f024501d10040000e030701c0f0468400c04400910714041c0c07109000500300c906000c40f10051041d42656541210000300341480c150751280c0342c14644505105c1c00d5042200e188200e070800c5030922150300040c1402d10b000500c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 343636429 1250 343635179 343635191
    0x8070f0c0b1c2004080d080903030103110d141006170c0f0621181501050303030a1d032a0d02030304150b090c0301140402030405030708031902030f0a 66
    0x31610120b01c00c44158040242000100e041c48481ca604821490350010201c4a2001c03018010884503610a13803044403281c0c080081c01d207005420080302d50b480785181c00076508540c0340d43c4500640345441c4481510074586540031034200004240d002000c40918400c40ea4891380d00898800104918003501d075200c02800b4080440000008508102c0c0c2320280c4203440c0c0907107085c14000b850700403044c941c1b05404600c0c1180e102607a41c000603480b503207006494074030071240c0d91149400d0107000c0703840c2002c0e48080c40050240d03850010459800251554001400b0780c0304901d0603110034000112100a40400101c0402e19510302c000651342d062110318148a500001ca020b035a141038500b102d1303001da0001d00004000c511a03008155210039803003004101e2080180000b0329804048450444607800840188105045925025241e2000365021851814151035032503503401052001441c0400000c00507401b144011901c02c04110920401e40d04c07420150b001c00d044c00030031910345070080e190030303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 343637679 1250 343636429 343636439
    0xc0b160e03010902100c0c1e140409030c14032101090c0c0b0f040c0801050a05070305070212030a0f020c03040b04030213020703080f2d04020f01020a230a08070f0c 72
    0x3218403403c084c1e0041c84500031102d02c40e42074032005030644040c0e6001c0c0c040b140002c0d40310400103c10315078182000e4a00641811700740c8540000c808050454050b41c42c11070b032600000c5d080307580c1c00302e000e42009085850460510b0100d246100e001907c044582c1201c1c0f54091700e0281c000c1c01c40c180c41305404140540d201280d82211000b4400e46c01034100078552000c5820140010550764006020b08042c01e482910313019014251001501c03407030407241d89c0d401000350203540752141941114042c800341400b40024001000d070741c080a807145081d13640c2c400f40d1507044035007541190b400c4a060810390362906c1d5100c50080d10390f045848140e014070142042e1007610380462080b50301542c0e15864020168507501444032007a80000d10109046104280480c00c1c620391288c401900c29107414665aa03160610600c4281c0b04c2c0c45503218107561002d10310307000103000035070300c0644c49101c403e102d6400d50501545518110140d0b02c0900001800190501840405800710910500500791021145d0342c81c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 343638929 1250 343637679 343637681
    0x30607030908040b0307030f1404140c0d020111030c0601060206071e080c0702031216020415060f05070c120b01031b0501020c0f03070f0b1c020c0a0201030c0c0b160e0301 75
    0x92038028040c10b41000180554140b0f4400345d0342040b80e900d40060310701100c0c00d07600111500c100038204490003100800c01003000792103041c0c240e46400009013108044034030206408054400002b41803061180c80200900d600300107443c0984100022143c003540d50704c0020f52108030966070a4002440e4a80c4101c81000604203101c110015a076a01120341d1200902201a04081401c0703a043c050003051241074214900030b04540c1520080d020840145441040300b141c08a41007081c030980781e10010422960044054911501030703081156031041140760031041d40401d50040e403a050680007a81007030144110800c0d0581e0b00c9200100100030408843d844004000d108503801a400082081a281400c1c9050300c818500642281c542c0380d00c80c6800243c0001c42c3e0400318503454040340f031005892800234210941009200210315118409203803a03142e4a5200e0041d060540b40c1b50308002c000e108841d8903885c1e64208100e0607090a0101003421000c020718101e40c002038115100c00c441e8501 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 343640179 1250 343638929 343638941
    0x14120c0712020303010311120a0615060908190602071b09090605010e090a03030e01020c2b14070206030601050706020d0b2715040914060402090a1b230d090203060703 73
    0xf0000c07c00201c00c00707204000c2900392031140e03541d0078050915540001000b03230040240d003e48528450031038506210000b03200040c9540002040d510641c540034031250719542d0100c40b036800c0b0a0140e669119810940020b44002c2c80580300320100e02c034002540001c9274010100a03110341020f00150f680c1c2e9142088504d42500c45c402150000c41c01d807000a40039500054010440100250038010142c40050901501c02c80304c0c40b104403405070000c41609901040d41c0c03178901500340100140d040350036000d894050307c10b00902444000001c01c1c0c8580c05503058808160713000d03405660ba0340d801440c51015207010300c0140d0148030b0300018901000b00000d4190754080c200e040340c0c2c00c0c1d41e0b50380006000703441110140d6502300d036440c100c0c0f502280c0c07075020201c40c519214000703105e141080e1050018034500108071544041c40d210400c0c0d003c0a443c00015040d42051600c400703505618a1800d032003a002c015681014040080c002c0d680c1029030300082ca095000314203403580303651020400d9042d50700d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 343641429 1250 343640179 343640183
    0x40204060f030b030f15160f0504060c030c0f150606050306060a080402150c060f010906050f01050a170a09110301020f04050d081e09100314010614120c07120203030103 74
    0x241c00c01529900718480d62040c0500701004003140c41a83c80490b0366410320301c0622808842184000c100140f44840c0ca1114615010fa4074041d907003503041407401800382c0128042c4604000020020005045c4607540c0c0080d015040b002602d010786440c501550751180314583c0113913050402c64002242c0307020f00d040c0ca10803000600031500e00010641b0407240c1c4100104100d0f44a1204610346800403891009070007400c2c408401031500d0b0501180e14010844140c3c081094070382800c40034051611040c3d180e1210b8503003800e045480312280403064403c46180b10307501c07840c2c5c0605001c01c0031030581c58004607421401102103c42000401051600784c1c80707460340c84504e1403410401008641000100e10031024050841030341003035804181c2124907048450106080f03103011401d01900d01d408010303241d0800041c203040114141d404807600010304148140c00c00e00401c000391103100d1600300b04070744409070550010140fa280c20041300c07031160000c00b0255041e20f000d40c00898a03a0001084030b042e66 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 343642679 1250 343641429 343641437
    0x2010b150306041d0a03050c1618051504050709140937020a12180201090b0c010608010e070f2c061c0c0503120a050d05060a15081504020406 62
    0x642e5440a200c040e00d6826140c00244144c00f4a4080d10329040c407441c1c001c548070b692941d41e075465440080340b401d4508215201e00741600c000820806000b44c600015820414a01255607615803000160a12000558507045401d02c003c019916510032681c03010b580541110744010b241507010b00c00c248100b201c0b5900102603074036030700c4461070035806840900b603140c4800e00138680390f080da17035000d0b40c01552021000c40e207200744c4400807002c2401110048038101c10681c90181c800d80009040740c1071442044016080002c07011601071080d000000542078420081c40303d034001c0c011066440180b44154583c1e00c03581040411117080c800260f59070b61a00340508441d10f01e10000310442d80401400701035000c400e03114080d40000e0514910000036001e000511030881c0f0f00b50905040c440807030a544c0300100b041000201c0f0b203811600b07486190129000010304c80e074407140410440840b6801030500111100c00011130745074010b40d400e1140c039540d858101b2a0100380248810780c0500c0c040d0340081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 343643929 1250 343642679 343642681
    0x30314042907080715050604051501120e0321060d080d0e010f1e0501080616140405150d06060e18060a030c0602071e15050d14070f02010b1503 63
    0xc4803603480c2401142a40805003482c100840d030341c1c00003551048404880c3c103100070782403c10035101d82c8a203d5004000762000c5c89130b40360508058501c3e0103045441818010003e40f00784c521440e5500c200650400a02140d41e0740d1400300030f54400c1c018042c012024a400030300002c0c42402c02418444403a0741c000140e508188155a090001d0481d2012540c000c0d076a900c2c480200e01241c1c000d0180342099104196070801c0e840c044201510030581084031198490420300c203400e80e0340001d480e0300c16030030315202104044540c03a280680c800e5501c1664000c908035082c1140c2540c180090640c01c1c00c1d50001c104070380d543c3c0310980700b00310b0300700c0c1c803560081804100908090042e1042130780320744020111703514180c6076602c000020350b06821040040c5c1c80b4440502c018242e5210321100d250003451024031141c40c0002d500b4520000c5a1030204000c030226015545507015001002d400715114601c1d207103072400c070078014000a18081d022005600309401d0f600b0509180030021420001210130310b140d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 343645179 1250 343643929 343643969
    0x61805060c211504150f05060a23040509130302030406031a04060608090d0306120f1a090606011b052505040905100b03060c040e1806040b0103031404 66
    0x11500011045500507070b404000b8042e044115441c1441001d001e844030710918250014402220241e0740c0d42c0f810108440000c2c881e0034a45e00d114800c543c0d007100c1842d5100d02d030304411100220803105034407a03e516204041d10011044020303009507401279a10201c00d0351204140358008904220260150b0000c11050144030300c60342001a91041d0032840081006241004c201201c8031940000001060013045c8180041c00b40b002c1100c44000745014880310381841c0d060300d01e0410303120004151240102c1c04004010a001c090001519110b40f008460702d4007214046c4c4484080b1181070000e0000b2414000c113a04a184251202d42c00c00f000708a980c0d41120b40c49140c03400a43c14003003c540402c00014030380d03143e005078a2124480c00182440c0414260f03100e00340c5548002040c403940000c42041848804101968100e1361f040b0710700143c58441490703905d01e0b103001d102540c490740107840800c130500944005c1d4604891282c5d0300e2504030f10b080340030300c0900d005074005c1035002c65886901043c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 343646429 1250 343645179 343645201
    0x192303040c0305190c0909050709020a0207031a10090905191407060302090301060b16030e0103090209010905070809031e030402060f2205040c050307052101090906180506 75
    0x544144900300c1c103040c058990f00c900746818106010b90071800550f40d007079001c0008440e00b40005005c2c64105025100c05030383d410b1f0702c4405c24020381e644964086466079640d4030070040c0b08001c41d0001e641e4252034a0300c0c03888030364105088a28507032000110300002501a06840b8605030690850083c02030f80c00212040501144602000e235080302da401d40b11103043d00c0030301114006080e0b603180140d941d1440070916013500d074940d02c161322440c403c7c04400701e91448131001030120395043c0707040c5401c900c41c180160010300b844007001e900441008004074081001d0b0b484036001d10984c1c1c071600003d9a4010071207942e84251150203401d0480c0040d142d80800405c4081e64000d44010601402d001100354803545c1600105060414030000f003240000b88006621100e018000c142c806009891108a0160071484040c1050003040740000e0281e007070540c2903402d0f4841c2c0c0450071903500c0c25659082c180c0c01400c0c1074103003504c00501c0d0081d21307100e01502209521800e40d0240182c101941c0b6096109 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 343647679 1250 343646429 343646431
    0x1e0412030603060203090304050307170d0503071e2109110d0f0503180a09060303020c100c020901180e0304030528060c120507080f041b080105010308192303 69
    0x1040c180c0701e540110000c0d0a83c0051445164800c0046403202c2c502010140f424615512064107089803c0043d0b12000002ca441c100c5610141001a40c90722000f10485101c030b00c0940240c8252a051fa82ca051150b001580749070135071440a2003150010036180440c2200d45602c001821503a1100080d000c5060104031000854002d41a10018a0079600c95078190f030700041042c1c4c58154141e42c08121440e00c09034070405000000c00c02c009050441c1c0e0f01039a42c8051400051040d4006207002500d20b1080d021250031907030142151040e940e41c1c4415403881817001151400842c1040d481102800000060301c04a075000001040b0200000e0b00c851840840f404101014030346120030a40859900e024140f840c403019a1102d01a0181400c2d2600311040606041c0410034490184010800c044800d542c01c15040510501d48030b000c454034600c0ca10342580110b00d03a508040000040c410000f0203054045445511034044401d003042c1154810044944910104a141c1070280880340d1000a9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 343648929 1250 343647679 343647713
    0x90609080d0e100e0409060506040c020a0803150a091d0f03130302040b011e050415080114010e1917070603020408030a0305090a0606090b041a030d050310050a17061e04 74
    0x410340c50184e20210f0280c039160581542c002e5110014040603003400e105c1c101c10400188054a10051940e40b6414144405881c00e001140c4042d1054400e0381e071150300340020291301c03904018241d8201d050103a000d0030400a03003000e02441c1807141a103880070084510321891040c54107121401c0d982008020715803250000c4c1009a038200000c012201e010540300051580d84459403501d01d041c8000c0c0c1d40c1111488170204114240700104038400380913000541240c1d003420458180d1119002003021a264040402103101490500042800b860201c45013459070700c0050b114001d403038800c290107912413449412940d920070090098664402d9201d107800c85400c5098602c41d0f02d860b2211300076a0090b402c001000c0d0750b2010180000c0c40c0c40c0c8261044205046980c40c051045400003030b4a807007041d030b841810702c07900000103084c904000c0f100c1c40180500900b80001e646d01c1352240454264a28840c05051003030501207454085043c1c4881d94603134084003814441d41d00c598a00c00080500500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 343650179 1250 343648929 343648937
    0x501060509030d050f0c030703091a091503040203010b031e060a1a10030905060103080406121512021c05030301030209010b090a1203030b041d0111030c1204020a0312090609080d0e10 80
    0xf5401c84503040c40108400c40c0603a6072b20703180f0340c185200c00340200311030507091100c51401c01c0f110a2644907542e0100c400c1c17001d840c0c01920f90f0f0310f078004203001d07000d25042540c2c54041c2511201c030098400c201840c0d400740e401e00300ca03280d03a40c2001500443c1c401411880c1c1e034400207241c2240c6460030513042074500416160200b01e058465807064039048007a0400ca40e2040d0100e010702815920610604812022160902889802c00c0d01410000014020840c003007880c00810700c00c0d9280c252240c804000b032202078541d014031900304a0703140d42080c002244680901e01c00081d105000d030f03003a6605250001d06070002d5501e000051110984100c3c130450074580c6482592030642d540344114038107003e5184d40090142004640c0c0c0e400c4034214030790300f87e98403001d00601c4003010b001400d6171421b1074904441c480c2504c0b940002001d100d107130381c8003c21b040300100018041d140d000c0b01003c00c0310050785540d22680c0c0c0b20702c222512a00796a48403c0040e5003d02602001d140059400201522a043c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 343651429 1250 343650179 343650187
    0x60f08061e1015020d110d0c110609090906060f031b090a14070804030e030a0b0a150b0d020a1803020f0120030f2d030a0e1e010e010501060509030d050f 67
    0x10030681d03c44810101d900140e000413540302d10041c2c002c680104520b00c5040038004403000347e18044d050410b1140058419510b0164801150b141c0340c04a81c0c1e00140140366000d41d103031021a06564260464259016501c080504105410006180c0f00d1308030f03401d0103400c45082e020041c08050480142544103250711303413501082c0320044409150080b0129910705c80145000c0c24058089491041c40352700950017043d0f0f40340410400702d003468015401c443c01182c01c44c0f90034202d080c2ca207940e400040c1101e030001a21051904182e005044c0710115444035181d10fa50b10585984ca202140b10194000c08000d2428000350b110350361134515421a814145141c4ac0c503208068030b150810b4001d04070404001074a840e075140e02110203c6a180030010940400901c0b03441078a0500000d042e10440a4950022010340001442880c071000360008404032203041844025010707205202c10345160f5441c00001148261241040703801580c00079005040305e44000204441561000404416000040c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 343652679 1250 343651429 343651439
    0xb03100603050c030f1b0402090604030209010b04060e0d020d030305061305010605040e0a1107170f1215030c0609100c0b0a06260c0f13050a060f08061e10 68
    0xc450340001d98021401070864020f240c0515140603138a81c1e00302e41d03513404100034031101d6540d600c01000050094401503207450034000800e8143c0502d0300000e521074000400403415207042c03001307070089540c5a686d43e507038800c01d035042c803282c84506038001c1e42183c03d005140c004240a030f000300350030171405806048550909540001101d03000e0700301500041000904102d04280b41881c00e40040e050401007115820440e8a0b140603c50a00018540b0340c0244584241a8620f0141d40c41030103060a0f0a5581c002003800000340341c002c03207400b440058074408a4141342230004841100c0c1101401c03040c5444e902c40c0c00c00c040541103050100800407030804450001d0903203c0618010200300501041460501800c510103a1444160900300340301e0440c041801d040001d02c880e000d00096a0020401d8110b50115065090303880840c440b09040506000f04910346512848c1207543c03140b55a0030b0540c603058425101c800c21f07101c11041c1280820502102c000d0850101d41007810324080c94015660f403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 343653929 1250 343652679 343652681
    0x30b040807021002030c0c060405031e0f1f0c031b0809070302030f0d0e031f09060209100908060919080d1404080a0305150d120302090a03110a0b04050a090b0310 71
    0xa40544006800100b418400b1110401c6100c8508100305d48c7c481c2000c0c18000170a681e03d1001c0440d0300704202060782000014024003031240342202210070756030341050b00c481e00811740300010301c00e8040d130740341c07408406040b4400d214072852800311503011900359482d0700088031520703009000450b1902030041c6c0003005960030440c0c958a40c01d141d01801da024a03819000e401c0c0d03d00c41941070701039042010300c8400d4004000780342d17031526001c24001521070103034200200240982080c05400c400c0d802c01c903800c2c40c0d030040c9141049608a070112001039684001280e1901001c40c1950038101c96149180002202e6601a10301c981c6101c2c0c0c00103150700f4035030400b817080d6070980d0281c0c3c054200181c00038449078980902d0b07620450180700362000318126004507540110120b805000e52202010004500e403180d0100d6001c002c00408120744107450f4203008411040c00d100c130074031480d0740410000b905c442c09000e80d0304446e002402c03121024640420742000d00084160b4540c0341c0140096002842c2c19 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 343655179 1250 343653929 343653949
    0x3010c021006080a020102070312090906031505100b0904020d0213060c050c15160501110a09090f0501120b070e150a27090e0f070e07090b04030507030b04080702 71
    0x10650040c4040c081c1c078202401200c1090304403402680141921a0150760000350400450343e010807901c0c201e59800300200c4141415800c0020000d09041e0000b041c06040300740c0e41d050482d010000c0105441c3d0540f8964040094880c080c01c4200520680f0b02500c1c1035405031200384120940586041400c00d40c0840100094106401140c1010743c00c0043c400c0410007600812002d07280c50340303400030003540d42c00280584c42c0d400690340d00315000305041080a42200c02c0e8450f90b5044c140d00c580540340d015155051318010840418940040d1507040140e5018440c1211030710150404001019140c00301d5000703008140c0740502c07811200d038200130307220b940d840d2508105651030161205c80c54a4024207a4055041c0c40300c0316500507080d015400e04140c4c440e000c5542c169400202558040405410f05580b600c070024140910200002c0950b10b01022601c40c4500b903541846d006c2d02c50003000c0e424007c502015102d5404a0814000164500001d41d0014090a000c40c1400e056900040b42c09070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 343656429 1250 343655179 343655201
    0x1050f130305071401081801020c0d02010c030f060e04171306030b0915010905090a060308030906040c0609030b190e100b130902030c06030402011b0309030236070306050301 76
    0x2050400c10801d2000602501002d8504560315030000b03070405000030210003029106040c0c1c10201403920004500942c116031030b00007000192448603100a60184c02806682c02c83c030302007030800c201c9403520800c030702c0b0b0036090711124040e00b241d81e26251070300010f008058084402e040c00800800380c1c5000718000c0c80008000d242e401242483c02e00c2c05200c07001c0ca0240c50200d10100c00d5542110503a000400c2c14281da9050f070b0316501c1a0b90b5655000083c2c04d4562014104103000004d0092002001c50810311460041210900382651070808945120b96072201900050100010840f8003424440d02103061300040c0c0c0115100c9000e07500e8500b132212422014500555400288410781000280f0400d4000f40388420494800740e6004079845101014140d0b101d13060020002c1d085a024a19031100342c00022404000c210440ca401303003080e550707400143e10980240c021502400340808150310020f18070020b8404080725401c03e070700100400340040040c0742d1904004201602d00740708055200c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 343657679 1250 343656429 343656457
    0x6130920010c0c2403060602250b1204110f2805270f070207060c080f030117060109090309060c0f08031e0a06060905060f0d050103030503091501030b06060901050f 72
    0x20013914940d0030703003081d030b0284009040c2401c004005458003c80c4036180e0124000c0c20501d940d02000c2c00b40d030005440c0d00440c40180000c039500902092100007144030350720a91054202c50300389010020141420003940b035100390201c07040181000e203c5602020b50b44030402c020340341ca4441d80024594413a469031a0282103034031090514494440036019081482d580500103c1e0038001c00094503442c40780903885c00c1c480b0100014040280f1042207940b941401c1c40c00b2a142d58441d4140000390b5500300102c00941718030700001c81c0a001130700c41c003182c00b949030710f850071101d01e041c0066400c500d64220944440480c05040070100784240002c500c2500c0d00e86624216101d0a500c411400700c000d4140345159107010428402903812030300b0309045c2e0b0000ca440b292120f001e0a40c2640038400c500a10083c030342007200000400d03821001840c0140520b000360b40d800c0c84039100e8081203400912001d41904c581c00701040c1e0502303250000b0034401c001890311a1030000c1c45640c5038050b6101c50007032400b00d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 343658929 1250 343657679 343657709
    0x5040e072313140601030b011407051e010c0f1418180906100e06092212030b10030e120a0201020d050108060402030d080705030c03130f0b06130920010c0c 68
    0x20105003c2d509034440402d003002c01031501a040001c2010304c0c0f05861248074440040c00b58140001006806002c04004500103080008004914041c0c18003800e0900401c0f0301c884090303060340c01680310440c030301c592900860030f100305501451140b207090003000e134010840194028003450b0b5044603070721031040c0c00001c281034144002c000383c01d0b28560b4840c441014940e000e000d0345a072080700c0ca030303007100c4803030500001070f0212025003203064044070005103034003c01c0c80d808040c290950840b50707440d8001c4600b10840f80d42c0800c00d4098886ca51178222440d040000d03210202c03103d42c009040b1280852000506002d2010350040413030f0000e070000c1417594440410803046190411080785410341c0c0d40f038040310a0030085000b40c03403800f01030846242c00c03c01100243c1590000c024801201c3d4104409a091981909280d8400350003550315070300840d03480b042401c0d4a502d500130562440d90080c0d1401c00c1624200e400c8020150016095040040c6401458085910203001074081e10302c1c0502084d83d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 343660179 1250 343658929 343658951
    0x30b030706050a0210051f03061a04050106050d050403091e080606040e19030c06110a030e07180b06040302100207080c310603080c011505040e072313 66
    0x64504141d0080c01080010000400c00c554013281c40300203804a1040850f803600e98018040c000c2440030300c0100c001c20461000420301042d604025103042d005000c8506c001403007010f00007034840c2401040c000c10002c00c2807000b2b250482d030102e64080c2c003c0c03034584c2030706440328000c900701c100d0380300d07c90011100402c0034800080d003441210b03000042120100a440c019000907601c4440d031000b82020803002c0346841080c5401a49909400f50b03120b1010800003901d440545081d400481c0c0340000246030200f4099146000a0400140e4840c2c0c03003c00ea0806c031010302d4401409c001502d10750010b806100000040e11000c4060b1804c03542030f00685241303070810400e070b80f9001900c2c8482d4880ca0b100031403201d103203ca42500c004c200d1210582562aa04100c10803c00b400b002c1d880107115010001e0181c003030f403006520001c0c6910368407055002443e90380381080300391103510001c080c2c1c1e90040c1c501003040700300108280c07078074a82c0c0c903c003181454201000140707841c030074100045010f9211589021 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 343661429 1250 343660179 343660183
    0x50103050c030105012304050319050114040201021b0a030218070f1806050703110a0c082103010905091f140a0c0c0623151002030c0a0303020912060403030b03 70
    0xa849003012016504542c900f84c0000c20f04074280400900b80c1e80100d24121070f105008084070081d12000e02102d50b1840d40e20980310349111601c500303403125442e04405401041c071241c1428000c45d0140d004041d0004c2c5111400307844010003500c9544404010b0f0001f00688445104074200c03102810000540c1c074003030b9405020268001c41d00801c001c20342500c8c0080c1c03000c036001001900d2551030059220402e42c5400d4904005000d170400040c0b0840022804124910301c06006807100103040d600c00e0420315141c900d01c07280c072a0b081d2080d01000d1006010003c0294003540d4002412b07411107665940c100c00c4010740d4811400050300d100d440d0b00980158400302559142c101801c52420814035280e100e0040c05c20304054002400c403511000120503200d801103807810850510310f680005810400c00c00411807070361035801d601840300380845254150008c03094551011141010700418245076034124001c0d4000c0b11400d600c042c4003580c00300010b001f001610300c2240303e40c030002108038048003014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 343662679 1250 343661429 343661431
    0x70b0c060f0702120906071b090b060a05180a030f030203030115140304232b02030705150c0708040b0a0e03011505090a020708030c030f0703050105010804080a09080105090705010305 80
    0x604103007100000d104603140c0c0050101402c11030070103200c0d29801107800240030352141c283c010f00088600d1085207200c200b11038020f41120003640302042201c540406010b0140034280c1000007103078007800440b44100c24841014007518005240140f1103031203590301420506448401e6006900c007000601c480c03100700c8180341c242c0803c0c0c20142139403814401030800502c40200000c1110044403058008035131840a0504c20441c840181e558040c1440000ca004840000e036440e011564540c1c0ca241550001c405c488026801c00050955171154120b801034021300030b080f40503011802c00174030700810300482c0a04040c024112101e9034071010303100000c014600c80700f01948643d251500d01a982c14a10b2980c170708540003a2020385443d0f84540c400700083c000d00c80c000d080c0003000030401418036441e1000398420b01c0c801940c91455101c1e40da0403000c40c0c509000f4240401c01100200c0c0100cac59800280c0b69071491071600480c52030311003510742d00303403441039580940310b42c0101e0f03041c0650740c1c240c0141 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 343663929 1250 343662679 343662691
    0x40c09050702120a03020d1b030b031e070506180306010e0103030e0a290702040c03090c0e040b0c070519050c130e0a0201050c070b032502010b0310020c0a05070b0c06 73
    0x100303d954511031005400f48982034080701490b03400503600c1c00b2407280fa0448595010382c2120301a81d1042d8280143c0500894400c2c64402c0c01010701801e4441c00c6120741030078140c0d61000901a81d4105402c1c0311003a0302140601111038110405a445a9010040140a44602140d100c0f46514601c3e001e0f28440c0d00144080c40b40042110500c80d8031032129a45c41454002802102c228051201001007032087c2540650081d00344041c411a0720f416030000c2200728442c1d1401c4001a076104d661006c2c0c90002c1d500145004424404102641e185c0f00c05001c60b40d00681c166a00c04484a0540d60b200140200031a2150011220b443d01b514100c1c1c1025000c0a803048107000100c06d4903482600c80950782d0f0024140400403c803509100300420020000d0480d4481e120b5490078071182c0d0400e145450001b440c3c0b03800d15070000340c0f01184107029003c10010094001c1c081d80c03a10301c0450313010307400c000680c2d541e500c2103a482c600800c00c20051000140407040c0742c0c60b80d03412180100760074001d00400c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 343665179 1250 343663929 343663933
    0x3080604050609160e060d020a08010f060801060e04020c010f050702120c1c050c0d0203070c060e090f190c0c0506011d010b030405070b0a031406030c010c060b030a0506040c09050702 80
    0x100b2031191241c00300150300c801039510104480000b60020755000d001d2200d500d81000300440c1002480c09030b40d008000c050403544074682140c0c2c1e500c2140c106140140600000034610a00401000d03001e1718140182c00700081015042000f900480350854250b07007941240070341c031102400307060740e014411204800c0351041d90b00e207000e08403000c2a0b5140d400e44248408120303141d4034003102921a6068417105038491099403000b02c01550025603e40001400744d504001261000884c2801000d0750a0030080c050018009503984243c0c50701e110500a16140c03015549241c111a540940c1c89640000481c603119206c90112900741a0710b0168142c000c1200f500080c401c4400c000c0401c418941114203a00940b0340d2941d6a10b085420602d030766106030b250f4130020404103480782c0c1540000748080392403d44020f84e9601c050400d80d5810300c80107001d001c42c130a1092000443da40790071220700c211015044901c101c84d43c0d9105403812800320740a0750600428003080c00200814010242c11036641d00c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 343666429 1250 343665179 343665181
    0x6140c03090402160210140921010903090f0f0e0606030402010c08130e0112051f0902040908040e070306050901050d0c0518040c08060106080c0304030e0907030606090b04080304121a090a0308060405 87
    0x18a141c4103101c0c08112501c10480c0d803180e000c00c48929041481c40941c81c0c0b002f4022a4024640513041c42000e0140c811f81401c081c1011461745c0c0d601c074401c4101c6031803440c0e51019848490a20001764400740040e03041064842c401e4000c40c030b908005107407440c0c0020050b000d4610740140300c4400c14068101380c00060b0720b0090800482c40025580003810814044000d03100c042e41c0c0d200004281041000350070900b0442c0c428240300503c0e02901c1141c078100750082c019954258224111001402160741c0200a60700510550400b004241c0500e40314a00031400d4a03112400100034180c0e070b0041c85c000b091014200407c2220382e80152006204030703c01090a541803410103450100001c000d20409500880041d0030306200d82c584c501c62a50140035030342c0d0b81c00d00210040c003408260003a54040342d001c10700011309000303180845048900110266003068240241c0d2204030046080985003aa5201c092a480803034035000c01f07010312201401403640d03070658900900300f298020310083c0b05504d084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 343667679 1250 343666429 343666457
    0x9011413020705070b0310081504021206041205370212030f012306030f06091018020a0905030304061713030e040e1f051b0406140c03090402160210 65
    0x6092810b43e020720000c5c58a90b540c00388400c1240700154400c1c40d1074880c00d07001c16458000d803030140c2d000310300a5807224101e071004841c250752008191001007255410300f40c6104103a100d080540365001c0c01e6980c185c0440012181d01070070440c541e0056200708500700000b05907540401c02d80c4105090300c04c24034110314000800c045152414450507003080c40f084c210070342d482c040c2500c0b02c5581400900440d04ca0501311251002144120703a0a400741400f440031031340c0448048252001c42e104142d11500713100c1c120341c9200181d000b41e810142030000103003000c01e80780d4051000e000544469510304001c0c4110140303a07440482d000e441c600021440c90064004a54019500d03c445c501c10784001c40c50300c0c5c28543d551b107040101c822100449542c0101c41d4858040c1d03400090080e03104060f00c140100c1688072400c0d040c8039600c2030001050300900c030309511075610409001d40da85800309490070040802e0100d02640c3c07010309213407864060310050300114600400c050b410b1840626201481c41910 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 343668929 1250 343667679 343667683
    0x70602010912140904090503070b010b0405031e0114160f030501050604030201030c0e0405011e08060708041401093801080c12010f060b0a0807020d0503042009011413020705 76
    0x10b4180040201000b410030314548030f01c0490f0408800500100600b208500340117841e9045404100e9404010000010320100300809480a8501c004c0242c44078640c10703050505551890300014002c0c4d522000740c114003501d00074190384944009445008159034401000b850000d8a200000c2450b190400500240e2100c0d419035098a03820b00b80050494003461050380d0903801c1942c0035601a0900001003031108000720502000520140710b500e601d0744500150307899100460304580002d80400002e40402c030341c080e05245100b012000000c5d00c00c816203c030742d40303030482030014015902010301107078000f185051034401d000d1a260810500e54104040c0e903480300981c10300284034101289d2201d0800c0070a5000c021854042003040186943d14030444849070072071070f5000e0126280c0000a1034240c00821400c1c14080580c1c1c506145503550f581349440c0700302e041c401e031800c5003502c20380403100e0b1592140140030341200d6841807144241442000742003140d00490104c1540188034000001d030340 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 343670179 1250 343668929 343668953
    0x50d03150b0904140709050301150825151e0e0f012601141503010e040b04231e390a03140c12100b01051c06080706020109 54
    0x40c1d8050150355110850018000d401100005810300d80d10b0403c3c4481d080d00710030003004454090f030080c080485240b12000c0010705911420141d034000c1c01c44a20041c400411180304c3e4100740c100780e01d83c039403588646010b5214500080001c100c80f41c0e0300140c503188038003c0c0c004e42210703480c003450402c40b46d03c08698132038008002c06040c4401c00810701c407403070081c2c4032450100010b545c11610640c0d648441200000180441f6402809481c11411280954008a0781a61564003031103956072140d82e070707006100d10001c000382d509624510140e140000818064190381e05010002d1414440040749030b041d20345071010a00c2154401e00842c80d042003d084052580b401d201801c0d4044907800c1b1003210030a8552103000e03440140d00802104002c80c5203403809d044210681210b400803500b03014020b071210101102015a0b2203520380d195414555003010b0f808180c10700d042d41c01d10700c415807030486d00e14802030f2212039141c030ba0f1428440c100e01003140d080244200e20092240c000191554409400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 343671429 1250 343670179 343670189
    0x10051306081e1c09030c06050c0607050703021f09060c030b030a02090a06081f05060303130b0717040b0a020c1906081005060a030e010b030d051602010c1401020304050d0315 76
    0xe810020840e10b520500104146200c120b180b80710420100d50700401c0c018181c002203078424030500020804034481c05c251503078510034070014070307064680070429942600035640840441c4245103c0300d03006144915a540c4045400340d01241c3d07040c0c41d24240c6c060741e2090f50548101032528000448036500042c0400102c0d030144c3d070400301612500c171a00060035864201420520803a03104c0c84c079510003d0020385006007980c40400c01e0303031241410592640f007018110003540d002c01d83c00703000b40002c200003814264400d000ea840c00b4208081c01c0d10040d000356020000d20480494000c004c99014840c803910900c044403040c0000c64440400f1501e042580030340b01c00c10070440c00040c1c04840b00c40540c405000c0052070140c590341401d0004000c0d090000c254000d41d400d001036a0306034180041c48010201d42c0e03444040c01e00032284042020a00e0b40e41060b81001100d1b03503400e003c500d68072910119135449070009680c07850325007051484e103c1b0000042042614202940c038070f41030031505000c2560 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 343672679 1250 343671429 343671463
    0x603010911270102070815070305090c0307150905060313110a172103040302100f0b04060803040e010605040312080a09140601050a08010603150b03151005130608 71
    0x520030440168803801102c2e41c41c2c1210551030242400301c210040342e4400d8207802d07800c80c0d102c2912031015a07142c010f00c1c00d0100c4198408130118001900039049150b220007a001241c01d0070b0002c1000a250091580c0140c441980c16442c83d07102c154032a215402070b040503200245107080084510401580c0b80c0c4c0003420040100c0c400c6d40103a9607012013540140307a000d41c029140301c09a04020f0f20b80041c01444144160705000250008507200241c80c41141c268000d404540d031071442c090041c104010781812803550f50616501542d40d107105802c0508003203001191102c0c204080d240ca080c0e0107800070030500005000410008082c610741c5030040f81c0e2031400782c00b103480b103121050142400d140018243d03e03101410701c4a9140001d0258121881191600512b41e600d103207881c01ca66a0780000342c1004000204801c1c40310880c0c004424810001d0700305d030740711440f40c0880280840d041c1e44410703142200020400952401c0d041d10440700301403100800c4140e140c240c010380d6984000d07895823600 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 343673929 1250 343672679 343672691
    0x630160c060209030c0310020309010507030c02100e010b1306140a08070605090303040f0e04050c0418030323010b030a110918150a0f09050f040b01060503101809060b010201090206030109 82
    0x952001d0016505d1810b025044482c1c0d403a545012202a410440d00800a5840e001c0002c00341407190040c400c582c00c00e03401416200444200801c043c0090b076201e01031542d2243c40c240d0507038550011084404024510004506080c001e1070b4125071105a00640708061043d01442907860100e9020101d40e03060500c5581e450b03a81c00440d0860040703a1203254806017104000030020903a588041c0300360310400644e0b0405003076408000494003080c0e000c1e00c4005101400000280c001e9100c4c00c01720a805840d40041c00c00c6140025030414243c205207110344010082c011010401d0103502448444600c6140c2880034820100e4000100301c6d5848603a41e20400106d032000c261011a88070100c0060107801049480d40a50719541c0600e10500c020203103040001800d001411590b82e004030703803040d00c5250316440d03c2c60441741500050b02e4242c00c544003000004103240c00b49070110b824108000c0200e141c1d4002c1c10030304101e80341c050f1179074196410840c0312001651400100c0341540c031444000585 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 343675179 1250 343673929 343673947
    0x90111011806090210030510091808160b15060a050f090d12020d142a030a031d06090c011b080d051b04030c05040b0630160c0602 57
    0x90503114075860602610048140280030b1a034100900c128000e480400c0e440c4003030b9808504803042100c2e03c2e00780d6143d0800900581595411804403c00b0300aa00d42c02104551030b8541e03190310000400300b0640d0941030352000c000324038646550155400c05655a00f80640d000b00b0064410f40c0114002c00c180098450f82000011017030318200407014006045012a030f00e0403880541c60081d41d80c015101d05822070042c1c900c220a041c91201c0040310181c00c2003003c0180c688006400c016400e0705c011041d11441510b0740820140c0a0003080d0707078000c103a040c565000344801c000c0303007601c6820300c1e04080c040022400300050664865082840c1c004201c1486c14400540d15201030801071040700b0001c2c2400044ca00f03500110700555100c100101c0703154169058486903c21484001d1040302011002c11143c035080d03100c1d10389840090591894071110340b030040e0792036544178644410000e242211150440000d6120340c1d2003060440032508801403940060908407000340b00412194000950000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 343676429 1250 343675179 343675181
    0x60403050f09150d0e0606040e0c0d0c12060614010302071101110c03030c1006140d060f02040302062d0c0c0607051e1014010b03191b0e040f050c09011101 68
    0x1d0078042803c1e03988a1400c1485070024005908006245108001c0444c01501d0309204040c0c0d2400414000c140d201c0c0841c003440303183c1c0c02c0b2420a441030910000006411141d0300b1105084620071500000d040342000c41447d070b0400718260090405205110703220015039a518001880b0384c09091816000c101880060328202414a1003605030001090561041b440040c02002181740c0e070100b844100d44034480750021210341e019045e40003140303142c88008250140d210720004400d8810241c9000c0c0c0b00d401245583e408450320004050807180605501d140180c035040407003012189482c41c00151030891940c5040d0200785d20321810001071203008011042024200d85020110200c0d508081c52110580780d4104c015a00c48850a0542510008807030740c07a103606803611040210306640b600c041c2c11800142c00c0309c0880000c0e03901c3d80440240c0da001e0b00101511794103540e69560006000084c03205030390b040181c801810742004107200c204042c2e0310a4075103000081c80d0541460400c552128 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 343677679 1250 343676429 343676449
    0x8130504020a030e0616050304031d1005181f14220303020f010c08070e011b24090209010506161a101e1505090411030a0c02060403050f09 61
    0x180c0e00c14800030b55542ca054040d00030b80383c0f80c080740b010346205982c1d04940381c00c84401a4a4003000420800c0000d00083c059000d1500402503104079490241d22140428565184001c84030301188010426202c200701c011440034081d80180c8001c20604544013000340c01c0b08424800001380140300021850b04401107040d200b50310b056070903040c13452508081c114424290303804160300600032944404601001402410380322030b0300d9540e40301182e440c038408942c901100300c81d1a042107101007500c3c015180da000904160307800307640020424403003c655a4154050100410551070034024040056a5101d9a5a0444030700b514000da4981008800c03038405801184020902481842d0018100420a05041c4100d0a018960742e00f55142c001698ac441e00b02d00345003211015804060080340d44001b02114158641c1c1801410490044001402d9501d010128003225401100b0440d9005140c0104085440300b4009131070123040c561170050140c03040030500c1c14280790008500030f40e038880f89404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 343678929 1250 343677679 343677689
    0x9061b0204050a060303021504080301031e02040e0d080105120303041101090e25110d0e0a0801020f030907050d1a0c04090603120801080c0d151b02030a1202040e040813 74
    0x100400c0c5003031243c02c0c006201c2c502040e001442088211600c0086502d520340c0038030341058659086130f10759660101c103148100d90406a0205140450700182c030340c0e0040075081c2e03100e031000e00080505890010103500050303215510809082c0d04407a1483c001004032500280c011080e003038804049030040c0c80035107040e4454400c104804082214403498008001e5145a041c1000e280d00c8000d050121141c50300b059180740b1136007021250120701406560403808113034000e001d507001c1694800555007240c00c842055100942c0010400203098014007120002e03107404c542e03c0a14000780d40318071103e07058000d4071000384002d080115a207480d5000940e0020030360404180503003a01e03440d222660312146c11040d00030481c814004202c1c5080031401490410f0040c102e48110003164590620010020044d000c69075522100d0160700c10115103c0a5281d446030001c613500d64171100010a5030156400501419206000c00d00400c8c0114280c150010307001941d1907115100d020400e200380005906c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 343680179 1250 343678929 343678931
    0xf03150b150406120203010b030112110604080c0109090501061b080408390609010c030302070c141e090a020702011205040b0a060e040b0601230406080114060a09061b0204 75
    0x11920840d4050340207200b5141d10344d0702c455100c41812007802c2a404280114100c4103414030050080c00540607e80000502410103585907803806008152243d05ca80c00c802e00c01e811400c140442c0e0358100c6c00c1c803c0106030701d040c00c000940c5095401403e10442c20b4443d0041f012072903c0405200e90142174802800c5240150f40d29003400045103034070003c022824000454502101004151460f9000750508801419003490032103034200449004a40310700407014103509000c40c101198110001c0c201804401c007444194061a42c01c008008251012217907844580d24603140098035480c15951b04000038a80242e1502070520051313460003e410440b03060745140104110500010450242c003d450a0004005903038440010036030721401241c01402007030010010a043d54407070b141c00f400c00820460b5981d6245813040c1071085560096101d000040c480390010300c051140100c000849410460f01503244c45110322004e480c240880c49240c040c040d4070710281e080014403050402c0c10940c0140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 343681429 1250 343680179 343680199
    0x3050612060f071202090a06032f090414130807030c060e100c05040501050f030408072108060a0303120e030c07030f1a060d1202030708030a050609070503010f03150b 73
    0xa81c400750780e402112007000082e611031300400c43c02120702c00c5643c40500030f003803220503605001c020703805444a010b00c1c1c510042d450000710058072001070030500500c04200c0c1c1d1076031000d2520800c41500c040c0b9841940c046005028000707510540804030802940c0310300019141c0b240d03410f058421010407900545902e05181001e400c5440118804460140030b2104201080c070140e4100c4190095010720750201c0c500300150381c806115880030315409441001002c0c078010700d990751164003100031a00300c21456030360b0020300c070f101d83c020006c1c0c0d034000c2054619445c142d2540c0c0300249a040c003c0c1810a11aa9800e110481c0325002d2044881108000c4110754a00d0358a10301a218008108070990b0301d44e8800810404000003840315600a001c001d1006c0003428072600c81d04001006110032000750b10040210303170001340f580c801451044840e241e00150500d400c070b0034405040d10080031601084410401480314551072500c3c3e0094079044120450350810110f689c40041c40c0250009910059000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 343682679 1250 343681429 343681441
    0xe0d1202280302060117150606160302100b0301180821070c03140a140f0408060f01080d02062404390201060f0501080a15030b071b120305061206 64
    0x111050703116807007030342121410780e43d8500d80250010800c0c4061800d402c0203800e07a405410300348000307411980042c02c15240440100c030140130001c120800702c0140c0c004440071030b2048018442d0300d104c840f041d4002d000d0017a100001040d103110540700144406404101107a840300180707915213803688000a400c0c3c1506080e04042c011107aa901c00b24000340c449454440b07031030304410030340d40500c4582e2140201051000020002600010402d400c01d074800e12001032012420802c0c14080c4600340740400281d410482c43d43d003028461800174042d98032800c248078204c0400100c41655500f9008040c180c0c0400324001070141c040c0a50031525142d01134603418510403082e001e80d2036507550b09080c485d603100a032402d85c00d03500148608078446a812800708100c2d40282003255204c0c41c0e6180c009404200c103000042000159001903844200d028200040143c2081d01070211381c01c0031001c1e00c072000b12aa510080f0402d00e11148080580b0307000411410385550078140c6070a0307a8101640c1c00d0740352203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 343683929 1250 343682679 343682743
    0x80912030f150d110f0d0218090a0803010906150302120106081e0a020a080105090127020912010b040e0325080f1209011b050a140c16090c0e0d1202 65
    0x291305003510070f508096000c0d0342443e10315030541e0041e9000d41010315150451403248442800204030501b680680d00382c2c00000783c01400154003901103010001000c130f0800d140c5819004100e9002c0e402d161040041d0b4400c215624005411034150340fa00305a141e60308010111100054240340c40d60f00901828448010015006880001d081c1e944100c010782e40e030410400450028401c11100030008d044403080c01604140d0324070030038003040780541b505010402280840a0340149145240d40d00c600c540c3c3d01b0b28041c0900c1080317074402c2000754101445015009034205000868031200344002e22400304004c0f000060b40c1950155524540e1107240850a504610004407100141e6519210000c114040f0580309002007402c00d90b01d160a0a52048054411613101400000d003a03c0c28000e000e040c006c1002450081d1071800008454286000600001e84101c5161b9100f400150683d10b06540c1f601500b00400c16088940c080020300c07100400da050400c90180c5014480456000083c00000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 343685179 1250 343683929 343683953
    0xd140708010b090606120109020304020103021b0a02040509030a0914040b0d0f11031f05040c080d0f08060904030507030c06060308070c210210030e07080f0d080912030f150d 76
    0xc241e80b000444d640741020401c1510a411703034440541142c40041c42030485550180d80c0c06441070400518090314114050800c0840c0c400103002903000780c0b44bc40c1103003464024650081400030003507040440705030703001e4040c0045010b00c0c0c42101c18000080d0580e515a001a00c0c142c802404c0e4000180c468144600030413120407098940700d903482c211500c54100003404003500c40000c090005d81076003c41b00725001c0e100142c02a0380c45800102d01240c0c400042c048600307000c0c2c09885082ea00d0780c2ca45005030103150002c0105106a00410800020a8003c4100c03035030260b05180030743d00380042e4a4404010041504050005500400e6040401100d64a82000c1d2f407240032103c500c1246840e4031f524041d8504200070340000010000100684c040c1e041280d00080c43c4040c2c64605444481a52602ea50ba00a040c06e80d84a40702c094030b5107402200007600044024045d0500055140d10340040f888080c00d0720178002c0d0a04009441e0420b02c1120100704100101510100e100600301342141c454 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 343686429 1250 343685179 343685201
    0x10b09010f020f060106031e0e0105160c080d0504030504080a08070b0108011a040b010203040503030d020a0305101a090a3201180b07050c10080108061803090d14070801 74
    0x9065822000228000201c0825212019008000d00ea081506c101c0141c40589000750202084000510000c882d41c040c00440301d01d00b00c00045c81d8030303040c404840c0c00b0b80c48035070b04401e114841d00b0900100f66060102c0300680f1140c10046000d481c0c600d000c0f0b07024840d03540014514090f0802c408108180000180512400fa070f4045034180d882c0c094243c202c80d003030000000c641d2aa42886085410315401c501d5840005006403801c20740c2c0da0740807a0071a4440f95408280d40c0d800902440fc0c940c040c8580da0b006402c035025000d00728140008020340f42c0c94860003c8041c0030201e24034400c1e0343c88813030a00c05482c000c2c41c0c041d50030081b0710105889001c1181d106985181202c0f4078603165105146a02205132011800381845142120f40072481e4420101500c49000d00e10700c01040b519144448002118140c1e00c0e00c242c3c1d894001190305012002e4850081c01d0b101c03000710802c0c144008240c42d08100201c6d0000b907210124500100e44101c041c4150105015500000654540c107502c10064a8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 343687679 1250 343686429 343686437
    0x6061c05070303170a141911040603140a0b060a0302070516081027112403091009020a0905130516060e100801060518030703080c0c2b030203040e010b0901 68
    0x51175a00264003501c102200d400c8004091b50005120000001481541c11048000c00907100900001400466009400c0900400d0300e0b5203a1780e01e074a404400d920b9124440300000c000300000c0000007043e81c070414200608040d00031980c0d100340300c018011590302c42001000c5540c130705c1e90781d000c042d00d41c2e900f4002c1090040c58421000600100d0703101250340c10000e206c15011503502d548d01c044100d020404420340140e1003501c0c0901810404000203422242c002130642ca910b41000307500d07e40842e0644104045062050360001a1100c20280f801d5030f102c0710021034599110790103800d00e8229044090309501c52141500e40c100c5c0d204080900b40c6da101e98908060300409000d1044e14403509141400140f030550040016a1150000c0c200101c005485242515402c4000919015298109403041e06000a0903108160100100d1148610540700b41c0303004a1481d40b004070089041443e40300e12070440303d00408141c42031044a010707012540b04510300d0358542c04001b419401c27010300d043c045 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 343688929 1250 343687679 343687681
    0x23030412051005040c09090510090f0b070c110409140a03120b030c100305061306060207050108070c05070317130f0e070918090618050d0306050d020306061c0507030317 74
    0x2c08003501403640710340d0308070079441d011600d407501300d00081c91944c0c81a0ba250080f05020200707103115000b00c00440e40500d065020307a00c8681407028020101800074170030301c501180724000090035520880d240704406c5a00090041060810012144592142d04580d0050b011928105a0849803c0c100f15814010030001c400040e410305031707239402080340a54010181900100014403d8001079842034010b4402e80c0d00041e01607541c0c054030425003102e03000d60031000082c011543c1c041c683c5540712000d0700d464400903444d6102c1e161107203428000136054a40c0c10118510602c0520102d564010380c0c0c000310031040c0d03552140301c244110a800f441541030381c0000070407400791056403900301707a524815480700c16165020850300100020002210002c0c0c036000c01c040c0482c9103a541454a45c05040500202c08254200030b0490b00c081d080544a5120480002d0141c0c40028515501c00c2080e41c4001d42455040c0c21a0141c01c00018010154401c41801208056020041680303540281000b1070305c0e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 343690179 1250 343688929 343688953
    0xf15090518010e0703060803070206070f0813060e0a0302010c060b03070b0c1e0c0a17150f0703060906080a30050414180c0a11030c010b130e0303042303041205 70
    0x6d031007162250001950082c008140946043e100070521a48120341d9429205080c1d035a0070981e40000d944071303041200b40c81c401c101e6541c200026006402080712140102d0342141d0000e000b003504c8600c00703412241d44000d40c20f2a510100002e80107044c4010450780c452920b4111039643c1c440f4802c10741240504001581c040130400a03c242034501e00800300580542001549994200d080308045168840c0c00401d1554800c0e059225008404445103c03001e441d003910040e0941d5030b10340c88410b280d840c0a104100100001c5501c0f0001035005084038518018103161100c40004c01d01818400707005008401013a5030030100510448242d0702083c2c81049080e01000451a2402c0320390240e08001c00018400340300c02e1340200440580c0781407252052000404461840e0003510424405a5450303070061440e1410404050200d050a9014072518400c881d80e2a224003018100070064403810489002c540000d500824492444104a9444961b03030301d84e090000d200d41c501a1003500990907a00c03a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 343691429 1250 343690179 343690181
    0x120c100605030a020120071a030618010f1401050706060e041505010305100e030c0a03091a0304050309100c050a08030a05090c1e0f030f06011a040f15090518010e0703 73
    0xb60f0560140c444950084007102c10f443c00c0c104140340c80900f4004d0340404651041c0400c00790700c803a5000c690841d101c0c5816810b000d12030107160780304920311028400420000c88030503400710541e911902d2101c0103150740001030302d10b4040c2c2d480c010aaa414010040350144007844901d1080d40901d2049003443c0140c0da00d20200c403400e00025045812190f1540100c602075045086000244030840f07280840300a1000d081042c640c0c4104c0009400301401c12900d0303038180100034801000c070700b100d1440c2010396440341e513441080d002a01840d500b1340c440d02c03810700619402c103000360414107881410000d490210700583c01291010046407401f004242c404100050725804040d0151003145500810071000301b1070072141ca6079a5005110001b64211928140012113003500030900525465040c00e40601c0143c0c6c0c0400050b03429402404104000718105015800312514107042c5654180f80c424100c804803820340110760089000d020704907149510000c050304035410348600f0483e41d11030a108070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 343692679 1250 343691429 343691443
    0x51005070507050c060a171303030507020102250c1502060106021902090604050c0d090c240c120210060b130e0c071403090a03080a030507090f030b09120c10060503 72
    0x80e1460b44001407010712410b0480003806c00f510700e414007490b442c100403d030050487d4120b428041450304105100d0400d40c03d03000d1290407807000d00007513081101da44080070014103050181160b086103d5a44020312140031107490180c40d5035003007104802040540695541020f201d15030040c0720707501c412100c6000110b80340403480e900501d2408036455040400c805814082c14070300c12503a0070403040304990402e20503c1075603842403841c0354501d4a810f220403998248400f440d110080b135080240c0505510005090075a0b503c180f101074245040d550403031404910740c842e0703031480d4030b0490b02050f00b05182d001f601c821414604600c030781e0394039a0164420003c1c19200050070420522030781002a2402140d10b2440340c0550403a4148500c9034001001e0105651041d200405d0001d5444640d80c1d05001d2154007000c50300700418500c0c5805608001410184000b0b4084110100403801d1079105100c3d281555405624141c0c5940d21020542d0b280d482c0e0f440c2030340040380b40a600046a080110b100c6c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 343693929 1250 343692679 343692683
    0x7150906121d03041404050f0103050c0d06090519140111030c1803070f0e0a09030e010f1209110307061b0f1e03051c0524010309050a051005070507 65
    0x2140321a44094400000d800b0b69007801c80140003152581c000c49008102030001485485840164000303040c0902049680203800001a42d40c0540148085100002c800580c01e0003610515040c00480c1020030040840c04001003050281d19185400c05800c0121041c1860081034000190851140b80500f2680d002aa46000038024170004086800c1d80d070280c00c3e2903c42c2c1c0070762404102c86c000000d080451a4100d002c45020046c41841030354400b150a55015090700010000c402050b00c1c00b92a0314000601a4104507000307982c00c003058421010381180019228040c40b000019160001240440c9a0103c2c000d01c58050002000e620a040310285140300f0070021009404030b840758010991040001d49000150001c030351041e6403010001d80001e03000b82d0b1410f40782d0001e031114000b00d1280c120a41d4003242000c051211101005d40441c007400110401902e42600c0407005902601e00ba01c0c002d40f0034001d11641d4000d10401203403070a250718002804100360750310780c04140c031540111100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 343695179 1250 343693929 343693937
    0x5070510111c0c17061c06050f0705070807110d061506020606031b1207030c0806040c0f050f01031d0d03021b010c0212130509090c100e0607080304060207120207150906 74
    0x20b20111020004254000324054803a4840c90170200c00640c0540d11b005c0211016940e450402104001c0c0d007503025040801407400626000e0907854510782030081400180c0740c42525104900240c9e1070550315001640c0c08075041c0407414500c0e45c1c0c100c201c07469209074405030084500040e480d20380860800f1005524103040011b221020703040c84541100e03001d0b1003905108000012021a5086c4818001000720100600d454039042c07070324480210603540070728200101d25a06101c00e585220071500041820b20f8005407419841b900c2c0134080c5042d5080f0501030089201c00000f03103078942c000f00041000ca5a4440811784888425402c0f206c3d4000918010380000071200703d0325501b0001030440c8402c1c400b1108015880301c0008040c4102510f042200d0ba010b10424441c0d4100086030038a02819400c152006203c2c0c10041a40e51040d540010240100000028100304142c0e042c0c980141d0000c055100302e100054020b580c543e42801003008840700c0c010b44542c0305109454840c25101d581e91 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 343696429 1250 343695179 343695197
    0xa0206010f120f170304050729030705030910050703060302010e0a060e0909010209030d0f0314090601060c05011104030305070219140105030403031e1b0c1205070510111c0c 76
    0x50310305880e0f19161003128030141d8001881d0f40c1462120146010341d0050f0050802c452031301c0304520f50741705c002c14842c03c0103e00b00701404030450164282c9600c01020b003805503503a5a5401900e060010700d4609540091030481403280c0e041e81540a84c1c1541d1003070300d1304085440d41e901008940340c0f20744203400c00500c3c202c1401d0fa56090102149420010a0300054102551480060b0810511040e02000181408208411140d00d40101103031211600940409400d001c1c106940790300c0c050140d07030140300d2210322960800109500c0450702c2e804100c2c03051344440c0c0300c0c500100244c0c00200113910422081496607180c00952401500301c5000c020460220052203005403450b81009000342c0900d41d880c07002c0c1e64190000300104500e50304d0b240c2e00081d041e6117200b1054440c80800d030200b04111148030801c0001c0c01c5003540c0c0d610360016041450300c6040500c1c06e40c2c54092008080035049050440a940860303169001c3c0c45e1f400c4c1010706000c9011048600c3d0001c5600f404401000031b2300e440 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 343697679 1250 343696429 343696433
    0xc060c031508010b090c070201090b0f0702010f08040203121c151a0301080606040b06120a0903080901111e0903030c0102040603110703170709121419171612050a0206010f12 76
    0x30011f56106041800b091542ca09100403a50092081e4074403907240055030004640e403008002417a20000c0c01d0540c402e05194000c00c2c2d80745014281c160f01c5401c0010707400050700c11044032809000c0c45200600071015182d03807200c0082558450f10341d000e9001c0244680000e92401036a069403c5000103140c1036642c20100070260403040c40040d00080204080c40c01060060724091282c0f03d00e15010074070041c0c03450010f103030600080041e00769034501038020000703c858804443c031082202031407000c0c0c1a210303c1d1038a00391081070301c401e0345480002505070788400d040d0050401c440290f02e00704000b0b074080e164900c0e640700b44400200090700c92100742900581c80700300035801000910b002c008450301c4d03a1204040f81c403c00c0090b11a21141e0031040c084105c104800c90560f00e0420f41401200b8041e42c03a800410500d1209030024200419440c030401d1f00e441c02c0900c0c0b03075080781e0740800504603d2006032459100099400c0140074801c0085030306a80101c1c0340d41214103c00141b51034142e29 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 343698929 1250 343697679 343697701
    0x3050f09011209030c1709030c0904021f080103030914010905120f16080c03010606050702090403020c0904140d181806090501171e0312070c060c031508010b09 70
    0x40100c505101c80071038103440e5180184140500350f8440c1c4c4a10b805135417113082455108003401c480503a40c450400c004d100c07503107011800c01c42850059401c510749444501c0000c1c42c4c0f594010411780c000c1070000c03100d55051784c041080c5048074000e840700d003034041d2203000050f082038000d0308280c007082c5860782c10045030401451424240c00e0ac0015245101201c24645040103000441d50402005e08141449103640900c0350414150f011002007110322724100000d89139010720000a44142d00d0a0b00060a16000b440091000e0034010030300e809a18040c50648898805100240c800c1d2090a4400c07040600401c040041c0385203050481c0d80d12441e00c0581a000e0b00e265101011b96511407100040c01c3c2c089005460280c2202540b041d040845440c60700c4c5084440341c0d4510145224406800e845174021040340c00d40307a6210761107422a40c0d000030035a145400400024076943ca00030030340101036450b0f4403031002200e0102c01951035036640c010242c241d50710300718010f90002111000c10b000800b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 343700179 1250 343698929 343698937
    0x60e070c0218090a210f030b03100b031f050703140402090c0d021608120606070c12030e0603091605121c021603030801060305010f12030804061d1608030703050f 71
    0x414200c0c2c034880c201703503035660901c101e001880451a030310380c0c0030311043c83d00710500300450f48561608210122044002030740e52518058581c61069803088006c84035102800840161584205034280985214541384010913045903400006840d0219200700c4c400d40380060350260f6001400400306440340c0040d0a07059020381c000c080310950810a0340410b000c0d440243c0d0641f0301641030292204825140484a0b10005003541c1c4902e00c10004400099086c03003040b4107590111031451560303400e80c035040e01d40744074440d5810f074005004010404800e1001a0390580988108864903400307603101d0601900c0d00c510721030389031240c024906007002c0f440e40c540704d050b20131451b104540054129205101c00b081e029002540002c0310b250042c06a40e4041c01854010050940f80030581440c105004c004109000070040800203a0705c04601402142d40112103944d085040708050b90340501c5120342e03540d460081890001c0c0400400064002000c002da856054041e10384620700b59034503126000581c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 343701429 1250 343700179 343700191
    0x2070506160912080d0510052d060d020319110a0302160b04030507050d020a02010c3201060e0108011a19030b010605030a0f06030201120f0e010f060e070c0218 70
    0x30b100c9900003803000105911042542c0243d00b60b40c5d0791a100c0c1039a809440c0c00410f002400c40085408011940320519000314410801100c40380a12400302c0851800310001d81065201d01c0100b0741d002001c0c5140d00650044804190280c0740030b040442100c00e440189004280c01c0c1414480b0460b124000e400405080504a60f5402202215650302c0f810202c207840030303000100f0103d112001c101d0100882e10081d21580001e0a81358400c0c0d00007041d06101c490028400c080048500f900c50314a009510300101e43d450b60f1800d001d2000b500c4074002c000e075200c2c00441ca4010000001c00341c2d018805e411044c1010050b80c005034200701c01f4040c03029075076040480b60b0f00000340000040350011004c0c2d40601000c0c0d840aa40341800b01c42c100660f03c041c000000701c6031400e201000184c0e00301910b85e40c480c00265011038001c80c1212240020310480e00d03652410f50901da06414001030740e0b4018015503004000a9200e9101d54200f22010110068004d401c0103610408445229100da10181d01103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 343702679 1250 343701429 343701437
    0x513020405030a05030703090e010b0703140c06040305210c031302032407030b0f0108070f090f03051606111b04020910020715170105120708060f0a06090207050616 72
    0x740e84002007403502ca581c100c1078443c2c1c1c0010a1020406901480c504003c1c06945040581c03541000c0e8846618400c180340103040c03044206080c8922142541a509401181ca06407101868a81030141c4240c1c88a1100c40f0b0007803540011b050303580c0721a910107014030302100d001c5095075a60781d0080c00010381080d090b0780c140b15030300c0b0116882c1b046450f002118540c1d1307407440610f410032900140a9508241a0710300c01c1041e04180c07800d40e40d00403a50b030341c072625500c0d28000c188413102c02501d2910700764004c04518105440c021050180001c1d000748030b4507450b20300120440c0d403203008403145000f04c07001c69001d401411901c940702c11155401e0035050402803006192100a4001401650703802d400307000940c1140a08001c9007080805108108589042240d1089003495050445080c1401820b1190300d80c10700820b0481010041c10000d819804100c4038142020408207000c0d03402194001d002505001000c100707803029000b900e14092b484401002d807501c0f06044000841c50100f00f0300100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 343703929 1250 343702679 343702687
    0x9020303071509110405090316060b03070803040f0806060a12061d0a060b030d0203160c0e1e090706090e07030b040203180f160b0c01020d05070e0102010e0a0309051302 74
    0x1081c0501c0344500e0b1110b031120002100d000a16004041c42c1c402d12810344034501d05010007034002004001c44504680700e402401495240e850000c0c01003414010480e010702c9040301c0803540500010080050b10600c9241c400740b1a60f1300d1019984400856845400145100c010000006802044c0306458802e01001c500c028111030306c40e1160000b0107480c1d450303500a01d841e4007440054407414030001c40940c05003086800000f406584c074810f4171224a080c1004200b14414000350301c0c0d0001c083c050018030000241000c5090303484091046122069802280e408a81d10040c00120801160411340302c0b808801d2074200030410001d0000c295000b407503101c01c1480c0d007030f0f9100d1000f144506c44840100d440c19400d45030710741c80c18034071541c10701c0c16612081c044120348030114240070481d1040080c0e41d6880b024842e4050280c090302104038007980c01c01d028071000c1600540b0f00b0490110070380c002c10949a0b42c0c04201c0da030f80940000640030500d80d40c1c0c140720f0703400c2002044a103440c4620000d0702d8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 343705035 1106 343703929 343703933
    0x1061a123403060504050f0f0114150d0b040e011505040207050303060904030c05010c0c02090c190e0411120103031103040b040504020714010509100606020d050d0902030307 76
    0x741482800410300c2244241c0002c009408040e009120a09004ca005400a801511015410883c203000420456551640d41001c140c0080c8100b0f05485002c0700c585c41035100b00c070009009519800703132030301d1034556002e43d650048010000213544410f43c06880d000c40384681290740301301d004101100205200100752500300c40c04035001502034985242c25980005c445000500950030701ca085507600b900000300b012601d0080e10b04110070355a941140b8114420101c3c20390070031101038035040b0f940f03200d03100e800041c404c090000a0f203d00003c1000c0c1080d000721f00c507062104d2a100c0103004056015295058110350480107600b01414800114214051802082d02403a40840d43d041480b000070008001c2d180304c10002c0003a4104894102d4403040c43d4070610b80200d0410b0f600080481c0300240c020400e0a0030fa4800d405d04030752a80100244c00c2c010000d0343d040c8030034461640 = true := by decide +kernel

theorem cover : BRFrame.Cov 343525179 343705035 := by
  have h0 := BRFrame.cov_init 343525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 343525179 ≤ n) (h2 : n < 343705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
