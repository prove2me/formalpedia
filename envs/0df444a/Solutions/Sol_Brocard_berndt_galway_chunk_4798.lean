-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4798
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:45:46.377233+00:00
-- url     : https://prove2.me/submissions/c5ee8cf3-d346-404f-aa87-d236cac1153c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 862769784 ≤ n < 862949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 862771034 1250 862769784 862769819
    0xa0504030201020d06090c0e27040f0b070e0a120203070303080c0d02040b0306010207170a0f0303181406061918091a0f0a020f09091f030b090d09060207 67
    0x1c40d0750811001c0048015840740c43d029240100340070a03079010120340104500c0615004911910501c991010800c03480c0441454107600040400e00d1a0b0b41c5082003034030510090b40240668140c407042181c00f0b54085240300350780b04100c4d128413415440c2c803085040100c6805000307400d0752004e9000d01c0032901602ca41540309505100d000e24210318050030000f0381c0c002c3d9200c0c10000c0780c00f01c1448038540c1c0501c40040602a0440c9003109406040a880d58031201e40d100501080c44e09140d85044c588030b5002a0491441c101c9802080140f40c40d000780340c200f0580c14a626400b031280452011f103000601510383e105215000c40c0d02d00c0c200034801058000441c02c210401359100300f000005017041c114401c50051074084008170b480c1140391750006600080102d032180e40b0401884800301340b5001a660085420f4441103215618062000300c02d0603020030500281c200801c2c00002c01c5844580765102da00e02074180c4400e403201c04815130701030700c035801460056006501c1c103124055460641e00302 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 862772284 1250 862771034 862771037
    0xc051c0b03070e190c0c06110d0e0f0d0e0a0e130203010501080601060201050a110a05090a030606081b0306130f030215070801170604020f040b0d0605070507140a05060a050403 77
    0x80400552002914114142d44898001e00048003000341d040c50f41441c800104c1c00c01c18061126140041004000f40d0200100402140d680c0d811140001c4503881a10820b48100c3d00c00c201c51000258103650b982c0f00410101d40b18490301b81a41d4056211308004145900c01610000e042c0c1e05105503d800e404008001d42c629084001321440540d5003401024000c041c1a00904141c4d418000300a0a40d5001011004054103001c030a09001c203200c0115400901c840c03030542d40762007856000070520380e0070764000380c03500d4101400420b0752440440c86564010f030381c02142c0c0710180c00409260b121002103695400d19401c505242c0042001c40b9000d0207064400d206a45002540301103d0240c0541650000005501d4000502c02d05601641080e106401c820080041c0d191a60000340400010318900707000f02e440b001c0e08080c0d61944810201e1050b4800000d21661070202401406074204040903610f07581101001c40300d845001c148002e0058020010344001e940e485141805844094011030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 862773534 1250 862772284 862772291
    0x41203110a06020304140312010e130f06020c1513020402070515010311122b03112709010812090a120b0a15050603040f030207031203021c0c051c 64
    0x44140511804115502c195001a282d0900d420700380721461800701c14410583c0204007a140109040c070105044814103c105035442d501c100c5105001e0341218802006004010b0520f820030907a82c0152501c0078030301c8103d03100c072600030b114583c0c030840c00d40d182106588000e2003040503080c960000d240031400f490840320344c038100c6110b52005201c01d034402e95080041e80400d18440c900200422030118440340203020710300240c04403c00c9000d90a810f6070300e11101ca004020703103a002c0d0700f0009000d80c04101042d196010340c01009101051100303142ca0050200c10803090610b00f00c89450f050360f0300c1e0710050220100800b8035100a0f404903075101d620030303080c004c002940c801c2c4204c81c116142c400c0404032446d04122a21805035008400401441e5101c42c5043c002500d03504180e0b035015400030a03498603048541026030401b0420b40010b040054001c1c4204461a055001808200d03030001060081200c3e00039001c00301d890040d000380003da003c025030380406d0001114200c0181e00c868000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 862774784 1250 862773534 862773557
    0x70c1e0e040605010f0608060609040c1110020c0d0219031409100e0f06210a0e06010b1909030215091f0e0f100806010809010f02030435041203 63
    0x15440d03900498084034a951035034010f1000c8071070300e20220000c21040c10420301d1418130400052090080758500c0e8081c654424500385100d1140c2410540c0b00d075444107840c44140d9040100e1f001c0d500c4980d500000380700f0342244042240c400902040d9441010780c16940f94400303643c040703078441d542c16015071072002c0500040c9043e030f581c03000185540825855030907082c0100b9050054a1041c4034000c0d03c184000c0c40304844103025110559080c1c18490000203a950301d405e103540040c00e000840444a1003018008611001510010408408900000344965145c0302c070482301501d850100a4004400c9a284004040d0138805003204520003450806080c50490014031401c2d2002c26940c0020107000d0007410b1420460342c07445034907a0a941c03e041c590000d0300d0180640e40054607207410000340ca000640040c0003984600d450620f01c40b4255900c0c140360504144e001e485521344000301c1c80040003041800d05400c001a0742d60100300f1454103040c540201196082c00242c801e50600251403000d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 862776034 1250 862774784 862774799
    0x221b080714071a072316034506021209061b210708040e0c1207050a090e0601021209030c0306010909060605060c1f110c010c0806010203070c1e 63
    0x29072048542503d5490f50602d03188a0050100d583c10101c041c180f1000e10340440500c5615044540c050030080f0720350b80c030242d24035044500d580c9041503111441c0001c14010400d141100041c544154404d40340700300e4486181a0300344440703545c07203150007583c4002d02852184122001510040c4801080039050407283d80d0714480d80352400721404000d0b0002034208500149d01030040c0e207611031660415041544668030340c10f40c0d00c103d00580c2048241c182c001800550301c1c40c2140e0642c81107006110b002c0c14004005000e5801c03100700940401d01c00e01c4041660260408803500c0781c00c059000381640c14043d4082540b40c1c0c04891000d130580640306d40001d85890400a0900915412400061489541c140b100840b0001c0c0c00c042c6c4134400c100201d034220580044c0001d4200c8130202481c00030345006000000525004058010001c1d010034144040803040d848501252815190b40405584101c012a1213100b10f000060021248140602100c4440040081801d5071000c9600640343c03a80d49 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 862777284 1250 862776034 862776053
    0x30309021c121d09010506030604020f040608010509070807080f0421090512030310060813060f0207050c040606050429040b0c160b09130b221b08071407 67
    0x100342c40164440030995029980901094004102c4000d00445824400c2c002200c4040600c0743d0b1f48280c00200c0492003075961039040314690111820407654a958440e0050300c0140d0910400344030b04003503000603030060701544a65120345026561100141c2c1c5440701e8000b2008003a2003591003800700f040140707400d600091000d12501168680100861400c410010459030905c10366915400900c01d0200400905225500303403055420190070980d600e00b080451403111040240032542400400406040541e0013019600d020300140d586403001071060005840c0d00388605e00014404100400c1950301c1c12054400000c040c05558000d608c1030651980305401c2900644203100c1b0000b0300c3d640300f42c0c04100d01082c2e40d04100705034207a40e00d4001410264001d00040d24041c202440744506c5a0043d98407400d80c00000030b15039030940061840042c092101d019103928801c2c900005c040301010a41030707014400e6916a11a9400e542e40481225040182ca028026900d414003010303000806540703 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 862778534 1250 862777284 862777339
    0x311010b030f0f0705030d0e0904031202030c040e0604050f01141c23010b010203040303030209030a151e090807030302090a030f15050f0712020307090504050c09030706050c070303030902 82
    0x80200801d80a40303510f241050340d2584994400d5102080b42d0301e41c1074000c8a440e04018003103e00142640c1c5500703056a02c11f501c011f0500041e440002088464032510b030140c0305461052154594075034800e001e210844806441e0031a00fa0041c1004205082426030340707450400000c1c04402890700420145054144203402c105e40b9400c21100030150f103403805400b00f2041c40050000c2c0710309407450340041d45a1107140800b07020541c00088030b00307444d1000c20000c0c46c0603500c41d201d1400c003040710140c00e008042020b80e45000c03410408113090210306c1b90245a60880d0802d884625003646039606030000c0d8800d08a0f00d40009070700c400000860024144811468000c50510001d8845140510101c0314000d00d80c260f07402d00c41042c0055580c2c0100e00c520f905601d100c00681c1c0346c0720342500343d0b0503e00340d0380101d9100c0c0c00c0c00100080c501e08900503144030201507080311f03401c98440c071080da003a014440324503240f540181c42c10030120388a900100d00743d5001600665402c0e01180403040d1814100303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 862779784 1250 862778534 862778563
    0xc0b0c0f1605030c0d181a04030506150a0f030305090603280902090709351902040b04051909030e0d030c020a0e06060a0305340f090506070311010b03 66
    0x8100c81e071801e02e040c010020682064900030b034804c40714040000651030319004d130f69035641c0340700a51704612101f8400c490180d50000201c641501d4046c012b00b0024408810322030284020600c0000c0c3c40701800000300541c1c0d0b140c0c80746828103c0d40310520446030070040010401105944842100c90702003145000100441d41c2c0c0420b4035a5103006121446402800405c03c00010103020000d02076031440300b8064911040911a1f4030b214000c141d55060500090700e0070324041c415070035079850f8500071145942c5100f40c0d0140b12801d018000c00084030004c684503000c2e81030006140e200d4140c42d0f408070105501c20300309110038030b94010100343c40c11a10203044003c03a5441b0054019031074643d401800410fa0640b249500713107481e101040d090300840703c049007850703201c001245011005010b4400319503803202101140f0084003032018101c014503045040858141014180d440344910000029120050704040c642203c554007211070346800c00c040c4021b956602002e0200759028000c51100d1403c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 862781034 1250 862779784 862779787
    0x512040803041a09011b050c031c080f070c02010c0602070609030305090c03010606020d1b0b0c121005031e010b0d080d0605030f061f0f0b04060f0c0b0c0f160503 71
    0xc1102c02c071104000181208403080042c4860000d030781e801700ca0b030111105807481325208034941d8a01f00c1d00d00039201e14041d40c94060402c1d0780356040b60060404200e81043e907a030f448189c50b6800d031400c25113801d0317540e000061200140000994040c00d109001c182c46514014a07106058542000b1a990b03e0b0040780002c0d2640b060090002003080b0709803100303001320b00800c030b050700d4100042d5a070702c520058101403010b10394540340c0400700e6245800d5041d030042c03038802403442c3c0704070815581d5020b100603807260128403020401c6140a5001e40066680142c01001c01c80101d01c03461541c2c141c001c844801c42d640f1600b92803070b10780300c0c1a81d0341d05440c82a0322098a82c9100421079041d100c0740c0d00040e0181d40314220302014240700003051030b0003810000c0c80049a29035402405002282d80e00f003003000d50903038500018200304110080c805c903001a0360b074030301100b880c0300b00312803100d40c41c0800380403040c010380400c034100e170b10400030500b803092035126510305104030196a400589040050310941c10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 862782284 1250 862781034 862781039
    0xc03130e10050102010507021e0f060a050f070207360207050729040302041a061b06060a080d0305090102040f030303050610482910050d051204080304 66
    0xd42141e84002c2d0209000030b01880c544030000960300d0300d480c000440c1524503002d015034042d1040c00b80b0000d00034060144c520030303e40024000c0c0501016a002c0c82d01c0d8104c02c0029200c14800328156065070505a00c0d200c0307428210010440307821400c0081c4180c1c0805459603030003083c00d44001d064070f0380f0900103000320b14505500003006080350300f00d100d028000c107404402120002401c4a00b500d0741228002810520000e040010441c0c021525030000400070303d4440c1c0c000004101e6200035030001c119113180c3d032144188044030403544214580780e80711001c0f03483c80b00d0280e00020780c043c00c1e620005041a0350740940c5240100190b1042e40842e41d62003c6c80494100802580714140c0c15003015242620798041000c944503a100841600b080e82481c2d03200d1044221030a0700c4001403a1030404c8040b441404c00d02c0b0907102880051402d0000c1c0c0003400018030700448514030442c01c0f0ba02800f000f0340ba0a0074031100320181c00040b200c6001f01c0250080a01000c8082c10180c0b48481c000c1d62140d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 862783534 1250 862782284 862782301
    0xe0c0c070e07111b01090b0d0906050c0c07060519080a14010603140f0103050c3105150301050903270604060203091002010b100311090405070f030b0109050d03050c03130e 75
    0xc2c0d81e4541d04150070301c044c900540b10b0360801c58140864407480f0b24296150700c5010030700000c0145920040488d070038007052000c82d41c0c0c2c01c03024141c1d500429095400041c2d55803000c0e21188a8601d101400400403182219142e005420046d886041000302140e980161852103c80304000d070088000300f55540440c41d290024107100355402041e41215002a50640e00d42c1079407100501c00040c410038940440345030103805d03070f103800da1002c9214003031885140c68402800d014150840f0400c1d404980451011004d150502509020750f0900c40a507182c840e03806080300309904003008075040306101e008140740c07649440d401040184595030146071640c82d11020040354003603080c40d00c1c085a040680901c0a90b0b1380b042046010380c000d00300000c034150300c1d011500030790103110007465100e8504801c0041c03041d00116510795510aa580400c036038083c00f0010b4444070b0181c01055045000410902c00190254004002e5103051004407070400010104801c500e0f00940c001c1010640d50364140401c08 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 862784784 1250 862783534 862783543
    0x31f0507020f0609070e040c0905100e0601020316080a0c0213020408010608030a090b18030a050c01080601030e03042d03050a02011209050d0e0f0604080106030c0504060e0c0c070e0711 81
    0x2511401503c820b04024003210340d500040c0c0500043d001b2170801007401c101c002c07000d0000404180703009100354074290503001402550b0b445144540860322000421a43c40401201c88280383c00e00c408882c13038815200c1511640050300c0140c00d0260040d51311000da61011420380380c1c004080009a69141014000c0f403d480301c50f03124001d035920a0042a4040303401c15126016220380088a40d15045420844000d42070400a202e41502440d03000505010002c588083c080600b0b8a4a608940302c3c400110200d0314402100c04c0b40c1d40081c002840b40520002c1c130300048034400000e8120400d03a49040100708103d42d0310441c3d003980f04c07600c528119600300d035030030201c52a015000c026485c1c40f81c4889880f40a000c02020820003000e4415440c0d94075121020009070340076150035100c64407000172a0080113180010b680f481858600050b4074501401150305441403041c2e20400780e00c034482c2c001c2d1582c111001402c424003a1b0711020900c900304860044c07040b000717075039040d4440a043c280a82030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 862786034 1250 862784784 862784803
    0x203010b0108160302090103091505070f1e0c08090612010e0f070c020f01020a1b06020106090608030702010c0c05150702010e0f01020d0e0604080d02161d0f0402031f050702 76
    0x40c0b15280041101c0c55020300500c0415104506025a1301c1c0c9040700120018900d5000041030303e02c0c0c03444909404c00e087d6110383e00c540c1c91621703610b641404100058803550301c001c400c80101003030494070b40119803280e20a030102c1841090010300342034409000078415049000015890175607a0010006010100718194102c0d112189104c3c2e20f0901003002800d031841d00d47c01078055503007003101916903442088401c1a91307030014040718900c03000303608141c054900791107540019030a00c040401d900209100e54001c5840450045141440d15070064074400b50640b401d0352034034a070401c00a11070311607081c44020015508191503480703102d440054a191a0342c5d4009006602c4001103c0090360001591450300c001d904140c0c0303030401c2d614000b81c102c4c0704580010350709010781a40c5034001c0d034000844034018420b001d1a048410748901285240c02c0d4809051300d03014020710007196803c410308c4846a00a400a802c2c2e0300b00710080307841c00e502803100041d03003c00036543d40704000000e541030203500807 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 862787284 1250 862786034 862786037
    0x19151413060e010b03180f010e0c0a0b0a080712060602100501060c05280807060c11160e13020306070f030b0a0303020c131506230301060503180c030a0f0203010b01 72
    0x440d040c5144860401014068012035400000c0443c40001d400d00d50009181011007c5500d440c0222880038068820005528214803803c85511503d1a00103201019240312400741c0341407500c81e41e4111115200601600144600c0b600d21f207506103c2809200c01a00b130540040c215089003a07844801c50350160b0100c1c08100a0910390700c0021004950301d40c2d80107941c4130a48400094501e02d0240d40c0c904500200007400004404003084402c1c1c1180c900792441d0346804d440403150440c07060b00d940c0302a80b0f80300e011a11003401e00480c0210b812060300240311081610001e00e46e940440d1030181d0070345001c0040740d0300400381e401242d454024061841c100f6103420448514640e03004e5580c0a1038004144255039803424000c6054541e40182d6000316a03030f00e0054410303680d040c090410181c501064403011010b520213001a138080b01101d04a0f000307950741915540d500c1c000300d04010702040006020740920a0942c0319a5001c0220504450050391007400e0914148101070841e122100070a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 862788534 1250 862787284 862787291
    0x120f0e100f06030b0708091b13110f1c050604090312090809040c0315061115040825060f050105011e020109080c030a110703031b050a051c0305060405010e19151413 72
    0x100d0766200d034400c22782d401c4000b10b4040b44d0f12040c00084501809100e030190f202c0c0c403011600200042548a20301130500800c4401c1049407118030600041e1502060f01501040e07e4007103d0036400406d5101f03071403442c0503180c1c282c100000b00c000901aa041150344030002601d030f50204402e298101141f20040c1818202801412040702c942d685495401504003041d400110004062100300030888001718020400310400300c0000e142d2092a9000840903541e0360314001c144050302e500d40c854039042e280c0503100c0c1ca030a04005041784142410141d6498115501c550001d40010800d0000c0c1208500001c042d5444802c2c0301740c010044691410020442d900c109802c2011a40080c0d161a50705030381e084400c03910a29040c2a86403030f903030b420700410390b01c141c03048814a072040c4d8200300c00004041e42d0500081e202c40003040150f68080c0104510800180040740c884ca03584140c83c881d0f0410018080782e40390b00014050350b41c4209900c627640b040c90701c0040050524103400d0345510001d48031403c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 862789784 1250 862788534 862788583
    0x2040e0f060705180303040806090d0801120f030201090510051602070b0a0e0a21170909221407050301150f120809030d120f0e100f06030b070809 64
    0x49944500161801003803050008044d00b180d44401c0b0f404403401406012655030b241c0d24041c3c2559441e003154030b04454000d103c95101d100d0303c03441005040707900b4406941d420004d02e4071000405900d005044055650f100410340000e5402d01030490840e503400c000052515020b61540c03508500c0388402401c5402c05001031002c080424190b55982d5071038505880311445030000b051405d0300c960030069045000140013002d0b4520ac6410a4080b4481c1c40ca0a06500307c21140c000342e030040c0e01e100c0c0e43c40691440011210207001c10288801d161003803010442c1c02c0c0715210222401e0300c8003901c80b20303900304880074402802c00b40100c1c01b01c42007202131040c0a915140074180b0b14451400b403004a43c4003c04240d0601400740e090f03842d44180101a50345d80c41e14a0380261800351040c0d00b2803103036410542200c062103103503c10800008051700161120301200d004450081010070200320f0010341d100004008903141c0701880f8820900d03074032a446c02d41030480155143c99180704a400e010b00d00c10109 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 862791034 1250 862789784 862789813
    0x31b17070828111815191206200c06041109040519051606080402030c100c03030509010f020f0a03050109050403050f070309180212060907090b0d020909100302040e 72
    0x20402c1c0c0d40c110f440c0a034601006030024106484445a80400b01080390910802400c1803a80c4000d55034200d4401c505200c000b51252155031541c0310f6144a000120801004102c280c3c10045243c50b91a14002041c600c2807101e50b001d4010080c1c400040d40200108410042012410045036808403448a62032426940d143d03900c100c1030419452100d055440e003400c120b0304010242c2c88540600651250076101c070401401c030310046038141c1c13191280114401e0ba5081c00045038405440560307131a402c2c0700458500380d0140c80e001d05082904d6695201e00b840c10320b12031000d4902c2c0303140b81083e40e6494100c0c19009064a8041e00710030850361901e800d000000303812004490b901c00c1c0d501e845944031480303424184c8003200203512050421031035070450030180c19140e00504120001d000d0000282d2540401c0c00600c9508a4503003003c200d0f0300740c040c0010424580548010b800c0e4203400343c81c204000c0e02084c43d015058502d104040d042220900c01c61500d0300078900d6046c00300c001400d013100617a0a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 862792284 1250 862791034 862791103
    0x60503190f0c03060b16150b09010303031b080f1b0f04060504030b18030a0806040b28061d011b061103061305071706040b0a0b12011509031b170708 65
    0xc0087c000700c800300502d83d1800454102d00001a00100001d050350394034240070f40a400820032050641924840c0a12114040c640450040000c0e002d50030041d928060141c4c1e4100007500c641102c2d071800c0c0541e186940c2c1178402003001d8002a034078542c8132851850030180b0000044e001041441503414034a21100c2d000095800200442c03a2400140c2c8401000c5801081c01e042c200d600001c82c21200600b800c004400c1c80c824000c004e01d1001016a9602c00b21410a6403103d460740818080d0140941d40d0700c19996149517040d00ca8081740780500c60303582c06049070706000244c0c128900210822406240040c0e4205103294550343c244091f10308500300400d50b120f411140070004841c18086199070308c6da81d10030480d00401400c82da607500d03290700c005030700707600b060030320070290304a140002c100e00081c0e09030b801100744140c880200c05030440e0345800744000710401d0b01c00e6105007650000ac0300c10b4441c20086108106501400d59103041c003d490741171000070303000c000b2005145140c0d0095a9040744 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 862793534 1250 862792284 862792327
    0x903030804122001200c060c03040c0e09060405070e060906040504050325021c02010207090f022a0c01020304050d02040e100c0503090d0e0604060503190f0c03060b 72
    0x501480d200800c0345400d0b54000c01c0c2c50300252a60b0b800f5291601c10240540c07001801406162065a0401407140d0350507841c030440200010355001800803070360040b040f03000703160024412080b00345030383d0300d80c2c0c4810780c080e44c00c88644d60241d01c808144002d0003400d0001c000070742001500100d2902d0f08002140e410303800504803c1c02641e66100080030b02009200350b55090707401c0061200c003007119044804035040c0d2440c003644100300b4400da415240f80c1c0498004a55503040e00580b000b40e00d0b081119006000c032170f4000b9a0b503a020001d0000b440c02d071341d60206c041001c042d0000015809919607528045080c1040c505550040005002964505c00e0b142c00e50703541180d010070f01c00810304210f410200480e0800c4a400d04061603211850707000406140b0941c0881e0840f407104000410444040304d040c85075030740203902048144030a0b482480150351186000018036001810200c80d03500311405890100e130016520351054885542c140500401041002c0d016811b0404902c40110011042e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 862794784 1250 862793534 862793543
    0x8090d030c02030601080a030e03190b04081e0406081506180a031a060909190f06090525050105270307361a010f1107081c0903030804 59
    0x1150040500c01c903524651035601405544041d69503009540d50342c0c0c0401000c0740171408200e4103161313905000a8540c0356001c0041c80d20901d1103652500c101f0088050400c4d41d5120080043c21503800716080741d021006075110b2029521458a00001c00c280030107044080b25140f520b8030605140c2d100006d81b003c05a000502d1050800b8810000300c0b40e603801c0c2d100504034070003840c40301230402e403030a106480ba10040e034041440c0c6c0d48942c51300e51288080f11051803000c1560003c603000c544200d00d101e0030680300707070300000e5154106e0702d4951030000d244028011107454901503090310000c401c4c088009241c20b0810361300b00b070140341c0c41d80c3c091805020985004110705032880c4140d40d0800104e0300428005030a854590194140c518140425201c4540b0884007820b001d070844e215403003904040c40700045044130b180e207030390011240f841164034031800708042190040c164003803c0c0806401824484010048141e81032010201d02c0704010300c10061200d0840d0800110740c000c11000e510a911 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 862796034 1250 862794784 862794799
    0x1141b0321060a0509131509021915050304110612071e0221090d03050910080712050a0f0f0e0f0a051b060f04030302030901120513020405040f050a030c0c050301090809 74
    0x8901d4400021b520700712025005054035a0b42d020894000d60055401c0d5000352144a440030f640c000103501d5209500c984034018140580c4001d0580c07045001d160001d100c0d241e054420070340e4400181c080e0b00180540d0a080380c0207000d001617140c0002440e40b900b6660000861444603c0402a4568080001d508a4080402014008086c111040700c010351401840d00d1141025410000e0440e0840803c0c14081c000d0307151f0030500c4501805040344102256501c0440060000ca20796001e80070180644010686403c0b089102017080c1c0107104252124103000184200314544a51a100c09881c204102b508002151000301d03001003a040034160b01022180ca906402c00080340003403040012400d0841ca01280210405901100814000d40240e8491044125140f0200111101528018400c184490029006042c2500419402400744d19041400a031a45881d0b040041c00402140080c4007581d0303c4082055210000f8080c01042e0300030031205540d55105407040c441c010a19202c0d030315 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 862797284 1250 862796034 862796041
    0x11808090406080d02030307080a0522031719110301030317180313090f061427011d01140109260d0f110102090303030601141b0321060a0509 62
    0x89980102d0002d03d0128210341d0032000200c1c00a48a80050321244000f07034030702c0007041c01e0b100c060285900543c01119184c81c14000200845408100400d0441c01d0003407485a03000c202d50140ba82c40d11410706000702c0c0700c8032202c820b2524129591030b1b04000d01c0d02811700051001c40e61002008603055111200741980352200490100c511101403d101c075580700014240b00110b00d0800400c0442c1c5200c58140030582c6003d44082c142e49883c040d1910280503041d26000c52700e0621409044400850021100da400051420780000c42c04d0700429000040b2080189210001c6450b4070b00501d103140000211018000008202c1512846100c40100810300400d6280e0599070401e02442d000c2422201537920090024003080c074241c0c21400841e100e4400010b40345c0b010b0003110754450008001c2c0d8510740d144c5006541078117000b081903000800510801e11032940c2e180c041c3e48054a41d1005580b50401c144a1700d00001c9030712800c4801040c15420321040d038940e00054000e49004451820242c0d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 862798534 1250 862797284 862797289
    0x9050f06030f0a1d2a030f060604051e0c1e04060c0b0a0204051008060f0a060c1704180b03101b0c030e21070605040f090203060a05040e010c030e01180809 68
    0x313099030741d5076409002d0b42d02038100712032403001740b000d5050341d15560302c1481d4440000c140d00d444a022990405400c40f00c0000c00501d400e512195101114408085a40460310022202c0c000c080700e03000c3d0403080000702811001c4d12403030000b05200305131640c1403500d41400001004e9208640c0010b0901031030303c011695040c400d40588000c1c01c0040c00503560780c6000c8200074506841900c0c1c80b07009065010045180342406140c110a84009440e15400d450305590b03000c0303040305c100c211045145020702c400300344ca0040340420a280c481c0b03a040400c82e01040e8040501300120914044410303450724a00307072990051010400060900c41c100100c2148081c14190380140503062042c0c0e000701d031240e10352070b900d480b010780d6110000b00c0402c40f404a5280c4000f506c8500c2140203001a414240104000c07094440d0010743c0d20010140401000643d40c0000c1070130346101100e4241c250351030b8110046616413501c600d00c0da40c0742079402444801030303c40040120304268100504524800900207800381c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 862799784 1250 862798534 862798571
    0x70b0a0c0207120606030b042003010e12030402030106050d0f0b01050a150c1a16021c0503061e04091101020105071814042301030201140408070b0304060e070609050f06030f0a 77
    0x3c40e0047d1010000b840d0034034003c2e0022089400461780e445103c40d40c2c43c0c4034101445070b20300c03210f80d00c4000c0080c10a5050305100c141c0000f4412680f540d04c80c840400c0d10b8543c1014074032650f02c2018800440c641c646007036484450141c00c00c2d03016219000081125243ca04140003404119040c075900210f20790070040d0a50750b0006800b01c80f80b0188040c856941554022140c1000d00c0d5420f440300180240707209442c00010200000000301d00b4008200203240907504580c0c400c1c05c501110308120301c143d0115003520b00100341a620014040c2e07441d441540c0a001741c40c9d21940da0303e030140344001402d0141440540034040d5200c1140b220300e0302441303a00c82d40d00000440c0c07035a14081e80d51040d04128048102c000f400101e0008a010380da00b100d401c44c1d00700741d0302a201c2041c05406000d040c0480690590401001500e00c40c2d1101d000082e42c1c10180402d1000d412259180001c003420141440f050002c10000ac0340030341c0e170410801c0081a450f0071125004004003202081c281d20a18605848 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 862801034 1250 862799784 862799789
    0x1c0c05060115121505030111070b0c032a0a08070f0903150204030f1101030b091e070c0b0708091905061503070e01092009090601030b01050d0e03070b0a0c0207120606 73
    0x519280180c0511380c04500c40c811011694102c0003130200360780401d81c2903081e0240d0308004108400300e0001c0360900301c1c0b0a0142da4402000c19105000001011080e84181c551b010780c2e8004a40008109603082d511114290340180d00d400c0105051509503c01001001e00c1c0c4006092180404007107006810150121001140c0290014401c5400d5042c00f000e480d881d45031050200c6e1a0004400040c1410300315a4461100309003116060302044640a0600301c4c000c00003410011800c10400000f481001d42e140220100c1c0d440747c58901d454004245440d401c0c42561200011410015000660016400b030740318041050f40740401c029440401c1c038100707503508025440c000d01c00002c6040400c5502591058000e075411081a0801050103038072840b072004500d8100c0c0440e000600554001c4e002002c8504062501c90310b842c5442c03a90400f1944664001001a00005999824005148030942d0040300d1520100095045001d0103940c80d10b0b5442080b091100c240d10b030105101d03244e03206000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 862802284 1250 862801034 862801067
    0x50a03120c1e0c0e01120c060c020f0a1217030c0403031d09010602060f0c090904111305070c051204050f1c051029061c0612051c0c05060115 62
    0x4040707091401c81800403443c001c0d04100300301100002000c1c040d01074040f000725080406103c2c11801c100d0100c49c0c02c004103d0903a00140262200300b0603451b40b0190318001d02109500070005030f50341c0b500c802804a501c4038540c405809106100e810030418049804407035050402030b91407034150303820407100d0b00c1c04c440d8a68040c3d600000051100e80202d009403180e092401102415640c3c0021641180155078009800075000c0740000c000402d4403440b03000220008014801502c44607401d0010389104a40510020b0000801c0604001040189107112050344121070f00301402c21002c030311000e600100f010310030801d40c21003d5150180240c403040250300f00c42511442c40030243c41c00c02602071607000c000005c078400c0941625546e40800c0710590b0b0b0000300424038003a03482c21803d82500f881003100c544290360344000101c2101207180c0da100e8504ca07070302500c4c40f070211180012410803400c095405201c140802c40b0005000030a0300c3d030541d904030b0014540114225005c0350300362a400207182 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 862803534 1250 862802284 862802333
    0xa090503060a0e0715120b03010b3a050303040209060d060f06031406091b060909010914060d03090902030c07021806040c0201110904020705010212180601050a03120c 73
    0xc081e8100340c028000f4185070310100c480084c5c0c1c0d6055a5a410f6115007601c000985d295400151a2686e070071003110003c0003800031480d0551500055220680580e8001c0d5000844641c0c0075480b44030144440341880c0c07035903d00356104c140c2c1c651030740b284030003030000740308a2042001404959030310a090742200d400110400c01403518512620041c404c50005441c10b0bc0e43d003181f0a0b211f84000383c0c0c203108298140181000c0c00041c80d02e02200b12810010603405a002e010030f50240e02c81809450013000c0701c2c040818400b03140e00490701512405400d035801f5041030200c0801203500304401a007120080c1c400107903079a54201c060340c6d0364010214029808500890360a03541d03406000d04c00c0c0202011542041155100c0105908076504501d040004950a0155628900e4546e003d010040d0003000094617141110400c8044440101c4841d11100d240040724000203104002817805000242d4400c10240c0c00c5032150084212840d010404000481005a041006c2503100c01d0b07144440c01d4496 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 862804784 1250 862803534 862803541
    0x1b15060f0b1e0304050c0f03070504021201090e19110a09060603020703080f010501020a0f06060b0406021c050a052203020301020f090112110906071e11010f0c02060d020a09050306 79
    0x1000203500c048942c00b0000a071000390325024001004481c000c1d584a002088080d024130300740844803408185c40c6034140603d420008894555000409101e150700b05035800560400c8011400c50301684185180c5a01c030400401d900410007000601d03291308010034010000d1140002065205182c0001044e1424040002085a0142c0140c080386210361600001c3d0b43c0c0c1c075000403d01d60346c24411280180d0101008001290000c2203600880e03004100c0441e4650711591100080e0b4806e41c040302c0140c2c00904150340050707299461580c68121494212300d00090420010300c0d901030104402400362802d440c0e0f01101113b04007602c011035002d002503403a080449000f41c01c5400c04016240490a00d40c08490003859074811641000841c841303080c2806400e10500c00250050300302203820b200f007900d8021601031170f07103004507a0500c68500108500d100c200014000c075024440c2c081803094100c0b104005980c0d0070306072640d811440000503194052088202c80e600700c1036001c160907000c2d04060 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 862806034 1250 862804784 862804799
    0x30907080d0c062405060c0102160b04050f0d090501031107020a03080318060112030c080c010e0309040c0e151608070813291e13030c05011b15060f 65
    0x241e14010078007004400691014004100b404120501a121004c40240440d00d4944094400d60800b240010706003094913070034000070501c4070741c00d03500701c42c0203070030081000801c0040c00421007481c40a00400215950041c00540c030354060181450b484400e0a612124107030141d441b072030380091242c018a95a810403032026441521640403400103030380401e203110700009000c3d04888425180c00c024242c140c4048440303002e0100d04030748000041200e88082c000900034890011400400340da035540d0b2000400045502c1d1001035028024004402d1101e5035440c0c1c003a24100d10641e0300d0303c0d034401c0900c2d0383c1c43d02000c0c0302d017005180c030b0008203502e001d00600001a14807030780b081c40303100c4070541c8030700e842c80003800c1350018dc400035114047c48071140280c0e030019040700a0308001c84520307a0b11400d458420b0b0b401c200c0c0d40c0245241c11900810600c203214201d00001c110a00342091381108041c9002e0a00d002044050130004003000442010f0380d456001400911981200c0c800781c0351607810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 862807284 1250 862806034 862806047
    0x6060501080903091c0602090a1814150918030c030910020106030203070303030207050705090c0c07091107060509031909091a09060d02130c0c03091a0f030907080d 72
    0x10a4002000d40d0001030040c44000100d6096510040110904202038640f81101600f0580100c910940910801c1c40d19120140200050180b251605400c442ca0b00c3c0c00f441156402041c070025003820724140405203482c161401d222840560b003048544d6a0504800218603811720444114071000030001244140840500b0000d1000c903004415154041d0040b426958a4040694507810120003080000c1c003990007480c041d80700324140d0b4005551503000401c203000840e00c06445030000a01c90100001c00c2c01050701401407060100110f00c4603290300107481c041c480004011701d64032000310308026070400c00d690013104c00740c001c902c05000490004102c0e9585128985549040c40040c03150344404030000700915902400d50503c550b941e00030003a46a01c0e40100766000042d40400c07200d000c031540543d66098000351034004118400d440c008040e40c1183d4440800c121103042845083c40f40704003110b030080000e6038101d81f6921040100350a080c4c2c50790040c07440d4404c800c090883c2ca038204d017 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 862808534 1250 862807284 862807289
    0x70906050108060306042118030602030a150b041512111308060c07081b0706031b03060e04020603280507090501020c010e04020c101d010507020a1a0613090606 70
    0x90390b104081d102c0b8018540e452005903002040394080907001a1420070800c1100e520075006d19207405205c900a8260416604c103400903070701d0940000030807143c140140620680314220600040380030f072404404850382c0c02076004004113589803078070b4485128803500c2418503000070384008102441600152514551120b0340030a9495082100050341c480003107815031080c4041e130f5010b032401469a031003803090f5001c210310300352040b02600c030448902d90410007100540000d440019400d0101c01c1000039848605030480c041504114051140a95043d203107508140c2c103541e11a00c0c0d032202c83c0003180c2c035107401284000516100542c00e00351045504014002c04981e100c0001c1c0320384903001241ca503180044050702042c1010b2226049041a600034901c640c880700c280c0e505a007552801605980c0c2429011058030150b811500c0750390000e204031a008a8603000403c0d080c4620707603c0044420241c1c2d1601505403500b00051056110b200c400110f4400401c010401d2200c2464508000d08450 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 862809784 1250 862808534 862808537
    0x60406091508011d19080d0e071a070309180e0a0302030a17160f031803050c060601080f011e1d09010506010801060203072a0f2c060907030e0709060501 67
    0x100b08071850710381e64040c40c82940c01d0064510020000a8001c005c13600c030108513600b006c1080190150050392183d04c0903041c10340c016100907072030045080c014072034101144103002400c2014070300081e0482700c001c1c2107941e58001c203110b00390782a04040c010509039084412a01458400004240c0c0c080300402ca009455102c0020900280200ca241d04000b20307441e50590011001030300845004402d118054681440c0c049000c44d1503c801c0220b2104600040300454404190105000c42c107108069200c20280f170304801e10700d012040e02c03031244411321072010450500910101ca01601c521220058500146401360042400040c0c071142042101d14000742d510306808100258402c807000c070304a0788617500650901500d03484a4104010402c240280e501d402c1c4450f43c8544441d92060004200b81c0111395225440e210355103101c254400705d40524062107622045150754041900c681105068416240f6503036100c0094004250355902480944547d00001030050000e0304840240d0360207 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 862811034 1250 862809784 862809791
    0x1103010c09030b28050433050a14010302060a0203070210080103050613050309100e101e08190209030114160909020310030f0c0b04061e0c170306040609150801 70
    0x4e00382a40025241103510542c0003207213100e400d5000060740c0207260014014800810b403110880420b13583e42c0d013190000c4a02215200402d9103401701c0d40300c1c299110048480500005210070304001e82e8003814000284a202c0101d0011842d0b4420010341350700983c090040c0980c5600c0500241107940301344422075148c411000042c040203e8001e00304084c0790f2110085080c0100c0c0d804001c60700090079900d0080060198401d0010758401d00c2c030200c0c1c88419219001480802e409001500300c6140b14002400340b00810700c80c1a902d414040b131070540040c3c00041e10340244c1030001e405080c804005100142e84079041c40300c2c06000c101c442d800c81095803140351050f0f80c1c1d288054164002100c00b03214102608500300301145903041c01c0703120a80320f207019a803da03445803503604958105411100010701c2c40e04010004204c14040e8900d074040c0f600b00110744008581da80130003004c0d80c0d400c41e080101d0220215031591102e401190181c4113000007400099401c0da190002c4826901c2221495802c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 862812284 1250 862811034 862811041
    0xb03040f06060915051c2409120225050103020a0e190e01090c09120201110f0706090b0426070906090f0c030504081206010c021c020f01020d05161103010c09030b 71
    0x1c15425a010151300d1941c01000206240c40709183c0c51f40d599a2540c0c14500035591040c041214814400c082d84200300c041024609000003d20f018403100201a682100321030490000f983e0341c54900880c1c44c01d1030b01580c0c80d0441c00e0101c9003165502c815540000b4440d08500c0c41030070030300345e0105a590070301203440e0681e0785201031703800d0b100090300c041e01044000906000400412030741d140030034010f040886041c15484016843c24150142e61001500809414000d10b60b204003004001c050003540c290409041020804c511002c0d902c071030480c43c2e05220518204101484180002d0030841801c008a0743e440d6a0b0304080c06980c800d400181d4034005030701207401c3c068800c1900030354001c8042424005c02c9280f00b000b052007c0c14440c18410314202920050b500c180c40785490005840c4100c0300704846106202d507041a0f28500da05540010700c1d0f0382e20311644041030728580361401000f120320700c0040c28580126a0340401c4a50194200381d1080c80c500d800c50888030440f882109000403559 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 862813534 1250 862812284 862812289
    0x41205150f1308161a040510050124032706050c0c120703020a0c0b0d1a0603060d0804240801120f02090c0904050f07170603070b03040f0606091505 65
    0x120864085003000452107840003c500004090040000c03490900b030022001e90711140d5801180c101d5000058184800f00000c1001c01d02203450044a1010140055410100c181080c00b0510b10000c1c4003c43c80008803003014440c0d000900d191020001d68041d12540b28100f21381c0810516003a180a03080001064603140c3c0003088860348501d96018001c4d03007240303058680310350f0300c24a41030b0110b10a83c0c0b4040045480d0450100003004c5d0307070100a590b0b042d0b40c2c0548054900500507440d024205241000803507d40c001180d9003c80200d842c0000c00ca1249003003991800344c1c0e08403643b4208000e1903c084281d54000c0108074028540324100d09aa03100200d1104544107480100b141121408502c010300b05000010b1301314035041c00c0c16080c90760242c04501110003c4030010f0399001c0c40014000340c40c0e0061247c0f034050b5409580074030303140781038404203a50f4580741c80780e00303514540000010144001c00c08228110342c1d10050501100f80c0c0c2c4d4400c2000ba041c030451152081e40954400601b52 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 862814784 1250 862813534 862813561
    0x5190b010e1305070512070207090e0102070221010905012903060903071e020415030605180601142d03120403150527100b090906010306020f04120515 66
    0x2031400602081d15142201c00c282d001e840050180f200703200080c01012416840348111601c600d0407607000b0600c2c00c1c43c04503002c0994200341d07860740250348100440c02c09a154010b511100080301c6203820741682d51400003034018850514054819445c0020440a40040705090058000304c1c02c3d00e00d140601950415456000a9540100551042024900042c4403c41d5030007212000030712004482c000c0c0c0c010800f03682412590308e1102c05c01c940c06008100311440340f5908030b580740105003004210201c3c0240d0303510041c00341c00b00020400d1103014440e0b640000016101e44000c0751045291307100c10302017040c603048900c224030a0003031b140e04840201c0c7c14019101140d40100780144107812800036540180400f510403048480940400d403507003102c049442c0c0400c42c0204c001d054481c8070142881c21680b8000080384141101800e03c11104000503406055941009005958280800010986210320381c0101101031030381d41d244040c0b05c004100241904031148004100b81e45541e49403100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 862816034 1250 862814784 862814807
    0x603021509011b060b0607150606030b01050403150213082a1f020f070621060302010f12060503010c080106110705010828060803190503011d06060d05190b01 69
    0x3403441003064401284402a07510f07682c1c02200c00107070920321040821119449620700b80d691214540c0d1510b0020414071906c00200101d207020419001c403a4002070032840f4910001d00710348002c40d0021700882c89a07049603c04019190109011551550b540303807901c0442940760449411b2081c039030081442614a100b1503d0002c00301c12003c4165030038040c245400c440c200b401c40c0305100103020740303072000c0081d407024100340d890703480b02c1c030040480010100013248a122526820901c0c1000180d0b005074821800c01042d0900c16500c05000e10643c00a210715401194950300388000c070740d0316540007141603040c1c40c4140d54011000007021050303a550031941c81440d00080c4401d000410f1a0702d25620300729610500c691400d64900c010340c0c1d5a00ba521035401211894200081c201d403e540c040004032014003080c10403c0c00d40d858081780c034410340050030311258441000d0001403582c0d580d000490b140c40d69014400c20640c00d005441008003054404240b040620300300c1040100d60203100304540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 862817284 1250 862816034 862816037
    0x20a02120607090306180f05281709150f07020411031312020316050f0705090403021b011101051905100b03241c05070b0a02191410060302150901 64
    0x4059141d0f45d5440010314680c245140041a014000c01c001207449540b220258043d4009007a54030b00c01c171081c184601406d14000c15042000024000500d8240341014130184100c60b4548800010010500c081090101d40001c440006a9081c40c503284c04c024000300c0303000f81d60410810404d03500b0400030b072000b624002552205000c1c090700141d440c06620b204811a4815641800381040307984a071280e14201c21035458001c1c800c400410f6208202d9000100422142c41c00389007890f441c040c0d03d0705203a22150300b41849e000201c0f815039000e0781d07001506210101c020400740c5407035012a0044005070140107034650070300003c05c100a00100d030755410f0340e6400400c103145407100003da40320001404964a0848615214a0107030343d01c030b450104009090048419905d040c07440e01904103020380d0060b05411809010351b1200729800207402402e040c51050071010080c02d03003007a90b0400c036000d942c0e4034140325036402e20040d14813035000b00307088130b00c25101c1036054200005106c3d080e01070580c0190 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 862818534 1250 862817284 862817297
    0xf05060303120601030618020712020d12110f0301030506090f1c0c020f0303070b041101020d2012030108011a030a1a040606080a030c030f020f0d031a10020a02120607 73
    0xc0001ca0b0520320160400e005040000d090390381c078255980e4021040507000802030340850b40c58144601996840040f0304140701900d0300484d54400541002c450b0b0b240c100d001a0784005101d400049a012103940c81d51000c0380d00c0d12985d40c2c1c0361403942c0e0300017219140340d140502ea40c03506d10000b000580340c003454517100c140721607031042000448a560001500303030390189100d031a0004585050004141c601e000d003803e03499a141c20b04181050940f454003460465010f100d1a404107a8040c0344549081110700081c4014000c0c03c0c11039140a0904400d515840800000007807421015804007174003803001c0d0040107800c0041c10405480b040803403005046405160a984013403164821541c0c0c0c086e10032000040d2003034585112916100d40d0b001e00302c000c0f0b032444040c401415081441c3c0842e20400d84010007800a1a1509036200e00359140401d00349a10707100011115031050b1000c144181000d00845000c500306c11009580381c1c80200c00b60b00464000b100a6903240303020443c10b100d80c06586886d03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 862819784 1250 862818534 862818547
    0x20d080103210e0406090920060a210606080603070902040b040b0a050c06100609080c031510083f1c02160605010e0a022107020703020d0b0a0f05060303 67
    0x281082c69031804600030801e805407680f2142e52507100380ca015100b44900003400c60341c140303000c00300c4102d0005502d941100c3c846446415503501012034400e900f451922401c04003848020302007041c6c035030783c0781c8082c03c0c00c0201c089050f0703a00c056803030300c10f01c004c03130440784a1941c907034105c01203109500030b0600700c4000b00410700085c2100740042c0100d903818a029881d10628802c0c445c103181e001c7d4ac4130091550a0402000840e13030116540002d85100d101074440311180341f0000303590740000091400007420b910005000c51600a06a000a285980598441c0c400100e407440a03001d499921a0f01c1c0f1044502425601150b0070b01e80f400c0e4000081181e1904408448500d80c2103403034112462195004c000c1c03210103400100c01c08107420700c5a4804911541000900d1142c0040100510320301c178414408144000074600700146030108505803400c05413a1480e00b00c0c2401400c0c1c0004e90030881d00c2002c00100030341c6144d01791103103032070420030402041c60481c44801d480080e10325a81c55401070001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 862821034 1250 862819784 862819823
    0x10b0427060908041703130902091c03140a03140915010b090307090f0207050c1009030623010b03071106010e2403120d0b03061308030703020903030d050601020d080103 74
    0x2481045004025281c2840d5403402c5d41d4004a0810560022035003001c548542c074030843d08408006171821940550034601710388040340598118208042c4000d00101e01a010b040c040d0350305c00121075207010343d65904d00e007070300001d0050710011051300c0e9080d080100062840202094803c49800340d40600384469103040d4202699410100070142c0c94010400300090b07a10144c400c000400c16921000742e03c404080c14401d007003803807130048035000d842e18000d0080f20a910012003030589a000300d0000b00506d00036140b40c41c0f40715000c81e030704d80303034000c80000320f01e401011002d1407180c01a55074925078100780f2101180c0300e050a202e1243e8001000340410300b0085400350581401e090a101005042e6034040000d04d007119111403408103050009081241103210701a014031000250000c18003030400001000942c0c1c1d4000e0040c1c66588040041100f039480f94040351914100102102d49070038041d10203130300501d416910140175102c0c0355918800c41b0701801c141c81c101d03500200da000100716100c45 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 862822284 1250 862821034 862821041
    0x209130e060f0a1b11060a05100b0f040306060b071430211e01120f02030a0c090f1b020a0201030209030c030f0307110924010c14010b042706 62
    0x2250f02c40c103803900f0b90005004001206807071408400d40c0e88200702c1000805441c10b06c0c03805070610030603d04000070003031495103001892040310361a260140d507820345901420318a028a8000509140c20802c0012340390540501809440b40a11290b2050001c4255a40c1e551403140181d40a050070b5040002003810b02c0d03210004031a02d02c000c0706407908010041c05103148080740c2d41d0300e100903010410b1200c2007207486c09542c200d0309581d003010308650400b102d0015004009000030301c120386000e02e001c00c5480600500141c0342d4001e101e03d210a48691701032014080e03a0158140c050700c1c0011a4211080d007442c880300c1a4810303005000340c10306a80044020b94402403005805210310404807420391410003510040c2c40c00b49010b15221501d80c545041d1340a41c01c2d0301184100303420320511482c20112400b01d1329100c41d8007200c0d03901418150040e290b210104a0141590324452511510b4040642240d00306a0342101d04001d4130b95584c8014041a800440c502c0c8501c4c5036540d100005580e550 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 862823534 1250 862822284 862822291
    0xc1f0806040f09030f020606010203120c0903030415030608100204030f150b0d030e030d03090305032d070c0b0105093c04080c07120f060209010c150209130e060f 71
    0x20804500c21002c0c40e403450a480d0165400c8001420340805006025130620131190440c6e42440914034020780c5001350000140040c282054031000090112200e07030703041044078002c02001742e0034940103035503030009402840c0f42e2142200ca0300608160b00c4c9504030034404c41301540c3d0301c9134148880324210344415580b40708000c0f0b4491515034503195810b403136541000c0c00ca520f91090b5241d0144917001014035050405018090003414204a41c2200103034100042c1c0307074000520b01186050048101c14080b5110a401c1400d080c00c07400b00c00d0104450b4840c4c002c01d1101e0061080c0c0f142d81e41e07a401440305010084660303c1e030079035111011070501e405400f145c1c2d041803484c040c2142d140100040c00300a100c01510200e81424002071340c24913a04050103144008d00e84000c21040300300664036800821000d4640c01800e83d43d00007070f007410b640e000311415400d280d00300c4496507a0f4000e2100c0340000758080405144901f03d10649080c0e12209405111900364101c4040c0c4210303145c2c015000e8040e14080c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 862824784 1250 862823534 862823539
    0x80a090f02041e0f0203040c050603190c090e070e13090203030f0310051507020102030f09180703020d0f05060a0b0304170d0203070305010e04020f010e030a0f1101020c1f0806 77
    0x94624050b81c0d4502880301c2e059414441c0d40005030705101a1012280d20041400401e8010f004000125441c0a52841181e0701035400540d203a80d603c0102d8079010404410040c3c69141584030741c18140d01c945120f0035a0070408a406098540300b02c1070741c65030302042d00305130b120306014641c1c04840f2994000c4103489102404403818458584200c50454008072000204000102d00405c99450300c850898040c180e06004075151154a40000f0340341d1041c06c88044601d000020038060703e4847c3c801080f24651080074103546410a0400200698040c1000d5451141030125806980019104680c05900700602c0c41280c0c2c0c0c503082d130151660300010000e540300c111003444c0c8541040c180c0000d01d03096540e03600040e6686014400641101d40c1030300b04121001d50001000300680b21810144181c00003420400c082c2c90100c00003d140c2040804003c0940c032030080d0300e4003002001c035a8941c0d800d0090302a0f91110300726030180a51214a4821190311410440003110110300600078141c00000c003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 862826034 1250 862824784 862824803
    0xa030e0a031a0603070e1005010815040509011409010605030a02091e100303020d0509060d111920060906041e0204111305010e0d062301080d080115080a09 68
    0x4a0301c0b00301d9225051182041518110740800000b442c0074001e0801600d6151841c0f1058286410710b80f8859404c5e02071a418400c04101181d10203942425003011608014018065440c00151080c0a0404030348a03520107440000403529910041c002c10064450150042c940550b2a80801c0382814001d0040c1c1c0d00c0910190f01d03109465048407445110342c0c1d072251200b03c0580f0750b10780203152900d8146024100308090008000981e66041110018506c1d070a011800c0c110020b03d4250520462a0090045103c4c009143e921a0045112402c100c0c0030b4035400d6460000c03100d1319440b4007084492110030703009a0000350002c0c0501c94584454244903100100c0c185584e030116040380c6005030b04288001d808120203140380900000c403006000e080c41c0802064800c100030460b4400d042000820180d2149800d14103551102010070782c5440c01840c411055030b64010182e219000714032884005448400007003020342c96603daa52410050343d4554034680c3d255484000148035040781100c1085a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 862827284 1250 862826034 862826039
    0x20d020c0f06011a0f0d2004061d0a14011d0a090f180320010b090c0901020609030906030f13140304170106031208060a030b09100506010c050a030e0a 66
    0x1010084400018007110042580d54148040032402d034030713800d4401800301c1040081004040008042e140445005000407401240b10340002411081e1005030003034080300840c00103200c1e6403000c80007561600242d01d40c0c0705070f00c04400340504203145025040000380880d080c04400c0d48540b0020416410002c40f401402c81c3d50000280c01e0300c210381c040301c0d5941d01d919440d1005d40c014815403140d90b00e01040b0390414946076802505020b02c80b240045429a0f03410906c08251003908005241c3d80010034011040c6005203100340c20350050701640740103201d050006007205000008031502c403a00103002d04d0075603a80075403c0d080300e44020f0815200ba600c029043d0000340c2c140e82410a881c100c1e802450b201c2d030400f2005600d0207258148540d95a041c03410400100d4003180c40c1441d60111840c21140a5130341e040410040381140e40020041700903401002218000400d4a0b1540e854000042c80350351600e41c0119410030803a14080c00542102026000080c0905150000c500c4090920b92005a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 862828534 1250 862827284 862827307
    0xb10020105041101051c0c050d050603190b1008060c2d090f15130e070e0d12030b0d03030c02010623040509010b06041409010b042301090f0303020d0306080601120303020d02 76
    0x4141045100c0031400106400c62741d481d6a0040c02d500c02c40a030020881003009088200707004a5600025010760700a10104154403502c2c29007202412800e011039003542840700b810705069010302d41d42043d100540d20f0880c10100341410705003a103680f841d5203a080c110103004115002072240c819640c0201d0030203840c20450100409844502056200480058642442810001d10041900c0104a4420042080d41d5104543d400f41141c011a40b940d240b01c103104207900030041d0351040c1d54072110000d01c0100709545a0040c0d03102e0601036009010066440e18040b0b0031100c2c09105144c80700740c0072403000d00c500b0301e54005940319000100110b000c050000100741558000d070420700740e01c40314102d24401c608203c20680d0041802c1c4074040d02e05407410000600c440040c1a24402c1444184403900c0280e105800c100f0103481481c082c0020580e59140180d51025603840710320204e07080c40e1b8000b402d020003180701345c103c0703d0043c3c02051082c02a81c00324001d60210aa040f40300754240221044d91 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 862829784 1250 862828534 862828541
    0x16090b0612040b0604050a0c0f03050a0b060309070807061d010e0411031f0506031e070e040212070e0a030210030c0504120f050f1b0907031e0b10020105041101051c 72
    0x2d50044a91094600f0440144070a40394020404102c19082804001c825644070151f8034490f5414540041d082d190207000f01c2c050032019110b69405030022080c049030300000711303540c1700301d03400f89040720116641c0f0302c000d50344c1384080c0600e02d032000349071448082d503035000383d41d1078840e450001e01c001007201400b690005581c00a960540a50744885500c01c0c010084400440191a04542140c114030741035588940141c0080940c0703e00c034102d0408035400e01d019803802e940321203000f0f0040d500c031005802d28806a00049420710000f07a000264812a0f003016103105080d80d4010380640d0190100031815005410690807001c2081001c100010380c2d07286c00034080550307612a1551524101c058203001e0300e05240303445000c205402004101c40c200b00e807001d54003418201030300d02c0c03c400da44140c0113a0060031460600413020040980180d00c028042d4011f402e4141c0c00c65241c41c420520f145d040f42250170031140101489c0201014070030560103035000e41420030a424104030b1070030029180300d0a6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 862831034 1250 862829784 862829791
    0x5030301170d03060f05151e0d060602060103020d060902060c0a06020a031b140c0f030408161703040e0c0d1a0102100920041b0302030f1303050702120106080d0504031416090b0612 79
    0x100400415038089c140900d001d10b000070304c610300c02041954119000035816007280c010040c05643c1d03401c6150308644404003070703a910140d81800d80d078598642d03040c01006588a0340d00c3c1c034006440d240351a0303485000410300546000480c0e5400070164411845d00010f54095102000103101d10309185a025004000500140450381c0203021202c49405035400c5960b00b80d0000c1e6420300d0f006012003840329001081c0c1e4125802c1024034503c0d42c5503a150341c55107108240c074070b140c03550a001000044c0c511145201002880a90803240200000c45100c1c044840c046801481e002040040d2000b000b0f1178070f451303031010800400000e803030032940002c80d100c0c0135804a0300021940220800c071010801c0c07482070b540141c10300d54030010080c0e507a400811901c10360300020b1041700c420b4500f004000c425485800600030200c110b550b4000c0c80d06014103d50028881194220810a416100131502280030002d82c2400d462484042d42001070140c041e0001e031900540140c010710501e00f89600040c80701c2d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 862832284 1250 862831034 862831087
    0x30a0c1103040b180d1203090204201305060c030414120a05100e0106032a0e091b190e090a0b0109051911030a020c01020705030301170d03060f0515 65
    0x80e602c00448150100e030490a20302485509840100c50101b030007000d260311030a000e841c00042e90311140c07000500130280b040c00160030280c651180b0313075180001c0004101c0584410305031003520b170b40c03001002040c0c403490b2007000f8550410f1104002800d40781040e452007420040c0f510480840c6844101e00c1c10a140c0d00a49503a8880a603a900000c190300c1090b05454001340240003282c1140c41e911050624400c440050900c07840c121450103007a41000703c045c01ca415804d040c3d07401d0840300c103595102c41c070b426051074040302074404881d850800c0d1034400080084280d20340180c9000c200c1c101c00078000380445940c0c011826064001612148401d010304808200050581050400ca40890203d54070036200ca0b46840314507000700380c44009596002031001c030090784d103a0010500a0181c003030f07198014818440032001164040806030560028200c1c44211003401e442800c08900303464440c441c80c00c44001d610024045c504002800c4800c0800c120289841c103082d4500214481400e00d02001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 862833534 1250 862832284 862832287
    0x103110f03040b090c1e1906020601050f040e070e13080c01050f01091401051c0804081b0a060c02040504030c1a070f050c070504020a0c0b0106180e0408030a0c1103040b 74
    0x2c10441c07000841d40e0001507120040c01c00c045514081104481072580a85400c10151b82000c03880c1e880620b00c0c0341441c04d01c0d8464071815a6040302a640760405c2c000c440c41544500f41c4c42001e030400c0c0c8143e40741c1d1910b6000919130245402c0e07a640722248050075200040001c498018003248202c03000300800c00a010001800e03180140303018401c1441a049402140d0070302c842d02ca840b240c9000c82034151002121510f52820540d800700402c0e290380d84008040d11404030300007625603000b0900111012845011640401511341040226001c40c000c4201050078000100f001d0700303241d8000c991061190400007103840c030b0703a1699411207100c1d050f05028260020100206160b2210782c507020300c0c1c040d0402c0c40c101f0490501c0b41d03489855a000b0280150340c00310700188000d20460719049907507006402007103256150340c0c0042600b40440d5039038032400b2220f480011151100b40142e0722580c3c004c00070905544a44c01038101515404a1a04c20000e400b0709500107058240002c00041c1000001d09 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 862834784 1250 862833534 862833541
    0xd180b010e0f07030507170702030c120405030d021f0506040b0a080c03100b010c0b1009150924030b0612060c0d05090610050919021b0c03070f0b090103110f03 70
    0xd00c200c2c0e004003900101400d04040c050740640142c801005001e0a030b0f0ba4031116542d4400c00ca01c2c2d402820b0107591544203240440e07146d040d510000b44103803502a400e0314010149450181e958014074460540500041d05400d17011105a500150700140010400310365030140800062100c3c00e1a00110f40359000f01845145a00d8200400c2128110260041c4052095540040d0141520307a0000e03001d49604070000c1d15001c0240c50303c1e000713080303a0f5008001c4580c040b00e0b401720f00d489a000360020589409505040d0f0303400792544c0003c1707044d6a14800501802e40d40c80381d50316a00a491181c200c00d80c0344040c030304841c3c00c0c03000c644641900e6903c40c0c1ca4868455444c816030fa005849048150060010b105600201404440503101d00b5680d96909407980585201008a10940c2000092010900c119816081140f084100700c0c1c41c02107808000c0e15200301511421103201781107500041c41010081d01051002034000a801410005180e001102804a141e131040103000366444001080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 862836034 1250 862834784 862834801
    0xc0c0d030504141e06071e050c130504080306010c150e060a290118090509030a1d0a050114090a0f05090f010605070b04020409081b01110a02030d180b010e 68
    0x2460103008030781c020750100f1060004c00c06104078030082c0703009007030000302401400b000807420040c406480d070104100b040b10303003090f40c1c8035a980c01c40f0310b1182d0045103126180003480e005042c010354003c01003d1131500c070140103451807001064221240c10140b48501082131080c403178080b071091f44c1342c060003152820400c007034202c0d13002c045942c410744501148042031403402c24003840303601d10a0902c00038107098400b1210800c00a5802a4400b03070800c810080304120100207009040c003a511081c480260260040c8400c2c100b041e41075070000b0b180602000250721656200241c4062510b1a916004d85100070598200c02ca400c1524031008011081108d0305010072400e911250b41c8030212210b5041c0340000700f65100307109020300115052008241550707170715404074810603809032449a070380010700c1d00e85000e110002484034181d441c1c00e00c420f00c00b440c00d0341141c00101c1d442d40594984030301c10420317070014041280e00280c8003040c9401d1000262101d110103001c2d040c0a24080f4080c5821200c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 862837284 1250 862836034 862836059
    0x280b010e03190209130b0702070806070e01020d0c0c1509081011030411060409021206100e0f010c1e080c0c03070b070807150c03060609050a08030406050c0c0d030504 73
    0x9100d00a6000b00004a20380700520080070304940e040750720410365121040d40750300798000080050540e04a500900c610642c0028801c411207013860103552150f5038802c8241ca40c0c2000700034207405038000609a22400d445014046e9051780b04000d17183c1c040751226200d084445200e80c06402080c4a01001d10040e801084182642a44141c09010010152070040700d90b000142c001042c2a00d0b8414444960b688c82090358058580c0d403604540b500d41108540e0710a4105aa8481c000c0c111103500b402154460841840c813000041d10b100c0101507140c0045540501000e029030340004185007180069142183c3c0c0d481071402801c900e6110320021030154100000c1111991092388403c00c1003048140a60035108800e41002d906512080c3c1800c04d4144141000381d105d00c52480c2600c1c0a007810b03010381c4003809460042c0e9541c175503280c4030b9081c80050320ba0350180c0350050703006000c1080036921600040c8108030450013520310f042c21400100700a15031800c0110049500494184810030b81e011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 862838534 1250 862837284 862837307
    0x8060909031603050706050f0f0a0c230904110c150106020d12021309061406070f080306150d0915021602010302160c08010203070f1107050108280b01 66
    0x11821615820000d08440e80ca20a5080950001203031080c00d000707160084042c1e03800030707400403014400d034540340140b040910303411900c00c030307420b0100d0000c5240c180e070318490041c072080c064036040c140d01101c400400351646032071024503c461041058a00ca40c4950043e11303d02045440500c2d26440421000c0d401e011600c102403000c044200c0042150a5000400420400c25410300d0faa070a00c290703002c040030b807288203a8414082c00c514400503046040d40c0c400e404982d401c880c250000303190703601040f070380340710344170700a040c05050141c4040801d0340200150340002000703202c010401319003c2c0146a035000140c0d90700d01142e892520b1003d2080c401c0c0c5824500c101400110720300210700035280126011904043d0405502080c142050400455001d00081c0c01c8807a051219039035a62b0b65020b5801255130300c0c0003403045280170001e10300030420920002140e0002d01034030f900b407800440c0c5240c0f005203c0310000490b18001c0b07982103101b000c2c02988900d50903010544101c100c0000d060101800f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 862839784 1250 862838534 862838539
    0x705031207120f090314100b0a08100527030310210f2a23090a200a020d080106020303010b1c1d250f0620100603030806 53
    0x8220070740000d0710b6401c50701d400301402d04102160070300005080740c00c60010f0f040100034424090700d4003495280081e01c840b1522a00d8414414a000c0c80c0900886054522500040b680414100a8841c80035006160f0001c5d072004890300b0b40c14009402494454441000d54a5070400010b0080d081c201640700009040243c07114030400c62010012420100b50645c080c1014500303410102c200702215a880e0040c00c0710303c02400000207819100300c41d01c50188221205200090440e80080c004014442064000207214115507075815100c070000e08200041c04852150401582e00c41961840240850701a1580108440d080d99031024040314410b030000002c0d03510134401000304000005c11141a00080d1041078016400e241080000e8280320005c3c0190300703c4080c001401710320002d6464034200c40031180c92418548444a42d0b0304580501a0030780c0d4114118060142038040d603140c00507005500c0780500e4284608540320308146501c034030813132802e80b1100200103140e80141c0c002e4011008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 862841034 1250 862839784 862839787
    0xf0d03050418050c0f0313210305090c010c1401020403050d0302190201060e1302150a18090606050f090607210215131b08010207060f0f02180f04021b07050312 70
    0x31308281c500d50240c0e00041050f82d1001000551065082c001c054078284e00441987c1803d901c0c1880c102d0300d01d0006542c100007440c0c0ba000034800000000e4808108a06841e881e02c410000d4131400c0a01128a143d11810364080000200141c1e0030014088070b040c00e590016111a001860f091080344403400c1141160f0405070288403080c0352042c0305800c220701c40381d04104412148081440200720710ba0341c0448481c0440d03030240c84ca8000c086201c000c41c103141084906922052a8001c8404078090710001800a0041030079031002400100640070004114506000ba1692801551891041d65042c42d00350483c0c0135032416010007441d41c401d804044201b102d450015000c4002c40d4510303c001e80800f44801c032841c125620400110301400141000755038401301428101c2c090421240d03401101c502c0c00d003034840c0030040303442602e50158074880e182169040325020088044908968158002d034204209a032000c443d92155010038070802c05030807800e107004c003014100310800051400c441e00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 862842284 1250 862841034 862841041
    0x19080702150603010b0901091506022118100306080106091e1104080d080106081302130b12150109060b03060d03050a1b050a12050c1b0f0d0305041805 66
    0x10046041c1c1c0000c4200c0d40c9a104640e1030030002800b40000320081030708484181d001152a0849400070b1541c282c00c2070207070f00c080c1e0b592402280e41c0c107040c446410180403030551081d8400c0031800181505030307212040c200900440000140ca4814009900d000320f551401e0411001d40c0c01e0052000401c0313280803c01890380c140c035450000045402c00d140e0340d995642843ca04a603ca20166006031001c94210341d1045200100a400c80b036082c05400007040d0100002101d0390040c01d001c100c40d503070241949604a407450560f8000e0041e0010136a4410901c06601200c0030f0100300c6a1500c071075064200d00594507161012086500355084101c103a501041001450340301c030f82c081e000c40d0350305140803540c44944410440703030200d100000c0000030340300d000c1c50000e0100000b0075001c164007822a00d011030844e0300080d1034034405d030300c0000120f80006202000348410030005440e00d4601030481c010f01034054001075144d880c0c4032411804900c012030103000480d5002c1070f2007024945c0308410405400d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 862843534 1250 862842284 862842287
    0xe192c06070203131206020c0d050c07090c0e01030507020717150c0301320d110907020105061f0507050f0102030f01080c13110c16050103151202060f1c02190807 71
    0xd12405075100c2a8041000760301041b00e9681141c56540701d50080d41c40c505000140202903500186100a2600c210540481c1510380c1d40f041800c511811b0b191104103440c1800190301400008060900354040e2000024000007000c061214402c2081c1c040e00050307002d03a1072400700c0c05024040071400d240901c01803110701e0710301840c2e992001c0800540ca803540081071142a10080c9200000d801212a0302c01781e0800041c1030040303010700001c031501c0c00d0301d81c0da640c0128200e40c4101e9545500296a01c9220b0710901c880c0481c40b45074803246400c5240041070784a60740b40543d070100040302c580d4000308105c6144131000c825400f4011a2024188055403540043c10883c032411201c0d081c241c0c3c6209036100310100c6412101e011031140242c400d115500741f181e000c0620140b107180e001c80c0c1003552841c6500008101c0c1810f80318104120742540d0300a400f1701c03109800150780d016040c0b070104102c5803a80422001603100300100d00d03000d03070385500480d2040780e005000d80041e02407040e45010300404a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 862844784 1250 862843534 862843567
    0x60109120c030602030c0d0f0f0b030307021e0d0b0f010906080a0c06080c1b0a0201020c0d0b1305150a150501030507050a210e0c0a0e010e192c06070203 67
    0x1079030060005a1039803130700100c5030240d01c0340d1600752001c985407009000c01001903420409c00d1b808810410400800c2180038151a8420f40302c00030b5010604940300411102c001c508006030507000380c01d00c11a43c40302e6682c842c0b50b2205075120394288190320010000c422481c02120041c218110142940fa82a969410800c032014020710b4203004210780080c2000070300e641580d548200c0131030300b606c00c282c00289403621000b60100682c014003c010401d030481c1406d0726400082e5034408900011a650403000040d001c4690100712a2805100c01c00c12218107101003481c00780785420380000b56802c410026030300c681d0a60f44030340e05150a01082100450f0414181c07419001c550800400c0c0d40481200300c40742c20b106091680780d8602e026050b02c4010400100803c0d00c036400d5502104650310380c1d20840642e4401d108192100c15103000003540040c0071032509102c2e003000403001c40e81c1c1c0c070b668040aa0305038000552410350411069096001c040802105800a01d540061490301c80781e9030000c0040b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 862846034 1250 862844784 862844789
    0x11040207050a12180b120c1e030a090b09060708160906180312030f15141e060f210f0705090310020d020a02070f050603070c05031b06060109120c 64
    0x3c2542c01c000810002e4020321007401c40b0744524090701c3c107803511000d459403d034001d501011803825800700083c0035401850203c03045e6424040c400254850001140a55980002c001306441501e5a21580028803040c09450098a400d00a40254a02014003c281c2c4400601000c03503600c0c51160000d0b000d0b0401c1350002030f0341c1e503440c0650300203c2001207030340e95001c2e0340d000030110303012a4094162107506600c00d052100e5844024411a001402441c0e00c03400c40d401400c40c00f5044180b039200b580781c98048207080341189801c120300c007403250001a0294010b11103401d502d500020703150010a122154400c1ca4040b0a1000175850410030229000404000c20300b00910a0026200c40182d400b041314001501d16048250f555114050290010350410110301d00035124003070020961072030100e03030b10040d9400a003405003142d0700c7c800211602d030242c41094034180010040d55803100c1e1400300c050314203001d070307030080503181004400142450303110b90244502c80c103c10410130000d0001c0140104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 862847284 1250 862846034 862846043
    0x80a2307020609011704061b05030405060a0b130c0306030c06110c04050a0e07082121070309050a052505060910020c030609160e060f010c03140d020711040207050a 72
    0x112260700e000141ca00c5c42a05001c144c82e98003850800c01003090a4011545040c2070400d4a40300107502c68080c0d070107000c1594020443e8000000142c40c0800c140e0103a69082402000407100b1218410203e04031101340307400c800080c1d00c070107040c01807080001c880301c0286160300d030140031640703620891600c3e001c4800e0301c28801c86e00e9601180a0308a1074015901d41020340050324200e80e512800c0c41c0d80e400e0401c003880220580030f030300c0c042c0d100e04a03000d0740c8174a1740b12089510342c5210b407081d60404600041c00c640c180f55503695890003160081101e00c4071984502c0051003a800340c14811040441d103503001800640d820b50f000c0c4915203456064681c04801074031204040c3d86000016820070241c009100c2e05032084104000c841d86000130601320800c05418030b00d40319900d8103011614040d04542d481d4004900b900e07001d080d5441604051141800bc5c54082481e11035034038522069440411090307499078020450301c007400001c205096052100300c50451030404681d940d0b40d11000c0e0f1410151 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 862848534 1250 862847284 862847287
    0x40f060b0105130b0705010b04090506150105040f0303020c041a010e0607080d0c08040b0a0b090105010e13020c0304081b0906150c0106090207110103060324020c0703080a23070206 79
    0x94031a4060400c0d580daa16804111400154990441e45510341006500307545039800c0c00300d040c0742c5003030910510302020b400c0340141000303985a2200103821030485050504020040000068a14140150802a621a5002e005c5c00c0e401041080180d03008803501c3e07200300c80b0200030b5554907a0011900c881300c010a48080b525403005003410300480c000c10b0302c1e000c441401c01244c0c07200154000141442144102c010003200c0d141d140003001104c1c01582d003035401c10000001440250b000d0728404c85802e000074034075107807114a4414901a60002c00e20f11219500124061080170818029040314032100c9525041401c41e203800540980c0c2d001c0c0095015420b6440003402d0000c0c1d4404942160907905c00a12400342d443d2030b248004e6001601c199940344c1c1380400710032198480d000c3d030310840790000351a480d880c0025240d0003140d011140b40c0c4403c168204001300030420300f031200c1c00046004038440703502e441e1031850190490100d181c12419210450003d40f207000f202d141a6841c03103405641c2ca9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 862849784 1250 862848534 862848551
    0x906161803020d030c0506071701170f0109050f2103011202011106040c030201090803090d03030c1205100303140a02120d0e0322050a0501081302010e0a0801020a0e09040f06 76
    0x180c6180406400194000070186074407024142c21994040080b0b10403070032900760b6641e240f01141c0d685201000040e8990200703004005c5890109040300540b442e1a051302c0212010745c071003c0c02c452901500320b990b50418412042c101c48140401c0045150025400689402e4007215445600c014040c10242c242191070902c00e591051120b195540014000c8528600301f03414001c240c3c10039844120300281503d5004144840c0220a90348841405030180c0e50b5048503560582c0581251522001041161030701301c170000e402801058081c1060f00c00c0070580504608000745100c140000a52124008118001c03074030b41d0001d800c00e4074a40442440c1d03144c2c0b80302401c440141c01868050f40c2e4901c0040b0f84940e44503100e140a10180503201481e0300495920f1044c02114446441942c1c0070940c42c8000848452110101000d060b105160001054441c500028102007554003c440d05039408210700c50900d80083c500901198206d070384000301d103865134130818508500c0318014506911800503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 862851034 1250 862849784 862849817
    0x260f0909040503070c09020c071a16020f1806090c091503100f140310060f05130b030d020d0906081b0d060b042903012607030b0f040b090616 62
    0x10381d0744030f5902610b00c0c40c031745990300b407484082e401c183d59000700c178060f250300000d988080d564601c480d0343c0d0804d07075142041400c2203c11122412500c0a0742c10064112010a2a944204440300b0390180c40786d12088030f003024014040510f2004001f20b141160802c03414065075221300440303d0030701011035459640c1c1da8416420307a5404590303200b40601807005601065018034080d010044200c150111030710800a541c199003501e1440c41045500351800d14244038034102101d1040401620f290041201d458540120f487c00349840b00103001600f0080d4040c0c45268010b0070b41c0001c021606d000c0c8000d0401800b5010047c09443e00308401c000c000400d2103490785542c00ca90014000401000e4486645189282d1300100d101b40040341c00f04280039441d0b0a0030344206a0341a24007070410070400c405030752501035505007405031000d140d200b040070000c0019002011684685603001a803c0f4900b400d2070051002900078014192a411110070400b40c003408a6007a0f41aa00500d003034980580c00491 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 862852284 1250 862851034 862851037
    0xb2a0a050d090f0516030309091a1002060103020111030307050a030c1e02061b040b030114030a0602072012060604050703061d070809070308070b0a1107260f0909040503 74
    0xc1d080e03040c045680103128900c40801e070203601510a980301141c94a17144043c13a44d240c0401008110100b40512507000e0039800691001c400c046150048046040000c0231b610b00300842200691083c00107104550380800e02c402600314010040d0f04500308200040c1032341c0140100300b41011303a55985841034a10804914103800880070803400da2850750300d030003074807150300301d8000103002d03060b40407200210484002c86040ba40032002d82c40c1540d0074415444844407400e0342017079046c0304120140d40410700c81d01c01001c03101c0c418103512502007a4480b0a107800301482c2d41051241c405a4089100000c01080d000e07071211044800241c180d984607402e60090665800c41800391440c4400600280208190700c0c0c060b02c1e90b0745460301b040d681d561410380d0350360a90100504503a03080c01104001085080040d8000c4007801000c95014075000000f18190040d04c07054034a400089062240e440c180d0941c90521400d500a482c40d014110a00565601c01c40d044a40204440400078013401410700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 862853534 1250 862852284 862852297
    0x150504021224011b021807180b19030f060b0a030b090f010612020307200c040c020606210102090d1a01050d0210050c0705031006030b2a0a05 62
    0x40085403505400c080710344100000315604a4500ea0080c5011141071844020440b901816900c50101110801000e4101c1c10844000c0760030014004806031381c2c5109000242c414138250b030724111811308401d0103e09150469000281d02d8400b041003030300c681e1000d850f08080c11100d0a0100d000c0400502c90342c0101280c2d44200606900450151141035154001e0042d10004558035400c98903081c42da0241381d5020321490f000720b02d07034441c4129000001e801941c0c0c000c03614200f80e03119541410064141d40c100340c040c4440b542140e9000800b5103440d1180400401092004240038600807012070f6110390800a0140d50304800301b005502d0140075011540d80d04c0d00544070055640b207914040c0c00e0302c0744c1140c41010b80f044841c0045000d041c04201086400d8009148014010b0600030903940c0e9070080c040c80b181802281c401040c0c64600300010089036110640029420340b550910700111980a04042070311003040304004514000000c000c1c4550089104070760340c4034070000d401c0c0c80c01c3c410300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 862854784 1250 862853534 862853539
    0x32108100501030b032a13020a0509090903160804090c170705280c140a0b06131d060106020d0c110603130f0b04020906030309012307050105011410050705101505 71
    0x100e15503404045000c1406d09185400e940744050410b90703010034003e03409100011000594140810b0000780fa08040285d042001002a40c2ca04001d05900c1203110100d003e05480310100041e0411028501d0700c5500c1a042484c98145050100c454000c3c0303030701038081c0140c010020003040d50294118035041e42049a11100200b00001c0041c0401130f000b0200300e04161000b0f944039006420300040801d0102c04903a1001c1c4101c159a01c131010003c030840009005040c0c15603030f6240030041c0411914403010b500072040100141c3d0b00d8180001e00d010000d10b04002080380c0d0351801d10005102d00d480510300101142c80740d03101d80e141483c7e0718504c14500d4010704041c0c1049501c9050120155209010724003c0c0c0da0800c1c41d541c0c1c0300c18140d0300d20901c01c8850004200b00301200c0215858426100040c1e11104128949459030321014250f480030b801089080740000c5840c0c01c0c40c60982e160036518042070030900d003420f01c01e48a090b1244c481103030b1981c080b920340007012020401c070032070b400103480b00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 862856034 1250 862854784 862854823
    0x10c02010e01090b13090b06030f0c070807140c04060807030b010302040c0e0d060b31111b060a14101a090a0308070c05150405120102070507032108100501030b03 71
    0x3140f5250031480042d01c034031b8039050f1a2104501d0982080f204981c800c900c02c40104c96030b078075403642600003940b1801c0140d50710f41083c07001744d0009209500d40c1e810b40740540c00030030400e14000100822035446510958059001110410000303e00f40042811280c0440300050b201828040036224005514400e903841001c45003503c080151503808150102c0094420001c1d04140c10040060b0141c503070405c03606102c03680300001c0b441001d1b0f0400c2e80d17049100307002d44bc28044400c8808a1518107103815480ba5000201003050102c8a441001140c1c0c007041240e00e400e0800030b0094000905078011402100815000000541c8921007241d4074400090300040e8055500c1c1040c02040d04038250485a0700411a40040c091030100c4241d201429040c00c0549854074013001c00024184551203410255004c4c01003001143c4180101c0000718090110180d01303808642c28120071040c4500780781c0600021109115000c41d1801c44031007a42e1302030134001b64079a13403c400689011112100c070000c1811 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 862857284 1250 862856034 862856047
    0x60e03040603060e1506070f0204050703090b060a0302010f0c14120304051b130e07030206070507060206090105090703061109091006020106050f1014190f11030702010c02010e01090b 80
    0x1000303204590540d503007008055240e064880d011801945e03880340311001d1006400940c41c08200074000c1600c118105a0903140c0c0c0d6020400f907901c100c0383d0300e000c81d0b500c1e83c0c035400340000c4560403540b28108991020b90581076900103403480c103680c4000c03c100500d4407103100811101803d1f102401c5c8100c021070308140c44000a94050368000c81341190759004482001c2091a00c94101c030760160001040f000c10f610005807208010a45081001e6180c4120f40b03000000d03880b02c0000f8001d0502a40183c030b110740c2400e8029250400c0a086a00c03181c1c03524041044801f40031809a044e2940300002280c0c0c00084903070540e2074001c2642c41680000710505102c03c850091040004884298000b403113415038a4003004000341c00801d2064022855400707200a840c4901964012065072481e50f03400c041080d928400c030300008180b0b142c0820108044400c3d0140c00c00040c1848000c480700441c81c060859000905242080c20000d050103019070044c1580da01079a00d45001d08441035200ba21041d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 862858534 1250 862857284 862857311
    0x901090c081b090912030907090507081504051504020a08011a0a021507020a24060f120b0a0209060a0c1407030503040e0405070902120403081005150c0a06 68
    0x106a52048415000002000032181000720b503060350030071a407a52110810a00082c000e03410710040c0a03803124040c01c1c111000c82004c0c100518001c010301e5000780b8016003000140e00469501400e1142440301420030007104509016400c5443d000c141c5e004540da0b00d85105608504024114040d0700c240086070710017442d48e001705014100c0b00b10400e0880c848590140140b085d1107000000d038016003100c5500c2000c0e86030752510070b8100e41c6030700c1220748014403512001a140301c02e0f02040310700088883c080c10700742402e010341e6018052081c0700710300d001c3ca030034141810905880d10003425807a5000001d281440f0990540e008600054007d59840c1d01d4420020f102d440724032070865070300d1031000b2213007901c0c940000c100c0140ca42c0700c00110316080c2441a1122001c40045c02100e2038850340380c012400010368009851042486030b9041c9040c2006c0c0b8003c3d210070f00c0100701c40c144600c3d9500800540d03403120143c3c0c1c490030b100141560394560603007a15042144250016081ea803d0081109000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 862859784 1250 862858534 862858541
    0x7090f02070c1e06030e1b1207080609010c0504060e0d0510050c0c10090b0403111011040602061605160f02030703050a03110a0506010e06031014060f01050415031d060901 75
    0x103c088003032801865403070f520243d08552450242e060035a0107814440c8034540b000ca201c144081d00140f41c55605000c0c050214504400c0d50802c42e01c42d08054203010240c4402d0060905019403410b00a04181c00c00b0310042c50b009c00c01a030070340f040740c07004110310600c042130181d2410b5440d000c009001ea0302d8514002e01c0141d200c034001d08100d01c030f514400c2c19080068440e15590680c06a802c1c3c05685503520125400d0903900e0380030744d09019100c0c1003166009248076401e005c850314601591070354039044000c0e080c24401403500c01400107403071400805e1139000d070031a0700400340b000d4000300441007030070501e60342a400c1f0802900340c41580c0c004002d005c800610050568400da0780c200100001c0040e194030b030400365a004100c0c0e4012801808810752000d01c00d940004040c04561082c000e030b8400c20180c0b0240c1c144044080014802c0c00000e081c1992800d000f0384003030a02e140307820301e440701c200001c03c009000901095510310030200c2180140103031100600142d0100c90942c1010b01540d4000d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 862861034 1250 862859784 862859819
    0x8131e031d01140739090c0e032a060f030f01050109080a0609020f031903080105010c0503031503211309050705030a0f150f05120c0307090f02070c 65
    0x8291000715018090340c0305460b5400742c600c402c1d4286081400c00d03656290003142d100e481402c145407040d0b585e40d03404000c0c100b00c41c90421103008043c1c03130f500e0840c500301215481e030114001c0000c03028244249490010f483d65602141190758040d45070b88524860300a0700341708520341d02450004105000d1030f05100a18091a4103d000c00e4060b40d0700e05c015611107819100391140c58100c40410b402003502a071000489900180150341c240e081031000170b00300b40130248442d43c00000d1080c60401d01d5404a60b41e4090002030030601290200783e210259070340401419a01031510a0a414501d43c0b024044641e409040c4420303d00819030300103000c042c0d0303000f0301c0c03540c00e11941000d0006120301e0b0502032540a6425500c1d65455500d4940c030f40307409000032010007085280c0b80c16003886500c00000140e0010040c01c0165002d803401c1c28208640b00b2101107180b8081d174480d40741c00903140d40c0410404101c2c1c0c070b006e81c00102d202000303000c40302034020903102500f600b8842000185111801100400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 862862284 1250 862861034 862861067
    0x40618051b0f10021b011b0b07171305060703151a04030605181b06090105090d0210030e10020c121b030a050a020c090403020c0d02060705010f0b01110c0108131e03 72
    0x170343c4070f20100119040e818040c0b0302e40040341100d08400100701c610380c1854214409241034484400185c480c00240041a80e103912000040c010000c10b0090134440b464100040f49800d0105054038031100040100ba800348a02c682420408007510980c018102d8008507030100c01403145150140c50411849002209201c140c0114290030f0351044041900c20100c1000500b0142002c041c000110b50540040d1541d035041038080d500e05015948511807900d10418959010451803451480d0b142030540c0e00c0c07415288640113103c00c20144502140b0302e014482c10030700640e140c044c0c1c0c404104e4280b110301d07102c22884c0400540d03813900962080041041405580846150001c2c40301400700c40d0404440c0540180c01c00c0300304d02c5403031814940415545000400301c0f802c00d00303151601030840d07180b1018280e04660302c098014042d40c02550041e85090350b80c1c041c09415070307220000f034401013004110311030081a01c0d0300e00080180201c0d660a0b5903000e824109482902480e0141181080300135100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 862863534 1250 862862284 862862323
    0xa170a0201260703020a021914010c030612060903170708010303080115080c1c051f05060301060f0f1e08060a08122a0d0503040618051b0f1002 63
    0x2039a0182030510b903020310368210030181c8980e50b44481103000b034004d00310900460160803403c840b43c00c45280902080c0b800341d40301070034240a4044c51400c40344d103444a00305060810004010604080404201c440d0f00888080340c0300718549400c49207990700c04000040600340a0900608070750040e221810381c1d121b501d4040307269032108680c50450700301588410000d022180000c81d0040f00c00c0140000c2e01003411342c240d81900340c0940005603002110101c4042000e14844c0c0000e0a008603820003c200658005155504040c0001c207900b2030803c02506103d21040c1c2c0d280058802d2511082c44e0004180c0010340321a5100300030103d101c10784e41a0310508000c0800300c2c50200210740e00061480c2c49040310314098a00012284500f04610b61300c0c5040c13010803045050080521900320f00545030b80da095600d2030a0b19103803080702d440607410895a908144080c0c000b4800180c000010107001d540740c103180210000240000c0d100b81c900e02e8000c0c00c1041808002c42d000510350051000d070340d0034031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 862864784 1250 862863534 862863557
    0x220308030112033e031e190c1502030601090e0c03070e030102032e0306021218010605010c06090213110a021b0d0f0804050303070c030203061605180a170a0201 70
    0x70000303079000c030743d054a410b16880d03000300fa001c800500074030501c044c100740c90034582c03048510f540032510740c0342d90740221030001400491302d944009080c51850f91800c20480d0031038192100c545004194a0700c690107507000010620582c0602c0a000040481504545180c50304210308520350708280c0f20040800c02e01c282400c01441e041c000d407407040f281c2013412001050f4020214608600c031005c403010b070300d40402d00440841c4460009206640646000c80b0b05801d003411820761020101960480c540d14000090011340c1e4065035440300c45421441c082060281800041c4a44070701c182d00c151513600d006080c0200c8801d0700060010b8071016001c0c2e030310b01d07080144c80c611a60314005030b46910900752880708001400e581c58040046004043c05402c0644800c042461584264000e03942000004420000c500e02044002d51203900c45050301d000c0098004054002c0c00344002624180c4802003000c4215248e512088004040c3c9142010910401013205900d800c9981410b90004d5803d1402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 862866034 1250 862864784 862864817
    0x21510052706041b0509221506030221091e0601060e0a0e0105190f031a070e13020c03070602040b0910110604120306050306040b07020106060309020622030803011203 73
    0x80340c443d42c1300344c10103841d542d1024004607880d40c0802c51280d481035040700c2c0d0784040c00241c80580c1c0c0303100004000240080d0110500344a41c01241e10031000c02d40100229010580a4082c2e00c0704600c0941220803580c5410b01580c2c10040c14500e1303040184442e494910545500045c81e5040b6880c50325448201c0d003c0501307200644e503d902508030f00310440c00c0100614184043c5a4000d826043d880d80701305522461407074601c0e000c07070f032042c0d41c0c0b0940e043c4000c5800043c02803503500904541882da2196200c440410090300501a035040200c2d800319280c0c035600303014400c40d400c0c154004c004550b6103480c1d04d104442500603440441c0140180741031411214010018203400c01000310003400542d60320780d140b0003011031002c0c00400309512540001400c2d00e0810220740124403d0b800c00705140f80c43d03140207085480740c2e400001003504044810300945c80d510304a4011010740103c84604030403140c1d131819100c0c45a80000c00114000000055088401c0700101800d48a60303203040f040f4201000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 862867284 1250 862866034 862866041
    0x51305301201121403040e06130c0c0f02190f03120201020f0403242324090406150b07060b090f13210908010b03070602151005270604 59
    0x18800c107019194001404000d903072040d1400141c1c82514049001c00c400800f0908540007540f000140d45034203014842d0500d0041900f2101c0703201050100080c144410b801420000c1007a0050032090314946100c0540d125601d1124000c001860b100d482555600c1c1400043d080c40e11081c0d50440c400340324001281d1040c001c4540206400720040d040134255211405040150103800390386002d5100000403802c2c0e41e01400c0c11542c02840c003905803500d2030305048801d80004008813041010341c00702806014a4010a810b0042c0c00c0d034018030240e0ba6840d0802c001e05105a104e00c192101e40c10000742885400014000b040c411901030001040d11414420815400d40c0e00d413040080100000d00070211101090744034900038800805600b030442d0544841001202c0881d000590301441400454024028000230000680040582606e0440c00035140d0311003040d2a0700c50f00ca0f40020500c59084122003102a02c4000c0c00010407041d81009001740640c02d100941c548202c040c0002d40c14039240c070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 862868534 1250 862867284 862867297
    0x70b03090c210703030c060b1009060507110d050f15011206560d0f0f1e0c12050c101407060501030c081b0405130530 52
    0x100142110200341c0100100742c8082810807440310906040c0c2d203001c4904002ea4001940a41c449148541a50511400303450213080b5141c02028450b01001e0219800401da00440e036440c640561145028580060601903600899500040b1880c4180c1030203c00310b20130740070107182404c40700603d60005c1040b525100c2480752103580209000c0d40d1010816170340181c020b6040d0007020303840740140d504184280307071b031101030400c4010240220b00158000207940c403800c4000781812040c01300300c00d100140d1010003186000301042ca407019200204114040c00002041c0c0c0030800b403d001c07400c0d52050200111142044d5400108410300160419407042841c000d16048000f0704803200c510010311100401c402c2c418810410948040c1c41c0c0c10f0b18004c00b52440b148240390101c3c4075450740c100080e00d61919080b890b05034001d03817101008043c400d2841c2d019030b00183c902140341ea8912031000109a410072018045e4002c1e42c10080d11800401c4458221900191048100c240250f02d190750b1405802d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 862869784 1250 862868534 862868551
    0x1080f070303020a03210f05090f0309091506070f0f0b061005220f0b071104110d05040303090b0405030309070f080718020c16060207060503041106030405011d0c0102070b03 76
    0x84500c80820b11400c2200b11b01d140c0c054021007110081d00795041120002d8014101d49030740e850501c000318406000009147c00c45a000f0f5051080e41d00014002a002404840140041c5071264001e070f00c511007a0b40a0540100c41d080a4a04a00340381001d951440021204a064200050f0703291421010750624103a00d1b03659142070030000f4010300074803000b03546440c04421643d0030010306199a42c03840b0000d81729140c801e940b10116460030703080c00b4074840c1c1420b00c1581085aa00c4000a0b8201940d00c560300d00f00d804280f41d2151b090560003040300c11000350900c40c41c1e104100500800000850003500600201c0b510b1039540d0a0b0034100d001103000e40b500710b070000803040020f054401001070145d904030100510700350400f50082c0c540f00740c10445020340c0480310010091180c051000000038a51400c05904c1c51825540310040c2c880c46c5103000b44501800b00109045c40025804030525aa00d4085050030107001c41c0768940d20a0b01e810003900600c1115030100303d0010000c1900c0c05544070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 862871034 1250 862869784 862869793
    0x30c050303071e020d05010507020a0215040506030712022104151a0112110a0329060403061e2a0c0b070e180106050a111501030b10030203010204090501080f07030302 73
    0x2030182d212400c0701c100005a17031003081c0701620300200d0020700c6450700410040e00280180d40c1c081c41807041c09003210004080100707003480200815110002200d902c041c051a1192000c0000880b0000900440c8120000303403c200500681d881d545c4116a40110302a044100303003034030f20042c100d05440e081200c02e86241078005500105501070040b003205064036110125000d080f481d08079a4a0f00041300210010351103107083d07010103001c801494034040c0040d00070503c1c6240e030300115a0300e22580c48020aaa40e4500a088030a4880d24030701d0320f0311800c2a401e00034108000c1c8280f03921101c80780c108844024490200003818094000e280d05142e1052405d003a694400307a0650f0424070072000d182c0c0140c0440789044880400102c811f020382956216591103550003c0020b105124030450b8210640c0001c107403c3d04490b10b01e08140c1100e43c0f20600305c40310781d02e031300f1141c11084140d44002e42641c000300300810a4075880e00003c3c1643d92900031035007001812062035590f20040e20000e03015800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 862872284 1250 862871034 862871063
    0x12131202012007080f030a0305010e040b01121703090106210c0e15060307050c19031224030804140103060b040603020906090a08010c08101805060d061104030c05030307 74
    0x4014403401e402102c14090b641c00540d14408a0305100002101014030380000074461103254041c4074840c003501c4481d505200707e01d015580c010b6103c2d07043c084c00d0075040c2c00508800c1045030300340180944019000304141c5038100181c185020741490f0060380584a0040c200c05c80d0810a03254101d0b080c2c0d044444600c030716190a64280019602603d800181000d004800106031100c00095004183d00d544207640e03000815441070074a103038100d40b20b41d00300300500c5000209071f20100000d480d004c20500050b107401090040c2034200856000c0140c1d04104042c00404c2c00441c0e005072040b1024036118080c0303904000d0045040b910240101c0001000c01d00047c0b00880c800d40c0504040200907020b249440c0d00840023624200e015400070826a45403502c8400560340100701540050b480801525424100420100522122101c10702c0031603032a0000b820543d0ba002a00340a150820030811038103030150010304d2981d02a00040e110722060f5580000c0d941400004c9603061900170700c0c015007141 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 862873534 1250 862872284 862872317
    0x612201e090301020a0504090b060301300b0a0915020a0c0803090a0206031303120b010f110a12020601051002070305070e0403110f0c13061d06060c1213120201 70
    0x2004695285080e000c1845000c4035502d00348014000303940940c03502c98032940b504051303000b644e004058490048a040c80104000b074004000d0407101c01c040c0941c2120320b500342541c02481c1400f0103000c0e00801c43c2c101480101051035220128290181c4104042c442d90500c00f10140c0c0b0800640c4000901204061404203039200040c64200d075200040d90815007007600003440303942050301d2540042c104e4124060400d50001f108180070b03d5041414440503d602d00060002003144045809010144880074640710043c001c5e8240243d120700e001e02183c21800740296111402d000b4580200e1680541c107101c14000640c0700220b962080003031040504152600550310700141085080c080f0001c840c100070641031142490581290b8010300704981640100440074a02c14078000c151842c0240a100b0000e411060450000303480e0401c00c3c1c142c50b0140822031038171409040d4980c60140c5800c4a41c107c960340000d100c440411400c0036860350f20340c0d031040a2a580800024080b5070002116003920 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 862874784 1250 862873534 862873567
    0xa050409020919092f1204150f0b010e0103140a05100305100903090b1303030509010e100c050d0c05060426030420041b0f0905030d080a0515031b0303070606061220 72
    0x2e0312a00803c46048e101c48904008d885e040020708018580b51448100e195074440c0003c51510b009203001c0c480e5524000031100480380c050010041d01d034560b00003d8200c0100702c001e00c01141d10030202d800b9102c0502d4504010b20842c0c03400c1b0001800300800203040d894440a44c1c0700c004280c45240900d615664054900e580641c40d076905002e02003d06180681d02d5030f01061040840e5114009074661500d045400e0103042c502607810b02a50040031004104001800c1c0e6200c1e0340321000725942800e4180240401a80c60000110802e0010400080040c84694848c4040142a8200201038042c0801003524458441e240c04c0c1320803a002400324501c140a094040765043c1800c800b01911080400e091801221300c1001141600c8140000040e0300d00c1030035440381051410410400009001903200c0307400c0c0b40c4581c107010311000380040582e828012101403d9000700104141655100e014003030071085045061140c0ca01000404201e404081c184000035005902034609812410981c90301e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 862876034 1250 862874784 862874791
    0x100c0203070f0b0c0601081c0c020f121e030f03160c020a090b030f03040e0718080d110606090103021f11060a200a050409020919092f12 60
    0x25110308040050039007201e1003844050005403c0d100c0d554401030005a19194041e841920954003a001d041c0d510180004041c084078080e107003801c1c0b0100f460002502c1661840c0006902c89480070590f10000000114880b035034400b0000c002c034480030000c030580c5a002d03012120b260381000300005548500c1950501d900e65040381091a82e51081d0f4000c111520929040a04056900c4803407090b28a020070820180c040704000640c82c080c10f0103540e1880300c1001e004202441405d1101102201c95800ca02020b45200340131a484203500100040030380c000c2001d00700c1d0304d015480105c0c81c0d9082401c581c9041e00c1d00680b640b0110001c0c005047e2486041400ca241080510403032040080e4050000c07a00031546103074085036001e05560303400540c1900038079a83c29500300f000816101ca4000054034100e41c94543c0060311020400081a00b60241410003010f40345d04510100b14407a4584c070002d4810074407580c1c990013501050003807a03000a540110344a07010240024010884c1403015244d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 862877284 1250 862876034 862876039
    0x5070b060909100e030c01060f05281d0613050f040308071205040507170a030e0415172d1507022505130b1c210504030501110405100c02 60
    0x71150001802800c0728040e40c013001c010380002a010302c04000900071040540603041c0b07035094003490a0005007291003178451003281d8030041240700215251140000c0d000f040388d840d210070f4843c0b4682901c84403150845902c0c0c480c010402e2031842ea401e441c464a4800ca01d60190886143c490341c9043d101040001c0c000410402901a44551001607001c0d650043c1d200e0030090401038101300152000e6025401c0d920398a0380304113466404a54041b044011841d415600090142510300600c094406540c00c4200a0040c03000383c200c141800107000c040545000c0e2031016141c12840c949460070b14040c600c01180e0744800442104001c0021400e40c004aa50040b41c9002c41c030801d075010900c4644d201181030410a510421403414103419010119078040c0c410080380901d4800115180d1104540d81450b0000c061210100814016000c0e0703403d06041c401d9803001d0007030000030642d03442800216500c2d400d1003150b4000c0710710301c0192000c0d110010074100038003d2049044580c8a240603050707a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 862878534 1250 862877284 862877293
    0x9040f06170102070c05060304051504031e0f230703030f09020901061d0315010e040606030b1828021504031a0403020c010e060904021b0f07030b010605070b060909 72
    0x800c045032001ca00066084080056250036403030501108110300d81d880a0b002c2c038420420840004d001145182c83c4000e50880c080550711a400d080b280e41c0741e01e028410f84030030304c131064499003a00503182900700c1d0165a203400318105200c03a4248902c0c040101000011024421000024060340101c00309010b41c0c00000b0b035251440e0005450400b003a84000085a071180e00000041d4864000c80c0c092001900100b0103101c3c1d11140c680360980501c03540340301000c2400440c08000c2550002d600540d001110381015080038060b56800042da513600c0601403060944a070007008000d110038a014011984c209000025a02405149000c0841084481104010220000d0380056944580180710f9200c66600c2c0360a00c0c020b4a00080c0340001c905005003d014008aa84c5500c1224501a02940c000da200c600903140900042d4042c41d0041e038074012556916008500002e01c84103d03800b540310400c0d42e980e41e407802d0381d0901c2014400f0300340c00c010600040450418455807500401c0c1d490444 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 862879784 1250 862878534 862878539
    0xc070209090f03040b0d02070206040902040305100213090506030a020a091508072402240406050a1e180f05060718060203090118081b03010507020705030c0d1b0803071a040809040f06 80
    0x4116038415001107100d00e3740802c0910600034108950703540103500407011031805a10140c2e1120004091045070340980c2c4030000500f00ea01c05000c00340005602405052899442d0a1400050b01443c8241c01100c00288000519942d000031440120b07180006094159a11002d11811580c84500080150311070483d52000c049800481000000d04280d144911810189850300950f4009449916150b08206460310a02801c0b4442200032080d260002800c8980d492030340101c1181740c00240440704c41c648803005100c000b0501501c140c10507620300000690320803821260307800380e010b8500140c1c01170005c4a0254010080780c00a99011a80011615503c02d103041ca00890000080f059450700c000d5522681800d009098000880b0700282400c1c47c10080401e540d801d00202152064070710584650130710075950000160500031460101030a90bc50040c213559500440c02280c04541ca9142000c00f2202082c10780e005580c882c0b0f20f0751500e00540100800340c118500d08410265450900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 862881034 1250 862879784 862879789
    0x40807110f0d0c081b400b150703080f1b0705060603010e060714031b0a021605100e0607150606050307020c03070b390109031107050d290c070209090f03040b0d020702 73
    0x106c06500c20103080031640d03000c01c400780300c41451119a20b020310031050141400003500410819032140c0d40b6905545542e44481120348801552455005200d100054110621001085142c41100140e00034080c010b84094595a21901101d50000040f00c8602003648030b0600001150130200756101c0c0c101194441e22501300c00d0744642c81c81405039010507580d951081072800d80301c0081c4000c13a45001c00d40e96201b0090100703140341070304611481000444108119400003504040050080200700041d202c42c3c01a15070782c403d03246000940b15224110b1841e03e800a4480c050f912040b41607820140a4075040504609082420f00d8030103d100c00d01300c80025240c202083c6854030800424460700c0e50601904141c480040c170b54454200f40004d00041d103940321500304842e8082c440e103a18094a04850a0800030740340c0c0b8449a80040060080d00d0a00c140500040f40c001c44480941d61a0b0306d0319107548280944a80680d0740080c03008001078180c200107008820420540946041e9030341d0700 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 862882284 1250 862881034 862881139
    0x7030f030b1c0219080c060a021011040f0905040f0312090204050702070f080313031113060303030911010f0c030302031e0f0106030c08040807110f0d0c081b 69
    0x1482c1c9240302c079111a040a600e4000c184900c185100d407220401e00d42400c40c100d4660100300099030240d50b002601f015010710800103c0c3e08a4039105080050f4460540304a04540c014491000f250385070306004a0115168171030503004581c00000b28400c02503595069804031500b5038509049640c51594101503107a40c041e491081082d41c0c058039580d410080321000d006400e41110209600a1151000142c810312201c41526088004043c1007001da400007814030300100f607034102c66403d101c0300004040d00342e00aa12841d1040302c60103800c0c0075902c01122101d039440d2400300011a84405140031902950007150801c6185d481386005914141107070309d040c0011b0740d05c1040d214405004201003503151042d0301c011142440c102c5201e007044d071909100ba0041d03e41c082c01c0c0c00740b02c2c0411a056590b500f003076200700c1d40103000303642c401e280c60502d0084003005103d818140d0152085c40e0052101100b01001c1c0540001d000c108900d14640c18a00d901d000340303504081210340c00b1f291520210300c003c07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 862883534 1250 862882284 862882309
    0x2070501021810020703030813050109171e0703200304050d0308180d140d140a0f06271d1207110306010f15021612031404050607030f030b 61
    0x340212801031810900c41500c1e00c0303c01c40c00844d04420020710000b0f9003c025650080980c1c400c11002e00101d00b0018018800311900a020040080c4000707001d01c2050050310180580151240d0b00307601203010015284a8a40d00900280e0b0242124480c0c0e11941d10b441e4203890200d044900b4551a00d000c038889402410080d00802e0f240410801460900c10911928101a0b00940314602041c2e9014182c0312020303005804820002c03a000d41001a10f070700000c104507040c140061203040c940c1000c00149000b1500002e030504004010407145414a902240b400e00041032140d520342c4001040000c0c4045a25444820364054100c412001c04006802110170b02098260341c1c0c440c2494000050a00d04012074000c0d0400001001600c40700a500c01c01c0b140c2d2f01500c40018180114100e003070501d5a0b900d5602d00e060000040b8060110440d0760b01d03524425200c0c0ca02800001200001da03009038440e071036015108004110000e0300c078502c81e0f4184055414040b4009001000283d80e544150 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 862884784 1250 862883534 862883557
    0x20d0c0f030e510610171807140405010b0405150c010e070b09040e0f0c120c0a0b041d0c0a050a0c020d15140411010c1a010305060f0c09030714060405090c0325050d0c030207050102 79
    0xd40d0440c0b5a403900c0e01c159330040480d048550302d0f0900d0500455243c518401c0c104070400e00204504120792000e4100800c80c0207480c0c19144410386840c084403141d00510507142c0503d28014240006100010b2030306060b0a01c0d20082660840c10003c00114510041b01d03110b0a00800d21807502c3c50b2140b19500c005001e100c01c40076141c1d4100442c00740c00a81100c01911103031008014043ca421408003155031050300351030714665030174200d1000d640451180030000c0d0492500c00c848070600006c8011800d100d410400f003400018003150088009400c190b070050065100f80d5504601980655100d109031032050501c00102c559965011907140000d901c1502d42d60000e104008055494840c01e5500040344090a400c206034000440d58900341402800d13401030000b2441e1170705507a0030090360020a4010200b500c9460034448441240d0015911003a4000c22089111060207819510b00041c00f440e940b11420300204550314405401d08051900916500304202c0c400b04030207000038111112074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 862886034 1250 862884784 862884809
    0x1a09150c0d0501180b01090b1e0c0303041104050a0c02101d031306080a09080315150703120b03030c030703081306020d0c0f030e510610171807 63
    0x4013000f40068641585545042218421080c04004100350aa800c2d6a9448201c01ea101000f00c0544500d4030480809010601c004001c00c02040f616075002110001c043d03a01b8040d40d150402c01e079003504d080d514400056000201e004807060034aa12544030701aa00d542c3c180c09031581e075155030855010443d0b50309004000601400440d4010403542c0c2c011680900030003580e10152501e01c40fa01000d4038280d1702c0c1c1c80d611103000983d61860560a03c400e02d800c01c69694080c00d190241c5421034004140b504542000c5000c2ea042c5000310030348a9001c40300000d10700d046001e650842e61f504000b842c1521400c01402c81074003099032840544088000e14100183d040340f00100a002c800200c1160000c0600701421801c504101207812403124507010952480740e41d21000c0141901120451140b085004210740e000001455240382d020380c01140c0281c110751100d406118454407446a8040802e003185101e003050200840071681c0401080035a247c079492008080e414098641d10021a41c501c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 862887284 1250 862886034 862886069
    0x90510051020160303050a1205100513091208040c081207110a030309060e01050d02180a0e040f0f03231309090b0c0a09080106121a09150c0d0501 64
    0x8000100229050040182402c400f450440a0f004080f4040101086404105070700003d01035122a40c0003078000c4424401b926280f0507c140611079489500d10404c0c10140c0d4a03010180d5101e1034610b29040000200c144c0c0b0254016140c01e440079101300c9003140b0143c00058921400d1016084d141c02d0516031a03030326203c0f41400800c01e601c10049600c6550ba0400c20030029400990306021144203003413000c014031030700005846500078420b1380301c100e5000140301920941017020740c0c40c0d0903000b22500341104e502d43c580c6e003201c1d8034102c030001d114141404504000c1841180d01d0700d03d9070f1103442c205078464000c801289880620f09c03d21701485101103400d080104c50030308000c015009020082118034003075110b56642203000741a00d010014001000141c0c613108104c008094800354000344412581d440404030403010002d816103004074404400c0e00c3c41048854400e00a0000c1c400900c03140040c405c94001001015140203000c2c0002c11144101201a0103614020589031125060204 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 862888534 1250 862887284 862887317
    0x30c0c070803040806071e09051002010b040207080d06061b080f0c100e0105090a030c06021b0d0906080a02070f020f040b100309050d080915040507030204061214160905100510 77
    0xd1007c030001d41241540e0304214682c4903c2e03000480d5800c42c0c8010031030001c1c000a9004202510070642c003e80002a04824840d20800600f16412414020044559990b404440200b50050002c03c46086584100f01042000e4003074003900b82d0031031500740307808101c043c030300d16181c2c503080c003885001e0b11014003c1019400703214456200308400050423070390030316a0740200804d151450040c95968080f4907403989410303500c0600d008503c00c80494514000000000d0041001032240c44d001034555030002d01c602d01310703000744c1c2c1807150302c031000040c54040c0f5400c1003915040382c0e0490750042d541d81062905c1d6501c103010803000f501543c1b8001030b40c10040c14114200340d25032403004280041d80c400d10080d924002203040c540e50f90714800b610940c4903440d04500b04080d03a40007950190a00c80c01003001c0500c02c040840c0c440c0b00c0c0b80820200c2121003001034543d501c40b4164501c0e443d66450070004910503400880d40809541d00303280d42c05031200000f4a4203842591a20009a1305216550148 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 862889784 1250 862888534 862888547
    0x9070e013c24020c1503101509030b060a1202010e13020f0d180308041b03050d081501030b011209060609090c0303021e610506030c0c07080304080607 66
    0x3a20744060007041020380c01054000d4480600c4c00503201c40000007d0004041c010100b014010050300042c46140354080105868064003007a5404084a07000c04c90501d44034250600700c030b001c0000401c64110030b400542e15102540d030000e8004d4640c070340c1c80c500060107100400f015515003a146803113400301c00264086038941441c10906080050407000401c2d0028075017640140e21482d13401d100c20a41200a0b103a0f412603100501c14031600c450300740ba0580011107a84102c40380c0441414a00380e41d00110152411950400c0c00b2505040019000340840d40010352860700840c008039106554a00c1042121008a02950508000c1400f07108140d4180b00583c0c202e6030001d00a04c0c18641180207548480310800203061100300c0390076202031004000005401c0391303c514544111407441c606d101d6002c40c0c071601842c01c480c242d4002c68005420031150802601d202a000505540c5d42d01031103140e543c440365130421144100c12000407841c10410082020b050b9000141c0103900b49000003400d00b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 862891034 1250 862889784 862889849
    0x703051c0206190e1c020106030314070b0f0a1e0203160801084b060105010c05060115090302060a03360b0604200309070e013c 56
    0x45411107018444482c0f01c45001c041c00c11014580010740c1030400854510309902084070000d681102414044140c0d0198014400c80340261124100350b412100103c039507100d83c81009021450480214690701015407500d54030801f070311000150315000c0d843d14000b685d01004e806c280690000100441c204d0000c1038809810303d10705015082e54100340174140c940d120454117840300c400090004000c41580822602541040c5e800d14480b081e00c406a8004000e0340031a507440e5100b41000003a45510402c031150344180c012002d002d02d42d0801d40c4d1b14400440c002e2541e41086884030000c40940d88060080c01a580385803000640090042d5451201c010004801102106405c104000f50900c0c81c0d03807a041a40c0c0070050312915510341d80040c0062103a50181c006400103800341440e0705c03a02034000c50082c0c10305022541d840da80c03003a030981c448009000340c0f01030080642c00c040d1480207819109003003007011001c00041040b00440c8074500c0f102a404600065080b4882c8050b042d0741340c2140c4e19 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 862892284 1250 862891034 862891037
    0xf060b010905010c03080606090604080c010806060a0e0d1b0f06020d03021c0510090531020a0b0a020a0b0a020a03150501080c07150c030209091609090911030703051c 73
    0x40d01e494400060001440043d0150070310100e900054007960740e8004070303407400ca40200801e40340c94076920b035182d651090003400d0340441c182d500800c81618111080c0c400c00740c41071b41c0308841e41c241c4006004511651280446080314403904058a0b81241c0c0b128a004d00303051000c0d80301d01032515000910307043d444080e00091500c1040b1410030504071440091a60702c021102007220740390340d000000200000d0b4003c00b0041e25101c10f10a04001501100005441c0c140e01e07218449140f5034082c281c00d0745c0040003580040e00380300030411241b862010f0b040c1140350b03005886140e1100d44030699156030443e0340029980d80012078000190b054840c0c504090300341010f08002031308203400a0000e600142644022560101d410401c0002c1e0030f036001450301a9101c24021440c50410240194102d0054644104403260004400c0c00b442c41c250901c02c1c00039543c80ca1302c2440c113000031000340003013002915a00d80544c82d07511075450820505d03000754416402001c10001c5840010121001030301e0500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 862893534 1250 862892284 862892297
    0x1015020106182a050d2f041e0806010608180a320c0f2202030402150f04090f0f0e1e010204050a053102092106070c0c0b070f060b01 58
    0x91469001c01550b45d070100700d00f400100005c004480f001002900c1d0705849421004c10300c4810a54121301c090000c4404107107a49103105485030200010031518050310071164000070040000920510000313800100d0440c0c1070000a640940040c1030007601e040a5580754041440c0c00b00c5141082c480291520424884402139100d0542d0141c0b2001e407038800c0c41c0b1551124220341350559460340d1000061001d03100c107140004201c440080650000c0354240d1041c2e841d200440301e40b0f910101100c102c0701c6d03a8000985054105081240100740c040c4a0103410340da22800074004c04103e214039160058250005d1144d841140240d246401c034480504000c1c2e40184410070080e03c0764465042568403c03150241062210240318915a4580e594011000709602d0304120460199004103586c00c030548201003201412000ca01c604006c06004440c1580440001031f5414882e00201001c28456144030366003030303034a1a52115035007041c4416a9000d02075050a4208007544c0318802000c4d1382801c0c00d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 862894784 1250 862893534 862893611
    0x1e14010507080d05070e12010b0906010203040e01120c030c0303110c0105090f0f03010f060e040c0e0420131d06130f29012408101502010618 62
    0x85007078002e0410340300c4419100c50104400f14006e03500100100c1000e8001d800e40c0010089540c0645040070034940240320311000301e8040c0d480402103405130340d04200e011200703903c0c00903d8030907600d2041d8146d44414542c1400b00000e000c00c18001c00a502079581d10840c6040d18030f60030b080c0901514802d05000307003005030b8603d94580800b03140c134021007211903d240260b49008030f405415500c0e4008403ca00d42000811100141d0034007500860042c646041e8817912001e0080a182040d90080c103041c40e2010b07054865442400d12480c092006803031151498660207900042d14460005008840200308107011102800c01605901100c0c2c0820f03c02c806a01c1d440d0b0444118400c5d07001307411124900040794964040d034644842c2420300c80720310318440d0b95640082071a42204008100304095000800158034403c1d82064002d05010281c010081d18188401c034581480c0114942903540750000020002c00d010124111a10303202400b2400268000000760004412484804041c0e0300b503414 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 862896034 1250 862894784 862894793
    0x2d0219080624010311090307030c08070602030a140f07050f010b011d1c0507030507120b160f0e03010b0411031e040f03081b0c0a030206010f0302281e14010507 70
    0x2289100b850a00300000c10302000c003540841807007001c1c50180c041c42032220000810000700e02c424103c070503440540e0382954448104a89912580c0124400101c07000640030744804540b0060903448515980d00d072500c0320980d149400d10b82024842c0010303940d02c00c1d403003c065800c065a840d40341c42c14482820b41481480000c0d40d0070000860411605602c6072128041090030000031014503005001c86010551b40c01000105981c6e800d4100c501c01c00d0200421a03103000d40318500c2100c8040d880e4110008851242111486415a001541992100901c4009840340d1103a80c81a20b00b40ca502640c0e854035054481c841e005c04040c001c601d02180c0d0800010030101d000152040c0d81c14070b032058503174a03540c0d16400e900710038100d00c5c100004001840b0301c001c40c002a030f085c22140720b9001d44a46070b0365903031440c003181c0c018030000e50010782078044151825600c2c0341c103c40032003c02980160070380e02d1b01c92408420540c0300310340001e503030751243c284203030064900c0400382e41c00c091074400c1c0ba041c0103544 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 862897284 1250 862896034 862896091
    0x1003061e23040b031009200d020904061b02010609060e09060c0d090812070f080912130923010b070c03060903030b220b0901032d02190806 61
    0x458102100c1d412081a806a466402161507404010b048800401c8180199001400710700411606002030302c1c80701c046146000320792801100c000b0b12442c22085c5c943c00b4480c0b06680148125190f83d41c402e0203030900c1c0002c414800740120142e0000070300900300b424020407120544c10000030000b8540030805e0034400010036550040e809400c25413038041d07680d4060003030407100034020b00c4104085480320300d004843c40c0722803050fa0207640700b84409001e0603069411345016034003000c0035044040340440840380d1800a190400d181401288456602d4034040b044404549001c4c441d055038840302001c41c2000c221341400351203080c104d03501d012129603a2000e45507552100800d03007a1078010300d0080c5406903025003041072004d403d40070745c505001700f0040d0300c442034082c0e005c40a02d40301d8460000d06243d42c03d07a060307980c000039800e9a0940102d031040c06800c200902204d101d4190240390050b12190a900c08410001c0720201c900307404e01c0b1195080800082042001c620805070201e40c0190221 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 862898534 1250 862897284 862897319
    0x2218020f0411190e100509090a06030804060309030e04050903070201021b010c03030b0d0b07050306100c0b040816081314030a0f0b0a02040f03110301051e01090b0f1003061e 76
    0x1d100d06803e8016802c29550003450f104001c0c2d00c49071080390b41003004d030008010840f01f08110303416205035552460b81c008880a81c00b01420104040c002400703864040d42c0440c2100e4001c1c14003100c8480f000f000101a210300301d400301c0003038101145a40465030100031148400010121100d035054000d00020300401c0008805030070113466922084170354581a021401151f0404003540301340c40c3c240d00143c0310398030a45a0324007401c201801c13190480e00c80c150302d800e13071580410a0021a29076466000058000d060703440d5003500300070340500015031282c0045c4501200301e0031643e2554501301962090840c0b442166019420248800000941e00302da1820000d41c0101000c4e0151208110b02d4002e00454005101e80107042401005001c0c02d62800700c20781104030028006070fa680024607009100b203040a00c22509928014004171042e5044442c450102610107950800e0b244009000c2c500c04446070008203076143c038240300c40365100480c041602a80303010702c2c840a10740650640781c000e044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 862899784 1250 862898534 862898557
    0x906160311150f06040e15042d0f020402090303030103060e06060a05062a07080c0a14090f090a02090a091112030d0b0303090301240e0112022218020f0411 68
    0x40000030460ba1741c0d6400700ca40b0190348030458010074030041c0ca080c070074001a54250b400c032a0a000440b004c0998941546c510881103502450300b1803e65a100e9101e215540d049078403d400340302c0100c0544007000038500850190101180100104e0400c0d424030301b02504050050342000300a2110f516698111a140c5d0446501403507010200103c5001c4a0b1100d10106480c2c001c440f00050491000500240303c1c3d40c1c01c445505c180396a400329140107854103d5500d40040400c000548105000d0b070000394020005c1041c0c84800c3c0055000811b02e110846020b503045655529034000d1000c0401c2100e60003905a8203000a20100310b07c040c0d07a0b01580458242d40c6813100d044020644041c4243e410f09034000d40244211104c041104100c0c0515507849080413100d041d002842111203c00c1c0340c12101d007600b89998044142e0280404840010640040c80c030310340e503c1000d6800302d031051000c40b99240c0500d601e8070841d481040038445034140c0080c801c2d03080c10745031002202d03030b50100c43c10130018 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 862901034 1250 862899784 862899811
    0x103030c0507080d050d060e0f010b2203140607080603100902010c050a050f0f0313060804081620010c05060723031f15021f02090616031115 62
    0x451070000d00d441416000040980100350f00b81c04c0a07500000a4900102d501900707110958031400c3c00c1e415010200c0d401030100010340c00400c40c40440100804541c80c00d10b400e88010740c58070345407242c1d5150690046415102606400c1c80c1000c007072020b950412030318078090565041c000b00199a07aa0300e401c0c2d044183e9540c40e014002c580c06810401042035100d025038603424803500340140c8501400d1812407070b902900409d0304a0550200866112000c44036035920b040c0c1c2042c6085a04440042c012141c008040041c0f0f0350414888481a00c50762048481004007103500e0398000070520040e21a505010400c004000010307030106d010350b402101032030300c07002150000c201200ca503008a00010a00d078000801d01c515016503241c2e5412814501d500c003455651342e0b520301e645034107400e0000d00058110002501603109000700160303a07003121403405401e0070310030380024105034400c2c00e001e00c0c2151240b00010826400640c0c0341c020500d050080c0500801e074450582880400501c03401e40d4402 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 862902284 1250 862901034 862901057
    0x90e0124080411060912010e1005100b1c060909060914070b040b09061e091009030f030e031e0604020913150c03110d0504050c091605030a02040801320c03010303 71
    0x1504d240746d0512400c441d00910400c0701c1a0b051503166084101e8407078109041100180071107585c0f075000001c4030080c201e028a4040400318194444192040c1940f040d130310740c540094012400d01844103510b00441c0006095130301440d0024030b80c803105026008607080080e0400140c101c907020341d000c80762955145561407481324000350481c4035142011010f0700c2d00003448005a400358000e0007640c00181c88148000034509000c3d1503455080c440104480301c4003803a84000b0b4410741ca0480f011801030200c6210800340c0e140445003c46014011007298018400c001c00e49c5007820800781c00c01e03102c545200d2134130003030f4a17003c403003c484400b0b0181c020703196899038005a100b60310180300e5851403003010b510f481c2491020006847d05503002c2e211031180a0003a441c618107100c40a00170555800b41810341e8000480c01e0321a5080140660301c055801c2c03100195814081c0515601a188185a80c0070000d8562405444076500042ca00884030342d2010803181d606c4410490f41500e800d4100400d8a11 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 862903534 1250 862902284 862902289
    0xa0f0e0d0303091419060c0201110d0c0c120201020a2a0803130206030a020703081e010611070b28051c0b060c0a0b1608100510090e01240804110609 65
    0xb00300030401c80d01d07072068841086044507101c40179800f003880f400b410b0200d40d4005104a0999451002041c0220802c000619035a203031036000180c51800350030040d180001c6501c4403040001e440c0300c0980980d40010360710713020550040700d2205801c03000c0458071a29642443d070142840203ea001001101c000000c900200c01a207403540c26603500500142d6a450042e18200181d004004224086048200402c020f40c00104400114040800904903184c0c80c0c0703001161111460018070700d079402004d90100c0c2da07142d00c000030140098501d001c500c400701d450040c102401c02d0341074060308103c0305000c5503550b519081009015100254400b040c04180c400005000d48950522010700d8840c65218208001e40d070700b180c500c9507888007074103508100f102d9801d0f0703840901200c4141130801c1002c0c0c00d00191030100200d9801c090240ba2104155890341031110180200b82c00c50f20041002c0404404808081c010083e00d1000302e281003c4070741403a5544003000382460402605c43d40c4049050901038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 862904784 1250 862903534 862903553
    0x80a0f090b03130b010e04020f0411040503030c03190206070801030b100b0d0b0a060c0209010e13020901060c15140a0e030c120310120203060406050709090504080a0f0e0d030309 78
    0x100741c0a04400e5507400e04480d0500c249007803183c02c0380d60741100400018648985c2403001c0c0b00380e8020784a00d00700102201044001c0c20704095102c4c40150038800420262002c00180100120710001540d440c030315206507c0341942c0080a0740d04548c4900204500c2c80c2c0d2026400d41180c0e444507490355152244a0345841d40302541c1c000d250340c002c001c00c0d159025041d64014084c04c00b801e55107405900d80724002258583d028400194100300ca9a004101c80b482c01d1400c3c6504c6140404103980c020385d548c0c006511040280c0c0203400041e10005a1001c6c884000081020310703c01d1001006914012480c100c001c0c08010301e410916682c80c4180c1c06051401d10890b201d02d40494183c401c29400d522400b40c290b0001da4252101c0e2004400208043c45800d003651582a00200105440c0c1d4440e600c170405440000e1903181042408807000500810324068503000b02e2191607c1d0303807600c10143c401044045103217140420441d810241600c680c44041c0c0500350700c3d03018580410341094500741000803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 862906034 1250 862904784 862904789
    0x2712032101090b0105161e1a060a0f23150309100b011e11030d1d01020a0212071104050a0e010e0a1106070629031c0518210d0207050904080a0f09 64
    0x641460990a1f410000c090420103058a150360821025440b8107080c4000864103000c3c4070104460161705002d2122443c40b148460041c2459100e248060030010402c00903201401411449010040c040d58103414800107204012203072003040718102100c0000e0803010b07001009080c0600320805154090300c5800021310080500c411a6941c00c074042880d0002c0010000341c1e94130408074840e107400b0341018001c48a880c001580244030b20012101518056071100e00102c5103545c65807400105601e4901446110b00740380e03c07000410044c40080da034256240388807040d106800200141380042e02d0b404180706200c0c010b41e581d9840c1c02035860000700804a4050101d0801901219031000c0c5d01502c40c0411b60080c203030f0969607a004511509000c204c0e105004c100412000d00c80c0031004464450b10803e8524000c00d0746080c8030b1190500040508100c00c0354000742c204070801c4003510b40411840008043c19940c2c104140b41940700d100c00c50254510042c204047e15180e118101e01c204130400c003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 862907284 1250 862906034 862906073
    0x160302090414070f0e10030e1c03060609090209130b06251103030c0c04090609060f090c08030408030f0a09030b1312052712032101090b010516 63
    0x103110342c2c842d81d000c15050b044800702c002a882041e1041c1d40c2d441141d04c19840c0401070100c10100c459110240e0143c01c0011a05000784070308111000041c002c291010006d14440e240007401c40d00b00313907000300307010840d8014006140c010040020709440780400f01d129003001810000d4a00440307400164a4440c50810519003203008042e90b8864146240c010314451241600c504441c10210616480f4040c02442410303a403c551021202c40c182030300300314429442140002071090039941c0310300880d80042c8000d55015035907201d031170810980101031008ad0601c04010760500b4a0142015507d2040981c010110600030903001d9040d800fa04200d009180d000c0d28151452034200303038105414003040301c05e031a00d1181d041d48450440c011021200c4004c0ea0803800ca400c03d071860101e610428500c1c034081e402440340f0115041300b01c400d0026001c401e50245030320750b42d011510344ca05c0f8403071810717000009110700e4440a880c0e103a82150880d8485583c60300304000c2580b113814100d40041340c2c034807400d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 862908534 1250 862907284 862907291
    0x20c1516061d0a030f030e07050a0b09031006052b020603010803030a050c03010e060f150a05090f030f031e0408030304080a031503030f140d020c0c01080109020703081603020904 78
    0x2030070890260055810403092103101101041500c404030359400d803000c1c001c0c000c00c90301084101c03030314400c0e0010100760f200407041f621480da541000c50f400319440e0b40100e1b080e02c00881c8400ea1450184040442003044480a0080358100300002d135800b55003100d05280d003644405504264514509841a42c0790001c080a07160340e50303074080c107840c1da10031107120b4030170380ca8200003400c40004c820540b07050312601030fa0402e49a9855041c0503140035042000e90303206400319035281064840030018502800c40d82d41d4182c941400c1c1c0c080c0007601f400080c0c000d10903000307800b03512804c031000403d4075941e041c0d540d04c64000c0c4555910002c00e43c8599000044240800800c0109000200c80100708142940e5001c0113012409480c43c9070b500c015000050000d0760342201c6408840c801c805140081503640003062810005090036801ca074020072504100c0d42080040400941c0c001c044503006005989040d4500302c07090794024502070300105041d00f08040001007858081c441d45c103403002980090801c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 862909784 1250 862908534 862908577
    0xc08100b0912151e0c0a030b040f0516020d020304230d0501090303050f13030c02191d01030c1502060604021b060a09151a06030a090804060903050c040c020c15 70
    0x280c03079803401140c0c03c1c070841c0003007144c0c0d5600e03000c03801110b440b41c2c0e24048482d080004940302280948190350403035601030f4480c142c210011070302d4403d141c05035580e4100f140802001001c00385c00c117002c44444000b136400500040040100c0007107641c080700300c03001d5608001e441d0760000445484c0f00500280056103020750840801d501940658000c1035661241c400a030744904003000d2010400340c0c000c000803401c03d9a180103040400704414400c2c0c2407140b00a17819214078030070303410b072034580080c2c40c1c3c2540c903000410500c0300c080c3d980f00281c01c640e116142d820404d100c3c082e54401e03000d00144d01035a80014940c06a01d110f20b4075699605182e001c1d95002e060a00d1540d020344864101940d5241040642c2050b0407280d12590a600d218185d071906540f107035004101cbd050b0001083e0060031900c490545c4009648000180003034030850302c4a804160441c105945003101c0c0d95409805240b43c45641d80600350006840742540e1300031101000406c9040f120080c02d4001c0e1a44220f0700c40340034988 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 862911034 1250 862909784 862909813
    0x51305101701061d060702031b04060b2802030c0618011d0a060e030a020d0c08090d03050703020c0a0b030c0703030e03160212061b07030203071b03060c08100b0912 72
    0x190080b40884207083d01394071000d2081000d540b1843c0d8000350b00d076004114541c00035a40b00444050700b04028000030300702d80e44c0c075880001c603031100311060b09404107201c1c2040c02c84903156101e0050203040c8010740c03c00c1c1c042541030741d4400c0c0c050003541d03001a86640c048604103094012004404c40201102540d0005111150f030303c241490302162a5414420744249599000003a540071a080c0d80c020441300380b60784002d41d0040d519141c01e407403600080003000d00a40300c4052100ba424032070750381c450313a81c8001d003802400c01041c50074040c450460000100188a03400c415250450034088090349e076041246416401018100d804803031a00000c1100724451050440c507000f502d0003552400d4090302c520070a035803103030811201036500740c0041905581030002d42c0003030900e1501c6401187e140c41a00d032104001030f540b100744c941942c1003545091040051502541003000e150303045c0f000c52424801005041d8110a00031413000da034010130402c070f42c1c0d950000405019507950045c0c91195669021 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 862912284 1250 862911034 862911047
    0x914011422150512210c0f011505090f01031203110c0a1407140d061e11031e060d14150115090b04030809040903120f0c030c05130510170106 62
    0x3d818842c03504004503d10032240400c1c41010b040580040010b0380394a844024020340010400d40d40c14070802d40684080c080c240318000c1c150000c0071804516601d01810440f5048000f44a100e80107611300c010800a9540a400c010a0015003804100b00300040455078041c09111468503151051040c0760043c01800118418001c5a030030039039010689900c0c000704c1706804025425005825900f00c0f2001c41e41c40d9001010305e8401c00d18102c1c8017040490481c0541d200180510a90b032800170600c080589080320b4138200031402d040446491501c40b00240e841c0c8030310040070740429040340c41000304400c203110840d0030131849004801d0035615030b41c6120041c07540580040125801c21000700e9a82070342030070703a82102e074010000f078906991a828007001d042c0d07003c000c400384800070304514800f807040d015403000354840c100001195402104024241c4400e910340d50180700042000c0003c5c0c040780004039098980a8404400780c1d817a4a4003100c10410f100300081e206460603001003070203948140c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 862913534 1250 862912284 862912289
    0xa080615191202070308041209030c1517070c0b0405070f090b040e0c10051c0207050c0f0f0d0b1801090b040b060118090507200304091401142215 64
    0x1d980300e0081041c405100104e12480d00e0203800302d40803000140c00940e9a0752a0001d4a156180c0384951903540e83e80d049415160381c00c288240c01c0d1501441d20b80c80d43c4820802c2c000f003aa0582c0000604228030094000000e40300054040c0f1480c02c00681849410031a420003009003c800c0090603079901020401000c10854403403040e0f007820680d50340082c00182201501c40014401c5001000310401a80c20307a10101ca41101c4504a01d980010003510b40301404140d07000d400500042e05440007086119030501841d14840c0401c910745400d151034015907120802e90243d580310b110b49404140c001c000c1e20301e50581e0425805c0682003410072055200d42401a4801c0e000790b105603c0e0b1000540f00300c0d10f80500e00c0b00c000d0051b6420003011405801c642e40090380c2e801c140f4600d2000004202008000e801c04000e00d610000c1c00b04841c1403540b1420402c2c1851411042c0254140317001c1c0c282500785000143c0c45100001007071070280004c2c41d044400c07040d04800070090070205414518001c003552 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 862914784 1250 862913534 862913537
    0x4081c06030c0909021543210207060e0402180616170405090601030207030e030601060206010f0602010608251e06090b031303140708030108070e0106140a08061519 72
    0x800c418400340030b00b00c3c20380e03024240c1031001d007401c001c40801810b60807c4541820a40c00c2c1031a00c2c100806031200b1451010f20f01401c00b13543c02103903901c040c060802c0d07403035244011580042030411003e64808500c0d4003801c0e04560142c3d030354401500e00105105805c0d209540028001000001b40501421080a0034031840300c0542484130411000301a0046110751604954180300044866101c1d500401c840340c82403e101c480c42c1100300c003203490400260001b20141c2d204034014000b0304181803462005000e10710090203054100449103403540e21800070914507201c0d80c134494805500c0031340c211000c0d040f403841c0c1e60080e4542c40200002c0c0601840341c030340441d1703c3c0240440c1441515040700e205840d40d4134241100109550f0032161382030b85280044e54080f05112510000309484001c500030b068600c000d2060b6414070585c2180c0f000107038021418400720600c80f6100a00c0807040d02e0401009003484030403603903104049189403010811b800281c100004620041c401072a91089500d50113 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 862916034 1250 862914784 862914799
    0x10020304060b090702030f1c09150b040b0607080a050f030412080a09081b0f0109050109020a051002060a0b0d171c0515060d1407020f0c0904081c06030c090902 70
    0x1000d102c0b40f8801921600010f8008008501e030f4100902e0040c190a040a1054141c041d1089485421281645011642c403402c0300035800300b00c42c0c1402652680942120100880316801c40052150710407042d0042c081d0402088003074906000380b00b541c44903414130700c40e155203113010720b0010815501d07400d210300441c06010220b60941c0c80e40c40762440003644080e0403441c2a01c1c4214807100400c080e2280810307031003214001c02101c8400c0c003542004a02c200300100302d00b03210b0720410808003110340019003d182c0c82c80c0102e89041d40060402d401400c04140003550b444001c000c1000c0f603803048006440c240b03800d000d42810700312500c000e02204801c8200b281c1c2040c0355440710801d8032002d56801c800d03400807032040101c034a0440014400188100320024840c2171101c90701219640441d18400981c1250300390695060050054020142c0100c1d0f180c0005c1ca441d540c3d032419400758401e01d45600c00c0003402050804100c2e0b00c654080d540041c2c1c0030803441e50b10031307041e000b43c100100220f01945a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 862917284 1250 862916034 862916051
    0x703050d0f0503040f0c0b0417150610050703020106030b0705030702060a090203030a1110060b0403050d08040506040605180a0803090c0409020d08070c031a160c0309060513081002030406 82
    0x7162844039012802691014555119600c481199481c02c0c0c4086e03038003950b0010000745200c1c2c0b050003031004011030ba0840304101035200d07000341420b89141c40d614215594808107c2c00f5a02c481d00050b000c02103040c02c1d41ca4240608089004210030f410080481d080c90081c01682500040a075106075816804c407100795540d103690006450650700002d40551041c044141024010b002140d2081548400c48011042c0d104000d0107944032940504408c040006084c8140301e01401103e19050141c10300303c00d14240b43c0e0f1100d070380d00d40050001d0b00340742e500e00c04a45801e00c4541031070f6507001158129441e0403020308100c803142c1d10607102108035100d000340c050810b040500904215540046c0302c48504440c1e030b22640990350018404664440b0003000100010b0100380c0c0d50880802500312802481c0780c42d02c0c400d040a2070150b4080180b05000d5200d00000f03910412160a4072b585241254861180804a0964542a4120502900903010141031614482c1c1c06588114001e68040c03000c400e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 862918534 1250 862917284 862917287
    0x2e090503030604292715040e071809080903030c0c0108070e060f130317030a0b1e1003021b0f100603030215060102121207111605040e0118050703050d 66
    0x9211410100101060b0016a0120f1500c0c117000c0c1a604c83c541c5802100c2d582414100014800480d80d6500508100c800760a0600f818414820004281c20061103183d0800d0f42d2070800e070002d041c9900606480d80074480401c5402c2c0309469181c00c020382180d4440c0d50005c0c0d042c1d110000003099600040c10b801c00a1002440b840300d00b4021400900518074060500f0b003001801e5100a0b00721411154114000001a00b540c2c5e1982d280c10343e844140d922810300701d40f481c041d41c0900703280364030901100c03902c1217101d1880f250b0001c202c10300721036542e40b437110101c065020b8002c814000400c400c0d40b90300010100008039200002000c0c0c00165120603662303510305000c50f09107000150050344100b141d081080c410000440e0044414012103411042181f40d07010311764402201c2c1f2501c11000e005001a081e0004001c900200140c4050903070610144002c1c01c80b003c852280c58401c94032450700140400b42036004030800c1889481c00c00002c0c1c7c25080403581c40035030748000c550600c02d41c0c0a40200b036 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 862919784 1250 862918534 862918571
    0x29150a0909112d0108101a1213170d060b040b0703030e0a030f08090304081b01120605060d0908190305010312050c121b070f060906020606032e090503030604 69
    0x551520200c00041207660044500b4030008118030091b0412041c003148000300345406582c02101510010742e98010030150781d65141024180b28221706120181ca4009407100c024400c1201342a0710241e22900403801da00b015140991040c080c400b0300140100366080e285008200305402070300c0510541140000b80c0380d40d45e1104002600094a12003940d1015105980359078000700502c0460741440d80352054241010300030f500740c16500d201c6104d03a00341d035600220b140c14074581240c400c124580c549801f1400512881103845041555070340c1c02d40811070504150380d00c2009645080387e64502200c40036004000c02e0100740c85000c502c404920030603218008583c00b96500f5409001c0c1c8421040c0001c100d130b0442003c00c20700d00760481525000c030104200c1c5400810903801e58825440c50300c0c4001e008000d55800070011500142c08014103030f1000115440c103034907100b01d91071150b4040e141050f140c03086036001c02151810300c5400c01c103001303000000c1c5000740c10490707082240c41c4140c00c802409 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 862921034 1250 862919784 862919839
    0xb0603010f050d020a150302040f06050306090c0c1e0c03060c18090612010c0e100c0c050d02010201020f0a030507081e07030b032829150a090911 64
    0xc01c0c19400082c01030342030050450f0040791018040440080c3c4448000a00788003115241300000e87c041800c0142003010102d802c01040c99081691850a017480807440c0c280005004030114080016615101d5104000000894200c0c0446807a41d030200031801e620303680d00c03107040c03846441050007180e00f000325501151091070402842d080c2c03048020041c0440d801004103007503800242c0a000384c01e520b00a000e1510001d21071341d0750781c441400410400000c41c039401540c00c10004150880d1001456920420f01611350450710004820780500c0103e000e44a1400fa0340c00c070007004603141500503055013040d40a24a942c036075400607a43d0798048040c02e10300c0d143c00c016944c548e4000c03440040c02035000592088015090302c408148074a914011546801003081380d00c5034088440b82840380e4181c10b10520090f40762040c0030040c9120f6016200c1c04050058808141e00c1200a1001d0391401c0111005041a080c148040900e500380040030001d80f02d4000e000d1018142c8500f4054030700c0728540c1c0f1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 862922284 1250 862921034 862921049
    0x3031a221a0d110a030b150a060e0105070b1b07030809010e03180d03030f020309031c021608030a0e0106090507120519090611030108060718030804063204050102010b060301 76
    0x208441c55803030b00595208045020307a004a143e13a004000f04005c610304511440c0c103c071404880c20701e076600f03010405049503c400100b06c074040c000103c0360703803007400c80310160f400242e4640c2075210509000350711800b2494003840c04100003030350b10800d030300000d2040c45944520000c0041100b00f10140b510391183c031468610490301600809024503012180281c564040d00d8002003440d040140340003282e105880d030918a07400460502140c0281c1d25100c40e292210300010350809544080d00e14401c0c9100c00001c04443e00480000c80741c900a5202802d54004080240020344e80c50701024014981500d00400045401c1c40e5032880c002e00d401811301a9403a180382144500419464100800010004407109520b80d0803801c20810f03000080c43c00303060b040c0060045030501741c1019221398800d507417405158001907000c2000c22102003c0da400c5a605041c8001030a1012182d003003804408190603081075014811022000344020141003070b928283c008101c055810400c110590100f44904078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 862923534 1250 862922284 862922299
    0x21b012009090f090c21070f08071a16030e010e0d0b0711071d0709080703051f020c06040f4d062d07080703031a221a 52
    0x420500301800c3c0c3c0b940c0002c681055502c0c1180000001e8100c0c02481c0700850140260070001e4074808052082600800400c21024681071500c1001074860340745200382900e40d4400d03110440206007040840c1c2c081203140402d100b00c18440c4c83d01400384413149200f00e00080c100c500a41c070701e0800f520007a454903000710514005030b8a154088a48200050100c062402080d800181680c0001c4000031207001040d055415890f11440040036000300e64070103151540175a80410214a020600201040c0b001075142c1e06504103286540180c41080f20740d642c00c1c480d05040001f0b001c080040c0d060010710920f00303803000740c1d0903921101c06c03040f00c03581c0140d502300ca540c004c10254010b03025115102140b80942c041050351400021002d03003222040f27800c5c00d455004009a401e070091500c01c011258064628102415502c8494070743c083c4041c01424940c0d203900d035003813003c00903113424255100101605910045520b4846103840003551070303481681003000141ea40c0010752802c2d0007803040644400c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 862924784 1250 862923534 862923541
    0x60c020609040b030f0109110f0411040311040228030c09150c2a0602010f0203070504031b05091503070806150d031206090e1c090b0a03021b01200909 66
    0xf0400781000c6541803049000b90719415100303019814000303000310043c2c0e2002400314107008051a600381014401da20b02920240180080010340b41501d4100e69500b54140841000c54024030800c0c0890001d60f5196500e42c40b140386580400aa19031199000c0c00020000041a6003021660007406002400402044080c40c402d0240a040f1030141004000c55800c0c1070740020001502d40c06288105079541080c03165a809003d0001c403c481900114a180b4149100130103d01943c04020000d01e250307404002101c0103802c1c8400039020062032500c840c01e00348251031010a8800c074aa0180c003a202d40001d40c0d1401051480c802c5265089504882c5940402c00c44081003200c1c00300c0a01074070080c907c00b038030101d01c14100900410b19000403900c1c0b5050170a840d00c1140040c001020459000348801a03900058620803502641003450310303141d49403019406401900e0742005095150342134039454880540103001c3c0e484942840d84110b104002c0696464413882c550560001a9072022 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 862926034 1250 862924784 862924789
    0x6140103090f06050405160f0b09090406090210200718110d090b06120607020d0302210c04031403070f080a090302130c0e120c130621050601060c020609 67
    0x281c0c0c8900d2007806000c207910300d0790b611541152004d58080c0c0300c5500a40c00300301c65900000f030702c0010b450710701d05c95180030340b0302103c051a034816682d40c0c0340201d0f0035001040800c45150040716480303900070810714418a00f103400400140501104100f4601e408600307104040003c40c1d031005840640c2d02e8540580900d0a40c3c402a100100d400e00a000007040903001003041480358664644c0701d24003c40310307400e000c2304102801010b41000450740c1c0008040c05411600002c0c50b4010b01107904025803295038050003040c8010b0300a00880c000050003040200c01001c5000402c2030342d108505400c900146503071080d90b2802070400083c44056075030003c402041400000c0c00c49989645070001600f5160350100311180404582c85c0c20280e120303c1d8851401c0e0304510405019001614442d2005080d59a416900e2a25410700ca000e000e05141e225020b403410f400a10180c108100710507250030008001c2a085001d45006903441d00810303001081d03903072046400405458000701054285100c0340c0c00c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 862927284 1250 862926034 862926041
    0x40b21070c030935061e07081b04090c091a12130516170616090603050a0b0402073507060c090e0703020c07050904050a120216090f0f06140103 63
    0x25500c1381d220610480c0c052011403595030000c90360540c0d0240c1070604000d6000043d5198807920702c81010364500802010b41d510a0a0513030100314002d00d00c008101c00100141c40e403189400140c0302d075003030006408000d600807115400312283c8008030a16a00c80200314041d034054036084403070100c03146010481d00505c20f06218601c40c000c0003500d0403c1c4509880c00320140300b690100501c040d01802d003955800c41405400c4c0e118000e50500c08201c110302d20300506810541c0500010f250747e52000ca5149241a401203201d031101800c21959070b031a9080070003002d1710903480c691211007458520703010110000c002c070205000a668031402c0c19515510507018002003001d820412410090000e000b55042d40180c0c010700b9141c0380141d880c41a000b0381801c1c03a031140c2010f400f60501c1814040024400200c0003075607900140d03207940344400180100d040291025403d60600c8480c1c2000c02e40c0245688010782040c1c0f1390804112070036102c448082601c05910419030011585031001d01b0550180c1c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 862928534 1250 862927284 862927319
    0x2091f230334080d0306090b0f031903020a06050711060108031608091c030e13140703200703091502010e0c040b0406030b0c0301060818071505040b21070c0309 70
    0x103400380c2a00c3d4541d4002032600b281c101d03125001035101c4c0010440000301e231080c04103441098034203100d18090000030a6a400403a40d841c40c44c02c40d06080c80040c14420701040318072691089060002d07080a42000702410340d41d5503041610301420700000368000c00001240da51281c0014804a80b030351945580c80a5004450426000985216244811840740d44184229486078840c4a51055200f05011546a10030000407245107058990074001c2240d000b6164440c100780707408102455800f034520000d8160b0b01940e54200800716a03103040680068082065410101100c540c03820103080c103d00b039442c5414034940c0d9800822036a036050030141c0041da6090390103800410300c150b80b0f81d510014010300f00c0c2c0c0c9640419001c801442500c0e808000b041c1c220204010a404640400000c1d5864400c1881078002c000d07220150070810501400075140246681c40100c0e03101c0c000344110210141992003400c01c08400c00001411403400f401805400300e0305940c48a10690400000128125840 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 862929784 1250 862928534 862928623
    0x1406130f030909020a080901060f060504140f030a2108070f0c140a0f0c0f0302010512151e0111070b1210031e0b010b0906030402091f2303 61
    0x401000c80c40f0001400242003a507040d40d181b00740ba2400720465801c541041d00040003070400c5003420405168460b00ba01c2c10350310510349030115811078a002414144486050a401d8040d1100742000d0000c45060b8030402d1201c2c46c40d070005180d00b1242210000d400302c40c00c40c0031460340c0c030000520034130960b600680b00f4401d40340700c40c0d07030030403204064984064108116101c07411480e500040200409540008101c0d0782003004049040d54006801c902a201071017440800381c000107281d550410004840c03540e400b030701a80301031303040b080c074a070503503e2103855540451a000d110101c01c01000590700c04441c580013680d0300b040540300c6419150000a0078207006040c1000000c404141090401030b5010402584140d00d001d4134640340c0c1500c03030140d105400600041c440c0d5150380d00ea80d022280d016074103c80890b49035581e01c0110011310449020a900542050b2012510005004403688c140c1c126060a0100610300e0f002c055441e907070000802d240c2495001c41c6e00b91801129503c1680701d141 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 862931034 1250 862929784 862929797
    0x307050a26010e030903121306050c0109060501031a060d03080a0e0c060c0a1202060915090312090106060e0301020c100924020901030506042906251406130f03 70
    0x241808a00f50341c000440c0b448590000110074070b551904200c080c05a45c074000e01e4900700200424600c5800000340324800a1201c0003075400241760303082d482a4001540002e040110b56141d080c80a6034030b0060f0f00c44200203d10b0000300b1043e151254405140c194150b448000554505565502510b40380d03404400074460304c1101d6109944400162948480c1140104480a0709040c5941e010707040e010b820081d500030b4400d11440c81c00201304043e803c018000b11401d030f03442c2d0045e114918850b108070640465a61414480d542006400c881e08640c05c5641d0107051142c5803080600302e200d000c0c4600c10700c0d44140d0b45000441010303002480c440c0c0c05109240007440d0021240500c40010b0b4080100566001818000a68042c8200b98100c0350a98041101c0904000d2100000d1105603088518107c1862514490354609044540c1e41c2c81c001c400001c103071903113854400c001e0800302c0c04441c1301811044542c284840020340720720031341040b51a004410602c0e1100342c99064031501c01d4040041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 862932284 1250 862931034 862931099
    0x31b1c080304060b0405100b161419030905150405040c0215090705180c03150a09061215020c070e04030e090103051b0103020c031c200a08060307050a 66
    0x4080618882c07405003402240010220b010401219402005450501c1c00d1042c14481e4801d40b00544090000720110713003115200714148552a00c99100c400100e510846618107034580c8000141c480861080c3c40d040500d5441b10204458100300700c00c0480d1400d01840200030f5031400340c001444c0da100ca401230341c04441c00c2da02131442031103040f140180142c7c000b850400040c24540c01e1805495040a181d01d03980c01c1015180b86240300191880b031808180704100700c020380c0d5400d43da40c01041141002c0085c6075031800300c3c2c218001d50b40415900441d40703c0200301e400e28a4001c55490500050107048002e051090100b500600a0400c0d0308200300c80a0b4030030562241c00d0018040c5000d40c008004c504424110120b1155041003014101401440412800c241c0082a40d816008103840c915200c511420380c03800030308030401420204003100100080c40c0c2107410041032061307040c0c0d55500c1c0c0d540e10030050507502d403450710030160000d004c040100182d5a07a403041605420090281004081c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 862933534 1250 862932284 862932293
    0x403080301030b0f250c2109030b0112050705100512271b010c02030c040c0302090306010605160206030408070606060905180105030601150c0c0e1005031b1c 69
    0x4009802c2110300180380810710451100140c44c0641c410070f05c85072203410685021140040042d2003040d1003c0c081050343c1c0e4001c112010401e9140d4580d074a40d81250292003001c01010905a8807007a1240740b03000001058461843d1541e19100c4c0d01304c0b0003030400925150a12504c107403a00306450410070b0034080380503111541c07001030b801400084e81a42102e0f00740407a100d905401001401c07903982c0a030b8240d0b0307460724400400e03d0100c502403c14440019850000c03a040506c045181c0d0f07172061510354009001707501070380600140300c41541107560b160703201d00d07065030203105100c0202d020720707446124580185800c0303004581c01485031041d142004196079508041e640d40b6002003000c84c0710380205001c14100940d00c80081d64000c010041d05525080220741c40740c506002e05c81c1900e040c0e08540e5010b0b4010400c025103e0790107121011010707030301c590301d1241003002e880b07114010001e04800a054580055040045070200070040e85401528080000700c1440d100d0003100c40b000000c0101c0441c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 862934784 1250 862933534 862933537
    0x12030415050a1a01020c01120b1507061a220c140d050906100e01090203060d150603111005030a0c121a0909030c030a0507060b1002030c0601090c1d06040308 69
    0x10074440b2400714101c041c40302c03001d410081c0000401e0466004040610b06a0b0780704104116010350b030f035000a008030082e07000c20f0044514881c10075000200040713140400215600c9000400145421804000d0008003084201c41c203031a604000403030b032a1114409544290300004480b106418499180324544032082c0454001c04010174050b0344c0c450030042210410b020841e0f0008100800c044101e0600d000028036070410f0251020740d5901000051480e1103e001c4124002d400100c0325048201e00310002c0007030070042c0012903c072480d904081c49241001450428041002c0d01c0300b030304554480f00b03004010048035020004008000204803032100442c4519010054800f0344101e42d04400018400321040217403a000850f4400c02640540c00804001d0701c0d0061107a00d040c5a80b090241021806003c0344001d00b90300064502c0c945401c140c0000c01016413000f10b4068414980c4c1c0c959445040f650190980c4000c18541a0311010481c2010340d11060f4400c0240f13090704054071381c1c6480915 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 862936034 1250 862934784 862934791
    0xe090112030305151c05071710290d030e04020c010606110304061e09030204050a0501080615090105010f1716020709150306050a0b09150a090e1203041505 68
    0x21140d48291003000c0c19850300a0395401100404440c0503540b003400071072214840b048a118415020322050420010180075250090001d20b102d162010324898030319869441c2c0c580f004036910b16148010003e1280300800042d4200c45111001c041400d1005000b200030290b0011006c00c6003d000c0e81282c0d54561024103101c030605000081c2d400e0800078040d082c0c082961412029910521040020303035400301031078085809410b40c0c0070b00500016403d1380c80d0a80f90300700075480b03400c01082000b18040c076030219040750310b0282190600d440d08030b18102040c4c515181c0391703000030100c03005201c0381d40214421900e0003182e1524a076040081207400e9180c40c400c0c1c412500b4090440c041d050195410018035026240c03865040101391038041c03103030458102a100041c0203544410000303c40d030007103520824540301d002c0c00b400600d00d440318000a0081c0e5041c400e500c03c854000300402c4500d014803030700c01030150305401030200850700c014042054200a208580000b0001b00041091489000d80d500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 862937284 1250 862936034 862936049
    0x302010e132301060f110304031b0807060323060306010918150603260a080601141309050a0603020612040f0f0302030c0607030e190809030d0909061a030f070e0901 72
    0x34650600b01300415129444824a0400500359814250140040111401c403940300080d0515050041c03268030009031594001241809072000c001032850301074000e0040054103500c6e925114501e0303845103200b000c06440c61501a0301c54001445400b010340d00c2540302c0140034034090106000755a40c1e801e200c0403102071884d120b8441c42c04000b008030041d00380555a1380350f040e4010313155048140344000d0003039114040800070000003080d0182d015241c07412a012a000b9625903c90900078801c20164a03485213980d079514003030004102e41294801c43d02602da00501042c0360440e962180000441c0140051b02c40301c80c581003c1e0006428a81d07010280352003070300510f44440b0100344090403c9002003010040c1810404a00c40004000c40c40c50031312000c50b40350001011150400358002c5c0182411b2030303050310840d141219940d8015015508584800d40107000c03140e262104008040c0c0c55140e9600c0c4c0000c01d02c04a1062542d5445003a8440356514040b940d1010200008890440c00e034009003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 862938534 1250 862937284 862937351
    0x81903020c12160b1603181511120903030d02030c040b03010e070f02072709060f06080705040903050f0d020708160b070804170c0c0306010f0602160302010e13 70
    0x5150200c43e00c5500010301c0c10710111410a82820010380c010319001c0002010095070000140e1542969a0704038041c160541200030403200d03040c1c01400060703425084e1401446001036446a0a14902c101d540006010700070754104000d11440c00c0207500040c005010310b41080c000840c05608440180d4001c01300303158265003904103400e01030b00d8140d98810081c115006614188560040b031980d640080780136462110b0b910b40c0203d1828000e201d0704034000d005c1d9003040c10310060000d00c1d030802c03070136541c03000c0568400d10350394400c03c02103d941260082c00701d5821b20941925000c2180500349041c0e0585001d0700d082056950303054180d214104260481001c2d565030000c0c08003207960160301c0441404d00000700e05194030b64480e040c0c50980c104c1c2d0b07040000240f9003000a0248064120301401170225070b410350b140d0000503040b00d05030150000520a9100b480140d214801541086a4040c1c5401c080c500c0e090040c451014400840c0c480503e0b151b1701e11120900c24540b1487d0048045003940 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 862939784 1250 862938534 862938553
    0x5120a0e15131d0106051b0d090501090603050f0f09070b04080a0c05060a0801050f0301020408060f09010c080c0904090309050d03090305070b091c0203120c0d0e010801081903020c12 80
    0x4075000d02564100c10f038410b00070a840300c2410a190006030548203503040554071003491541c004984078504095907050b004445000c0344494220528a0039500240c0f24a0620390320746038118103c480c11181e10000900c0c110200c2e401c03501642c0500e07082007801d000d4a403465200c1803450210b50050b84440f0690307100180d002e0610000c5565240a08021510f40d0b1601800410042c12900b060240b5403041000c1061582280c5d801d50468004100c840150380092038810400070103100110348100149d400c00c4a10042984aa41428852079209155a05010400003407000600c0420011018002410400b08003560b50100404125220f0b5032151400d80c21441c21908292160b17103c0e0f0030050040c03200302143c3d503170900300003024640d200030400780f18040e00000e0b280c00541014030031150000600c52031000c4000c210441c4031140c0740c40c1c800300440340c00c00446940c80244220b0700c1640081c445a048451850040c14007580248100c4424803210390020b52140748103c140c034035070b238401c0e0640d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 862941034 1250 862939784 862939807
    0xc030c0402040b2b0c03020304170703090b0307030f1b0e04050106121a10050c0601140a0b030424060503071d01290a05220305120a0e15 60
    0x490088402650309505103840c12400c50098050080400350f4050032002042420100c40007146082d9802da8007800142400440035001b50b00688042d180751000c9000e40204d417100c00f007215000d60303241e6519a40585000402c02c0740e41c1000d0040c0c002c06480f0042d05050080c18018030011000901c03c1d0065120b810001500f100c5810195601550a000040140503048203800d11000c108000208849000f500b80e0411059080d9415501080e00d035101c90405a2000103011100c40328401c03110305989130804103000340c450a09455200076400401c2c400f60b201e81005c2c5412034454000d007884030240d44280c4c003441c2c09011850f92125911075040015203400c001001c0104060103480340c08101c070078103110041105000c1c0421055400c41d00b40615030b8421106500510f042080d82e4a03a03842070001489a1300461050104100ca03134903030f1018451800001007200c0c0c0c80001003402e002c100c900b00506d42c001d000340900340141008800343d00d49840f40780795110348025001c0e075992000202c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 862942284 1250 862941034 862941043
    0x1030f12030b092d010f061215060306180e030d020f0d090305031006031a10050d1a0f010e01021b010215040b07110303150607152c0f0304090504050a0f050c03 70
    0x207404001402d160300400c104503141c5002c1c1b0555240b03103884040d402d41042090b0140a8170b01040e0912909a000001c04a51550042c07064a81c0340e425584104032a00c0c60405a03461826100d865030002c100c8481d0650181d80204000b82140207407074240b04242c60040125110501c0c00e5001c18800000c0051210000c00d0b00400b0780041d00b000c02800320b04c2c2900c1c0680b0303810000224000e0802c0031520000c2409501070764091a51203009120030102c3c1d80000f90041c00481c0c005004400d0036850071850b40c00382070003079029441030303005003802d5510031000700c0700c0908c03550b159040d40030354100303d030b046100000c440d407080380190761202d920b00701140000c0c80c4048619050280b0b4106005000f0300161101030301c480000112000e40d1a032180f03003401200c4154400a118a071403070315200d01d16040164207450b02c0d080b100d040340ca03c4000e0003806244c4402544000c21204d0304108002e100426039603000740d8000b0300480803101444069600c10b09816020141a101036000084044c2d161070f0800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 862943534 1250 862942284 862942351
    0x12010506040e03120c030c2803060501030908120a0b100c05060f0402090703090507123903140a1718010905010507140a05010c05130e01030f12030b09 66
    0x100211314015201c01442c03801c00b006440c02c98880c0000002c140d241201509a42405200c410341c14110340d840010f1000f40c00754111600013207030808000192035030007803160742892a044840280b46c9900c42e2541034148100078249402a075403159910029107962802400c010007030703200c00316035118500300305144c05001029019644124002c11005890301d462040d088541818045004131130b500d4143e0802400b0f8000d0304250012490701d8040c891450f0f5100720303280c840f004103415610006e04140000100c2c035441c2407411000c040c101300091148015804590741142522034144103541d6000c0084003254210404100c00700b41030092079490720611800d020f090a2441c0d03001d01e0500049d00303030300032038401501903841c05044d0300300c0305024800c0fa10083e5018000b00880850010090702540210340701e0400301c3c81c04840030448040028140c2c2c103a940000c4c1d060300040c250742d80c1e221400700841c81c01040580315030310300705252030301d2074441d0013a080d0540e043e24001d01300188451081000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 862944784 1250 862943534 862943561
    0x2107031713030215160309171204050f1504090b0909010c0f032a09180b240f0c0601051305061003110408060406020424020601050906010e1201050604 66
    0x70003240803030749014104982102d074140d0380a403000c040e504403a1524040c08182d10580d140c0803140302c041551000d201c10944170109007d600c0c00000b40402a594920309090701c0300c91000b0481400079141c08a0b515030180d000034071070b01c0510300035604070501e508158050100191182c4c41d000c2c03540350143d03900341d100304020001c01c000c04041d4401424501d4041421040c160f954440148601c0c621a00f4050050401000c00000d2810309000b84041090b100750b01c5066442d220b4140301d070501d4080c00420603030003000090800740d060741c49444100c2090244422848c04c0008410366007440c00585404400b00c0c016003182c0d85480140700c3c80120010210105d24500401c0005aa442c0341c44148030f104070303241c00241c0b00b98000c03d03d0307201c0c0b2881c0c20600092143c0020071040100302d8006005aa648415042c1e59001d40084101c045241080000140c0c12420040c0001d00300210071a5000005140100a0281c180d0200e68034400303500b910903099450b081040054103081c06200890501c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 862946034 1250 862944784 862944787
    0x1c09030f0c08270d030f03150b07140106120507050a0b0a1d06041d0103021206040201020d081b070f03080c03060f0d0203010e07260106060905060921070317 69
    0x155030303840b03894801e100144560010000c1d141e1990345660700c1c83d410100c40540030a1803103415003009010139001000b03140000e820000300000703d0405c00e400c0300403141c9010b8402c0c201809035848064020b100b42d8800c5a07503503230f403c00040140a590140c8001400b88001d017520504040501010139265003010103602d4041101c18100c1e940804204261003400554880c80f040000c0003501d648a10343c042032400701281845d121800c0091240740c122842280d0010900c20a0500301fa280c0f481140c02074007680141c1010f094542c01032048580c000f00c1e600405082e15503400a0318031540100100380c3c1c5040b015103c8104058114440c2904105004200e604500d05240014914500d54806030300506c1540149011902c0c2500071021308083c000540d02226200c550f81d50b4000c05500102c030034a90500c3c000855a40c062245000342c800c04e40e07445203c10b05040070f004c5d50768001d500707081d000413590032421601c0400b120140c0a41484c00c0240000600d10705108445030550500c00303500510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 862947284 1250 862946034 862946057
    0x201060f051e09180c03012d0b10030c020c01090b0d09110409110102070902190c020607052a18011e080303070c200a050909031c09030f 60
    0x400c000040100c074021294203014815044454900128019585800c100d10200703000b10481001c84a0728100d641c5811100103454210070035080c2c4050002d4082d81d000c00e5400c48110315060000701c1c8043c0c01d1100c012500090300408107980080305121000029640c3d1415402c00b40d050200d080d01280901e4240807050804a07045090f1080740c256440c89070303490110004010b03030404210404800100704100f940c015007441840301c010b10300518010f000320314000c920840d00d4400d807040d604411001200e100018038054900505016040c0e03030000007440b86c2c0c0c0002e5400c0117007901c0f103240c03285620511004030000a0000070300000480c82214001f07003504000c06000b803c54110355882158000302404100c100740b034005c0c5504000581d002c00820441055003003c1280b6040b48107021022106a500d03550a03c581c080040076644080c00480410135854401c035407640256943c4180c0b031520011410700c42041114108060b2090b03241d1340d14405140e040040640d01c0b41982c10940c02d28103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 862948534 1250 862947284 862947299
    0x50115140307031d01020a0e01180b0a0e091632090a0302060f18120604120201020c030703031d1606030c05160b0a06150e01081e010308030f0106020106 67
    0x141412500162100c0800010751052182d003103410408820380088100d0009075090f10f001c3d61012000030003040700c400000030030354440c00400241c82410f40f108081d007801c1c1118803080e0342c000c05d46032080191030504101242e60b81000c260003001c072821340d640c400b4027010002e00410f0001da007200d9661540b50040380135514005244111004040d8059518200c14000851510564001a4111801061140c0101c041900508105003a00c90030005154080108544000112a100003580082e0080b4000800841202514070154000036061a17a140885032554024000540010b610781c9001d00b11203440ca035850302c0148074000900402d5014500c100105002840b454007050b90f0360040440440c85181170300c080703d041d034021110070400b905004200013016945500d12a01c0c081000410607210103280059061740c2e2078060604000070010340d0074100080600241d05402d1441010f0b0320070a400c0903000e1403082c40c0d221780324148280e00c2d48000303905820020075a85416020311640 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 862949640 1106 862948534 862948547
    0x403020f0c03030f1b07180603200a0e040c0302030a12030b0d0210050a030b090a020c0d09120b040201172406160308060d08030702030904050115 64
    0x1e1404000b0180c4901c200b000782c0400c0001040001d824400e4004144800014041500c1a0940d1800d00448100211804503078650760750600307104010004c400c010510700485114a100714a040108400d0720490007114903000c070001c00103040107070840c03110300510390207130965207000e07c2454108106111358000d0400301c0d0901041003507504100031520101c03500148840f1112030401c4042d10960320101d140c204158940480f2001910368021840c0607142c1a03400690351b003000000b80f401c240400c1440d034101f00d40000c0410221041003030340c1c0b5030a07030000e212040381c3e00c9510050365000103641c41d122083c00c0400400c1400500c1c50074129494030401038044807581c034081003040da0301c5000040803500c000343c844d107804030f44a5110356602c9503001d0250000c5100d20b40350880c40381c000f00d81410041e44001085e40960800b8014240104990034040110403007998026100 = true := by decide +kernel

theorem cover : BRFrame.Cov 862769784 862949640 := by
  have h0 := BRFrame.cov_init 862769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 862769784 ≤ n) (h2 : n < 862949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
