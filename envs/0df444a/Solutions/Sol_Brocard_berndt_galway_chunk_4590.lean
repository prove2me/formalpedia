-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4590
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:06:33.511281+00:00
-- url     : https://prove2.me/submissions/5881649a-39e3-42ee-9c60-4485ae834840

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 825359712 ≤ n < 825539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 825360962 1250 825359712 825359737
    0xc0613050a0603090308090705060409090218040b010303120509100e0a15050108012d020912100c030c020a03021b0607020916170c0a0c0201050409020a0315060c05070306020a05 78
    0x100381c882e00003800410078904190003080d1148001101da440003c2d9000580d840604528205441e01094401030004e103001240e0041c2d100d82059803200c600b1284522650003545c0d18082c0d07504d5800c000d0015a20f42c0c0b85c001c00182800700300440180c0000d80502d04041e054000241c4001c000001418140070000060140c070310400e0300b000c0c20102d0342009050794500e40c001c0040c000c0d405511062a02c1102c01e1600190011940400a120135400740c82c00000281120005070004940030f4141000c6441d107501d42650f420204000540c18850008010064001045142078644001e5078469541803102400385004008814584030001a030340c405501a1100751a8100340710343c0ca00541060a5110001e80b00080040d6a440c481d4a03060060304c40c515954500100204112200007841c0c8090b03041c00003c1000180c008150f100600703610780303250b0f0001644901c2c2c20034080a02401d03813000c000c008100800c4004100045150307401c4a5210000607034400b1440720541e520b00402010181 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 825362212 1250 825360962 825360979
    0x3100b030a090212010e0613060e0f102009130605060703090504150b070f030905270c04060527100f02060a0513020405190f0b01120207050c061305 65
    0x24080395802c0001e02e140308990310200b01c1c0c00707054160308803a00f48440114550184e03010911512000d45d44000ca02d008603000301e2090310b01c03442c543c070b06402f41c101e892007070740030415006018800741b044a901c40340600c80c043c0c070200c1c402a9040c0d2802114620392040840100e8203100004a6000300010100500720f030b07850382c14034240680900d45510506001d50300300400c0c0b1504240b50031900c001e40d110941340c6400c2118a840b108088561000104c05000d1000c401080643d105c1c1e01c102900100351341030b510005044500f002041c000a061556000c40500050240ca50054140c400c040c001464188051441640881500382c84150f416005465041e1420f035695103d02c9022180700603802300c0345951648a910012a6012581c10400d0103405642c10700510b440c0d0400d42d0007203a051408000c4500340e185400445824003120907401e951280c0014095800005240d0b422480071011410030b500d54071070540350288005824482c21000a101d1491100e072004400a00405000800c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 825363462 1250 825362212 825362221
    0x7200307081f05100e010b0f07020405040804031209140f040605090c03160903080a030c050d050c04140d050601090c18060504050a0b0a1d01110a060212070f08040803100b03 76
    0x107210012180e4039201031420100004d030308100c0c104d25031085608200103018aa0320340409404075412100b00410550010020700c00540c1c3d450068030b0007907001e5200f0030350310b6281d45017510880b1106080310301440808007042100c0da401e450182c8003800305441540c084852180040c0080003c0e03040760b50702c0201001440503254151b0040c51080b10030007140304603450807880588940703d96100c010036058003044140e051910a401071320401c032076818814140743c480c4041c82e0070b03a10708a912404a0a020504124024400e0042c0103100e01c2621300d807400050503202d81d91600700c14001c0741c10168543d80c2600d10709100d408040311a00000300e040410030344400008020340e10a10915104000105005c5003402808003215580205034440000c1c544408002c0d2120b401080328040c1440034400b04c18000d0201440801031242c0708400069694401900414a0369000b80c141000c00c808107042c000101e4000054035041908038201c15269515155800310345041a0040d050032080801400f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 825364712 1250 825363462 825363493
    0xa02130e150411030703120f030b0904030c03231209120c010c08070e10081504020403030504030506010f0317030402030c0a120b0606190e04020d020301030507090b03030720030708 79
    0x60285200310f0702601c1c5019058101980c0d00c0240c0400b41441640c0d10014400602900c0b408040500b103040100b01e6642c44400074a02e010b08aa0603400700d841e8950305410103500000c2c40c50707100704201d090044480d04d46424402d40c001c04000100141201c008512682d208002407424514010b50301a45d034600c00d600c05d4042c040340740c0607101003058100031913251030183c0f05030040c80340d010b04000e43c14035141c142143c4804001e4550000760030380f008040c4003500d5500007000a1030007912a2a9900d1841c688185803000592050b10450b00b5010240001003245e1b143d080504404d100b510b4a9403164000a81803540e80380f203807a4801d41c4204001030190013581d124034028007a08000550340d43c4c040521505114001c0f41d0101c0c02c1094040c0b0042600514100100e070801400040c1080c00101510040f41c0c420707081601c4560003804108130300c054074018507680da642503000d0350038003065035542c0031400c21103402207107400143d5500c1400d54400704035600003811480e0880e20381d6020844070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 825365962 1250 825364712 825364753
    0x81902042d1517010e0c160c080706020d11060601140703050f1b100c05160819050903101a0409030c0f061e05010e04141509030d0605030c030a02130e 66
    0x4400410000300001030b000c141c046044e8806d5016200e010300d0b01c14042605101c2240e005811604030880c6940421403100402640d4060030303032074000780f0b07e2014443d8050b04070740c1c4103403168aa60f4003a4040064a9034030001c84425030720000e10160300d0f8001d500d8156040d001d040f180024408000c00c000b071b02c0c1101c2640c690380d034585810661b140040141855000d6640703100c000d10228004000300e844c0320300301103280b140a03401441207908182c1e50202d246055030710f0060360b500140000c2440600c5243c18400e075801000000c00401140001480880d9101c0380340100b0340c444c036a2080040c00f45402091310100709035100b000c1100355032180c0350200c020465106180f0845e00e001d0307131441c00d024052244034161900c66681145030781c0c55907680e1491011065449089000302c58081016281840445004101e440095521095446c4101080310503940c0310620a603c400c410001503200811104585074054071120506008110700001801c070f03440f00a00700344500c0c840c18524070f46941d131 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 825367212 1250 825365962 825365987
    0x10150e010315050c1b1f1503080d09061401030605100f0303050a09170d0216050604031e15050601141903050a0e100504110a030201080c0702010207050907081902042d15 74
    0x1800e46050745070a850346c11103514442803035907070301900010300c04900c100c0050b005a0195090119070030240b0f5890000f40c4405002d85100f07038105d1001481004003034050640c0c0107401d00303442c001007480c081e001c50f100880d0348800740a02600042c0c5006091080c03a40401906003003034000802080260350a540c0e80810b86c55a00600400c9040c0c103810305402420f5048a00c01001c550070b00f403c43c2c4410090a60146003618800a1103c50f100085c9070161160040d4500d04030000301441d00400241802c041120102c429210400140c04004100001900c24222919000940b9500c0b009240010040c0c0b4400f405c0a110f44d1025400f103c0b95030300010300c600e200320030741d003440e02264003400344803415400020302040081c0005071001c041c0b040a08601d900500c125034101c0e6a450100c0e00008050b241c07000085c0d41403040044001342c00d482d200011598902c114a01486c18911421071f10450303115505801c80015400d03405408020b502c000b600410001a042c0e15545070b0191a83e0403211 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 825368462 1250 825367212 825367243
    0xf230f01050c13030b09030d15090e0c0603070c050703023015040308070c020603070e09090c0120010207050d0801050310150b0c030c10150e010315050c1b 68
    0x50000d0200070101040d10280c2921070f8045420030305503a00c010000200902c0c282003413205200c074071030110040c081c2110508450140030241c030306240d05081940c0c85603080c4512944038003482ca14a44601e011254008150300d00340104501e545006814810590f00207540100078400000703101c406565002c0b086a040002405601c1e10b803416143c0311002e0840942c3d03d08030320400140441c3c000c0304e6499005a240c0707003442000c0ca447d8002012034100b40d9003000011001d1402c50f100d400d01d00f9100d070f040180304000700071402c5a0300c0020400d2140c032040300c0070018202e0008695007002d4041d103022035488000c1d941d00e100c00c20001801c45d070342485501d04c2882940b4405401c865244180e01d0f18810001e0700805030b43c1050400d070f41c2a444500c2e888410310040001103202982480b15860601e07403802c000c02c8074400c03c0001c000400700c40e0041c44510115400400026508010035130800000100103d40d40d6541e4001402034051000c0400008501d207070340042e59200440d040c151507401ca0b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 825369712 1250 825368462 825368471
    0x8090111060c030603010c0c050601030b1b04080c090124050901020a02030708010e1603030509040b010507080307180b0c0c1201020412080706050f06100c050f0102121506160f230f01 80
    0x21801146c0c28108c0c0c00d00503100d030b0482d00c014000b0403004000b055010b10548549403003103910140c141c0440e07102c0c1d13000340f407260031803042e001280c5044060700307004000f002c2c4142016001ca550401c0b00381a58403950040c00400940c4c441c2c0e590080c0304c4000941c1e0003c0c26a610282e0300e841503070107424804d00c1c1900f1401558240507a55001540d040e00380c03034160340c54a04111007081404002e0002012090510038107000810002e00b0280066102d05c100740c0e140d00024410b0300b107107500340d01642c0101051a0050004280084002840f0000c1140450b01411906194051130340284203980191030300480e442107100034400c01e5001403c6641c42040d0030080c50b035030b000b45240940300c01e551003540b09401c12100c158907840707100208101400780c41130351f40184d00e8444046c01ca9000c4481c1c2810101114208010046101c2d54540e0444040d2510f84c507004d03260403081092070120400402c0b20050091070001d002201c6d8800d801180000100114950034120312543d130302c40d00e41c060f00c01d0b42c00d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 825370962 1250 825369712 825369731
    0x121409011b0c0b0903120108150c042d15050c0d0804030c110307150c0201030f020a0f080c0418090b06030a050d030c050d0f0b030601060e090408090111060c03060301 73
    0x810020845076035580d40d048098069a800d4040c0c1e4000e4425480c5120501040a8140e0b01d00c2c00e0074000d1074080700410120380f00d100058442c0c0c00c0201400c960b0581808200060803090b9016640c442050507040c090030708031003007000948103a401c00800d02d0b9440d4442c1e8200fa030403071b00a2401200c210100d03188402c0020003291030440456005002460017100d080c001840e101c0e200310b10b102c00a0a07107405540b6900040900d0f81c0c2001600c0028043d5036441d0103558051107500c0d5441420282986800c40810010f07000f000701c900084100300e800f10000300d980c0e0010040e58080c0c040584512800704174019558007800c146c0c00c06840049a00004c5500c070710300011039820301a07005000c2c10f001d426203e0254001d0480400b02e0b8140300d400c200c0a25040303d03d200e4031002070f00d03498000500c941140700303151603d00160450420b01101d2070020344c441d0354890009510542c02010565240f0300c11004a882d0824000758090a109400901101884490255100d0981034000700312034881c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 825372212 1250 825370962 825370991
    0x2012918060d0809030a02131b0531090507080406050109050411060901090504180b16081f050d030c0605070203120606070f050a080304030215061c0312140901 70
    0x5081d505598801d460265030030005202c1e070068000104000c0030744203560410b8012900000d0850b1040070345a42d5141541c41d00e01a19004401c1543c03185000350800c0000d0310030040340e2402444c00050b2807000b8002940311200c101c0580080c048400e414003190502d26070103040c0070301c10b40d0300300d86240c18070001060459541c0311ba50312440c2c02202c008081440e050501c41c0e03e40c00300c0011381c10007080c80400b2902d510b65019154410751001c007001302c3c1c46641d0a04103580c1c00094050882c0400140700c07030326810342c0801ea45410440004010428110394079424404243c554841d54201c81c84507510000d1603000340b403002030940900c000f1322540e9a42c0070100c1c0c1303034803c1c29210f440104242012581e14107006010b0070149200f00501144c1d6142a21030624202c1030390701c1140d210000204001c20180d040c884204109040300c80304c555800c0c80c0000030004c0d15901e00800c29510780d19400c0c014507218864207404000010f0b001c1203041c0c540c16001c0c0035120220303001c42540d801d0840c103400190 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 825373462 1250 825372212 825372259
    0x40b18010c0b0a050a020903070b0c0c0607032304181e0b06040e06040e06012d0e130321020d0e06010e0f07020304030b070807031524020129 62
    0x2d52002c2601c5441e500c00030710300020400135018100c039981c2802000441e4a04200450150940030383d107a4880d60101c400900e00450b07440c4190085209218040010341c00801c00e13025501010b14110011144200301b00d4580101d5001250360309034002005500e48907503110403e8070004000b08050000d0702400d40c4151500c80a083e03030400305c100010411424490907654100400900c046410129040322500d07007a020303000682d9014800150300c0124504050071969900e48007403521001e80b82000140048030b00501c00381c2109683e4552a041500c42c0785048404d0402886900c55012118007105c001d40180d0921000c0f0351812034072022024000450b24120b07071206121406030350b240d0054a2005001401040640c8028000400020401c40e1068810301080d03443c6e601074940303114001d0903500d0300c050520f0010003040c1e0612091000841400019040410001140c1050013049005200a401d20700e40c0711341152000070724940c0030190b90b40402c4203e039060340d03002c0f00d141d652041c903 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 825374712 1250 825373462 825373487
    0x180f010f050906070302030417030301170606090408090f0306040b071824050c070902071502120c090307210b09060705091e09132d0620040b1801 64
    0x71010700642d621403030120002c2103e18801d00c107590a01d076480800410080c000001940b07203400100050080c023480791140d03102c0c080c0c0a8010000e600300940810032506003d40068040301000844c00074a07110381000c24990f49024084940d1403400b820240e55005c07007a60300d4400281120020041030300d1104a060554854005802d401c542d02c21402d015a0842c84807001403000501c091751040e0f1051000c5001070485200140e652019450902a55040081000b08951040c45600c00b00007071010080e034809200c1c005e0780d64840552000920340245a4800b6491003200c8001a43c003210050102031a9845443d8020051b1070718414030340c507260308583d50b800250060000c40c000d86803c860361020002c0d030403031a0000007907400105202ca0380c225a040e5424000744008010401e400002e04400d07204100801404927a15108a500186042d00501300c9038480c11212881d001003040343c644164551151591117656243c1060950060300d41e0903940e082120754200342c0d500a42d0644440c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 825375962 1250 825374712 825374717
    0xf0f050639090414090a0c05060406022d0f25030213050406020d050718060e06040e0903090303070f060e0c130e0c10090305061b19020f03180f010f 65
    0x1054030311081c10090300b010450b964065210403030382c21445424030340e06005640d00c1020b000003600605112120003500d501560080b03204020130009103178045502500f007c0c0040c1000c0105844258214225610104080e514040e0041c0c05000080c00a010400c039160381c00700f034400c21900400a4040419840041c0d04140c44404548500300c040c1d0001e40d02074400c44005040c4030440100c003045a5044501c6008911102c04200c40200e80400c100014500741c0b078288603072881d100c04660030b40114070400401036600e501040b0252418000c2e61440c020150032a9100c1c010b5060000b41c80224950039100e10b840e040107130882140204151500c1070000e03100000b00301c25524150024858240300014900a10340c2d09203145d43c0d4082840f018120980c0c4910103603013541481420400c0244c50806a041c408083c101c90340000c809881410480018290b80000e0001c0207074200000100d4040d030502000428012000184103001e2140c142a00c4000ca400c031420019904680881201e401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 825377212 1250 825375962 825376051
    0x50604030c051216030b091006050f130207080a0e10050c03071e0b040b0109141332100e0c03070509151e01031b1b0f0f0506 55
    0x51400c08412001011003034504540003540313031612904d803051082d04100c0d8240309603800d100c00648200800d4078650101041040b940e490a00052440704503070100a001e250f012402c203040000d40d42c1036614154202c41c880d5520f11840710010004625155100d224100300c405070607403280700d201070395074510b601002545029070b00e40b02c44807a0070414072442d42183c0240708030800039004448480c0980c2c481c005030002541412250402d48100c00304464401c51402d04001030b056100209441c0c1e590004280e01c400203c9460451030b4144c0340801003031019000703c03200d441d83c20014510b0b003500801c583c200105010348501507243c80030024855851382c0082400d10480c0741803c0c03029007204d81129400244040c440200c2c0a00d80144110100344204815804017540c040c081ca41b01d000103e595421580c2802401a0110b11244504101c0c0704e05007158074100140d29920050480e0041706a410004c1d20345485135a03040221003101d03600c070124100401c2c0021b0715200001003903d035120b100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 825378462 1250 825377212 825377219
    0x15050621060c070f02040903030905010b192907030504060206010b0301143a051207020a060f03020f0d0b030d110a06020c03130e1506040f0b1617090901050604030c 72
    0xc10a4020140c142d40303c04d01c504124005030380310302c04c1e800c0c568800e86000c40d100b2110b0509a007121070381010b0f00c1c002e07041055820f4580c01040e0031141030703582c0d0780d10718054001020402401c0c070341c0f001c0e502c43d800e1b88002481824180c00070054412215075600719012030ba224058001280000c0c0b007900c0030048840d003405030621380b8a00c440d1400e10481e0010740c5000414641e4182c0e551182c88030725009081402d85400e10805100600c035007641010b41d02d2404800b03501040c003081003885020100302014004080701c62080c0c04807810200c4003c105d0b91a1207002180c000103221811015101e0b10401118401c3c0c00d0040544540c030044010250042070580d40302c000c0030754403090b600313420b5000401414442d401c803606410050301d030b0500c02c1042c1e840c08011040070403100d100b0389480340030305001c1044081050415081500c0d52024107a886407089880310502841104000300322899280c18108940000d602801c181c420455074a121a42c0ea9410307c0840e10950101800fa12410802070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 825379712 1250 825378462 825378481
    0x60f06050d0906180501110408060414120d020a0806030a031d0a18050103150b0d1e1505060a210b130828020c010c17071505062106 58
    0x20030720658942030218a4284035a01d14085a804244c0011a0a2400010001c0c84024490000552007251816141a00700021503583d06170040004080c0c0d00440d000c0f014400040c0400c030b80d000f050002c0f040c1c64070080f10292019401114015002800010000c2d05526002881280721341d0141c403a50120140034280c184051244018503401c84031000c2c000901c40340d460420b035203092200d20300240c107504615150ba0850030610100c0700c00f81c1046090402c036550321603001031320390344410130034202c08454641300c03415000881e000e415030a00e20785031a2220401c3d0442c0d807060b6803c40d804030340c10761542030708001c2e0f046100101282035070002d12200010782c45e9801b5900480d4094003449000c0320703035a0340b42165004c40030a031150380403085161022a251021140ba043c0d442c006040c945c8190400242003c074070060242103034460450006000d42240201e90b0050b410510b0450030a15420042000c0c4c281510041d014452f00c0102c81140810854480842c9000001510072501e030351072030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 825380962 1250 825379712 825379717
    0x10e010f0917010b060706020c0d02160e1905040501140112030903150e0d020c030c040212060103050703020c030d05010e10080316020f10030902040b09070e1e030607020f0709060f0605 81
    0x21a82c866680710109007059990300c01a000381842441c0160351858041c0d081400d0541c030305800d20a540c0300a035251a0015a42078003c251007101c491030001c1da0781c3c40348081a42c3d602520441c00076261106000510206403c800e050191003c10540166030b941d80c6175a0348520030380007400144503103109100080b25041b01c51204031801d24007040946d0700e00d2203241000000c24080025a1000c151590141028040c0b841510000c81e421810444414043d0200c05c80040110741050365032000500c0c114000c4d81514004c080b00c000300c0303880d01d2400c10958020a001c1c003500c4510001140090429101010b60000f0340302050040c0d42400307041a402070004034060300890340300c44c00d51980170041e140d99048003040042d036a004242c8020034010700c0221800709001d039000750040c1003003004054000d907010580040c103842d5114134861543e080c04601d00d80d9031100d541405140300348a5020350000300003000012000580381407540d40d01c0341c2403c03240c05100d01040054182420481075004502 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 825382212 1250 825380962 825380999
    0x109150305180312040606140a120309180603020f0409050a0b0c040b0a0f1b031b0312141f06080106080a090c180e030403080306150d060311010e010f09 67
    0x51034151100b2244402e400c64002441d0081c0d00c080d03410420050040300d00030080100058840d4520b50071020010600445240c0218000741d445900c581003014030a100c0c20000348084290b00c8005075000b005074010300344520040e8030030411072940420925051007000607180d031081c010308050303103165154032030024002c0040e074142c1c0c428000002c0d503072001c03001800303541215581c60451101c044005460404e0488140010f0044481580c00280d0000e103c3e0281c1e94400008000580e5103250850307501038640d41c6281c1190820b039101c0071541e010030f0b116004081101400d01c2d106089a298144d4030039611075a0300013440400100009400380e4190782d0490181003020072600d81d1512002020b03406030f0b0000503000245035005040011038401c6030040078080d006541340031706e19100c1030b24601002d00160b00c00c0081400e00c4152106030004c4070840240f0600600080d562810018002c040c0c0c1a107072800b1459580000311a580705841c0080300340c466888001c03885052110083c02807082e280c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 825383462 1250 825382212 825382231
    0x1c03090306020307030c03060b0901170a091403090f120307060c17150916020304090f0905190618083408030115090503070909150504030e03010b0109150305 69
    0x9101101241d02800158416030180d01c000c541262221402800c480140d0300508a419051140701c0e4140c0e4454011a0050420b0502c0c0240351140901407000345040d2400030f0024030111291401a000400a00740c251000c070303103100c1c0101c0710105000d0051240d403031540c00368004105110026450b0783c44401d5075007007850310b08600c111070b5a2451f0400c60548100000009600448107685403900219511680c0856041303103016000e5000b9641c1c1c003540c0240d004603622540d00912204055111030520754100e0100e6008160600c0b420100707003280c05003a59a541805210900814050403207003032194400b80b0b2500d8050180400380303d100b00c01222484040022480070603104190568010440c00703651441d07501d5240c031414031819065803100c9410b1254050040040d50340108d5545c04461254101107044a001c0c0b428903099100f414460f800c1a01c3c0c88140814533620601c910580078090303008004050740b00b001034600c003095205100f40c14235040790400f5158800c0d0087c641003030164 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 825384712 1250 825383462 825383477
    0x60d080403030c1a0a0506151303140a0b07110c0402040b03070e0a03060f06170109020d0201051c060f031101171302220509060709050f01050a2f16051c03 68
    0x614a003040340c501621080b00d880d03140c1003441f0461400705844203130702400081d1180390030b02c4001c1505603000340340b10245c5040c144071b0110785540000c0c001032001c81d9000410001c40e2911820141a4144218105044c2c1c8070700e11440100b42440d1017141e05448450646070304580d00c0e0320080b1480340402241a4002c1c000480002c0000c103140162070365151401b80c0031070392508101c000403010f81c041d12100c80c940c0c105060038001d6144e21700c00b003001c00d4080c40e00d1a07585800c0b40c0340907052684050001030581c50007000046103040801d45500b940d1107220300030b0141110308011039800340003088800702030341841c01003568a110308242c54002171020386901540194a00751101141d0509000d2141d280c9a008200740aa818000107610508a06142c49814207140c0421407014081600c80e0620800040604000740607640c1d1042c0000641440f21243c96062510700f8047d4000740f005480b031141007101925005a01c111a0542d82d020b1f007102c0c100c100304d0b1403000581010745e80960512200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 825385962 1250 825384712 825384743
    0x1710020c010b0a23061c0b061908010302010909200a0e1309020a05120304120303020c011b2a0627081201050f0907110f100e0105060d080403030c 64
    0xf0850311000400c0c200c0f00301c04090b40d8441c4c541c003445165020742d510030541000507080d1491246050390144150b80400a04000000089241c0d0721a01d0f1502c4540f24a254100c3c4001d9800940c06060364400c1e41c58025481d5500715060503290746070030030300b403c4060802c40c41002c4072000181100090034a0219200700504010541188010000c00c0344903803540c600c0303401c0d402c2440a010007410251500f40c089880301c0c072155264000e50143d22400441469480e051601c00d405a8440942900080100c404052401c02030040c8036200780c40440c3e69040f4140a000d003888200400d00410080c980345a10294bc404c0d00420325041c4182c000071842600700808508441c2c1c000c59507104450041e92988216500c14000c04140d00081c429030802d5245095074035845006504001d4606002000c0c6051680e0181002e2445401c0d0710640310b00c4960803940d11864201000126440e00204402d440c0c00d000e124a100319036001038030301c1c2e0f410002080080d2080984402e031a0264940030741c440b10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 825387212 1250 825385962 825385969
    0x320d050715031d070f0e1005041103190501061709070b1306020114011206152408060a08060402012d0504060e0d0b011511010219091710020c010b 64
    0x41148103680000d070f0356290f44400d00c4401d2076190314410403000802c600d5191410a0141161600507120f4054801d00403a118120500b84030b4082c01000744144005800188400095041242e0700b400f100c010480074001008188181c6043c0c0d861aa220200040180c20844000c200900303000c0c01d61144840001d4040070360005010000c0e02040da1035030035407801c2002800e6411040d1070502d0000001700400140b81d48010078000c1035031101000c00d20080160613032503002d40030b0340882980103140301000d8103100701c0b80d83c1003900d00c1a902c2c1c07000e41d91689002c1c01210715241c054011a0361085000c10050340c05610001440c0c4846a00360017400e2004210326071520500c61641d0100342c020805120740fa4203d07022803250344007a02c80c03446034030704d0361604204800184144d03a40f06080382c0d11550074501c0f4030941c00140000600a640d100340009214040302e004450040c00180040c801080c2102079002e0311103101c030440021715011210b025004000e6001030002da80640d40e81c4c400001548 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 825388462 1250 825387212 825387239
    0x4170a12020c12010203010e0f04031808010c030e0105061e0604030609030f03051602060106050f0708070b09060f04030f051303023109020a17011113320d0507 70
    0x154080c00d078600041c81449883c1041c00300c0c40c02c607640180010320001c030b40050710aa0040c000000900c05450380e040070703140154001008070b03500310f0a0401140700c1300150050540d803000d90ba810482c00404030161401ca8900f612407940c005026002051030700c01c4005000e400c414024801e40c80c0030b5032995200215440705d0401c82c0071520a0901030301858240c49030b26400b00762800904002020030100035140e090501500c1c05004010424001c8500349005403410b00e83d01c40541980c0d0440e6080061080c00704451041280c450a0005005070404040040c0074552540312080c1e818440c5005450f903800c8413612103154680410000050781d149042c046036080b8040c0b030942400c1c02107980b03518003400c5007005264103041c80e00c1000180c803844407480440706c0d0014800e4446a041c40910b01400d2098080411321401240130b10500e140001c01808944e2800f2030b21101e003210b0400d0740800520901d612020300c0c121802c0c0d1004d0306082c1a00b2342094890415201925203a249540845 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 825389712 1250 825388462 825388493
    0x40c021c03060e15090709080a0b181915020a0504180225020306090c0609120f1c020c0a0303090b18090a0b0108010f03050604030f0e0a090902040f05060604170a 71
    0x61003044450440c5041c02520300e1b03045581e52901031101030515502c26652210040010605200100001c5481c1e00b47e100310b051a140c442e094a80054900321112801d80490605136030111003028242c6129400f40708580da4201191541070610349486a41d810b1800c602c0d242040180d001c0000c0501540e00b8001ca08a2881d803200310744c40031085005240c600000106440c13400e038004058030610b544c0d52402e40e9002c1c44c0448030441c4650105c03d0740d5042c681c00d042c1c00310461003001c03049001d180c0e00c0100380410343e4140d400c4504090500b820840408500d10010700814441c1c170007031040a2000c401401404540d0400c8058141100c001c1484d4010840301c1080c0382d40e0381d21003c6103640e8013404507401042004074444800d4216128075840b1000030300020305004072058840040c0d0b016400c1d4090311480241202091a82c60484001421810504a1040f442c0c000d44180d070001d40e200b100c1c00703010060314503400d103402d240440c011450840102e94151044090381000a05c8021420320607 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 825390962 1250 825389712 825389731
    0x30b030a060501062303010510110a030c052109150c1506031005090d0813170331080307090909060207031106040807030f111c0e040c021c03060e 64
    0x1258134180c80284004500c8816504802d400344d0101060540642601c0c1500d1040b64100d0b1106042e407070030f580100c400c0842c1c8915000b21802c1809064000c1001c9888900500587e2017280010151032181c201e100040c4002c4e02c818003115035a030402c80e0000d90301489501d00140360881c80c00100340340640418002d21200d80b05000c1040504080c80894001c0100384018041e42c00c003000c04903200e241030b00c4034204000300080011a40d520141708000010741240c0b00700b0060960b2480103410b544200c85c003007542045400d0400c06807034683c1001042c03200e0142000030402042d52508800e0307001410703140400083c5000820703117001612900c0292445010700507543c1860b0715018100304900a150b8049402440421011a00123802c40390096803515203600798100c4628203407110b0030b0074010800c45108801c5841c40c260410b0b031207010b06070003c2e121550303e801c06104000559002115040050700641b1014481905c0049080c50080050502056507038886d17001050300c2504480c08105d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 825392212 1250 825390962 825390971
    0x9060e070501030b030c0609060c030702060a02010b0301320702030910120b060901170a0915090303050c0a02071e03050114070810050d02060a030b1905130606080f0403030b030a06 79
    0x10660709071151084c05501070700504a6203005400103015409010811030207207000041c03020300c00342c007401100c020b5a07004288940721086018024020803501c0000da01075864a000d01585c0704400000b0070410410b030322940780c08181c440400c0d41480001e49098203510060020b4205035503550054000c86101c5d50b154010700e009002c0c080191810030007090300880302000b014100341d80c0701c480522002402000d09400c0d444a20301d80000340101403000d0107121720051403000032070440e086001c40c140641d07028040c0d91551a04001c4c144a01c0c9403140140e4000710040100803101501d00c0300804940d991007000c2c550300d8035140e0a44105a59084c40404250104034810b50081c50446e04000b40b0700c0c0503e00542440b011030349031560703104040d10400e000300d103441445202c1e4006080c10400034220f036010b01d88100b03100007480200d02502c0d1090804480044246910744112030845599598901380c0e034a400c01e640d070540c00c01038000d90800d80c0b9600c825846c0d840070070910b64050f104000009 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 825393462 1250 825392212 825392219
    0x90d021c0b151f0912030503090607020c06160606080601030609170f0a03050a021b0c0102070e06030709050415050f070306060c02030c1027080c010207150f0309060e07 74
    0x903803240d001000104801400c05806060b0740383d91150640b0050b008406540c4200e4500c002d8070f5101c2194000a0b20034041c12020042642c41006540600031039001c8400380d8403500c0b0103a8813031085820b0346410920900c42c11f41e2030480030030381c2070300a4021003002030f1880e182c03a00d4608082c803d0700107680517a1122041810860081c006200da5200c400c031071418441090700301801841032039070300800c05803220045245407601d42d0442d01d9040b640071161010844140d0f0503902c801700c1002c070398054094048001250807058020621500c40200605001400c2c084c03420000c0401800585030825011110400308106105180c01100005820f04d02403510320703402800e86180c2d070064010001000342c198010388000507241d0046804a90880e06410340100803151a51500050f1103414102500110340103200d056041c00e60b4a20000d5a012228080040e40e64070300070311560600007990120b69102904c1148059011030041c039022500f4242511158103840555026000c182c20182c0e040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 825394712 1250 825393462 825393473
    0xf0c041205162102091b13050301050a0c1e030b10110106271d01021318020304050d0f0216080d0206060405090c06030a0e030429090d02010302090d021c 67
    0x110040585028405400207003c96812401e008880001c0c083e02d544400b00d02110710828070302c90802041001d544e210800810928801902c1d072107841c0c003a51805000c02c002c001c45005641d82984c5c1601c4510000215804200081c103400d807600003019518400c441407591039004c0e181d00300700c0c180d866110002d0011112403c40b080b581c0086101d6624040c40d00c010688541811007540c40b0250006448200b80c5584c00340507502001141c00f54400641044842c088070b402c04256a98444184840c1d001030894004a10058401502a0f400b421b03603020030520a4820241f0110700d44142d031182c0304103450740040c000003a000181113801c07204031070000a03810841c2c141d0208040f03400703121900346400071603159007003842d465010300000800150308401c141c1190102e41d82d02c5007100da0319580c4582803000183d100300c548800980c841503071941082d024081d140c030980300034800740d0f0104643e0b0044d070096104a804070b40210301c1c12a1840969141111300c207000b4000c26040380690310a00d000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 825395962 1250 825394712 825394753
    0x80d140c071b0e04030f0c170408010605191a0f0706050601020d030c09090e0a050a03200c0303030a0522150c020f0a0803100305010e010912030903080f0c041205 71
    0xb03007802c0c080e29501c100700302049030f6500c40d0001e40504010b00b030181510300c1214616584080900f414800703000034007010800400810466031a0402003000f191104200000361103410f000b40d2480e2100c0030f050100000c1c0300840080410803800303882c0f8100d52002c8a403542d07044040d05a880d02c0d601e1003046010b580511084424051034a001c04c507481e040a00a010460a4052404860707600c03011181040e40c1004010f0300140c00504503030140c645803a0043c401e103840c44184510841480500101c1c54000031030140c40c1c50002c003d1030660703440303680d410300a1400404a4032210304c8009960f00c120680020807401d140100d034020800c2c0720822140c42583c1c10b2002c450115031013444601c08090001c40c400510362b90001034155243c4a4a45808014229400290082d442d0442c0c800070790905510081c1036500c1078402c0005011040d005030304031180054050040307420f400000d00454280798110b070b40140080002800e06803502d500318048900060300721a15802420003103a01d0450a04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 825397212 1250 825395962 825395993
    0xa030b0301021611030c190f05010c2f0409030905010311071a06040209121501050a06020d0f0201021903060e090609070e09030403120e040e1207080d140c07 69
    0x95280200900008244100800300a003801e9450f01841306641d4080c0710644000d1401420080c2650a005854070500c03220300c5844407010908600003120b5008894401001e07030080c010319003c0013000e200c8440109580c40c6511201e030000c03010a41661688140460300f4040d9859000321410710001404407618905032213440e0390f045c4400c0d0f00140392030809400302c00d002d5034005800d481380c07000300b00640103d0380415440040311001c69031101c0005480b125030b410110300c03103600d641d98005001c14941d45005180050b0850345410200d0313401180580c0e024200752000515200f01034980302a002411b8540070300181d00c0350010408150345210040c1c004803d1400b408590400c100c030240c0c1c9032a00e210301c01c0e11400210000321031007820300540d00154ac00c09500300d403030124220000c0c4076a0354540702611071490503440d01e1400c0700020312a0500650f0212140c5404c200380c80b451000d402194408043c82d4603591000050180d410b40c20b40545a5100d500303071107071401d00d460f1645415440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 825398462 1250 825397212 825397219
    0x60c080109050610050c0a06050f04060b010e010c030e0f0901081e0714010f0e040501090905011407080105060d0f0606020f0d02011e05090c0d050309030f0a05030307030c09090e030a030b 82
    0xd20402c4d0740c5400715240c0f4032402e4108a03a4901516043c20b04200070608007a090510f01401c02c840103030007580f80ca102d94030070380041107000d01c1d45005403150003080c01010b0008448041510020340551240102000c0040c84580020b0b0722400103501e40e03500340c0141407240c1007412004805850110201507a03401c041c041c0041909080110f001d510700401c000381001016122600042d00980c0780344100f542c00351050020b9038592540c000a44002038040780c0e158680015144512503002920b03000b20420307a68010203900e8041081025041344051500e600d65a0106002005023881144010203068002e0300c00500790b00080c81c1018003e080a2042d079060000380e800001c0c40d0102c51025540002002400e5102d01d01801c0c54000b542403511b401110b02d84c5000c3c1801800005040c2ca010700b2011a02c2e50500780b1801c42d00e4003120031000700760394030074408901e80c02d009402440c118085440d02180855407101c2e10782c140d4299880b4082c00d500000b07241c0c4022981801583c0341c044044c0d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 825399712 1250 825398462 825398471
    0x20702150d1805250801090c0e06010804050a02060d0b0a2912010e0a0b0409060b0a0812070816021503190509061906090911130b06030406180f060c080109 68
    0x3e881c1c8644460f4101100c0d01c450822043c10342401015501c44070140280400030032000380e003441c00e042c81c1290f5009060030890900001941036104176401c6204644c081c014007079641481c0e00748501c80c0c2024190702e031400e071142900b80a940359a80104c0040c004051a800e450200e0075642c00350300041303c00700c000e940c400c11044d02444200c54440d41141d482180c104160341c0e401d00340714014800048c913030ba4482d0070300d00d00b50f041c44001d41004034043d000301c46112030565251030565075085078500400100c01c0c00e203d0707000440e0501c0090f010580000d0100703264605954006160f00c1c4425030401c0ca410400300600505404149407010245410340c0108540e041030354043c0d94a400080840e4144d503d101c0010050520640110009010300d034014040034a107840d154000305240c000103405440b19001054034160140140014414007804440c5140c607603032101c2014100c005940e0300415085208000000c49410548400f07600440300010b007031106000c014030720101a0712519003035051 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 825400962 1250 825399712 825399761
    0x907020c03330901020d0501050102030901020a020114090402030c070314070309050d05070b0315030c04021207050c01060819020f0f1c03090b031315090305030f0a020702150d 77
    0xb440700c1c02d2082d014604100c040c0c2e60809098008100b04032940140742c40701404203040d41500640040c0c1c0c0a4001030103641e07241d03030049070307207004565030140140d001c0344480340036500901e01c81040082c0d5043c8070340f50114110104050f40c0c030503111443d081c040000e0701c005040d03102120700d44503444142d0301480c25129842c01000845180101c0c0d00c030701014881d4001300700040100c41c0003003841a00540d101d00c1e19442d8004090420750916009004d40d1035018000d02d0b0501c00c80785c4100742c402e04640b9603200d134176044410303030005030320030740c4c0f942d41d480c40030510702804c009001246040f0503022540e036450741305201c0702081d0240c2c180e006140c4240c45000d50760304c0150001404404400740858841141000c6406985650100b41d00d001e0010034070074000f0b400c0300c0504940f4003982005080d9829201e01004461466a018000820510225241c05211040f031508010500b170054148511500056103074200000b40c0e280115002032a50019442401072140389090300c221200380e281e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 825402212 1250 825400962 825400969
    0x6030b0a140d061a12070f0611030c100204050406090516032403080a14120112020112050f04060e01020a050f090d0507060f14091804080409020708090907020c 70
    0x800340105102107020702946141c9840700e000126149801c04800e1007108038034503c6101a10b2000d03009030044400e0403c0c01d082000000324101200c410745040c44103249020700c102c64844010030080c5003070108100750038210340108550100085450001641d41d45008200803c07580203920840c040c0e41824100030f0240042c0c601c24445c81c0ea142000320b903425201d070000d09110300d000020f031400021400c0200910411384042d2041007150780b541412441070380d1030014039010f60f5402a00301c859400044c068641c00300c00c0d1800031803040c1880c140c11903000e2106004e80354100d07001d6103000c03940c400700800d10401c0e010718034405001200031403510a034a003000b0003a1003a4100c0c880d01030340009803554941c4a02c12442c03003441c1c006080c1c8542a07210780009088052003104000040c1102d9140229410650225001da2030014039581c80700071075880d041d21082000f4420b9401610501001030103042a000400e10548903895069440c1d44c1142000404000605108215407140311081c1040d207 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 825403462 1250 825402212 825402229
    0x5010f05070c030203070b0a0609020403031713051e0312090c01090b03160309020d0807030c050c040b090103020918160801050c04060801120f170405030607020c24211006030b 77
    0x58201081c7d0b0311550316075141c400640416840364103860310000d800028103602041d0282d0100800c0030115098039404ca20000c000d0180d4805801a00107c840700708110344541811109655401600d0503d210810304030184402102e40007040e03000b15240060969020304e07040003030881b440c030340390a50516100c42180075034000c1040c4141940c4203001001d554070425961080342d070040c80c1c0390340c41d1460314005010040c00c00040350a4814503400490502e803500564800c000e014241420f07507131854080107400c900140c0074094460306c0111410754504140089104481a064188000307440d20303940b5421904010302c200f405d640241310034010385a0010015044507060f441d5050301d40c201342030560007100304a40c000c0107001041a01156005224003070401c48400f1000d50b400d43d581c8000990310b854502c43c0442d44800c034500240c9000c1c80303a50241442c5c1005d0100d081c2070a5000c00b030000ca0418900f140303803941c070014041194662840c0f0340f61000d0002ca10b024042c0d0207601b40442d1151 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 825404712 1250 825403462 825403477
    0x23060d06051206250203130b091809060708070314010824011503090321060e130302100c170a06030605180c0d11041e050108010c0c060b0102160305010f05070c030203 73
    0xc407240000d06040300c0c420402c1c7c421510f10300d030180d4400c60b03403940c0b240c0c02ca500134041540510110044840d10711440d424042c49079200c0005440c0c25501c01200b1070b24803100400d01030515540c0c12804820550101d209400390145900508044208400302104906105070301c4403079002800040c00402050910108280040d0802007003c0040d450181c0720340144200003024001110301c1d6600d8030010380c0041046503480b0f01c044c0000e8940d02d00d08480068155409809644042c51100c14030005500502d0191141d14000a85145a2002c20b0307520390281da0f444040d58940c0000c1c818401a07105103904003034002100755111032090300035502d030903994000c030f40308075843c03a0108107018004d0705021201c0401082040000c28819125a01c20000300c1e50040461804001050040d01417040e81001c3d5060307114103c0210459660700003518001c007400b8118002d089443d8140d00200039090080d41c0704e44008505003081d03c0c011011620001e040340c0402040c904144003083d0048121500b2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 825405962 1250 825404712 825404761
    0xe060d0c0b091f03090c05040b01080f06150c0a050d020106050907050304060b060c0f211c0603050a03051e120103030518060c010e0712050723060d06051206 69
    0x3204600c400140d09032203502100c03011600320b4000f000340d056050b801205120f115210303a019241c3c45400384012113000310340b40c60100d00c111011840c611001040e090b402200201445030b6010900c2070041e05400040882c81a036000340c0705c600c1004001d000100c24004540f00801c1524070304000502c0c1544042c010380f040c014004045414004242c002503582c44019082c195140c40c04042e090b40d03071100000c0100d450103031200c032000319800500c200000081c50318110341012110f45201c450041c0c1c0107000d15280d81e03140c000000240c0c0520440704680d010b0b440b01501d0702d4400d0011190340700340c1102c000c45040f042058042041042407120b0640e0f42600d4203035150304c80280c1c070003030f070300c102200f215031103400880c20444892054020079001c0880b24140c0b03c64540d01d046100001200080082068100b85014030a032070018403886152070a82c010301507031303052100218006c0e0348030300380460702c1c0c0791100d80c01e0140342020032109507a010040000d00303851030107c894000020320700904500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 825407212 1250 825405962 825405967
    0x706121a0102210705061005011e200f0a03180b0306010c060e0f070b040f0807080c0d0f0606080102180618040e03070503040e0f07050403050604030503060a120b010e060d0c0b 77
    0x289115103015900c40313540c8001100d40134105140104441c000718450309000491185920340b219210703400310800c961081e00c0302d48400021204044503003c1d0560038806600c1014049003001c1c5080003030102c1c0780d0003901c3e081c000540340d05200040345219001014413003002c00a2107900d0b40d00040354403d16030003640c0041ea00e03c0d8080741c07605190841b28603102d01d2190350008244251110000c2c41203030140d01d420f1345c00d1640d030180c1036240c200c2e0348500c00c1d542c0c01c1402c2c1222035090a014007007002e03104890b210865441c0d0741e1030400b290002d8202c554170769808a00d103004814881e4101801040848440d030400c0006052010b140c90201c0085000320b03143c180440034010200283c2e000b04d603001055a48071602d80d000171004460440e640300c62084014049060f10340200200c1b0103a1b40c003c000341c502640d80b0384050300d055002400c0c40da0000403044000910011144207560311318801c0b9003021240d458291210341c500b0000e002540b155141d010420300040d6039024032011200c2c3c1d000c0c0d4a8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 825408462 1250 825407212 825407263
    0x31503151a0612070f14030a0c200f061b07020415090f0203060f0901030512091302120411040b030c040f0e01020a0c030206091614030c030706121a0102 67
    0x401a0926410050b040030001c14070f40000c40d03200781030611841e469541c81c29841402e400071103070002006042e0405e035408001080c2d406010350003001011795203081c84100000c14880707a00440640010110840d0020381445416600c240100d41e002000041051441c0e59000300c40106441814030080c031541d5503e0100d040c10504c181031000500e00c0d80c0d001c005000c0f40424800282d403046515902c1001c100f655525039140c0002c0c42c5050300c0c1c21000a144207209190541c4050780b18141d215444441044000c074801e80600040a0039440700000c3d0403a41810f15001c2c44240d5000394a80c840c07420000500700c2a14001001c50780301000316400310300d0840401040c0f00400b59070268143c2c5500024050034170a4105041c040307076612a81c00c440c903a583e40941603449140180c020004084803510410818080510304078010381c0040039900510300304400a45444800c0d400100400c40304404424041c6040c49101c09919a030351003845510003c00000307460700000030000051029040c03110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 825409712 1250 825408462 825408491
    0x8130803130b131221230c030a05030a09080d0c0e040b13150f080c09091203010302010e01051b0106081207050a06150308071a070c020a05010f030906021903150315 72
    0x289210390340c40302c017007001c0000e01c81c1c000e1292048111200841c00ba41240d0f0f070305045074504451058082002660900030b062204803001c0d4005440a6003503030f1a00000c2002c0750f1004001d04400c909001c0010300b0000b24540034003180e80032000c040c8030300e2502074034600c96150600c911072041150f0700006404000e281030302002011303540214006054402010070508070005080e80108400c07503070075501da61030761000fa955021514030101500c00500040005501618040300100c8050502074201880910104503210014400c00d046a454010400c40705500303005c0b03544501d00400803a0701e864200e4031101c1c0d0300c5a041000900c45a51680098442031205e20620702940d40060550368171461030404400009250000c1e5080025610206907024041c0300ca201000b580509060103c0b0b15003401580d8011060001d4000d154542240310001815131008000340c05210300484550140000000d04031011340c079100ca011101c0100610108a8881d0781c540c1c80020041e000c561040e00f050203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 825410962 1250 825409712 825409733
    0xa090c06080f040b0a0e010f020711150706020702010c2109060c2301060308071103010506060315100201020906071412030f15130c0201090308061c0f08130803130b1312 74
    0x4003047d46040c2c200c102211981d0020b0504c0340c000c04d0300c800e41200813000c000e0740c0b02800e0380c54404103c04000b8000040c6139a0090301c403450050500500b203c1d01612484403207203468481445007000b8041401420790800d1940c00a89480d2078040b203400c0f041d545c0c10103000100f542d4807071800180344084080010940165001d10303480400f240e01c500c030780d280c0001c4400c4c4c0c0201813480b0303500303000c0042c4441c20000140e910030221408086070280b0008248165208800703045811550204a03022850b240c500c028122144200002d582d2100c0080a060034440c012200301c440c56020800d11000d10310340102c003500844079010039080b03018018001510158240305110001c0c3c14030351500031682e010360102c45481e00a403100c55050b0788030010459441c60362125801c16074028550792000c101400c0e110480319220b8002c2034540603481c28542c1000b14180c0c00b0141a40c0000f07040c000f0311207861000002001c000340c110341081c03041c0144240d80c81d002c0c014020301a6003001c160081c043d01880707 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 825412212 1250 825410962 825410981
    0x16110d080a050a020c04200a0903081605010e0307030906111c2a1502130e01030506070f0c0507050d06021c0c0f021b090912030a090c06080f040b0a 65
    0x8140e5a200140d2102521a0300841c8102000d0f0150205011031410a406a040d120400101c101a10062000303c1e680c139400c03280e402030400180700e2000c400210503200911000e00c0d114148005610305140813820745a0f034110100c1c00350030500100700080e0300407103940284d0350345040112400c10506015031404c0c8511040046981e50203101e0740c7c06503003100ca1500c00c00440c803041c000d10007136200c411400c0c42c2000b000420402c8480e031010b02d084e07202e5010b4203c501a5608050500d80d680c103040410820a801c00e803203d811585c00d1007407442d0000c4030292900b2083c100418249090f440b800d440c1c000d5449000c3c0a41842e0644c0310400c9400c1d8100c600f2400310104c0110702520440300680145800014000414001c0c40c1e44070701d4a0001600040503001041380d43e504c07540c84010700422020207460708000b4801c1c400404155140e080103584600035182d00007807d03034010b041c03821102209074002c60900042c0340501c241c0c262a052925031182d0030120310350440e11600c2c1188000c042010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 825413462 1250 825412212 825412223
    0x4050d02150c0a0606061e0906030507020a0f06020901020c0d080706050c09090f040b0108030c060a0f090c03051b09040203100b0126160f1211090d0320010216110d 72
    0x12803c420081d140c5d2108064032141e90343c03480e600b0940f4402c007105042da42120310114405a4003000050f1082e008590f0000062060341c0d011b054540c0c5000c004103a152048891a4001c181e05c001960b041003034041440d01150044107405550300c0b101c0b103520a02c03002404090b1200005150b26000c1070403503903c260054a05442132411500304224984159012117480c01448000103106000100766800650240040c0116440b128800402403071080e11122120707841e01048408079003032078000310046001d40301a005030400d01c03540c00070010713081600034401c80c0d20740c0c18000561800034440b004054120400a046014040161402c00e60402c41d0704000c001d41c488005006c0300503004a01424800e44031407154076180c00c040d928020207580c0c0f000001c0ca034110780103200b4a285c221a04818120744e10901e4000303490082490001713281d005072b01040030a00c0c0302184060301600400421140d000071401c00340c1c00410030001110051000d4201090b11610711030395903621070000c0340c543e80003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 825414712 1250 825413462 825413473
    0x30f02120f0702100e0f04050907080f0706030b0324060103090b01091d03210714040e0402190b040b0705070b04030b090706080603070e180a0501020408070b04050d02150c 75
    0x14202249550000b00200e0085500c01c400ba190700f4040c0344160000d240c0180301d104880b590206200c01000018400c4005114001c40022404428401000300c04080d5000e041e01e0340c14000c0c080c0c15141c1c0309030064040d42c03007203800d14a031014801803149030445850320300c142c5813103160048000d00800c04e805400e481c0120b0002030050400d5205120301e0207240d01500c07614041a44032a00c0b802600802c40203a0304402e0500b1b0403142d08211280d1001c080e06104103000c0025070508100d810542101c0040882039044c0410341c6000c441c1580700c48000f06070742c0006130030401c20300054099445100e40540010a1400400c0014003e080c09003c481074815100d56407070820b89032000041e190f9040a000c0d100011071018400c10301c55200d4803004d4001d00d00e0b40d180155148180400800c0700d100e01008410b04024818103200615809018400260f191410304000310300b400030315800b05050400401c020421601c5030742d0b100c5a9150120f410740d00145094000d45105e00c02d8182d210954000c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 825415962 1250 825414712 825414727
    0x312032408010f0609090f020d02011e0e1527180405100b03210a0c2a0b090108040f0201030b0310150f051f0e19090c0516030f0212 58
    0x1540b000440810f0030009000e8160b44004841c12104031540192aa4094000e1440507081043c0010f5034284103140421048015058118600c5074981e0355100003600720001d10100e24010050422809000344002c0c070300300150050311070a602a051224030090301d40d420003815641e48000100f80b04140802c040c1030700c3d2900e45107485081191501c03040d60b280c41c503549024240000c501c2842c01c03200101150010130030000c00055001000580100001d440c2410009103c6104440c0e240040400300b024201074103c82e440e5008490700700d010401d400380300c0411140e03804900700307402c2900008120110441400101e01500c0032040440d01842000b9005a2202c401d42c400c1615036801002842e08036200c518140201c1e4540c41401c2c0e00030650000e10318409000001e01c407071207070b00c2d050490030511b0700c501081d142c800c40d4005880e11020054100700e003d4075406101401501440c21500d0050391035030018803501d11800c003034100a4421040c900c624000c02400081503003030a8040d889101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 825417212 1250 825415962 825415979
    0xc08062508150409050606090a0c0f030207021306030b15010203190c080c1f11031302132a110f03040b0d0e062503060e0118020706051e1003120324 65
    0x1b02582c41500425040001a1151445102c3e00b000c0712440c1c0d4400005005c9014110f0103500501c60030713a44081c81c1800386148000f14890580214428820381c4500c2c600041d86000039040018a02e040d50801c10810300c45219240c2c40c40400b00305402c01c1e150030300050a210440b402664a007004034466111440f048502d24800c06090603140305081c0501c0587c210002d8440c00305580d40401e0201081050005103420b114070b10a440242c6000600543c0c203a60101d1090b8000010b0024407400704050088240c0c80031780d07041e2044080d0f0083c1100521220301e956640f087d44a881d0380780d00041680710b106078154001d1510020020219400350504200d4804542c2d940124200300040005051414a01a014100403100307400b048940c0c0fa072034a581400c5440d501140c0200142d42000490001601442014015545c00719451200910742c040e010194001070303da0540204403180400000314001090840b0342038510740072410111f015900d0700d440c0a100d4003400e070100400000b050100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 825418462 1250 825417212 825417223
    0x30201020c031b0607020a050d11030904090c0f12020603011511070b040e01080c01020703140f03030a0506040b0111030f09041112090d11101a09040c0806250815040905 74
    0x2a000700f0f58161703031155181a0b903240e0380060020304c3c51b00300458050f6104d004682d8521a48805020380745050700a82c00101150084081143c2e040e2144000780082d110404400e40078020305288a108000d0540025000f4041482603070302c3d00d480820340542c1d480c40b03100100b54681c0c00104a4403485e8942100d000550064000e03850000e24003400042c4810300028a80f244000603005469401d00303540703562003013032440401c1302c240d8491000d002031328039810001184517502c03c040000d52410a007080100340c607250403040c1c1c10000070b00001d0518083c0402202d554607010110685d0311646540880c016283c0314900f081181030114040009012481c00c4034481c41c1c0c40d0382620b150300486103050741c00c0350200ca611400e42d070044902d9498151543e2090710001020400c819003000756500003450400112022101e04032420b00070403682400f08502034100c1110141c03890241c2e0701c021641080325a02640070204482c40b0701007110307011042c3c0584002c0c08050030911510400d42041c5a490 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 825419712 1250 825418462 825418507
    0xd08030103030309020310180210091503050a0f0603031b0f060f02210c0d09140319030c05040b160f05060705070b060609031e070801022701080405100207030201020c03 74
    0x82c00750901907d0180e01c0f41c46080c0075480d0410844900c8c0c80d0507000c1c041c81700c8180329840180324440c10081410a0783c014003c0e28a5001e9501142d0303441e002401c00140d500c0d40c20b080000c681000e800f48002504400aa90745805402d6500301c0641d00b0b041011101d400c0c0000604514a0b0481d00d0003108520b800520b9102d10040c8401500100234100f400310040c12288135510340020301c034185240754550029100503004080d04d51250000c50200c07819a8021520f450700400c0140c0f80d44411501806001d01c180d5190401c241445e00d4100c26a045104421084801c0318540200908214284148030781441c0c1203401ca8820740b03402d840c0901940d1041c1c105550584103e0005800382c40e09000311585828085c000e4206030980a400d00000f985001d0400914044d0070300c0444d080409201034900405480a223150031113000c614400118100c6428604000a020810011640004110b5290000c2d20303c0140e607520b02d030070b04900a020720b445501040c000098606807240c000040c840b80e4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 825420962 1250 825419712 825419719
    0x1a04151206061d09010302011d0303070b011205160b1b0a05010903080a0b031b100c12170c090a030201260f07111f05060d0f03083309060d0803010303030902 69
    0xf01074001041200c103190905c0002e0005040c031070b50006040b07045807102c000500103400c4a040a030140e95840e0144001d800c0522381690220307444090040410404241c0d000214091003e0b904080541d80241300d083c00d400204401454140983c00041003030076403554000c4001c01001c2003910b070061040d441a2520110710b81003c14559141c81d000c03c00100c44000421410a060700360010300c0040d020343d0341a1000c4c82080c0310001701060080101c8503c00d0055520104d842c2412900d1003030302c50f40a05070705540f510038007511119440b180c101c0400d507030f02400c01e10101d45070b509880421030100281c80914030030241c00d004101a401030014011049a240c9204007010700c50780c0f83d80c0701800080d028000c0c0038024075000303846199004540110016003611501c00103900c41403040c035140d980450004184804202c1d01035211040c41c039030840220039000b04102c400340071032218080340c445a071140c104030001c65030f5070b078880e00c02050707035903001500b292a90b03543e003406001009a00b41c103900 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 825422212 1250 825420962 825421007
    0x300e092805010612140a0e0a080427050c1e09030a080c0d03090206120705090d08070201031d1b060702120607030b01030b06040e06010c0501050a0b03071a0415120606 73
    0x407600b01406450420b660f1301582c698a81e440180c581c015014030b110301f10441c00b448480c940402c0003080240007074550b50b59580014007080c4903050800c2e5055100d00f0300c01389800c1c10b01c41851a900c0c111100d40135281c2030040012403aa0020b609e500c0340040b0f2507494400e1030201810010b9800141100d11861401e5940703860704000c0503000d6480032000294000000c10400c0c00c151b01c48040207400890300e18050f410003204c100428500b0100042c259403a0038080b80780421903901d80200401442d4801003a04501210114242d0341c1000b140d42d460b11120b0000416043d0b1108800d84003111340080200d0000e020b4544410b80702c01c42920b104000905045200806501078058000d9500d0b0140c1941e140600e48942210301c1240541a1410070149600c2140418424007030380c1d010b11010480000e40b4150b5404162a040d8540c0c032590b641a4501c0e00b2910024180c6c054804517080b600b411501c0c48505113044441002510600c1e12007441c00c07101045141c0c1c4032a802c0780e84074011401d0351 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 825423462 1250 825422212 825422237
    0xf06020d080a0c05030c07030201020d0504150c09240201201b0d0c02300c010201060e0402091515070312060602150a020d060909300e0928050106 64
    0x2010f81d651109a000400c00400c0410030032400100142900c03802480014100a098030001003600c1e8161000e0325510100140c0c500710100f903201e0745c0b903c0c00705800c00740d00c0709140a816010b10805006501c4100043c0203016056030b000b90004180c550054816000111031507280d08401d03001032041c6240c50b40b030310f000b90100c2d40000a04242e080203584890006000d280e0801406407203448850000c03030000030360424044940303010003581c40380c414050061151100002401c40f54180d2049801d103250b9018400540c0f944104140c00070400401c0780c000c07004910100702c910320310f012511140344000030300c0018180e00030400341414800341d1042c003e050f610300d4100c0e5100541b01440e0590f0205a01180720040f0f25401061802008500422007598403000e0108555000300191041c03038003001c0c1c0b070203e01c1440303000502c4001034506003200b14810000080c00503141d00c5410b4010240003020680f6a9002c0c80e03900c070751402142c40701c02405150440f45019200070311403d8040f4050b0152003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 825424712 1250 825423462 825423481
    0x608030304230d09091a09040c0509090a0f1502070209090304090b09280e1204030c050117070503070e0406080a051606050a0e0d141612020d020f0301060f06020d08 72
    0x1a80303004580e540d03d40d001818905040c00811b9050300c00c2100c0021750040344891b03211429440c0c861809010060000c134500001e11404050050a04085070004c051200c001a1106811500c941e04011100680801040c2c1017000b449001c2c2c002e90311959038820003111100c008003d0080d501c080c48140001106481404100c05065400303a0328941040c103d41100100625444031024400c2d6000ca000340d0301307140b180d04100c01c082a0a2440c03c0029046c230600c4442007403032006010038030b40502100d10704d50060400c0903010304460104100000403812492007800406c2071018021310804c16103540ba20015628000c0b1841110f9078050030600d1180d4480741480c84c400c4482039151a40781c20000718085690581c540100f9a0040780030200902140386820703c4030300403008400500c044030380e04031901c0140e02c8a03840b01089134801080301e00161075043e41802203c2d41591408207211035840000c2c05016103800c86403002c8444040010740a60006840b42038003925281c00c80030740c46d0007940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 825425962 1250 825424712 825424723
    0xe100305071532160614060609100905090f0403021b01091202030f010905060709120507050609040b0d03030b010e0a12081b0303010e04020a080d02071404060803030423 74
    0x40704081900c0c1003d56054400342609081c1441e06030605840c42c0040c8000d41110f900400c00f02035007800301c290aa01049000c2c0701c2c000d043d07415000d903040c081c40d044d000111345100d03901d0301d2801008100b507030280d064050340b298009407100038400300c098502607800c0c902c41c0100700e805800607c1030101c3da101d03480c0d654440324a0700c0c1040e9900c1390b0f00c50800d1000c00c40c5141e60841280c00d841a503c10981200c0d00780300e07a020052140c0701034419400c010000400003000c3d074200400840c01c0e03090b940700040000404008036601a5400c40d100d030300c1600024000c1031241039954200080070300c4a8105a03040c3d1000d45080c5098a070380e00b0b0f02501c88240090400e203800350512a840e4900ca8001086d80b1002404000130100783d00329106803022201760075500281e0002044152200600c4114940b80030043c01a001580060040b400e02c800000d603144414440c07040624000b0f42040c1007911290030041c06010048200ca82d241464a1300040180084000682802040c0c00403013002e507022a0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 825427212 1250 825425962 825425999
    0x311031b21090f0603070917010501080c0315070819020703032c10020c01091b0e160206150a0b040815010b04050a0e0a06090603142b14040e10030507 66
    0x2440c041560f48004d1081c0c540c0050915814010341c0c11000074640000c816110381101400000310345c0d0f5152140c2a46040c0318055540e210b90000d81c3c0140034010f0088129512010910b41210310b41c40d808040c604502c166100e2043c25030000454105142d017542200c1e0300c1c070741440a40062180d084560041d6020301810441300d5070000400350301070480640240010306110400011181c0c0c07655203a034119409400440a02c0050003000c0041680c3c812003941c0c8240104404a500c94503100002d450304401040d298403400980c030341244940b03076500200003420000d42000d56032602d0b0f80ca429130758154a20b01c143c030303c0321310000401c6810400003942c00315603000c4d15240d020303801d002c11003010700702c028549070311030340d40303800c00503040d955805440700450044890101c001025241e480c00d024880314400041c60092602415a607003401e0154081540d500c1d0100c4150091a1b91305030074071895112020070440a028800d841e20541000c4048911039001c84d204540c0d16180001c2520301d010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 825428462 1250 825427212 825427219
    0x80a021b060307141821060901090f0209040318080c0a05101403040f0209070c050114100501230c0f0f1204090b0303070501052809050601030311031b2109 68
    0x400541885400c00c080d1048080d0090b0700742e2a00c0c1c051000c20131048404d0070036001d041c48416400a242c5050180d00c2d0800303510402030008ad001070b1211340c2c080b808150024040d202e0070002805140c45170418403641500b840c02480307111b41d5410301135943e07030703800c0c24543c45445c0c42900000c0303903d0000407950420b800ea40390700402e80c083d0019913031190801401903410461101041005998080074030384611020385655100c0991401c0c210b086490300f81c214080b0b4080d00303040c080540070000c461000c40b00c003441d0564950712903c001c060064003402404c605207001280c2e00209100116024000340100011940000d402d07000c0c8984c1c40c214514900000e15040105010304100c3d5000305a00603c00f80450380307821041d81e103aa0840340200c4400445418071001c1c500903084102036104200400700302480103480c1500c0751503da141c184401014020b4040403030282c02c505005603040c0b00c4521081c50b0799244006070b01621088100710111400700700c006034900b0000040295000d910024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 825429712 1250 825428462 825428477
    0xd0509090a11040b07080307090b07111c080d05010302011806080c0d0e0616080a06030209180a1e030f0815040b03011b030b040b0906030a03080402010c080a021b060307 74
    0x100514020194070141102c040380c200302c0030695203001c600914a0921030b03803840b0359901c1c101000030720f10019a00100c207205401c001170008100050740300d2603100c0e41124102e0749042a005500014845907400600d1500003040602500c0081e0f440385048134002c1e00c8044882c41c009a961700c842c5418016030b408284808007207070500e000c2e600609101c1d9070a4100140410149580600c0d0030030403a10204802c1d84215540c003425882281540c22003000b407800d1101506650005550780001080d10b41418101d01300300e80915010400000b9107070700f05020007000410b4004440c5c0c100001002900400c03050400d82c1c035030602c5040300a200ba840c40d208103221400780010031016016404503d070781503413241610300791321581c0418403200b64615100001d03506000428002038400d280c4001d8400e095040c100100d030388001c1052030740345601d450450825607440c40140e501c11b1000d0805055500017207039034001d00e600094440855175480821115002d403600030040d881c0310444070300c00040c002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 825430962 1250 825429712 825429721
    0x4140702060f06150d050a0f020f0702040f1503030804051b010801052206080c1905010206071206030b0106030507020f0609070b1308030c0d08090307030c020d031b050606030d050909 80
    0x100302d10380c0040008001c0f0500600c0c01d5241d0900f42c0041c04029031090740c030005c2c07140b00c032000d11900b000107482a40950502414651350b407400e00400c00e029004603103429208022040961010444070207401103c4d4402d0b4a80c140104614011141140c6500c82c40c4c5482c00021413000e0800328003c0140d548240503800d090902002494418035042561351306000c24000091901a0102800d1a0340c010711219000ea010454401d18001d404100c01c04802000c0c4003c1e41d0204000c1e62040043c2010015a02c181c502c00703005066a0340040c05054004001291131030341600010f0080900e642154401c1d6030b02003140e43c0364501a21746422685c03251408120030601c0c100a0302c01c1d0250501800901913440c40c1a5045a2044011400701d401030869a8042c541012419030000d000b48008d6040594554001d01400120306c4007911400443d040002018441d203801d40c00d90295914100c0041c4d00791810a66546098510901c203014140d04d4018440c07007041a28540100280300700c140f91178 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 825432212 1250 825430962 825430981
    0x604060c0201020c1f170c0d090507030b040606050f03010516201e1507091809020324131a060d05240601140d0b0303091801050414070206 61
    0x40c034140032410b50003404540c010a5030352110030104010780c64803088900c0900e0500400c404100c1050408000b210014803d00b4500740c0300351040424640310002d9491003e003051781c9000d190743d0004114040c13000030001006034540012040750016101c90141000080405080e0788040f9120022540440e01079440d4034400c110034072180008101c1c0c23003c41000141c0840c2082c3c200c0032604001140c01403000040c0314100700e00c16207410360158003c0c071810014001421562688950800e001c060090700362249203991080544039030040880301e1500501c0701800403001c0c0c42440b8410b6880900016500c20030703242880200c55440b810f40ac01c00e0103c91054245258080d04443d0441c143e4170f1040005001008000141c840309007070360103080b40c001490782c074100d002844181000b950088030040c5600c548107680f0599100070000c0384013404600444d2840c0206480d0552200034003855010515408031100d050b40d00a5074284101141242500703402d180c00d460400042c0c0c032103000210b40d0301c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 825433462 1250 825432212 825432227
    0x11d03160309050d061b032007051005180f0d050a050f0909041a010f0e04230d0306030b060d0317070201022b1a03070612090c030602040612050105060406 68
    0x340300b82400d15280381c485011614206605000300c5145a4600c08503861192030881c2140c0d200c820300c0c042c05100011801c1610030012024243d0940714046520780403c801413141255149d2050300401140c544002846100e40d040b0381000d01c0c500032043c890b0090718010643c0743c402ca00d503403a818036040d0b03511030440d4642c1c0064001d0341864000d0040c04026900e4144050007076004a0b103003070407440884480d1101282c107900c510350300014043c2c02c00580a100003c281e0107038200706065840e0b1400c00d24100c0c8403610582401d05e40c0900c514070150141c040e8007020541c0d00548000c0c509a883d48180704003480394180c0500440d2512031090580e8250780c0c0e12541c05141840058108441d4421040e0100f2808a125803c0a008c00704401c40ea1014460082c0201c1000d1031401c18103041d802090726520640038030400c000f8813404808100c00150000002036500081400300c890b03880c2031410003904140188000244a01c0c0c0c400000d0781140500c0741a41c42c0140901c0c90540f40050070313107400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 825434712 1250 825433462 825433507
    0x9022d010c0308061215040803010512030a02070b07050a020a0e0106030e0f0c0f1f05070b280e1f05100e0c040510140d0506040e0a03021504020a03150e011d03 70
    0x500c5291b01c0c52081303e100741d0345240180e00c5658000d440307504003c10040b061401d0207401250358424030602d40021b600140210440d880f864003aa6110100c1c10100d0500400b8100a504284103110028030316100c0b440755812600d240d501002030060165441d0f84500c411440000c0d1607000300b80d003401501d804298852141c800030a45803c03000f4041d00d942c2c07040301100107040481e80c003082c1c480c00d000ca09410349078800003038140c00003003241c10320300e03001540c0e02c0e00c4250b0816a501c104c0e040b25803070300300202102141050704403804021140450b00c06842c04452903ca24018603200140d410602410340c2d010b600c00901c400d04107070500701446900005900700008200501c51311064851050000781181c0e0000c0f0401b003160700d0503405000998401c2050440103038000700406000c244d01042036801c0d030107149040e001c0c94235180002400c4102c19000605440c05054002114815030f911442021a01400074000006254407420000c03515101d124540e400400200015000341e803481307103a1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 825435962 1250 825434712 825434749
    0x7080a11061207030209030c0108130b04230a0c050d0305040b1e0d09050d020d050405091e0702030301090e070f090209030a0611070c05191809022d010c030806 70
    0xd2045050054400040507a42e03c800301c0c0e800076140e0b09505007840982000f490a0800241c10b08007a5a291151411400043c2560034804c0c040350402c1b1100b254000c690303010200b201986261034082e80d444040f9010b0480d004a00c14900040504200c0300e951940e81d01038807468209458800c4603443c56200744540203204c01d011404903c1c1e40007260143c8840800703444005840030709031418510b41035001051005641c81041101c1d8100d500408031030645006aa03001180d4451900119910821100b1640100d2604041140035940000a0b40c100d43e5411000e008681a0807100d94840805000344241480c6101e001c0c480110f040d0010450030401a003100d500d240076449003021507420711110703d1203e40c0007030600d0a010001941c4d41c007078881154a04040d1358900e40b002c150084a03c114503e02001082c40a61003a26500050085401400c2c0c000c0f040e080e000c0b241e4020390180f1343d2024842080c1e00c4410a5403244c0100c2c40384a6051700c441c503980d00c1d400704002d032441020030180b10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 825437212 1250 825435962 825435967
    0xc0705010f05010b03040b0f1005060d021c0b150304050c0d111018080309360c0409061413150512060703050112050304060e06042303010b0307080a1106 67
    0x709405031140900900c02e00441e0790710b81c10071707240c00d0b01c61070405002c3c0e0244820032820b0110b110010f1814004461040314101d5031400900c850302d01074081c3c039a6100b20100030a056044107080b03034200001000c0210794200d255070200d0144011400240e501a145a000c2c140c14142801e040c1000301e440780c00f43c0e81501c1a401100001f0741c400c074090703a43d040001c0d4403a0804443c102c0c071030300300301c041d0032254003660504001c8000308694050300e8551200070300c1c000103010391450b2401007040c1880d140c402500c0d25460462200062640680f1901020514018001030500c00c0500040720190000702090f45202d0448129409000d448202e0940c0c0b20200d2000219642d429252030319144119016100d545007507031020b812110140c0c8020001118030200300001080030080b0ba00751010742c2005a02c84110300d001c1222401a40c000d400e000f4880707807014005040b0000300c180081d20440003401168406c0007419103a0b510380c81808650b0b8448004100060f11010180c42c2280001e00840e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 825438462 1250 825437212 825437231
    0x90607060e010c030b010305100303080402040504110901060c0b150105030a2c0714060405011211040906030303290f010c110307060816090b03150102070e0a020406030608010905060c070501 83
    0x30b0031698001c900c0d1022954510a4030800e50301030140c56405854036002908180c0703941c80c0900319000042000344116a00c00008041004192030581d41342e001408030700c02036031a6800944401c081c0081a00e150881000081d281c00c04817215202e0303900103030346403410342d12452041c0025014407410600e0030f000d0400c1e0203141c0c904640a0094240d0901c00034001c039464000d002002c0d02c100c003100350061908100c00d02c0307a82d0700109454070083d80440c000804003070341e48000d4468069600144101d9041003000814180e142c2c00041480b103854000d410600407480f44c0d804119100884c1c183c004403060840209580508a04054140a0400e034090040048000381c1088907541040380814128001e1040c16429410119a207a4032401c00d480901c0c1043c10a40307090000410070000e5110001a0304401d910030f0021701c00401e01d281050405060886001002e90464011400024a012000107040005028102149400202030101c03900d03110855603481d0303c902820b507225904c0d0310170003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 825439712 1250 825438462 825438491
    0x2118061b0f060f02041a090d0b0a090209040c06020f1f021e030a0c14071109070507020a03060605120102090f010f090b0a090306050c030f15030f120a140a0509060706 73
    0x101d8290500d000185e0b02c0e070600c0c201d80b40c10040c00c90300440442051000074499118560080076039030b040804002c40d0751701d41560b500a00846500250030158a02c01d000400c03c054000000790f80280d020354002c80d0000721913554036941e00c06e01100080c0d200c069003000c80240e0780201107020b42c6401506c084803010356464031651060b0b41484400342d442c0c185508503a0b000100b101c010312103160790b5260060036100d106114625103d0035115050750300104060034014021180c200d940500305050140d40e030309000e40101403510585002e82100d4007242512030040c0700b190b40d16007006010541319040d24004450603281c2a840e5070600c5200c0501085642510000d000c0008403590780e20090307821480c0c91000d8a601400c5400c0750a42401404074000481020b5540040b20006116001c07a040000030303c0c0c40c0502841e010240101c5007040c1c0300340362480050101c1c0c003082e00c985940c00c9224000501034032880340a000011010700801e11903240035401085100e005810214620000d0780b00c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 825440962 1250 825439712 825439721
    0x4050c040501080709030b0c28170702030708071205070c1401031104030b0a050403030b191a0c1203070201060f0e04020103050615180d2118061b0f06 66
    0xa4051a010128042040d036030b11401c150782c0100c00e8508180318903d580d45402d00c3c01e40140410a00d444041440007000c88840e08202144000c8040c09a1088100002800c000244201d030b4010380700b032400040071580000700f01e40d402075200711000d01d01905622440c204103403403001c407420814108000c00110f00a8440c0e400a000f0f16015500b0001c103290000d0102ca1700e12403a44a0b060302030104001042c072941e5180e500007241d003800704090baa03502d4210001c0804010359a482454402c2c003200d080a2024400240c6008202e09030b81d1221507903c45286000768003840c1c0d019400070b40b60700e0f0003980b039101864000c1018000801e00300d84860a51032600b14a03000301d0040050f0f03034100700956a050250680058041e215401c0c6034480c0c4805e03105074880d6400a14948084250031496521001c16441d0059004281010045990082c1104170000841e00710001401241280c80484462800c44110f0324542ca800b51404080d04044001148010080c1c2c0e203030b181c040d220f4001c100c4c240207 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 825442212 1250 825440962 825440971
    0x40812030a150e100e160309050a06020d06080705060f0415050405040c080f060d1104020f0f03010306050415020909060f04020c070b0c0d0306030203060609270a060c0c02150c010b0405 81
    0x510001c92514203107619041000358003030098100054144181c0b800d85400010742c06c015450080344000180c107025140420060004010750b100188568400300e0603485403003601c0c0c103041503540743c03551001004958041c0b0300301108240030410040002c240d4502c0700180124860400e10f08080d600c10001e0304454400c1038210103e80c002042002000c00c0b94a002d510400072204049071090300c3e2200c40c80300c4400300b2414016039000407604903842c00c40c02503600045504500d55660340e100c1c60309c140500380a0342c08684502002007400c140300e4084c001e680710140043c12500d41640c0d082e04024448031048802c3d41c12550800004440716018817004002d0100c008100d9512403146011301e01e803941c030140800402d850b11034113100691303010480c550400804c482d80c02094640400d01c00064001c1c451601000001940718030380001c0215491006a006a00c10400c0d450030450545a080c3c0192000303500c0090448a01007945000d80600b80030280c0740000501ca10080e00414100c6201b600c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 825443462 1250 825442212 825442229
    0x1021c0215090d1706040906110a0216210614040302070f08010c0801090c020717010b180f070f030213030b091c0c080702031204091a0105040812030a15 67
    0x8048441c80d985440020780c02802050040140c4074060200810071400c80142c1181c180540c03000c1061507075076800000c9050340001c0c0c00c001c0d5440c0191000c81c1c69100203c1000940901b07500801f4400811949008440403407400e941c410b085609802e0505403911030440d00c20745d55010790303880071509580c0715126500c01d4000744507a904104503004a07058560080700c0301d0381000d200d6038060364407909441c11a8000c40010483c2c8074640c5040e400c00025030011040140030303e840c03050511054106444180041c2c0e09048402404229803607481011100180003012000100c0c0301944911403007890b201051400606007845130703508460320000c55100b0b07212984840c050000c503480a00c03410084205e01d608000c030015150002400000381c20700007900b01d400100d080e801f0354800b40a290b0210440392281e5582da902c0300201c0b0020003001c000b1060040511310319112550142d000c0780d003903950300c0004248008000ca120301069100400004c00c054580610180e071841c40340707200025100b0308 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 825444712 1250 825443462 825443473
    0x303052212061a01021902030a02150d05070507030807081803040902070510090f02090c040e07050307500c1e06150d0302150108010b100e130b01021c02 67
    0xd007490740030b44016805481c0a180c46414030f0b00c05a03000980c071303200020312050a60071031026000180c10807200c0070020f908016500c1e030a019034a6030000400d40c0d103150b03c0d800c1081e0b440d0030070300700d9540c080d02034020040781c079180100ba196401342c21070940c008040d12400201c0d05010b0701c01411904260300111003950041100010820140650759850008036070801c903084407525507800101258102a003d07004100205241600803411100a04502d80e0004007608140d0030041855000f203d43d41e0005011600d042d01d03060705d8a10070039a00310030003654404991b4405c0540082404491000e10701e86e0b0138070484000c8800e54003c4c03c0400b46420140904910380c018088001700a485001c0d10b5810400412403860055000222000010f13610300302307030110394a010b070700d40304282c0c5040461825038000020411015085050341740016520030081c00c60345003098801c412007070010340d840000840790002003180c543c01254441e00510480d12000440703c45154040301700c403281d4005030400d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 825445962 1250 825444712 825444749
    0x311210105280303030b060f0c070e090d08160905030a0c0321050307050f0c01051312021501180209090a0f0501060903080a180f080601080d140403030522 68
    0x32411600c9a0141081c003000520402d200001c040c1c14140402070a06940388052080340d00e580b4156880885c40c041085d5a0300481803043e03507102c04603c21005403091001c0010f42c814008144c50511031800d454401081c1c84600c1841c490b0300c001050181003000c24040050544d40c10409040c02d280161921800c96041d420f00030502d841e0b4003656008a101e403450070303101e1684041200e500200c00d16256480d11200e00310f1801600c00d0f080918915820041801310709403040742403018013407080308c14484202c0092001d0343c0301c1894400d80060980002c0040100030442c42040211043c07103000141340010160004880e400b095407461000303070fa51b40e13480c4060b02c1d06208843c05407800c2d0500d10007a82c03450341e030140a84200e455443c20031a1848842e9121202d0480410103032600c480c0c940d1040340c4644c1200d40e0b82c4400d1040c4503d03442400e825241b13090050080d01603801c04000d26502e0a41140c60a540039403100400e040c030400d440c0d428041f525032000301280902840481801c85499 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 825447212 1250 825445962 825445969
    0x6180c0a031b080a0c09020a09091b0f080106020703020d0f1a01210b01090b04060911220b1b1f0c0e0316090c02010603051506010207061407030311210105 68
    0x2c5070382140996900402c40b81000c550500003060843d84155001769441c099024101c8101c82a90702c8815064103203000c80c0604510070380800e4101d01107a40d011214580000205c500072021301c90000580c010500500141c201401c8071410035010f003c0300c0600d000d842c0d40394032000f640b5000350410115a10018407040c20700c89000d0900c1000e802c041d0a41550b00d4403004815401032180c040700556074061103c06031500e411000081000110410071140c2c01500307007030b04c1ea000304030b607884100442d440d003004280350800038025980e5030001141449050604d0300d90f02c580030b25048205100d090050758038105800c0300030a00710b8000c0c0c0041415061800c01030514050790740701610a80194810f4204031010303042840840300301d03c00104010ba88580c0503401401180c0000d13183c0e016407501c0800c1110010325840c00395000380c1c2164003d6544000440c1c982d4a02d06064103901010080314003c248070b90407002ea04c00c06104c0640c5010700005119505000144185802c1462a40100020f14 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 825448462 1250 825447212 825447263
    0x30f0f160e04080f0d1803120612050c21160905070806030a021905091510050a08060f12030d0509010c03020a0504090c14070b04060c0f0206180c0a03 66
    0x41ca4aa5035030301d050995980006024460420109a5001c900d4050001c01c0c2d030441c1076454a03001c49011103080504008200200b2000350300c0006041040c001000150450301070340c500e0f082809043c601e1400020083c88a050b01128080c40d01203192643d01100700b8000e40350700c520700c0c043c0c01008515100f048000d0303940040c10541400303021000c00403e501d02003800c580076941120f58590241d0814228907030011150000c45e04030383d14800300415031420801c0c24640c10802c558440c4001d0016004a0340b51056040610004140d035005c14841d040924007510201c3c0d005043d205805003103d0fa56140d80c1040c502c21711001d407550140000ca040a00c02c840c800e0116140c2903107000505071000d02030303200d54031410750706542c0c8402c0e00c807040b8032a103403022910f2000382c08203558201c6400c1846401c001503070207032020b501c0c00007040d42d014001c1c0144000d01e1602d40282c0883d650302085001010180c00c01600c03580903c0c038a0403030340e40e6040c030303e03a018521400e4440c03d1000004112040700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 825449712 1250 825448462 825448469
    0xf091006080a05130308040c080f101104030f11040b040908090a05100509220603031805040c08060607050f010c09081b01080117010b04020a0507060c090f090b030f0f16 74
    0x101d10b004140400c601040005400c44c0350107051900281d140c030328203110410655405048980500302040405000c0841d00b10501048404180318410b1a250a55070500c5540b0004000249800c603180c00261a00a16080902e00400c005140c0ca4140c02240680364440e00440f800c9400194070406840c001480a019040c02d4a0411540386030002c0504035106241c202889121078414615400200340441c14065070400014032481d652850080c1410a016200c0100c0790b55500002c82d0301d090911881c1003420550350b074a0515258601403041540c04080309039218020140842440003090041e20560112940d0f5a01007620302401141032401c016059061001070400308a4160b07070202d10981540c0d140200360300d00c0709106410724014500c19010315000f0307001180c84c10019402c000a084814010201803021468510040700c0500c11802030422002c0049018481c6407020744c07015000740c5026040342c9030514510003551400140c02a0480185d210326601300322642c1006440004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 825450962 1250 825449712 825449731
    0xd200304060818010c021b27240609040c1e091401030e03030a050601020712030801090f180803061309080c0717030304032a060e060c09030703110f09100608 69
    0x5e10402c440c000713480c0c01c1c1c41039121740c515041082142d100c0e5903003d42084c20201103a425020424500031244202804950020307544000340440d038100c025003208903442002c018400d5143c10407002c200002048803900003030800c20306400b20304016000d880401911200e47d03d44107095482c4c022443c0950382c2a100751410181001494010307200e0000c01e42e07401c21801c0c14042420f03030f91500100c2c40c10209901020801c40e40d2142003080c560401789013410380f001080280314503002d4170351000076901d1079817199a12a00112088000c02c401001560f00310000510900341e01c80c50030290800c1d184107510642c3c0c0c0e8a80003440d0b0656107420844040182521100c0c85400303104a4860b81c0c407804014009000d01c0072000b440c80c0b52079498181d0b0540391030502d0000c1078449450800000410b001c80a0303441074070626000c06ca00360041c0c0d00352030110000900a0448508542d42c0340044001c0c822600e0f000302080380d0403101603440c2a0043d10843c5c0d650328180300d19260040007000108040c01d01c584 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 825452212 1250 825450962 825450971
    0x150501031b0e19200c0705100516030e0604090e0115030c1806050d0b09070b1317010603021f1205010b070f032d18080d20030406081801 60
    0x180d501c04501264002294070300d01c0061900602c440340a40b01a9a44405410030b1300f41d2611440094009800303043e45400490b00c031903407908140b109400f10743c050306010400a001c0140825020015442c92900c00e14001c50005101030224030300383c1064001c2d2900e00d0f11022901e00c034000c00d21400440c00d0220034101c02c0c0710b203540c8840840080c40d015030000a0001392000598200f01d802000c010100030382038690720051410a030220200a58500d01940924100000c44070080c13029129610b1046400003a814904504403c050300390322083c2500d0354131030200002607500e91a000b1101840088407a603111a10000200014000c0b0000c0381070520309001032021482c0c45064031605648051421a980c0450a040c1d6903414940544540049007c05007449044c4501640e01d00e0140e5440700e41c4406074980399001c200c640c3e80646c10182d485045400311003403007040041103038040148031012038203400034002c0c00c541c4990000400b08080e4801e1281d0040240341070241140316800800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 825453462 1250 825452212 825452219
    0x20709140606093114100602100f0b0307030f030f020d0e090a02120405011d060f0402010305040804090f15091406040c110708010b01140c0d050313150501031b 70
    0xd48038094403d072240035800300803085280302c0340c415038450460000000e0f404210185801200500185000700d650440300201040c4d60300f2820840b481610700c103402070a210380310201018000c2024030072042a44c0d032120520b250503103082c0300741400b55020f00411540306080342006400b10215041d080110342c081e0040a000f142d100c00b648299070000c0311801c8981e00d494203482d019002d41584140c1d00103046c0180000c215055000802d03400c400540c00c9052100d03100c0d80340d101c03281219103040242022000500544c440d5019a510a104613200e0341096160700c0e242e412241004c42c0114920b40d24000c002c5024030b40165100241907640052054044400b8500c0c03854801600c06806070303441d00c02c0191103038000c081c4106801c4140e8100d40540340d1743da25243c041c0840316070403808983d240c2d105409050108080350b4040e10258000c010900c0141b900302c40c160700041030131035010b0603402400000f405144c00060441425a070100705541181080851070b282080c00807040d081c00c00081 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 825454712 1250 825453462 825453469
    0x40509160501180915081e0c0409080f13120b0a14240102010204050301150f05090105032e1a0f240903010e03070f15140c0703030e06070207091406 65
    0x342aa40301e01d030301042c0c0d1550130307800c5411000036400640040c054190116048005100c0c0003130172000764001c6502e0108c401d002e11040ba10240006000e440080000040018012008002e01c0d5200d0323022a00441d510000011071168a403401c480c010910b50600801e0784070f40c015481ca112016142070b1442c10855400340000c45650301280001c0042840d1400580c001e42c1034070006c007405002071001248200c40d03161505141e00464003a03080c40c0101040071b0a202e10301c40c1c180c410240042a650340500291490f003060075a2113500900c11141900da0314100303000f0b540c02c1000c588042d0b000403c040040082d444186440305000315410b54034a90b104100807092180481c00100740c40c5d64103040e0780401c7c01b400f8816441c0070b0f544000182c0720204010004111041c0f4003d0110400c1011404044000e032100c15000c80305818841e0089851001c0e0400140809071180c10006a0506112196414071004031850b00140e046514100f01460050080e01c50b01d0800b04c50401c180c0c6803c8001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 825455962 1250 825454712 825454757
    0xb0708150103090203011409070f08240901150308030618150123071a1b09010f0e2211280c0507090c0e0108191505040509160501 57
    0x203604064a0314904019500d0a61180c1c40c244641c503040000c0703141032840f1642da40018800c2008809802d0000500da0002040c4c00036981144072800c1041752030b01c0401c240610700540500d00c0d0b075507a00303180400326500b44504d0000794801e4041ca43caa192000070440640c07550b050800203c19140204500c8440011080d0082e240034208141e1848110075006440b9028852500051200080e04000e20500390880c4400784050301c207801083e5909007906100013010960082015024081051290302414844042030807516005030855803100000304a5601450700004900443c18001c80c8403589003d949005090310b0101e03440c2c040b0103250640540307000103800807200e5091445441035885001c5545407a604a0101d07481c1c0c90f00c8041110040ca0081c0390728002c10300921600e8040d5004c0c0c001c0a12658203002d4000c0042c42490710381019001142c011800799609850202d09aa80e503c0f525002c0d41303012004140b0302207482e4920741d441085401c00f40c140403240f00c48001400d8038080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 825457212 1250 825455962 825456001
    0xc03150b0a0b0a020c22200315120312100603020414090603120c0705091e06040b01051e091302040e0a090501180821090c190302030d0503040b0708 65
    0x551940c2c4111800040b800e00f41c0101c0034560100c81111268020024079086d03404000b0001c4041110820006a8841c042d40c840b41d00c848440d42800051009029241c1407240d200b00a050b00541c900c4c00486142140c0c8008950070104c0d45000034800c40319a2461403101030045030030214501400c002c040000b030700c000800d8071f12170070080700082c149450034446440c64ad105084040d071500c030076070022505c3d842c46003c1c042c0912101400941c0404224071283d560162281d00142e4584560007030002901b022440741c1c4c144034080040010b03515400d1000c81e18280400c01d82d54407000c130002084100302d083c01c03c43c00c40c0c500500080c00010707614103e03e504901e1a80d000104220240f034024013600d00d1040303500c4040c0340c3c0c080f80c0083c04910001011410306403889007440100c01c3c00e02c0b0114900507a140c1c0a50b40c001c50300c0302e05a0a090110b0110b40002810314495281c0d298006885e04000c96107400001d00b011050100304681141035641054490134541c02e00d2400c211000c800d18000714 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 825458462 1250 825457212 825457229
    0x18050106090812090613080708010c05070c0e25050a0806030c090f181204061106070206010b1b1c0210021801030f090605090c0a0e0f010e040516030c03150b0a 70
    0x641c00c0c90310345e40d0400f1954000d9041d038440c0c042e5656040320546074421442503c896501703020407600320521600c12030f09415400811008038600b0100f0b2000802350050414101250b894204000d10b01d112440840d001c2c11583d90701e96a04e00018000c040003401342c805d6000364030895113060507588110700164800f680c03c001d4003a9507a50411102e016841110005c0c0c2c1b40200c3c11460800d0450000520941e00d80f512070709114a507003030415a88880071540c0200517000a0014040341c2c10780300040060707131041103258685c0b04030861140d05007540c0d5520b02002280416200a5890f01408080c003104604d040445c01d000f5600400703005024100f0b5124105980c0700e0b401c07840c146e006d601450f032890300210200858038005203202e58940b0091801403091140242c00500001226190380c4101c060075031802c0d10380d00c0e0003800d405600303001c1c1c8212680c3c014082c14010040c0305613540301c000d5005034080350190303184d03041006c904103842c802841d006090003e5010540c45030b42200045a0428 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 825459712 1250 825458462 825458467
    0xc0507050a0b0712060f03060b1c03030e1f0506090702070f06080703060e090703031d0303120709170c130606020c0d062c060a020a08070c030c0b0118050106090812 72
    0x640481d03960000313421550242e4a020004520002c111403070034142d80c883d00d410441140741d1010809a04540300d8080c03641d81c800d42c2c040d4006403094011031203080e5032504884002100070b0302c1020074011030150700942c560720802c1000c01e240011299070428030a0010f80308a41c200008150f0320402802440188621a004031716454400d038400002083c1400360a2804d09106000a03240c4020340b000f940041c955050f980d565591805a83d0100b0364010700540c58140200c000d041c001400a016a0602c20488000150010365004020a17070b50f4050240c00d209540508000002802400861402d032402c0801d20465030001441c00440b5411505610010362a2a1940c0985080c913200c942e40031081040b04052204003400054000081c0240e4580d81d41d03010a2904a00548070400000740040022a210740d0040c1c0710000385500910741017008a05588407140606001ea005080340f40f441c0000180c1c0901c64070030b16014094500d05655164903002c9401e546464640325100d008400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 825460962 1250 825459712 825459721
    0x130b0a093939062a030b150c030c0d26100b03091e0118020906030a080a050d06080f1e12040b0d0c0c05071517010b04030201110706120903020109060e060702010c0507050a0b 76
    0x6805605446c4d01f08031802a40c0c1d20300322095591242c00030101c0361014030400030703503612840c015010500c0030b400b111240c0c0507400c1c0402c2410f40f481005803035171407401405e80000c1001151340009511a450074402019001c868095444071540020f00c4108245d262600c40501d15000c4d40031800f90903012140c0c1c9003182c407181c0000f401d002000000500c82c0d140003810302802900038001e40a24600e15104102d1a5560700c4400c0d15a0059010707142140c10482103803610032180c210103491004044200c50225400d440e1002a5031b0058200c01d00b01180816034a40340c0100d8011002d00c0304107441d2419412446a07101980c0e4407050003510400140c1e014000002449034005003070050a840a064882d603445030000d080b0b912078001070740003c2c01241d024036040070001e00c04003281c290f555908856000b502c2e0000040068450480441d503c4040260110340c85010b00c503c0d5406801c0503180b50b00301418081c0c00c42c0d4044580710f00f030050910000e40407410101e40d410b85140c210034004019030700c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 825462212 1250 825460962 825460969
    0x110d0804110a060e1201151a040906060804061a030c10030b0a0f0504050f090a021c0b1e1b09130b0a093939062a030b 52
    0x110070040340c0180c02c1000c0040d1080c0e0194811030f1599041d6030480c403404800100c0c40c240d4118854441c41c0a042030f00402030b0b903080322007011000301006a2503080949450695050703030641d501860014100b0401d010500c0f0461103070036080266500400403641c06100030a498100b00d0455074450049013003051006800303900003541099000300034008682e02c6805203444d01005010b50740c01203103002c0c0003940c000e2044117003500800f980c0001f0010842c40d0f50810115080031540d040c100e0905c1c4042d90300080704091118042c0c00c12150860f002074108401c1403000c90001e165048081e58004a83c0030040c0b031104513050000107070360002c202010901510f0191420303914150300700c0e41003400001c5100d11540005805620351078022081e440c82c0b00300d0050784800c0c0040703810404072a2251440c05005c0c501c4141c3d82c1901c104200802e10040c504003c01e800c0811000d10085184030580c010444030740714a10342003116103c002000f0002c07d50800001c40103200c10403d065540a88045968 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 825463462 1250 825462212 825462233
    0x11012a050c37380705061602012c1f02071202032505010b0d080304141203070f091707030308160504030206070f0f03051215060d0c0504170102030106020706110d0804 73
    0x204001d03c0c803503489040c1d01d08142e075414111145003040c81c2c1c0c1040e242580d44107020f000c0405480244514800b048110025551140320320904458814005110700141c80c001c0c402864120304000142c0329110350030020b0300920410032030000c540007041400c90b440c40c5146030504004071b4081040c030107400341c5000c0b4014401840d403a80d06c001c1000c0e900081210210056100d548a000211061a1410341c41a075030089038000036454241072000840300e41c07041722001550b4001d882d1002c250f03030b40c0d07582807005603242015014441c2c10042051080c190802d1086070440014071b1524440700019038024032034011400000d00c941c000080c54018000090010000c50340c100303c101078800b4981c84c0141c4554803030000509401d200b03000280340700f0700c60302d015210194050000c91410762900d10207001000c20700f5001040c0241170001290201048020420300701002d0001070740e0354100fa0029203490581d500080c208154007041c6000110049052141d144a9040118258549240400012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 825464712 1250 825463462 825463559
    0x1801020909160908240405031b0c040c080f1303090b0a0810090b10030e0a1b09060807030f030807030216050a11012a050c37 55
    0x120701d000500c2141e02d12144042111201d80d1900001281e035442141d4465049041541d52981d0080c607000d9030403503858801da401480f400c242e0345480c0041c0143c100040c004c4050900c0e562094803450700ba07007418403907121003183ca42454a80e130701e4460101400c0c6000144011174224089103180c040500400d16440645000700d80fa0b512000098001499407400704d49100718801070346000111595507200e901050440506200c40e8243c510401368080c0c41c506202078100d114100c503001c041503240e030704220201c00f0120b801141c149800c5e48a415500705030800035058029080400000e942080c070701d011a64541020b40b0141d4414000360000d001d140c6040364941d50540300c031400c10001103a10301389e03180306180b092481420030f401102d503440580049000340e8100f182240e201c0920340c2c20092075620417801c5980d050075000128507a0720b840e2140c040311f241050001c09016151240801ca036528482150078054030380444200070b03402c080d0a04404001c41102101c401c40c5003640180309 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 825465962 1250 825464712 825464719
    0x90b06010c0c15090e1515040302032e0207050c09090c090103480e15120a0f080a0809150f060102071a1806030c030105130e07090501080d0c0b18010209 67
    0xb91610b00c10200310b801c0c40020301441f91400c60328000c0b0a1143c20b0a43d41031300e801030010702032451252110a240d5200400301014100c4051000344c100040d800180798091088015005041c078a0050165140700a4920704c416080030112015a0329001e07202811282c00400e103026007250100300030380051018641c0310454604501d07441200703008124031860941014881e24000d039859041a00490050720b17100502d042c1c0300c1c0ca0304810725044140e10112000c900c1501c406e46a1a5203090a030400751108a0700c0e05030100702019030a0f00701c02d25541c002c0040020341900c40302c0500884200d10020150300701041c60901089080c0d108210b15130203402401d841c281c400d0140010f80e0300540060f51000504407460000c0d5406080c0102542d0181050080190659081004004040d442801c0102c00d0390794440c1041d540001c10004c5600504207040c0000c0d440d410403460300c0c10000c0c0780c50400c00b400500180103000592a0310982d910962a4108800d080035101c41903002e4400d007005182e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 825467212 1250 825465962 825465989
    0x501170730090f0317070905041d03160c090e102703080a15030f2406031101090b07030e100504030c081c0f0e0d020d08070303090b06010c0c1509 64
    0x4100841c207a0f040018000d855450f104c03c8181000c12090034225406000100307807070000c00060425402c61001c04c120380c005480110450070445c0c1c59900190142c1065941e1100400248481c02603010301908001200f80f210000c404040355603100e001d01c101c00026902c80050f000943c800c85014280b0311902240c9401941608004145c16800d0781c00d40307003151401005a642030340070a866411031b644940a841c001d46680c441d03030780c102c600750103c5c503065456540d08817141e04503200d8030000d584150342c00e44c11414200c0c00141030754482c0d0445c05006404011020200c1d803c00302c0c10b2019441181c602c3c40643c1902c104442d5801741c1d0f440104007091264000c100810007040900c9000c0c55035107035141e01e1541201c02c6079842c00e20120354012039960040050740d418008014005140060030000c5403600603640c4c00780070740c0007030b005400080c0c0c0c5110b4a002c000e0b0300718240c0d80010091030f0001c0aa00181c0300ca1649114034450311a400c120700484141d2a03008019801c02418058808003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 825468462 1250 825467212 825467231
    0x80c030103240c030c08070908070314010219030f1401120b06030709150e060906090c03310c1a04211a09060901021c020d060510090501170730 63
    0x2000340c070105007140c01290315a400901d803180308d142544101c0700030300b00030300c805c070300d15140c0c00205240c0340241d00392035408126038a522659180c420b4681c01d025900020544500c0318448200c0b40501400c0000c80000d400400c00700c51210144203c0981100407212142c40d80300c00a80f0307000c003603480742041030300b0602e442d2144003201b41880100d483c02d5015000c2d994880040151401c02251031a900940c0f40f40850407124420028613030010080d030080d42c81c01ea200060003104210500016600010304c0844000c010000546000411018104402d2030700d000b143c0381480d00948c041c135038050290042c0c040c0c03d982180110034040d030708026480904d116041e5560001002120b11001a2140c000070650000c01407003141c500d2140030b0310041c0758014210405000c1d510640c040c0b00410740700d08010845a0b140220207140b074110b501c4010143c1c0ca041c0025204101d060160420340c00d082c410406c03003580003181000300c1c1c207101304090a01402c25003007003019080460b800c4119880c00c003012 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 825469712 1250 825468462 825468467
    0x10806010f03150611210a0813020a1502010f0b060a0c05011d01090b0114030304050f010e030609010b150936100e0f0412051c0f0c0906080c030103240c 67
    0x301d0a4845c84182d07a80da0503000510031102c0e11000c003000c1a884100312403c100c0d07100d074401941054143d48d1850000445070005a280626500312031038206541e408003013800d030244180491808002c1c800d000503442c0b240001d40a02560441e1001d0000d11407055007041029841070036151116006201c900400000050091400c004200d6813840c92100101d013145500916066404008000710300d850305020500506040340301c1100d040c8402c520042159a80500515205441403c0002508500c42040001185081d503050130107040401c45840141c550640350203040400c10101c0742001034000c0e00301e940712101c1602011081500d401d10022680544c2c490f021100203c0030112261034040d510813680c0c4090703c0c0149004d81c2c00100e0201c0354041d2000d0500c11401d61107800d01030354201d02071002d403200550019800d6540d1480c014586400c8861003011b072403149059445403810415a0328a0311060001078000001c0411001c9044002c0c406200040340081091181e500c107840d02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 825470962 1250 825469712 825469727
    0x4050909010204140102070e065a01090b0c03040317180a122307030c05030f030a0f080402061e1c0e0a0303020c1c0801180506010806010f031506 64
    0x41c0d00390204c4074007650001c1d61000070040c0513210950240c14483d00e5000410030250b5840c1d800440107801c2d038051054400d440d001c035140c4180034140002c0444c4ad100c10304508050000c8101c1ca14801c0c81c0090007d90740c0c4080421f007511004903201e03544440c1b01b04401c0c80d5008942c402406c4170f9a01c0702d4100001c0d80b80000d480108a901107c0d41c0340040f450420842005901600d4188101030300d0300004103881c003d06049114440d400540032a10214005041c192903401c02e0b90b007004102d104020500f400c00c000341e507403090300c0091402d10b00300501c02030442c004c2d88007520400c88440042819943c8040487c1c04011510600024054140d00b0061854010314803e400307048900361090072080d998003450307810b14181c401911a401e41a40d040c1c0c029044118111a03606c101104a080f05012090340004e0010545031009150300d4032400560a0640004000d400e501700703000e00156980122119402201c00d0914940c2c0b154091401c130010302c059906424140d0104600244590300a02d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 825472212 1250 825470962 825470969
    0x3050307030e09060d02060a2007061b1211031204060b01080a14011e0801020705010204050310020406021f2301080c0d02030706050705070305060c0d0c0f0c031404050909010204 78
    0x201d00110940c00b07810070070301c028120782050b0043c8081400000601c1e0010081c0003003421420080560808005c0b5040c150002c8140d0386920342c4030040604c10f16400440ea1244e109505070100d0a80b1040c1d9a40040083e007402d00d1f405021b40c200c5000c040d8801481522003211400f064807040d4502810400d001c3c1c4004200a4041400d0b0004580607468070301a224075101071070021403a03030346000c20311a0314182e83e50004120840210f8085920f803c02e00003030284a00480002d62224103120801d42850034007481010500c2c410001004055000b1414400d040480104101c100742182101c2014069074401441c0401c40691140104070124141c1d03030585072880102c48020b01c6040502c0b109604002d0082d505a115820401c21144184010b140ca6440b0700e060701e0300d0036602e540d040c0c034081003514224054000404c1d11503000d4502c1c440c1c96070a48291138150900c1c0007502c2e010b810004908405030410055000d030401c220b1010302280c0040001800b129568038005c2c46080c002d420900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 825473462 1250 825472212 825472217
    0x70503040b070806010804110a0302041404120512060d0201050903010e150c12010b03060109080a0609110402180405060f0d050703060f0608030a03091a040809130516081f0305030703 80
    0x1041c1c2d4644901e54040c456081a1145c1d503003034031207481d204c5408400349401070b80411100400300068540c0d018203c0ea4564074070301c06030306043c5847c1c440044a45980e0080030018141301507100c05100b5540d1503040401034a40342901d0b42c050004903068495424900c0e015070a1480d030481d104000202544042e440040d50381c150b40b02c80c00502800d01c030702c84801020120500c01800410344480046400500c1410180c0d1455640c0c5241410301c0b5168106842203035a400c41c0070203000d65506040c01040303046404510b401e580310360440328480306d408424016a5038400080c11510780807a10400148003d2a0000e00244c52400035178801e024042214010709001c6000010f49490007290181c07980200910304001c0c0e4401c045000380400b000c140c17444041080d2100c10000303111210b074025030040d0041c9039142000c0c4280070074810401c9421011714545420000b808091210886101c81e59240c0407015448103c0c030301a60442c0e451000c84c4010440038000700b006800401000a14031a4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 825474712 1250 825473462 825473483
    0x313020f01031107021909090c0608060f0a0e0403110708011d010204060c02011101090c060305060f0907050406052101270b03060a0e030d050114040e03130504020319020307050304 79
    0xc40110207641000d4160302902d04103000201c014680502c55000281d00c40d442c45c06981e544d01107160aa49001d5401c0c1e4449482e00c1051040301c1e40202c9060713100e14141d44100c07080100780e010804041551041c40c80c1e000f0881c011070205803145001d1071140d0661422600309a446a00d03145c024080c50114041e541c5600b180c4d41403400040c02503d007103031459161540600c0f4103400540b0304682c9040c1d446441d541e500c48000c001000604028064000c50b98009aa450240103010554404045241c0700300ea00c103041113147c640c08400c403000c1e42e0a07880c005440f1a061000c05815021418001014003110000030030240c509641900d0190a03041949000c40d40541c0300d20200c2c4c1c590082107406410042c00280314032402c0d045002180a000101d80c41d2042e191100b40845800b078000140e0842040040302c000c0ca06800744500c02003e0300c0182d882c203602e422100103014a20f00c02e480c0219000310000b0301c142e109110601e0700c040540c00c1950380c0d250052000b032003a402280d00700c4911441 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 825475962 1250 825474712 825474739
    0x1170c1c0906151d060d030e010c060510060f0810060e0312030108150c0313030f0507050d0801172a010215040f0501060f08030d0509010b0307030302010504120e210c06031302 77
    0x1001d20343d0301905015080c10700704d20b01d9031812108428103070030042c1070000c0e2211880006000c0c1c8201d03803103038014dc000231004038140b20000381b2100d003010110007041a41024051501c1d284558081182d5140c2444401d03000600086414400b4160301d1030941400800000b035441804070304140720707080c9070f85c4000056070742c2001000140400e84840c005080c11211100000c1e004901c801c3e8140d0041c1041414080e40d540e8461a198200c4080000140c850004006c64140350300e16101076002c000240191030f03081c2203001c40d074400303000710380a48004804000f80b03164024025107544001c503039500c41c401c6c50700b410070325001300403043d0450341507103460000281849044034000645440001461070a05030102c1b6101405002c0c0404000355642d421000300c503a002c1014400442c400d800108640c5054206082e41c10030b5009240107011200030020100c1d41c0e001c0000700f0030000d0042541c100304100d11001d1518030401800c0343c00c22400800d00058484000b28191201c0c8201c03403007062802c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 825477212 1250 825475962 825476009
    0x170c01020c0f01060b0307050a2a02090a05130b0a1b02030712050301050d03030509070e091f09050627010c05071e020913030c051b01170c1c090615 65
    0x414403170201400c0b001e0020074036051103080108109800b520300441d05c00104007103000c0309c080e030341c081b40748107182041c2d4102141400c881c015030041011004111514100c580091201d000c804014409003617180014035101c1c50342d2241c7d0500c0c03044280d406403c810380c0d00c040d549070302103c4d06842031031401d800003841034420400c40741618000f9180c4000c0140a941c182d0191101400c50310702c5000300440030035807840c1c1c5407210340325460f188001c29174070003004601c07418013070309000650707110341000c00841c040303440002c2031500000403604100a000b00340401500c00e600169400c02d19508040c9a500344c2503000c4003500d042d502030300114280350f4058038240200420000300a410031040b00002d10124800c100c81400f1034040c0c140003592800c9039070740324106144a03030050002003070250808895648681c210b040b98a20341888462030400c00c00c29035541c050340c69103510180120081c80714500c91074101c500095413010041c0404202001c1381e01203408940601e0060b024540c1c0c20400710380 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 825478462 1250 825477212 825477221
    0x2a020f030c0c0d03020307150b0109091a4501063e1509070803070b24060d05010608090d09030b040f0c0b030a11091c170c01020c0f01 59
    0x10307003030401001c019000805201c40d980c45003a0030313001e50005002c00c801087c44501c004400b40e4010b41c0000340d140051001420740786194004814580c0790020100c1042e441d16060000703104110761102014200e1644680032598170071002250f4001c174201010f002c1c00300200e41449410200266001d40e884a40032111030859008030140100307010076440c4031604442c202040074040d030242c1d24004a07500c07007040c90b04045410303482a10708208204680c2010510640001c0c00000c030180d4580704017502d50785513807440074020a00ca80d814140740b0b4074006c0c2010340e00045480c0070b042c0a45851501d401800100400d2149001060002001500340e450203e040c40109030b060704d03218100c500356141d00c6101400244101c0b40307498200b90306000f060003842442c0060000031450360303030781c90b0010f00d410641d03418005a010360b10090009509a03600c4803005c005002c0703128a80c2c1208221401c0040403001040c803218001000011040d007151410b4008041c0700761120111011503603540e22441c200c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 825479712 1250 825478462 825478477
    0xb040e040227061302041706060a08010c020d0e0d02040911100801060c0611040812180904030903060b01140d0c020111031006050d060b130305060f010e07050901032a020f03 76
    0x6100801c00240c06142c8100c0c013000c5184005401428940c6415000311806c01c00d5131540c4550380408100422440d0200045014080c1180240001c1d06280c5000e90b40304482c1603002c050042101e108170380d50704c421341e42c4074103541c00500503c8925503c1c1090b0850302c0d12905407a0141c004048a40011401000b40c0c074101c60007540ea4180b01c4440362184002082007840340e40108000b0400040c0151041100b407801c0c10105890b5680e4155058800203100303c0055640e00403a0380f50100301c0402e030045003001c01c8941140012034102c01200049079006281402441c00c2e10001c654400070303010690000d5a02c0d04907800801207000a1007a1a043d400112030f03005407590303d18810710150f4400d134046e018a03840e84e800881c03c192101c00070285074104408508052151750b03020414084200017103500310108100c01d01d40c175410074440a4550b00d009004109000d400100101c20b40d00c280d2005c2281f001d03a031b05c80c1c042e00101c096413180070313044007201000600c81c0d0b41291041c03080c04000c41d40744c07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 825480962 1250 825479712 825479779
    0x60a090614040c05010c020613031a010603060e01050f031c050c0f1203040201031805061e0703050603070905150d0c090507021603020d020f061809101a03100b040e0402 74
    0xf102c1c5413000444d0400d800304001c83c0c1144040c0031001d00c50421000c1400614862181c031094907400d05040e908502c1d059100e00100f500300b8104100c3c2d0320840341101c1c10341d041601c4940c0d09030340c0d050200745020115441c0c2841741c2c5009458050317280d40180a0040c212491303055a1600d0070340d80c105951100341d00000c100521041001c94010741c041d61044a182d66082c200401564161712480c0c00c04108940b401c001403400e0740c19908000849140c168407400e142000c11644c14800c0200350b44601c640540c60343e195072000400c6411820300740c8801d8031040104012a51941807038140e0b20800c5e20310540c0401e0b401c00740800d10b4a8008550248501803052000d01c13010301c2d40d02004245001c103030040c0d8120f48580c49207140307511006c00826040101d00203025400800f072040c031078110380c01410f40c812060704040c01d2180c40c0744460b41980380d024804250751241c554416540381781829511031a8201c2001070001f6458030020400d40c8514022584044054020000040813206281750b0012 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 825482212 1250 825480962 825480983
    0xc07141b06360904140c010c0b13081c060807050301111e04090e0105060a05010513260a050f060a0504020603040f03021e0120040b030c070503070203060a09061404 72
    0x4015105940403440c00030050100c056020a0b01c01180c075491041ea002c2e00d0301c00180b5507920a580c402c0001e0302c0e0f07985080c82d101c01442e00310340318490f001348054910131414412014042c107200501090710b109003569001888407170359403d2042d00400c414030038803004d40210b010006407071406210308000d02c12105100b91911103c042c505030810300807046040e01e01400d1001180061080c403910790011408800085d107030408030100815080c0c254403441c10080f00b004100261200e141e101c03000c07503030403500c070106040c01c3c0d00d141c5003103003071200240c8850720034212082c003842070000700c10001400050039610152241503d5070141c2d68100d401a401100402c0070400148424643d03020301d078002d01c1514440355040220203090f120007400f42c1d503140c0d161000500b0034031245220807403120000c50040c0c0303443c2c90440d44c1c54440c007004007128141d000c082081c0007444024000c841e44650b0040039504186040c010490050130022000d8486618106445070242d02030034840d40150f4220300d5021 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 825483462 1250 825482212 825482257
    0x50712050c030735100315051918080f1207020705010f110c191a0309101508150a06060f2f12030109140f0f0c07141b06 53
    0x10100c50003020442803d00340f02240b10b994018580c000c1c050901401405c1d1300d54140a5060340540c0d405a034501d01c1c1106100140f201c01d004103c80001284020810b01c2042d1a02e2100c102c424202070401140080d003800460104401482c1e0401d40c0504500981c45004080b60b482c01180555404615041c100075499805160b0094080861078103d686a50700032001c2400c060060186a513690700d001d505200781c4a0250440543c1744200860714118a08181c5c07032a0781c1c0072070002001100340d0344e290910b40340760044074000c050510101102c0100560541d0040128021606000440d2800d00b0100d0000c3c450318040804c510165210400c2c4110803c01c10001006d0b0700513880380704140c1c541c40d018180140400e4070120320007404691650b03d0300c204003041da402c20500c041e40b0702200040003602d01203115031541246a03c0d03c03a041c15a00c00b00d000c80f00d88240803015140e240403800c004025900090034111070380320740c80c607101021255020b01c0740c1c40c015004075100c80300407170170b41c80c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 825484712 1250 825483462 825483497
    0x70e0f040804081917181203070b0408071205190f0201020c12091903051002030601200105060307060908100e101e1811060c10050712050c0307 63
    0x140e04140603815841c50983d4540005203003104107015090050403241c41c0301c0c14400c1c00d403410362030b001000d111245085104d68444952049010398944954034944c07011200e03040800c107403007102c0d6010340380703640724141402e084d40150018441200c45100001d0821a01881035003038403110f0741c0c1c078000300703880c48030f001c5040d200c0d6684400b0200456509110304480f00e94104045141e41343c1c80021a42c1c0c48c090079003846034008012240c0700c0c007035040003420400507100040c000150741c0c00c03010058603919030400407070342c0d0f521a00c4000c014106807800000140810340c007107802010128203d42d02c1642d110300541b0030506074071600d4003580041c9044803241d591508418100100350302520158500303034400f181250f011403da1070800201c10100d601020040c464041c00c01d1110340c001c60014007580d40c81d241d2641c420b00300c500070100071a11000c009800c006a40d5080d12a520901c160302d4600c0e000ad01c0c4402407070304c0034202410070011915003440b040440780a19070b59503030428481045c24a8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 825485962 1250 825484712 825484741
    0x627140109020d110f130c0e10051608040b12010608090a020321040b0a05041a04050a0b1c060b1e070209010510020f0f030a1713030806031204030b100602070e 70
    0x3140e080844d89000c45c4d001d54a035201d802014200a8001904030130001d4003e010010084541c1e00a50f103680c2409411a0040300b950311441228000901c2040030b07280040c098041c69111000703a01005c144200c005611001d000d0580d0301655a1308400c1d41c40c003000036510009064082d405030808010150f00507140c1c61074050306138144407681e1510b561400001540c3d8070407540800003030408203050003031265664081c1002d05514180608240c1090001501081984034428100f003001075001405446442c00401040340e51608021072640d4440c22442d030f40c030584078030400c4484407070840c400f640a0029100b110b078000e06281080d81c00c040c140403819804043c14002d5102d11281301d90641820401d0300b2006042c1c101071501c0d41039061014080e222030390710b4151144052810481d501c6e486031001843c03290540381c2070a9031385810022a04051200150b100031040000c0c000c010f0060400b1164041c0b440301b031610701e940383e0b2224101e0700c0b0242406100d42d40c800c004003140040040150 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 825487212 1250 825485962 825485993
    0xb040507021b0f0321030a0b010c0b010b0306012703050717100c030e0d020d350402040e0a08040302120106180f0f060e100e090a06090627140109020d 66
    0x111000303002442a0620170780010000840c400c900001000b0f45e4000d1070060354502d12082c00c210f4800400b41c0c0d83c41d202c207107050280e520b1000000c000a0a168403c102c1d51001400d00340c0d80c00002250f00070044028800c50006980c07500c18080b001602d42049040c010303613004000051322809401020b44800b034103c1e5603040c01015110096045803400c00c0c0541d01001060307800400040d0010913001d4071540c04000c43d401007004011150050402601400c02c1613222000886056629840020000c09030201c1d806420310501740450108418000180141da0085407003100c0d50036510f41d10360a841080c003469042e2001c0340209a401c901607008211169190b96000c0b900c05e9002c80420300722181039010310040e00e42d070310074071145010401c0d2010103042481c07082689840c048400c241e503500c0344003004190b2965030b001c80e01800880c0c1c0c4504040811000f041c91510070101032a8442201d180d0240e0762200710290110440c04144102c0b450180d01412401e4841c100f500d48803d152191403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 825488462 1250 825487212 825487219
    0x3190c0203012418050708060d050723040b040908041215021810090620010f050c07020102070e09071703070b0c1801110c22050a0b040507021b0f 64
    0x20f0400d2260b50800150110500c0a41406461031410b0844443c4000840403200c01c603103000180604030b03070700c216125032003d41642c41c41315580861030070b07502d840b0095116810000f800001c0c5102078100e0102c061899808940a02100740c41000300000c9a412940081040c038003000b040082c080d8038005000303991b004501001e480c4903a0508001a0b07400020039582d00e00300d490350802940341500418400084a283c00322095041c81006071020f20311321500d00c944501c0145d107820b40082500200750596001030b0030700c4142041981e0b84c00d43d810400d412400340c0910034001c01c20005404500e44100ca0b858014168240b0340301e07080c24101c041d003420444071f0104000800200301141d03c0c04d4026400f15210aa940d081d824a02c61241081c05000d030401c090669a880c1c41640010340c159035913011034026040c5241422428041000341009146040c02d11041210720340c055031083c02c580609075000c0c00540d4420310202e807102c06043c3d40003402042c022100c07403641890700303c000d45a400038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 825489712 1250 825488462 825488471
    0x712201914100e01050103020a060e09010b031801020d0b030708061b070303020403240e0d0509040c0c050613061a060a0f0909110c0f03030402010c0f06090f03020d0e0303190c020301 80
    0xd18003a0b0a0342e1620303007106030310780d1030f080100214104511240d0042c00c080c5407801c0b02c1d0304903600080343e0250601c1021104c0e0b4000c0041800184d22603038020f00c01950000031503540b80b00060002c06091502003143c400c1c01400c80004003106c02042044c49502141140740203840c404121013082d0304549016410154280b201000044140701030040c0c00c001d485217410800c4c035080c0040166002048010442d40180300d008520701d8100041d200e07401c1e0121000310380100307140000ca841e542c4424002c1e01074812003080c800400940c40b1003020140c041c4006010965480350400c0c1d103404075400c01c640100081110000d0284112801e021003001854111b1007507a5401022081e00c0c0e1031419480c0804001442c440551410041c0b8040e910184010398110700d400e80002e05030340c40b8207101810600300c4518400422201b071340130120742c6038008004240c0b0a11420f0013076494003004015004a00013000192440c5000015121644004515001c50b1003c0090465124150590407600356484 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 825490962 1250 825489712 825489733
    0x7030c020c09010605272209020d080d0c0e18070c2001020c0307050109051509060f0901170103050606100e040627060e011203050712201914 62
    0x400d502d103402401940c2c4ca094403012100c1c0e802d082061100280c41204901c0140a003054844c8400c0c0110300700395a0700b070104190004000c002401c0e800390020741c0310f050703104020100810710000c1d100c1d01920305010000c80c4800c0030203564035101c10790001d0b440200501106408107030300e08243d910030240d18005120180e29a2051f0000e01c4007000441c6160020800080d5540e041190201200c800c034014095240360500280c104200b40c01030600441c403c4c280c0a60307602e01d10302180d0400e88085d2040d17035a030716440d90303009550300715100090005020f22404c0c42c4001c0a030022a060343c0d00503010709071a0320f40320200142045680d42101c148480080340146568940c8107103402800e13103040a0002e107420540c5d0402c3d00c18480c004144c40d074600882408100c0c14821300605499115141c40510b0322a800e041d87c0700d02440e44d0003020002c101412484d05a0f0050201552012411026403420506003034140c0325004654001c0240b0041c8a0082c0815051210b0120000d500815140566131 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 825492212 1250 825490962 825490969
    0x5041407090606110312180a1401060f090c020c06220e040302060705031005060d06050d0309080d030c0e0423090604050624101b261207030c020c 64
    0x455841401c865940303802c1000700e40d03000b4580311030f0341d07001d1809140780200030314050a010300054828280303210f5054000034030b44810850b9801d442c0d0411100d009074079411101a020301428061218401c09400d0001450865400b40c01c40f00b6039a07401802c0c2c444014018407100790080707517a071b400e00604455103641403490031001d040030304200b07011180d00b483c040c240a454954098000401c0280c10400c00200c03000103031503e020b442007241c0305562101c00d8100100a030a090f00142c0e481401c00031071008140d004000c0400b11110001508c0c015284400260225405101c0c070301c01140c007100b200815403070158800214460f15286880a0000c20001d0011192017211450101e0b80290700340428000b0070003003c1c0d40324a03150502c1032890b02400030300454416032290280140b0f4030030b103d511aa80905480080132402600750840d41c801410041507003180d141c5029850480840244200c030140406c6603024405011204055118100301b1002420200d84840441c002c8402c03010035a038 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 825493462 1250 825492212 825492223
    0x105031519080303040b130b1332100204140103020f0c070b0d1a0d08030a060810091718090c07150b120c10110f03070b040c06090305060406050414 65
    0x1800215283c0ca09460004c42504020380000c01809104403058001043c000140380c1c003101009001846000a2a042202b61100b80e854180e08115a04000810300855075a0b142c002c0752004450b14a407039510090202e11a07802509080d00c50010b4240095000b81c00900101c0e442e9a40d00c0d182074200002542443e0031508032185c0514005078100f100782d0b00307000d02103104540d6042d03440c0905111000615261040d500106202e1002c40040c8100a094ac0000005c2a1000c1a2900158480c40c0c51009200c07094044a8601411401e05604058075059515196800d040c030320400300d40340100b005200c00108003d4007400c3c200003000000350726003581d18035113066079000b0548522410403c641240031440303010305075003c503151800c5941d07404c1c3c5070103681005040c402070050503100e2080c209082e502000300244000500c14080080c2c0340503591207240128031226915468480840f084200c0d03110142c100e90050010802080c070652019800c58407509004da14071510400071401c15 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 825494712 1250 825493462 825493469
    0x60a1a0303072603090a030305060301150f150302030f13020a090f0506120d0c060f0b031906110f0a140909090f010e0c1f11031201050a12020105031519 67
    0x1c0003e1100d00e24403035052949502c5244400050509519010309100d035181d454040c05030170141c403080030480316102940041d94a105001d049070082e6181c44807804a000944151483c13813820f10040000c09110f44291380c0101c000310000c0e103443d2950750b080c0410600781e400a0380d01c00b914180000f24820b80b4030500702d03507065103034010841d894041c0030043e82d04012103a04070a0382024030801001544404d600000c1036100200181000100c0e030028003e10090501c560507105801900890764a01d401710f5807020701c100c10130700c01c10000b030005403c240034100d0901801d11062108040a80c040d103600f4410803c1070420360308003826440080c22140099903031082d117804c8101040301c00b14082c02410207801c0742c10700030110000d1a101003050084c0c0100403440c1011120ba0711020b00b4465240003800d6409403080b40c5c0c89046410130740700c10220a2041340d01c14101c01c03600080c94654010408003082d0141c560a047d542c9500400044128030b1050030b500c425036003030806d1144c060031001d0025 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 825495962 1250 825494712 825494723
    0x204080d03050103110f01021906180305090a0f0e0103032d03090c050a0f05040e0a0b0709150207060c030e0d0c170606060705073f020120060a1a030307 67
    0x215451800c05028845884a03041d0082d682d46546c140540d0b00000c9a0b6100c100a5102c108040d0b101d0500e140202003100322550034045140315402413603885005032070711560031030b941c0f0009640c603800e10801d010107100b400404901c8800400c04280640c1a0081c8002c91442c55102d054021188019244070340d200c0c1b0740480e585020400c2031001d941800303406442c082d505a40414100303456010a9030903440350398412501c40540580914081c00054036032a40081002c07568107007a036000c1d09988450083d07000d030561441e0076240031840022000c003100d500352600d542d1441942c404455580400c42c9064005400710030000c002941d5004507030091a1850719801c821154900090500e1400380a07148507000c18400c1d03102190020070b112048611900340d00101050380800600030b54900c0664421410480b900360380300040c240078040f407841c400d981d00a203603984550702e00c0c20f14004480540c5180d002070001101c02d0000e0b841003042e40c0e8510042c014003510800040e25540c000041200c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 825497212 1250 825495962 825495971
    0x3020c0a08220609090c090e0109050f07020601180c020a0212030a090e090d180315150527090a080301080d0305240105032203210b150a030204080d03 66
    0xd40c40c1030181d0b0110344a002500307101420f10b0490020b08681181c0151054035503580141c0e060203010751804401892030b0b04140c000b039039503004090020403044681d01d000d0744520000074002c600c04600305041c1d4002041780501d0fa88015000801820a036100c0000e501c142c8207002e0240e07581e1102800009800070040d1317500c4003d004014491140c03644030b11720b22441201849602d484c041740c6c980c00d050041c50320310300d00076007a001210407414551001d8407054250102d440c40918a0f0000b001c1e10480c5403071031600a0b036600130b0100c41c40c2085248403100c0c0521666090700092050459001040d80007261061a1070791144410781e4001e034021034035580016801e018070358243c01000d81c889510344208020300c06d6208071101101703071a0001c50400c040080020400d819000d0284902d0014068506400d01c4a2401601d400b50303191321940c0040d1540003200501c2510700031110540005840350006c0b1003500b8650b1203039000390300c24005040c2c0074080071451000070007180c40041c6241e6000304 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 825498462 1250 825497212 825497227
    0xf07020d0201060803070f030509130609061d040b040204021c0b04050705030115180306060b1314030307110411070f140105040b010b0a090302060309030403060f020301141003020c0a08 81
    0xa190038150080c2100307690411404102608010050300d2189820001035106a4060320341115171307110712070700594040280202d104400b0050780c4090255110f085042181b00e03214003494144200001000780032030342c120000350002e03c64000755134000c0d1000d0009030500f402d2103548014001030a018030341403a5554840001c0c4e150a000c2c046d00700565044c85451941807520031814840002100f1091104002c200e61121845540c81b0300155004001048120346980d031940082d8000346007520032503030076200442c901154070b0f114542aa402030056180c643e280e501c00f0501306a000d50fa1307078440e503244070700034510008100820304188203000402c00c610103450454901c1c030801107400701a80c5004108000240d1041d0b4203030645048018080d16003011101c121420b0342d080d00000d40082011060001020780000980140da220700400e100e01c1743c40030380d150202d000034400e8500c003100026005100703003007118a03031902c2c0c1f2072803401600d048244288507140242448007156811000104070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 825499712 1250 825498462 825498467
    0x3011403120a0e0d050f03070b040b07020c0a0603110906041502060f070903020925030c0f2307020612240402031e06040915090204110a0207060513030b0f07 69
    0x80200070aa01c4041d080411000005118140e0032411074001d007528103642080c85010442da11460302c8040407669101494030304140c0c0080c00341c1d401c494400c0c0100104203402d00102d001c031016440030340b201e46124940f000403405442c0090703a0380070070034080003c0559915141c0080c000f034000f503c800c4203280070091009240003401403025856007101001e000e0300725448100c90f001c40f50116401c4119407111002096540d01c492050b81b82c815849102c1c003522030309078200040c040c64584412614500e13040003130f1290170718800e0140050702152100c0c204205c030540030342040741c000f030700b1282041c054480c8600020016215121101501003544544007000d000305260010250303801c2d800d41c144402c80003100c0c1520b0880709201305640002440e41e8135141d00c0030106c5500240c42c04045011a4545401004251420380c003a504014000c18940070460840e85034404a500403c403a61501d075007200c4542102c1003070582c46210040000108803610425805014080c60b040114201454003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 825500962 1250 825499712 825499723
    0x4140a111e070314070b0c090a050301150501180f09150f090e0706030902060706050405010e0102070f12140a030c0302040f06030b0405150d0b04110910030b010608160f02070b03011403 81
    0x504001c0b01e1304000310340009524450940c0c21003103400c21162600903440c0041e03400b200075081690558a801c0000c0d68403606500d50b0802c0700c4007a03d5207140ca250705031669440c2102c0b402008803000c5640010880d01c040365200036034800009031000760b1641c40ea000c0345c02c20034142d800340c40f10640703402000315180da042c820311009007640d04007086000c0d140c0d4080303102e80c001d090000d004d031941d03040081d05004003074100c40600320048008658440251400d200030b0419480f0541303180342c08401600d201405440c80a041752050100e01782092803408003140a8100804240e0801d9024080001d00c0312803000b03050040c2043e5240400d441d905801400300701c03100104001120480e0540c0140c242c0c880c6001c8078402e5400590200c410383d550304255010101c508080ca4010310501d003041502414503940350280c900c038000880c01c0ea6070341c460031600c030402a68034030310259800714511242d0b40280000c1900005500640d08030f15910840080b00e41c009070302150704000711103001c0445140500c00f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 825502212 1250 825500962 825500987
    0x8040e09030412030806040f0f14220f0c031709091003020105030c1b0a05010b031c0e0120011a03070603020403050a02150d050103051b04140a111e0703 67
    0x11410b0a2030000074003c0759424440103414805502c02080003034842e0b40100d0b03c2c54000180a0200e0300703821040700c0051466229054410307201c80041030000b4000c540020b00d00080b84032440300c8400c59212a03103919640202190516182c60b4000001400d01d040b900c1614180322040c1d4481c400319080c4190301c81b0050101c071503c00c403a801440142c0c1c006081d690410070411038a521071583d80e49100c1026a41d064000703462087c40c400c002042815000600d207604141d09071052080c4100304064071195020b0504041509070070b09406a52041007040c1e14a030300140e401c1d102e40d41c0304140c54215200c0b5030000012503a030041c0d548190904001400c0202030704d1904615080c0386403901707504e403003039014020301c1a034541c044030a03490303d100181c80c01341e54004030404c101d503501e02c2c0c690707514a1138449030101400f0340494109680b0341441303180c0305003030b103000151650f588a00151000380691440c0002482042c48141c10400d00c40c0111742d1204050210540c0d101d100d03081c0500f4150851a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 825503462 1250 825502212 825502231
    0x203040816051c030f14040305300705070b0307140351030a02060d150504050f06040b0a091103040c0906060903030e1c0f12020f030909040c050d08040e 67
    0x20003c0c00003a800300c0800d00b040c0b0989020722000c1c3e0500a902150b1043d544040c0c0944100300b5440c121880d03205a00622a040707031a0b81d10b03081784043c010b103600d003d031080c00781580e0449582001100b10701002590310460628190400349a803000ca9071054000703170788142d88001040741c9500f100000c980c0c80c003107400c42080c0c411300034007804980359802144012014950900001036444540303040001420403940140740540b540c082481d41d00003004078056004070200082d50000d1503040620845000d900c0d00140c0b60129130b01d03d07040c0b20151030715500090708010034071f4000881c1c000718428102519001440540d50341450f0034400044617554003c0114186000c000700000341e0030605800c11241d15040010058400a0008031120400340f0351400005085800004006000300e407503400c0b5110707401c907895014092800300d0782d0384240c180000c810f5000b04a04200c07860006d12256203d032248a01c1c1e24440d480b0400b00d5a03848016008842904001c90305001d0901080002907201e001070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 825504712 1250 825503462 825503509
    0x9050c0405061003090f0b0103140705010912020d17130e06030127080f040605071e15090f0215071203091101050d0f110d06050105130b0a020304081605 67
    0x10001a55640f940000e2410f00da079900f10202003010610403c810300f500840e00c1e10840d80d481c1007003481000001c000030854000e800d4041000e6006107802c00980303501c54034200040a403030b0b0034803000c400c80000a96160a85c4d0009007140d0784400018610701c90244041c50300c4925080000c0108a40503021038407a0f410090f002e154100307150300303040c40c21021074008a401292400d10107218420715004030000a000034000c20059003200040804501ca1011301c3c0011071446000c2d403410120450082100c0903044407003e07464040c0e04207540c804e00410a08488071310941c0050400d01c00c0303003201e0501c0701001c41e0000601000c403040d001c00c0152410306000c112031564455240b414900003450520102261401c01c10313105d9484400c4000300d07440c0030840500030180c030f41e0311a04030032a100102c0b41030802c0440c065100d8000d880c0a0a15500303030f90b900314100b50440351250882a81002180300034070002456420401c84610b60210340703c0c2c40a010307401c000a10120620284060003090040d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 825505962 1250 825504712 825504721
    0xc10030209040b04050f040b2d0403140705100f0e01090b0f01080a030203090103020703050403050f0c03010501060315050f15040e010821190320030a0501090b0a150e0a0909050c0405 80
    0x1c295a0003a40304041d44c84d243da03045503060000921608810a80302060a013110003c420005132b80268000e0b02e0b820008820441c06103070324031402c9001801d0760005000a02461044d400080d140c21049e180032900c1e0035598840ca08540c0304103001c0e1920861401880340782010f80811601400c29100a04041d00091320065528480c016180f4109039002900d54189407054064401441d408415100042d507820381141d079480f084003503288254601000060880c0c000d215a6503100b003101c0307499402d00d1030300c001c10100b0000f0100b001c0d0420307401c140d01c0d200d4001d80e0f001000034244021040c1f006504040d80d241c40e01d0700304d056881424004c100f81010000401041c0c8041c561186040f610128141c0800c80151000c2003ca1b28810f511030a0404035000b0180590310442000d441089075aa0b205100410784010382d0151b03070040d02d030240c14050480c58043c040304510b01800d0071142904030201251140e0a19031010508990710302003a020401e051140c1048503004035410302c001d080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 825507212 1250 825505962 825505981
    0x90303140a0c02060c0a2f0607020c0a1a040b03010e0124050d0b03100c0e190302010f0f050f1605010b030610120c090c0807020609030304050a03110c10030209040b0405 74
    0x41c058400a0105808138014142034483c0b03001c000141c20403200047ca024142c1a5140340c81225401d0b0581400758100003034501d40300141410301c501340200001c404618001800c24040410a1300600f0004100300200341c1440b8140110300a00c0c441c16180e0b45503152064a2040f03100341802520808428100d180c1c105038402c060303845c42c07a101d803000500c1e0020395001a107030101d410788003040241040c2401d49802d03003003009952501c0c001c2e41c509500401d0030240000204107408003d0200d0912003e000d0042d100d0400d080d800040c03410800c0c50b00d8400c1c00c0c8444a60854801a4040d0000d0703584041044400e014440e180c0800344d004007242d04020380b400d0480f11860140403d1502074404050a00605102d807100516800100300725901c43c002c4001e21501c002c4079400054450070011450b00b04001080300e108036004006071440c101a070383d0407100d4000e400c100d100d05200710501400c0541d140ca001d0301d8050582e4030016a0344c0070384801d0006407158400a58411890401001240320 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 825508462 1250 825507212 825507223
    0x1722080102040f0515090a090213120b16020a052d03031506091302120103140f1b0a0509130b0106050414190e1009060b21060112090303140a0c02 64
    0x6204882c5008554a4814400c1507409102555544000315520000c0e124003240c9c01403e07000300800c40d80440e01c0c1c550034207026543c03000c107004005c003c0072000604643c55250302d569210f00c107841921000321040c0c8801e03142400050801410f911034418000286640e6448401c10f0340c07256020b54118540626a4860201021451401440c001580d20707110340d80c3c0680b0302c0541e00d03100821074840c1120300b550703101c80c4002d0100300c0e41184001004a1503103400507001840d0a0010005c003c0102c0c8641c400340440d06040450b03400c0019507c011901d0307511040f0962040040304d12403200c2c4030050034078078080e64040e44040e0900800308014001c400c24500c04c81c482d10300c1990007018500340400441e080c0f2040d035001302105e4428106100c1d2504014500c1c00131214549418061507441d4160b803440e51007100c10054140d03000d00c640c1d500701810350b03952542c442030505100c49a60400c031b512409584400380c080703002950318040302c141d0f1142c1807075813900249140000c00500303002500195961 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 825509712 1250 825508462 825508469
    0x307080d1401121106040807300b01060c0c03060f09050d180b0310080109080a08062b0204090510150e0f0f0903040302041b080a110301121722080102040f 68
    0x84c00182c0c03d0303498040031a4000d28002c011100e100340d642c030b0100400e56407041423284a5184044a00c11090440d420301c407403036000140346403e40d1030010706450304c10601e201241c52081d42d490010200d00340e44294458507241c031030045400c0150b440c0c414200403140242c1002e06c01c076180a02e8544a980030307007034103a0305080f00582c0e83c1d4660410036240250f41e0781c06180b5940c00c003020001002460700140c00d45c9031080c1c4650045854003010032142c010300740551645101c5a45400c81208409000900614005440040c144cbc580740c03991410407050442c860103a07074a59a02c6e0504003140e9195100800b03a15081d03400d1810070214040465402620b04000da52445000c07810751481801200c0046500400801010042c00301000c10500103a000c440801d080000080c140400c0c0d01841e407010f9100e18207646103a0820700b000c1c000070749001c0b090710242c40c403202800e4150344180c028042c17040c0070010070f90b02d0080c00c0500306604007160031190309070b40180000c00c141061010190f068 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 825510962 1250 825509712 825509723
    0x60506121f0609050903040302010f030c050d0218101805040e030f0901110304030b04030f0c051536060601050c100506011e030e0f010b130b0a05030307080d140112 72
    0x404160401d0040600907a03000b01c60700501d800706000f5800310000040007180d100f03884480c200c5610000c294221a03550400002007175080000c0c0076625010f83c001d0003c200000c03c0c4411004c4020040b80814140c0042207020803005c07607403084550350704280301c402808111428001064020002c0b6207a008043c10b6188085000c102c480183c1c0c040c2200309812030400080b030340c49655909069961420603034081c0c01042c0da12900013100342c800c3c44401c00e00f9070007100500c8405081061040501001046060307161242e281c490422500103000712413840700b120701050582119102d01c1d00309000a011207050103400c21041c51102030110303201c00b03c040744000014060b500c02d00113075038841c0d11006481000a0400020401a815901c158440c0801e070046550b09900090b01c5800c88009400b8030394004006880e030710b8810303502d03007000303241c001d002c1d240318074907591b8a000c00e28507007000c1c004030f484560206820141c1c0c9498800e0301c0381e00001e802c1a4900c1c1d40743c03064001041c0d4410001400c4c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 825512212 1250 825510962 825511003
    0xf0f0f120501060515092d0d0303110c0c1201050f0f0703060b070302030d1d031b0106090921080103170a270810020f0306090711030d0906050612 64
    0x6116080d4443c1c0001e01020b400b1301042e11a0390420704560740200c400e1031103003000700503602207030010380310000d4510400303010031102070b20b0300301000b44601215008600f01030300c0780140320440c10080040c01c0b8504c282030051040c50b1040c82000810810303401900d80307a070b1500d1704001160032004442c039000404155003800c42d44800c80d04a000e040d8a0708510858400040c200d0304147e40003005040014482d40100724445420007890814482031180300c105500610881d00901c40407045000350660b05e00c00091079550352400c0c04161414004252852810034074200e405044020100f00c0c1d204941c6445a030940c11940c81c1070100700c41200201203800082072405c0500e0140000e869411480c0c0e210410040750003484402e2103400d4000d07030b045405084030b481c0702d404460081d1840613121801c0303203003140d80714003d200c0e6010b00105000100b01c9243c5052004000c01d20042c0094208808041483e2a460908a0560741c024001c0c4d406800402c11683c1c011002184030461403001c205c0111 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 825513462 1250 825512212 825512249
    0x301060c03050706090807050105160806040b01170103140609010b15070f020a03080d181203051b13050a06021b0405060607062901050a0207060e041b090f0f0f 70
    0xb2128003c3c0c620090006180a0980061084000c0a018150700c98030080c0701c1d6035144120f01c40d62074100c41300d01300031500e124003044180c50940c0180c10090010300d442030001100800302544030400780e10507961219000c8031a01d04090500041c3e40c0440408024801000814082a07001c0644003410a140c0350100700e020800c41081c40c6a0700d1540c00501392902c00d500c90801c501aa4040800034050302e103401103255960990421014a6581100c90780c260f01c9400e000c01d401030003000705881027010003800c4c1a140b0000d0140500510a4200c1c0c481400d24203210034008090300c142c0008003503600c44141d144404018150119600c0c0c42594046010b03103a00010400038000e8100042c825800c003030361a43c800e0198810001c101007903802107031030040700400540d040e1240405407801070708049003c0c0055030103034030007249595000d40000f42054a5400301580b1800038168000000d20000082000391072001011000c1c04602403ca49030307a24219030710250242c0c9201380b000307440380c03600000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 825514712 1250 825513462 825513467
    0x60405150301091202070f140f01051209100b0f0d17091002010f0609050907210812060f0109081e03090402030403051b071202121615020709050c0301060c03 69
    0xc500e0000058001c0c030402c440c510f8001141160b0040713800040c0305050000034241e41d1443c1490407923040c24241d014408810017880a0500540d41160601c5410020720040e03501c1364461510601448001c1e10b44442200314420650f000341c1035240c480c0880d40141c0809a4500203000d40c60307036108000b1042011044981e9a0310b01501004c03e80c04141d000041290640640007000208900300080103119241c0b007103203007143c00564505455502c030440a1045403000c1403502100c00ca00014160281d659590356501780d030100c01490800800032062240f2814055a02002d20500b400e0143c000c2d4105060701c0d81d2030f080760850350146da0220b40e02e22940c8609104480c003080002e00700755560b18141c00c0243c403541c1f1100d660b4038221000c007000c0040754008600b41d400d45c2c0a201c1102c10b903a4240d001c00a0513600c0170315045660042800500d90820b0101c200b400604020440341d44c07046402c880681000d01584c0031890b814241001c1002d403561030310032039041d82c0b01410190404021070508 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 825515962 1250 825514712 825514741
    0xb0c07060e030c010606120c1407150513050105060d030509190306020708030118020711010302030c12040b15040506150705070e0f04172b021c020315090c03060405 72
    0x2101d040c0030025041604081c190014010b40c0c0203034464040c042031405056040f51120203408001448d600d0f88909d280b40100001c19003039000310303104140c50f1491151202110002d44880c229501d02c2d0f008942084400c1c00f03015401442182c20007136640080c1c50240c158802c5410f40c1e8422207420b60241280000ca5512078059a04102c046403124800d107002e2009030310a01034083c008244a03040014045540221400d090340a400342c186003008070b00540113500043c04030b00844070b050100101c45092407815030b04c9030f4040c9404501d58148011080210b15400c3c65407030040b03040c9402c0007460b458040140c0708032421004800d96581c041d040150528034250880e4003030440030010300406000d40519075002e20b0092192203100704c4a080c0b2030300140304190102c4420407072580014680a4460f1758800705a000d4a005841c0600c80c141d031070000203000b07890480d11940807060181e0500070044401d0685020f442080f041d0821182e001c249010041005100e207445000180b00e07000032116 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 825517212 1250 825515962 825515981
    0x30c0706020d02040e06032b090314010f051311120a05060f0121112e12050903040605070b0603010f0603030c2f061803060106090305100203040b0c0706 67
    0x1c42d1288504900800654001c0c85203988490030340000c50440e1034080761022014006c0c000a49a80c20a5803030350724401070701c10844090140d00385000010411141518254040d050b00010b81509402c494108691014011450440b07840030150006410102c184884440171281c40d103000341c902c92039170f00d0005a000003d00501904007440340007041940024161101e81c0b0074008060700d10b9400c9004040d4110010b8440e103800303d42d4212604141d00c0f02c4d041c0000031040000100081c440600a0380c0c0140c890500003000d0307540d90989000d0600c01d4640102401003c1c1d89840d20700b05000b0a1405000c101800504a450110700541d40940c0607680d0780804100c180100f030303501d0802800100c60003030b050b01c040d82001c483c08079509104006504844c15240c1c0100702016141c14011584c005d00c3c02d07041d18148100380c0305090360f800c11415000f400190f039a40c4240d07085203001800e260900d440c0d106054010310911000413400d14030340390301c05003400e400c58450b4000d04180b0043c0640d10b4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 825518462 1250 825517212 825517223
    0x1303060b0d140f0c0405040305070209101e08010e0a0b01030b0c0408070303030608011b02070b07080c031218030f0f2503051b0a051914030f0406090b09010c08030c07 73
    0x4110388072103040843c2c80184102c10006071440101841c0038481a14000c0310000c0006800300000c0b0014508107900503006180c508000100c543c841c0035181c400114050030011201c0c1624040100010034002c90074911405400b41803140c0340c5a44c0d03030000d0070060000401000c12800010a807070355200a4500409201e41201d40003641e03406d01900030201070003120041d508014141000d0502540009031440040c1d00400c44c042c40c0005100040e00710790340c12202e802c4204040030b10500d041028103000464402c1c2076425052504d101e14242906411855a0303400a200d00ca4180c8102d105860601c0800c0078900c4c1c4e01c0c0c0881c8000800401c140500400e011a41003a02d070915520001900940d00e107055103900c00200609203e035144d220f8040180300358800720090b1075401451400c0d407000e5229200801c81c07541201c402a0031900041c521603218070000c6010040554040512801403c0c42100c0600c0c2a481400081c02407a00c0c0f20058141e000000c041100c9580c0181200c030441d4201 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 825519712 1250 825518462 825518483
    0x2f0c210d050c0d020d0615030509070608071101061e060908030415030e010507120f0b1f0e030a0b0406110a0519110a0c080d030c1706030c0904050d03060b1303060b0d 73
    0x17500300040480c0c2c0500e100046251803101c1c0c01c58028070030f81e4010009440105015840c0540880b90180010f00040c1007044107290f40b214103409000d14000740c00c49112460016100307040940c1252503580c003800800c007080e40100000a0040100d030305032607940030350a54031507880c2e009078040e101c05424081250310f00001c01600030744c030011880032445090010f0002801803582c16084da0100e20310f0320351000e0314040181d41c041600c500d80303441d0059410070f00e034819071800002c2c0c106284030b10203490f1200078070100070821a092042012009540c0c05c10741c00c100f2600c500408500411800c8610656128020000d41c2d01800c1802040039540c030848000c83d0b001c0c80c0180404e40a8403600c01d480c46042c00040005009000d1000310422590f034458841c41040b81080c0000d00c080c1c10309030503028900f0180010345821119502c218001c0d0003c140c0ba503030f9031000404960950b800300c07116450071b1000b00c0002104ca1800e10859800520214102c0891400203004a107011001043e031505c2307 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 825520962 1250 825519712 825519727
    0xa140105090d23030405100c11030105010806090f070303080c1e0409090302070b070302150408070c09020702010806010e0f06180604060f080c070b0103062f0c210d050c0d02 76
    0x1116030f014070b8811540d038000d408075070040314940d070f80941d021301035011741142205040c440c801c0107803c000ca4010380c1c0003483d882144000c00c0c211102a007290f40345410040c200081c4070001c00444c0741d0359842d94000c0104902e035440060004001504091a0074030010f000018942842500300c0240502a05541e1700d03640d82800100070030404404a000d17000d5100006407a405400c207880096416802074000c0150207004011514402002110301000a001c00c0d000b00d058010b009000c0c0c203560703000503500e100c640005413400c20010041410007016038510389030394031a0441603d051900b603a0710380e100c1e00c03000c11a2603090680c20019800000c08100002c9040d440305440d001030703105032601314040e11241c00154040c8a66440038113082c20f241c0040000400592100c142000c80000c2002c03403002404220304c5056104d480104206004100540c85d144180001000f003965096017040c1000d09801d00d002d140102d40200244613a1761001540c0020344004540040001400c00c5695516 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 825522212 1250 825520962 825520973
    0x9070c052e09122d080403030e0d0f0305090a060e060106091707120201030b03010f0f06090b2209140a0b150102100e012717090a140105090d 62
    0x310046010a960080000c0c1c09042858030420300c007a5006810f8010141d864042a035809000c9003000e00300c1588448504001a1a40d003040000c80e0301d50b403a28981c0c1028280201900c54400c024103540d0030a000341d007845a00483d40c41841869401c01107090f81c3c4940b505030404900c000040e048504190320100d1100d0301148013411703550144c0700d404503543c40e148110260003940c3c10011596201ca40240203d001c10440d00145620526001c1070629510f00801d00f503510300718080031685d0700d4200301a8801c80c0c0c4d0140e01c001d404c18040800480b044035000034200c0e031404000d8124400c01c80e5100d140001150002d500c8036410001c80c403055440810b4059440700c143e1026034080d58900b000c00c0401d0000c00200340000e005a004049031442e21020600421041c1442203c5658810300c054100320011070f50441d07240b09403900511486903003416500780c07800019000c0845001c00900c2e802d6030303500318010150343d411495080040004030058449104805032140e2203c0d00e680034004100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 825523462 1250 825522212 825522253
    0x9080304060801080f0609070e091f45050c0406060807020d0212120915070203071b05010516031103030a0b0f0d02030706030e10020c03040509070c02060909070c05 72
    0x5080f0000c49405e620444291902d49005031040186904951002c00018002000958000c1c403481c0c2503921820101c05600c03400c91101c44017860158030390381c0f9007051040d2030300c80c400c2c0c11a00990045030480c03510b00010540081682e1070710051036080720b1000f440b00030811040c0010010b00100f00f9a920f402c03024161400444803000140f241e0380c10315240314030103e103104c04441a07840c101c0c00d15811049242c000000240500c1c864400c0c2820141651858182e29004a900f50042c0d9a40c40c1c0c2c508055403200d02c0101090000178036180300304410399002c01102c07643d001c0755900e0300b0903010f1490b003290420b6450f00d1103205440080140040b0001d140e10503502e452040f650b44005109010034000a48040900650315230021581003010601070b81010070003191231400c0d2082841c0c03c83c4880101c0c0c01003088041590701c046400d0207642002119242c0080660070a81f00c0e84a851b400100316201d81c11071030780180c800c000858425406929840c604035485401c0c0d40c0b20113068240201c40c403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 825524712 1250 825523462 825523469
    0xb13050f061504063519020901020a080c0c030109030e0109080303090606101803150506030a020f19120506040b240103111c0f0f09020d11030a08031501030c03020a08061009080304060801 82
    0xb185440e8041b040c007214801c0761044034042c0c02070000c856443d25182002e030015513860807640660301007003030725a40c00c1c49005546840390312480745198607000014a0400c058106070707400ea0040050140c944000582160721144c0ec654529401420030b108460407203e54a0184410b100729a020003005514195905c030791040040403c10750b6580c00400d0f07510b10302e034070029400012003544ae0200d824400741c0c2d040000391000000300d000da5034245010b031554201c01c1c213a6a5802010a0004008188070015040704400d2400385648001d0f86640c02d01003240103815051590f14049004204500da054842c6144048103103c122200c1d040c1c21405003220300c050340d9400c0e103810b8404288102c24804d4500198000e008284049550303501c0c2c801d038013000c40104d585486102c040708002601000190312806204c0100901d82d15440009400d0f61036901451003030600611a40c40c40c0c907807251840d07601c84402c03075180604040449090b10340c019141c02c01003035800300290105400703030440702c0c0328101d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 825525962 1250 825524712 825524731
    0xe09010c03050f07030902030313090b13202109030d050901020310091a04110a03050709181503020604121b05060a120b13050f0615040635 61
    0x211246000407021500220307a200c0c8410710705401308a55902c00da1100d00d0031440034045916005054010030100c4019a02151690751111070204203401d00181c01c41000880040a21450203d841c000fa900b80050f003660300390020118480400c0038402040703202c086914411310f1024105200d5040c1c41c0d92150410342c01e21402c120105100540500c200ca22810b20741c50105034850418102c41e000c0e000051001c06400d0005881c03602035030703031445594044405482c07401d9030350880c2c500c0941034600081a490500107440170400003001c3c17103200c0046488a40200140260506000241d208542d8102030341104010074007080491070b4014141a060240440040d244180c84405c0c00610f0b29020780c81d0041c9082c04079420050040c00d150940308071194001c20300746441c001003040c40c010500301e0011a900e800520054141c183c44090300100d00b5100b8204850b207640031060705200e01d02c50301080004528240c0c0501540d8505c0700c1044451203c092503550342446407075003840c000e03100301c0703034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 825527212 1250 825525962 825525971
    0x140a0218100504092a150e04020705011533080702150f011a0f0f03090709110a03060e04030e0f0a0b120609060d0c030b060406170f2505060307050708040e0901 70
    0x103480034088441c40886c1c01075640311585c0014200126182d100e02603c40d07030425021302100d0b0010f5800e009407114109074141c000001f915200c2400319456052080030710390018220040d030107459103804000120258240502c05880d0120101e00d0200e04e0600c3c1b0300140c0e01c2d201823007004680300078000e04840c900015402d00b038524117409142840346180c0b41b0047d620070000c2c105646400d40103558069000c0c42901c01d241e90b40e940c48001c0d104c090110f001580d81c00140810f10580521400c40038249420242c1a1803606a8001c1c1c911050320240611a22182e0440403103550b07001003104c040e0072101a41501e0328286000c0a02c20300d42900d00d6441503141d04006151400c2c0313a0100400c2d1500241c480040501c1c2d40c07a50703005440090710558200e40c0383d00012892807881d1103800b2024100400a10021800400d503500381007141c2e080c2c2c00a18000742080c5010461190401e080e6038085400d00c1e5241c4800e982582d1030701c28600001d0a00e000070400161186000082600c1006510300a10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 825528462 1250 825527212 825527273
    0x50d050109020f10120c1704080a09090513020d110d080304020f12100c020c060a020c0108010e130209150a1203020708031e1b010f0207140a021810050409 68
    0x140e4680d040c00c1c1d00000a0f0140c0341d164018105c0d03003022841d407079942020320746035a0f00e0400c0900114101d07001d03143d0b8400058680100b5030701901000041000e42c1081195050a90a0140c42c110000c0042e2180c1c41000c0c2c45400d10054561901c81300c540185848600385452410340c003540c0044505a20507040401100d1039802c0c082d881d200e0302e00740341c0041d00500e0f029403001001801fa0301502e00440c0702d58400c2042030f4803480002d11102c2550f130002d09403503409000043c0b965005800c0740d13400c000d210317051020002c41000030000b0303e035040701c82c030700d099903014400808910840a00d5911000140c000a81025640d074959400390080e07083d04c0c01180c96040460350b074030881114072030003000001c04c805045540c102406c030800b05c24400442070f036042000e040c2540c041c440b84025050740081c00320100034200d001c001c8901010b1018002d203182036000109880300e01100c1045582c486400280039110035020386000c1c05004104100d004031038141050414400402c850600d1340024440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 825529712 1250 825528462 825528469
    0x30609110306010618050f060912240114010c03022e09060b0a1401020c01110a0c08032d0a03050c0d0903020309040c020a17160b131a09030301060c0c050d050109020f 73
    0x2440c01d06000352801c9c1c41d0841020a10540300c00070300c10031900740558104140c01c25010840d0600e11240b20001c10602d50401e210400035416030400f40b41800105105d0300e0000350041169601c0382c114014081c503404c0e110318070310041030003110341140c0503240c401440c0401c517055001c1104020260b64140c8490703214101840303680c0070140070340d000d680f00300c4404c0ba956200d207951f00ea14840322802d40360700410039544c2006404103500401d00640010496464410020030300c5080074a800d801d059040065850f448018459100980105a10703071001610039601c80040350b108141e540002c10090b51a03050094990b080b602e4030a10850401000e40801c0d4800681000c0c040d4014118180c6000084424001e650221404540401391b031110301010076810100140704a02c141240d07011110a4507081d0041c00311211450f14084140091060320180002681c1c190740c15801c3c140f1307000b0340c0c40c288100a03408d04e40c451580050103d1111003080010b4014031603030b1b403082e14103110301803004040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 825530962 1250 825529712 825529729
    0x2031c06060e060a1209080f03040506071e0503010b090a031506081603110f03011d070e0a09050601090f0b0d1b0f060e011d09010b0712051303060911030601061805 72
    0x144c4c000617580c013041c20508003066000081a51003003c007145072250204000070141c0003101c0645e21038121008210111f50082c00ca210765903828007a50001000c0d190016140d8017040c026001001c0e0b000c43d4542d00307500c3c1c4100240186812200380c08001048c0480071007d0042801001100e015111109020315a0252002d00381c1c0d034800c8000c0d078038006c03000c1070291141070928107503032564840c076210f0051220400032086410326100a0315a0f281031074403042c403010003c1c1002842d42d14050b20400443c0340400c0b400d041d11056400814401c03c2c804208024081e4a0301480e405694400700c802080090f907240f41c00200c01c011040e00b01c40d51183d500074056514401c4e080890050080b05800c3c0d841030225110f24643c8a0f10f080d00049160049840c4032004d8200c0540c088000501101b441803941080c0c4100c511850200d00c0c00c1c0503117000342d00e041c100340300007400e26072501080c07030810094050761449004060115140303036a50307400c000e040b0f101100d1a520383e50f04120000c903460800f07865 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 825532212 1250 825530962 825530977
    0xf061003030e091012030c02060d0608010e0604050c01140d020d0b040e0f121c06060c0221070312051902010b040e0304150e060403050f010c110109030210050702031c06060e06 77
    0x400c0e0b40c0080ca0404802015109400111b04000c2c40ca1801d4005030380d2a8013510302c668007050002822404c1424142c2112a4080e80b064a0352210f010000080e0000a16154910081c41e05142c0543e40c0c81d032070095802140384080c00580007040520310100160300507000700c0d404a0701488608541c01c41c0c0d58462401c0d00400f05035420100b0061311b02e82e501130041410b01c1000101151050031558503504403038144c0c00050001394404215415894480300c0303a5040100e6050058007501e48090b003c1d80c403085840000c3c9409000948255024001c00586007660b04a412801e800060960000e000b41424240d080c86503103030549404100c000041654180d8a10719800a034160104c03000b601c030850b1b1600c50310b07407101c0e0410000c000584240f2a2800c0c03610341c20004030381050807074800307401c0c4401d90f001881580c0c54482401d000c644e00080580c2e0090302032000040e90745403c4000c07801e5100c0c0e400201460659500c0b422032005455120b401100c800f60340b400f0100f11030000304010741c45a000c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 825533462 1250 825532212 825532231
    0x60f0105121f080307080a02070e01080727091a090d051e09130c080a0902090a0905030c150f0c0c0d440702010605030a0605090f061003030e09 63
    0x9000810b901e03003410a0802070281402140303820755a5400d40c40c41c40e800210308880d2a240854049a031540411501c0060702440301129119814580c2c401e42e18003051107000c0000901504070240013642605403202000e01708000e0004e0f2429003041c0d04030900080803015085030742c10010b4103e010101700b401d8403078110307030b6650728086840a41480c40700440089249810302003143d007031a41e40d600031903c00d11401c0e0b1400300d00e040301e104000d00741c2e00c8020310a02c085418111000f00503902c100c0c055030b0200010000103000c1140e401c0992450180d84a4000a0302ca20441d2405001040e00e465100d60030380c41c00181140d0725501c18079050b005d401c00803d840d6004031104000c00f4001c580400e4443c3c2e41c01610a08800240b0044400c40100142020101300414030091941484882c607070340300585000a0045500d0100426994191403401406140d691408190040003d204080006c00c8940031126107041c94114070604048a120407404610080b41d10880c504080014904ca440c108 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 825534712 1250 825533462 825533497
    0x50303060a061d011107080d020f0c06093304060e03060a0b0d120c0c270b0901050402091314191503290a02040602010f0204030f020f0a0e0906060f0105 67
    0x300151a02041062001d00d83c1c0200c11b00842c0f110001c1194003200b4043da80248400260000b03014205903000c0205030103040d0403c01c010309912440c51007030102d8004550102c0d010350301768400c03002c0141c03034151300504074000400003090b070362200c00343c3c4a1030000c405686040d12005200000c9905085070fa5421034000c40c400400b0441d0144000d848020901b040307104840e0701c0d0345500080c00740c0d40042c1034001d941e1000c426280b100c9080c291000c0862441005030a64100c002040701005100c0c0e80c0c440d68000411440381e03202c440038000342800300311060200703098081800e24611030441d14181d0303000300c1d100c04030b20f5020640144074942031428501c0b0f01076415a1107505250205060540c00c00d10441c4505100049244800348122413584005032901c0c20a6002070a48004030341002010b4014401440410380b114501088158111141c5550b50314040210302041900d81c4107102101907601003200c000e901103441c6108070400c440c00c16031415a000152014090180940c41c9403010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 825535962 1250 825534712 825534767
    0xb01031505040e0312130c05010201140c0a020c090a0504170304031b0c0e04110a091a120c031603121b02010e011e110c1c1e0807050303060a06 63
    0x2a030b03c451140420b520139680303821040c1001440c0118280c2d202e00c01916000340740390501071034071149009020244005d00c003080c04600f20400f90396024124510340000002c0d544040c600070000c5100300500901103182e0703442d29070740b5174008000446080c4c074200640c1c00a421031410101c1128412903140e25a4012184442d8480f40307002c0705120100c8482c40d00600c00301e005050641928030517449442150b000000b141c042c4051f0b100c0b26400072081501b816442c000d90031108410f00c4440d4403d450880179101804a55480e14681c0c82445801d8000c140702c0c500418041003205083d40d0240110069024040c10708459001c0b007a00c1d044454200716080c48010341c81443c85001c038a0051400c20720100d80a0148042e0000ba5882807001c62050140080700a03800e02c00603400e50411109405000306104201d0401e21042a00401c21080c1c01580c07058450403100c84107410b42c10401d219140c13000d034035105980ba401515064452001040700061710b83c429090028441104d070a2810724040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 825537212 1250 825535962 825535969
    0x105160c0312060b0415031b02151324061208160c0b0c0c01120506062b060306021b01090c1a0910030221010506191b0b0a0b01031505 59
    0x1a401d41c440641e0b5103600700042c11004c0351300540081c000c0b094541e0440d1840c4100541114000940c880e00725940510945640717401045403c601800c0c0c840c189031941c0c071785c12980d100520b250303402890320420107600241c10712040d00340348141800181c1000383c0c40d03d0781c8683c5504140f25000404441040102c0109034403944000758070281f05282c0c1c02d00310f83e00c40a40341c0703580d000304048042690054850412541e0b00c462240c8141a0203682040141000740110f8198840c440310b1101401d400c1c01c2d0100711800c1c428160794007002000040003515160f20301100079502c8296449144008800751007000350040c0b243d04840c071f070b10248103a2030b185000905e90704910341501d82c0c11041c10500100b810340d02c5840950909800076640182d840d00780804134072000311441b030381482d01c01c107100052095403695411110340015080785e0140d42c0c0ea4645044511428a141d5641400800d42d003000030454900340c468010f000c8070000340300c0c2e016410f0044084424070451521022041d1404000604 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 825538462 1250 825537212 825537227
    0x501031b0b2b1a0103060f030503070605060303071709090a14010501031503020910090606090b0703200a0302010914010b010c200a14031009080d27050106080105160c03 74
    0x2202d4115840100424007540465404108414804072501c00c80c5000b90303410710803000030b003140350384c2c40b00401c0c15a22215501e00a40c64001c0504c0c2e0303502e001c101c00d65000c2003a140d52560103030a071045004010880ca01c42e800c0800c4040c000c015900105101c5c0200d8043c42104801e0204415616032038a0011409414010140004500480c03400f00c050388864100903c21600711403414111850304508408a0380140e200e1000c00c1411902401658075010071140e040380c051400121000c05100c40c021f1060380c0207100210f1b4480c0320707030003020950103401200915000c1c0d2403440c8107540101c421403d031000140c1700c500144d403c50398000010407040d01c01d00318501d20100512024010700c041120086c0e0350300000681d8501c505c5048561404000200e01d000d030b030030410311903200301790b0303c0c1c00d6280140755000d070f1410b44454549686071141d800451380312402c0781700180031400a040c914003c0442c0e00442070761b542400300244130801646c0b0b014100e200c0c1c1d0781e2603040f03451581d1800c030f8842 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 825539568 1106 825538462 825538507
    0x21b24040503070b060a050405040f0204050604060f0e090717150603010209060f090d0b1608010b031303140903011b030c0e0f011110020703030501031b0b 68
    0x640c04403d80f101140c0c4008149416102c00703000031800140d581200e80c026140800300020320070183c0d020740c9803a000341c8040029403100000d00c0143c2d1501d000b04041c2540082c400c01c03004840d10b04640d03000031088291000e098862400d03003c400407020f00d80042d5807048850a00450b464902c0c0e0390070290450007141b411a0002c0484d405001d20150f043d110170380400c0d415800d803103841101c00c02542c055020002031814211160fa41e007940b441960000741004008122040c889044034081c584c802c0109003031f00c1c0c49550450711402d21b058060302c00e19052054956685003402400b011041c900c10090070000b00311801030131255003520361020844a40009005500e80103880000300c0028640069042c00c844a440d240405410b00305501603c005041410b26038564082030681e8850030a07900d490707036241c0e00c600041d00940180c04c03043c1410060010149050507001215 = true := by decide +kernel

theorem cover : BRFrame.Cov 825359712 825539568 := by
  have h0 := BRFrame.cov_init 825359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 825359712 ≤ n) (h2 : n < 825539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
