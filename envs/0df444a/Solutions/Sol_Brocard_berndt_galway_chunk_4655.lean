-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4655
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:18:52.953741+00:00
-- url     : https://prove2.me/submissions/5719eb80-f816-4e00-8b64-d78229eda4eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 837050359 ≤ n < 837230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 837051609 1250 837050359 837050381
    0x1b01091206150b21070804171b06060f0a08100231090f0902102f0601060908060c160c0b0706240e010509061804080310060f0c230709 59
    0x11025144208030555221030120b501c0b1002501c406c1c0010b000840d14800e0b040102c840582150130b1a03280e80700f140143c0d01c0b80304074002a6004a003041480c0c034102e1264131100320b0698402003158100340d0b00b182c8405c522072102c00e090348c001910314407202443c240c01c0f550380d5485115071070003502d982d6000600c1125116a01d8080d042c2100c0c0142513030355100d580c502a50040401c3c02d840c0500300c040d200c04d2990b620a8100400e143d2462041000c1008100711280d2000082c200e00c0d8101000a009a4055001030000358002c1003003084480844003116034051f841141c00000f00000c1c43c240340b84410f0b80d002840c04440220b5028100441074101c41c00003075210540d80549031480e180007284004a01c00e0412403448080100300c41c0c00c0c2003a445400c0400505104003c00100000005c2c9501c00e40d001c603210035000042002d800c20802180000e80b6152420142070b2038440700045c603032003034850050315910000e80d4940c0c038108084654400403c0030016940c420360b54018510080603801c401d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 837052859 1250 837051609 837051637
    0x3060806060619110c04020c1006172a130b03070b09010906120905070314060603010207021f0215160207050604030f030813061d1b01091206150b 64
    0x401c0d210b00e00101600d2a03403034000c40c605100c0315015802c0303420b080100820303611400341103174604881c2c4460004003515038415004008030700708410084100c9000d40e2202507140c86552000c00d543c14042071004490640100c00406110b094400b441c1030000c1c0c10001d540b0400d000c0c0040d609c0e4070a42c01c901c010ba1022030945458030341e10302d4140403e10900c1821800108001814042240180c01540f045156420000303400c111f29600c40d032508030980c00a680260a4800c2c4000d0b902c3d0400005134401301c168000e50030004554040b8040c405110017002402410661031110706208110882c061803d40301c10480c9400c00849040712417901549402c0103000d940c1d0041005c0c00c0c0313041107808036603018861420200b1940c804640445014220b1354480d1700ca01c4908000c2101130040b405640307801010042101a02d0000728036240440400300e1903413130322210034904c5a0f0001000002c03603507000300440d41305e0213034900705001340b65840071154001640b0310003140341c481480c0074114080300c000b1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 837054109 1250 837052859 837052861
    0x120c0923100e071b05030a1e050c061302010e04150f06051305090c0c070e250206150102030c1f060e13020103110d0228030b011d030a1203060806 64
    0x386a403101103082c0120040e400c4a01c1c08500114414114650390159501046115014a079100ca0450f801001d4010000d040d039414910440301c545150500980d40342491854810100355558440000400c0c0e1910b5000803c00c2c070b001e59004071032100150000800820003214005910344168180e4040c17402c00405e000c038041905130080e01211031071040b12900c01c0ea0f4074a0841041200d20006250740010442400400f003002810800c603000b030403d1020f28505858800121413107500203041c0d54031002465100d43c2e8945401040003a0404005091030011848500040c2e242d40705581e440381d05e510440000003541c080010301c8c1114130b5111a0240411559070501095200c4207507503920144c20746070403040040d0300981c000007407400600442400c000d84080c5100c201c1e0404401076021400d00e81e0030f031820074240c808144404402d4102000607044802c002014201c608296070b13144050106110300c283c2d02000002d0100fa840b140c042401902410002c0203000da07480b40780703020720800e4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 837055359 1250 837054109 837054121
    0x1b0b010e01050d020d0f08161103060a11221d060f0108041205070f0c0b03150411040303110a0602070515010f0303120f0b031917030c04120c0923 64
    0xc0307030032460190014280c4640d40170300d440303100d49208440c0c01110840030400ca105e04000e024010650060700568005031525589002d16090481c0282000d160790320f010310300742900ca52001614415403088140d1800c81440d130100420484403070f0091081c0c2044d100d902410388013030300d540c40c0c03058400b9500690b40d20009801036078044c000b650010b18001302110b44084c02845503019100e1a40a0760078402400c0302e9880d8005c2c0b07000540c02c040c003508000400c1190b41c40f201d071022105001c060740d0070410400241d041d601c560299000040800ca440e01084803d6402000710011a41d00020219901d150604c1e107155030703a036140304da442c1d00c0c84140e000007034400e100c0410008603500354503446090302c1e11030180401401c8a00780040e0582e682c2002169545040201d84030006401c41d02400303060b40c608000020390681c03100c0c50f407803100410810060350600010b0741c0440340d2210242d44080241e1401c01c84102080c0c00001e0b00c94a880404500800e00c000c0482d8448200c10b26400b80e0784600c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 837056609 1250 837055359 837055369
    0x30306090e06070c110402070c05030f1c0509060c070b04030b2508070516030f14030c0403080a02030c030f07020906031903051e04150f1d010e011b0b010e0105 70
    0x9900350400b50490320000703035040e000c2d105818205115a44043c8802c0d5254002130880e0030903d0140c0314079144510912942c04c0c20000e40c0c0344030703150300010004030382c9840400b100790008002402c03c200c3e0108020382d071074981d4010307129501000401e076aa10f54894008440580007440107440480818001c516500d240003100c07100340300c0c00c0300c0f0446801c5078200181c074144d502a00d00d10400000b005044440b0082e10449200c03c6e11950f6100e80c51070303403420b00500e00302c0011124054040b0130030502480142c80c60403a01220351080744c050310340400c200305034118020000c5400b5140800205d141e801c5a240000f000c0c1706100b00c03450019600e8036401d040d0348095004034190074000034a0b001011a001c0d0010b4a540304400d1004011240c900609401c1900305505c4075401c808500815084141c01c44145c07a020389041c50203841a001c01c0c0c08c204c1c0d03044020000d441c1808a6620130804592251881d1042c0e08524241400402e40d14500002d80141c240b140884003140000049007030300d04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 837057859 1250 837056609 837056621
    0x150d020403081911100203070c0f06200406170a0603080301060804020103110405011704020a09140a1d070e0703142502071a0306030f01050f0f0906072106081903030609 74
    0xc04c03c010210b11084a4052009500107028002031185c0500c583c0d000070b012000500401d4441c0d1800724600f64050f002403904240625114a1680f00b440140107069100020456828030580d1220301c41e00c80380e908100402090300050034640c00000080307049900840c085000780c2c803c1c1c0e010051102e440210b0350f1a40aa40a5280003800b03100c401d8080303c1014a51a42042c00201004c000c82da480c00c0300400c4a10303280d201042d03803d80c0c104124081c991481003048030b190703444180d0081142e1343c403915100d1750705004010824049001203408a44654000c4601c940d4003075025005080841c0115080f18003040e6031403040280f40d02a4100354404100c1c04100d03014070f01800300c0411031503200c841542006049540503c1040300401c4809400d0044c00d028151280d031400d0300b800e0040001145450081181503150f02c03010500030310550103c43c00440c07446802025403034155606804000c1c0031903a01800041c454140038500c84481e000e045c82c4a1031003501c041002a0380c4188100655807 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 837059109 1250 837057859 837057887
    0x304200901150807021c0e040509190f030e100c150e0601060f0c0b0124020706050904020c160603050a0c020c1e0604090e01020711030c0906150d0204030819 69
    0x3815201000d850240a07100d800c01000c0c01640e244183c002408850341b80d00300380070400580031003030780203190802d44206604030107000054880e0030340340c801600141da19100001d02c0d100c580942c4405040c400c21840590040c010101002d0000e4440300400901c0c0c1d80c00150b48041d101d41d16202e03d10031520a800b1a00c1c003807806000d240e03181080903500d0401a03a840780030f104032b0340909000a040011428080c0c03118a401008540110302c0403142c1c100f0210240003554010350090100f2900300042e50010300040360051781e11400c0240942c1454540d902c656041d04858001107041505900614030030640003008101c0b21901903401c0303030f449485c81c0045401c192101c04882003407400f0000c8503104040500344078501981e800745000bc8441141104441c0d96000ca020410000c992018100ba49812401020b80c9024040010300e00c0001a00c2e16124488034003013880402d4200c0c0507200c09503000790b0f0840d00c0d580c0c2e80c104a0110380c059040e446504181440050145000c0e07515048121 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 837060359 1250 837059109 837059129
    0xc030213051003080904020403140d1b031209110306180d180e0a060f0803040e01060302030105130b040e0a03020a02030c060c210906040306020a230d051b0304200901 73
    0x2501c3d5850ba04d00e5079104ca08100d411613020031001c000724465aa010200c034181000800250003c0d02e0006d10018012000d0b500c03c02c0c51185440200b68406603070000b2203103004000480c441d1710300d4640c80074564015240d40500965003080340401d1400c40c0307411400c0140701030740c02d210440d0b9411036622100400c0e0340045080141b080c440c680d240c09039640e00080c800000108983c03503005002240c03900354844102903100107014840081040141d500601c0941010341c04e550402001602c04451040c840d02144d5403080f40410340c4e82c903904291a420b00303000566481030020b040c020f40f00d8081c01c00981c028170800c90040642c8c28080c00f142c8040324250041c09010070406041e402c000e00c10350303809158001c14040d00c2c100da910703400140015481204010b0b1750303000d095005042c1c87e40502009481c08100d250b64200f910444007110940740c041500012103541d01c9000741006407020040e0300021038040200b108100c004030004070304030030303521290900100b200f0400424041c03d000c2c01c80e0306 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 837061609 1250 837060359 837060391
    0x160e0406081b06120f090d0306050105160609020406140a0807120311010e06070c03031a15220f061407210215151c0b151c0c03021305 59
    0x10345111640e403a0800043c0103624100041300030b00d01a0109450b4440030000300030074460102410414154001c3c290300381440400d00d880c002920601401c07412129811440409030200a0294021603030b80354000e10400105403146120404656a490910f01554003001c020454500001d01d50048807803a80b44c1c2c0101c05d000d0f96046642c112400c880d00225901c0e401c3c8000b903064188055441029981c0d2008644245400c00a05440d0301d1540316015060b84261070758035440d0041c90a03100d000c40c02103181c1d550300c60712000b0021200c2c0040401000c0d4801804940c0500140c0c03900102d610950710949030102d00c1501c0c884501c1045030040801000e045800e10310a5080c0d000c2440211034010b451408a000c140303401d40c000100d51a002503040720985040c5854031140b20342c102c002039030741101a803406644615400f0300107000c080f06050850203480c030517541e6140306800e10303858208500d03002d081480c0900a10060b4001284551050500702d404800c80d481501d01c5943c2d81d1b12030040c9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 837062859 1250 837061609 837061633
    0xe15040207021c050a03031b090302060a0e1c110a1d1008030c0a03031112010b0f0c0d020601090506090c071719091811220e160e040608 60
    0x79400100704a8018038181114100e240c002d80c403900c0300c10702442c0540f41c000d001d4607004085600c485044801d07082d4070343c1400700c20350b8010444003e032a415101e4507900d6007213030000d40f403900440d040300394001481c0b0a01603200290608038080c041c49442c0c110500f0b1028070400501c12454021075071030716050711260a0000315551000c1c1c00c11840710107204555265111581140d00503509001c0a0788440da000041503494403850203e031f110030b100c507030803d485071005486202041c400c0e104109408540c1d0030614104030111451404250212402101e42c0d050107502d172002441007a452500e801c001900600b007100b2280e2107603040720740b210701d80601036a42070b20b030140e14a0902d10300c05061114020701450311482d0798080802e07440d03000e074041c07404068100320481c024104194030b040405141c02c4041c04000d84c4d5225041c81761292040610b8041030641001c95440420240190344c18044004404c042c4482c0443c050381d84d051100c45410240401e440262103100d480d5442000705101c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 837064109 1250 837062859 837062861
    0xc15050a050f04030c0b0909010503060105010c020409051e0609280620031e06040209100804050a021905040b04060b160606051e100804051506180f100e1504 69
    0x1440307640501c030450070240c581d05c40d841d03810455000071002500005003108545005090755004190450041802e5814540020481c11460710000d000e181c50308082d40c2000303014800c500c0840900c4288030901d844403018603a1760b0a003610b828003240034940a044207110685030520728001c000c6103041c03901c2416507451008145083c203184241440314203101c08001d00000460040e800910306043c090920584500c02c00009401326114900c10084d00c0041c0d00c890340d443d0700514290a00540b20303616410910308000c44120000e43c80260700328041c1c54540240c06800540b201139800701f00c0d80003a0410301c01101c0640c017482c00c0644040c84049140040c03801100c2075644516401300d030059030786000c00c110304400070a03201418005c800ca00602d04001040c2030b17450780340389020a0301e4101912040e440c1c44010100c1490035200b603000500c541c641e00070505040c500700c0056030341c6141c0016009407501003a10203441e881034074800010310005815250740603031190300480c2e043c6c0c203140e01000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 837065359 1250 837064109 837064117
    0x503180a020918100e03131e050d020a0306050a0f140f0f150a0b0c01050c040b032403030c0c01020c04091106071103030408010b0a090c02150705040f0308070c15050a05 74
    0x8030b0f038410301c02482d55841a5020b25480041001c2c000e44c0c0780c90681561a8225645411440d0312058080500d0001040c13840c90030101c400696101100c0350300e60000c1000402e8a403c080c0c407041c1440140600841c840d84140301030a2444403c203c003080e5544001e040d803d007076400844c0e103042040840d200c0282c200c0129001075165404041985140e4042180b0035040d03482440301080100b4090b682540a01030160711003816804146080d040005442ca507010103407140701e505000f030040b00c2c0342c0381002c051403480d18030040407a9160a10b9068140e96400042d41c0a4018050001040c5060406000700c051580e4000e1000104001100a101c03060308940310903180103591081070780468600340001c201402143c0300100c0e080800700c0074404c03420400d5102c00340c0c00b8902552802c40c40e5000c6100030401c2c45003240c2040d0790300c4030102100d041c000c40c3c1114821000005d0000104040304000f8403001d841581586401e640e0742108103040c03030001000c0070101d9400c010700788496215800070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 837066609 1250 837065359 837065401
    0x40c151d09090c0d0804030605090a0302100203100b0c0606031c0f1d0402031905011215051015050702040b060c071214160602101e020f0403060203070503180a0209 72
    0x3d4411030039000004003825510001502c0c240f000050030b20900c211380c0540303a40880f0342c8000b0500c03a50b0590b0700a40e80c4888201030503100d40e002c03001c0b80905400248420061400c4009140c95081c0740c044561500c100b920060b20920903040409016160501090b00d94032050310390301400084c004043d58900d009800003560300e02168405e207810f40c3c0d41d202450160892009178440d501600e4071034030403603106800801c0303401060320340c0f04c00081c030006000c00302d02c2500401141584031503013445900103094000c00400c25141d42c400725080d40c40406400d606000325400c1c0100031a85051020038803d0710f44040e03454001c90070a00c9100c0c603007058003281d1031040040c0320b120103c604225090170307001040c81240d155030603800c0000990401280b010404894020806140c0380e28400c0b803512401c1902d107007440c0e00890700d6031140d901c02d42520001c580101d01590349141460303004005500854440e02d070380c003030f10615928071000055503290f0f540c2d02429081640d110090402d840b61a04000c0b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 837067859 1250 837066609 837066613
    0x30e0115240c0b04050312070e03100e010f0f200403020a12020102030714210a09091109060d150b13050415080d1205090f25030b040c151d0909 63
    0xb8120004140a5006108500802c05180c035411602c08625482e10003805803010000c040c80c010350a558049015480c41c0c100d044c001840204030086c00b80900401c5102d1003002d4545904003641c11520f802480301c5840b80c0b001c8120191140da51944103004900001c0d400034400c000510000403002d911800060050040343d0900c02c2d19034030a0500168098118082d80110710704400d0141108541031100c1d05002d50340e0708100c2c5644006001303699510466455684031680020803800240c00c27074010f400301a120940d42e5007040d07420b05c054040c8840780c4074081c404020006142da02c103030580d8040c0b152440d445034118541300800018100c040c0f00100d2038803051100007400c100130030005001003003941350600b03d00c00b9420b41004403a001455a9025006040c804040c1800821040030520000e01641c01d0021200c000c03002621254000404501c481c00070701051080501c4150304845c0d00c00d0582c1401403007002c3c1210b101001750b494250740c041c0c01e01e2042a0703280c0402c0344e40d805142242 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 837069109 1250 837067859 837067877
    0xf0b0702040209270a0905061612090302160518070f030204050603040b0f1f0509042901090f0204050f0603150603011d0901061d0c130303030e011524 66
    0x20020780300c03121070480540035808013010f00325148610040c0d16884602c0107010004952141c482903140c80000b00603007035106180041e03d80e0305000e03c0504210354000320042042103400d240c041d640e944505009000e0900e00800002e9a2405410008500c107000130300b0b46451729600000d840d160b9031000c5010605400388004501c6030dd81a01441c0b086000705920550f40c100340849242d4203002401010840f10044494440804500100c0f801c640b01901d122200d950744e414030007540c07502c02480c90629181c50070104100e0403414403682c140c1c0c0380603404000004521008108038030540c81480e40159032241c040ca40c52910700d0195510a4020860940510b0201c0000e03115a0098101c3d14448003004500d4061104048541317030302181b1240200301c11801c28900003d003025154280c0e1643c0640000900d0100211303050350140000010141c44803a00ea00c7c01030054400a0358002c5150f02e070582c6204880d15290000040342c2030903155500d51070220b01040440c00131720300300c3c0050140c491 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 837070359 1250 837069109 837069127
    0xf050708070f1e020616110415030c1205071203020f0109032003030112060c020a050a0302030702090c090d03030b0303040819020a060903110f0a120303051902040f0b07020402 77
    0x10090640b00b00039040e850031040c0b4007030100c8490310030140c0380e00411040290042e21200c04560002e100b4682078003200e121858850a11096040440d4026050110500c41d15880000348802d030b0344217805a528603510b50720807200c5c04078100b0b0054280d42c080c0c1000c20018401050401c542e901034070685004c02038103900242542e018200440000c1d0b9071506400503291400008290070f0ba012019519651602264400001c90030354050003880d41c0d11030610f1080e000f00000400c444c0e01c0780a4581e81645402c002e0b440703820000c4181d01404d400720004e919035040d002200d07000d23030703000700024000c100701e4034110014030340c51703801c0d41e01407004220106025004010402980d060380c0481d4207c1e41444c03041c0500911940d1140c1d040c001b4502c0188009401e520800741090025100d09686c014028002210f11800d0f43c4013400079888050080103240e072580103035200b480544800e05192468182100c100e00c05d62103400201006c0380024041c8240f44401000300c03600080c0f0140c01c004501c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 837071609 1250 837070359 837070373
    0x90506251403071b0906030c051320251a0c0c16090b03030301050a270e030c06011403030a0c060b10050403030e041103040807060f0c1706030309030a030f0507 70
    0x260400741c4154140c3d609180280d404c280300200503102900c130a01001d442e40c1d88123143d00141c0c0c054684151071120048038658001e80c84040302c0d820700001801900509a20746440b948042074907030400700d55029070311101485003802c089403030b4060000c440c48100c3c0c00080e42c003040e01030840303030030150304202646a4400130800700580305030300c01c02d90300c00c03074944111482210010b500880c02b036041031004000d16076031084040202d0302e503103901c100c28040c403910500742401a100e0712000140742124601c10190004090450304204004417034942c0d88901d400d090b030301c2c4d10300a070300c0e41035000300050021540304080c07401e40c0034810a8082401d0205100090f80101c2d0f0b841fa86001070301c00701e01042410307402821001950011364041180c0c4070360085900300c80c4001440a030000740005030100402074035502c11740111002903410131027031030117200c0180065520640c14203080f00d80c901041031841c0201c1198940600140101444000340c1d4003076500c0700c00d20340d042c82400824030104c000700f121 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 837072859 1250 837071609 837071617
    0x306150c0201200d1808060714160c030b09160614041a030402030d030e03031303020a020d150c050c190c2c130c0308092e090506251403 60
    0x1410010300542c01107410300411002c0d072441440d041790706080c810040070358045040c1d5000f500b82d2034100100300d6403500c1c03601280301c0c00b0106442d03800840c51a8040c008000080c86c10b40344540c240740e040c0e440d00000f06941d611a84044d00e14074001e0701003044490701541c0c1c1c0320000008101c0785030500344d507041380301040e00c440b00c0381d00b4990000000700421440c00780240310701d86165007010001d017203080c480703070f65039010040c50b0a02c254007a82c661002e041c020455401d0441c0e0081000c1b24401c000c0c50800b20a5541401030003400e42014480140301e40604140d40da10140000140080910448900840f040003001503990b2a0003880100f018442401c40b840d40094001001e841000654000b40c55a900281200c202a4401021a0010b02d1034401001140c0d00011255107500001e00080c2200e000d0005070110000f01c50003040c580c03005540241d902600b40c1d01c40540b001d58440c1800024401e6020880a140201c0d40c0c0f55040700444c56810300c1c0d036005407a042a141e000001c0b0700d00c4c60388 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 837074109 1250 837072859 837072917
    0x6030606080f060f010e15120303160905010f08130c0503030a0c0519080901030f0f061d0705040501080103080309011e0213050a150809010207020d08190306150c0201 73
    0x70368060701c02248208040350700810b00e04c601924940c90405e140d81541405410700a0000300341c09a20b00c240d880c0303044030001d4101c04060300e5032070401c0070039181100c290030b55400108441c440e00180c198000c1c00341c003500704a252a14002ea1b900c02e0021360513118a0501181c00c06480507001c900364804001420780403129880b84050003074982411850810070100c6450134210000455002420160030354044940c01e0801162104034004c840002e89484c221000301c0c0ea00d0030000203951003404118110f030b8000c880410303259884808040f81c0034416401801e001c50342e4007004000092042c001954002184400042c03072240e070143c10240c2c90381000b02c0103041a00440d00f80c0240081f04020401018101d60040300b241c500717a011000c203901c800b27503101800591400120104001c7d0100c98100d64000d04c45e0190030b800c0c0c908411160000000c00d4450303010307069600c1ca40750007031181c58151003442e401642220f0444800301c83c0442c0c8038000303c7c1000300054a84411240e50001048000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 837075359 1250 837074109 837074113
    0x1b060e0f0d080903030c0d021305150904150e01180609060b030402130b1c02011404120b07020106060e10030212180c040207110111030c0609060712020903100b01030603060608 77
    0x2104003400034600341c1c014201500fa038100b0024041c01880035811291055252407002d03803a03500000301400e8030130142d4441c0b40c001804210103003d0b402400001d018456040310f0401034020942801d0484459a0080200c05104480180102405804201e000340d198083c0401c0c0300c2c0e115120742040d11240c0d0321a8507050004401d120442c942000c000990418540b0100300b00c0c943c1d0b00000f10056505410441c840d5048400d440659101d1041c03228034201c2060311541d96a541c40c0d1408041720500b006a4207502d0000100d0840c5106001d02d1089034020b0703584000e8800b080b4200034248880c051888140b503420008070100700c4002034405e225003070341118a00f914460340382072814403000e000813501c9184100000d070b00040e42408440c00142080c03a0100c0f0320340360400000d10b507110342e04001b00356120b1a010005034040004015228580c10750301d400118000310442c400b0380c00780d003000550607044040c407007000e0301c4550320442c0340240525001c5a0a039580e00d175001101d0854104414075 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 837076609 1250 837075359 837075373
    0x40f02031f09020f01020a03080a050618040506090105090708061f051306031b0e16051b032206050d0b03032511010e03150a090b090c18071b060e0f 65
    0x141c5010140030f602c0134001c1c0050003000d41c260703400a021110003807001c01080d41d1400824040d48400800004241354180301c180207080c6070410b5030744c5030703002c448141c80e96082a00080c0d04c2c00e070114000046076459001880ca41d101e1006071400c8465100ca000a542c81a6400150340d030303922248d84505d400041c100265060031800e00055030b484c0010944102234503803a003008946c0010410075440507000945d40f1741c05086090444070351245e10a01100340340b4040c0b030301e8500c0501000801001c01c1da00302c1c0a55100c801071007960b00e4411032141d00701242e820700c402707020540140c10055504400800b942e2405000d51608034101102c5034600c0c5100c01c0e000e600408010754076030182d030040e000b405e11000140407400042d07a00e9003a50401f00340a48104041880740c12190040c2c0b224640c440c00c41032003481d1a01595a4031500c0e40d44061140710745081006014860841e50f034017501140d075420b407500300185210b950030b103411507088401ea55581c2c1c80210710f03c0140300c14031842400d0030240c411 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 837077859 1250 837076609 837076613
    0xb0a12151415150309030403030507050106050d0312060504111803071e0f12080405062511010f030b2805041506091e0e0408270102190209040f02031f09 67
    0x801c094658840450f0b041c03c205002145000109035402c50703926140a0b95120510300d04540507040130380c41940c102e1502c0084400f0103070070041040810721003100411100e0303501c0e0108400d42d4840c0d807603c12492410440e81c1c40f0a050801803603c800f20207800c5a160326561561071141c034110282e440030540f1480303010b0045002d001e9024009003144406246468515281c46076507100380d105144c4600380006400f90b40c00440062140d40007141e483c40e540c3c6442d1070810480f81d00310441e115000402d0002c010308035078007074807800c03071a55405840481880041c021044060404102c107c1150b0b03800c0c0ad0000e91b50703440d40994410442c080c1c0741d608075989002009018040140c100d4a20500520341c0341c11046512841c02c0200c541e0b08403048101d4423039040480c0d079071003601040110300021501e150307420301c4024003e210009081c0d0842d80e07030800e60b080080101d104080000d501030207410104011030200350302440c120380001c040e0781002081c480308640c0706009040400d10503031106d8010342 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 837079109 1250 837077859 837077869
    0x120c010608010905062e06050a08013201090b030907080c010504240c0210080f01050607150b03031309060e070302042403060510050d0b0a12151415 65
    0x401001d10500a01c1542c0030750b651a0344817800207145000034104250000c2c0100b0307000400b00d00381126004803213503071922280000e02c0780d4006001d031000b19403404000200390720788281d003402511280d407180c80c3c04011444a40e404144003140c850410180c008040794101400008500078520032005000d81460240042e0902e0742c07940c40241405400d0008210f0185100f68400c00c000d5841e03030721000b44403826020390741a040380c2c2002e500034070802c00c1c98044d41c0d00409003d02900c40a00740c40c84907079940c01000080c0c40384803402400a100b01c0c0641d40820b281d9009004100320040076a41030890081c480540c141c541d52040309595261502080504203900340c81c0e8001d1b502d89003c3d8a4541060740b214480c102280150000402c14080031800760300c41c1c0e00940150034010902100f00c0314030b010007421f5412038070403081e04502d000d81a004a150117051782080700e24901030001c0c8003400b0b07151030300e0300480101d00b00403840c2c0351100e00c0c03800e03c49564000e01ca2034103004a080c5005081040c04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 837080359 1250 837079109 837079121
    0x121006090e010b01170a06030c0306050a110c0c060327060403030507050a09120c0902030a1d0c0a031b08030301090204030506100503071401051b01050118050106080a0f0e120c01 78
    0x544907490714603101c43c103036030040c0c803410071640041090130140c4030441c0b180d0042000764030291184092403000310800070745400030380c010f0440807000d2101910280010740c60b840303131641e8240141c0c010640d0210780c1c2003003005140c0c8544403011350b54413200b80e10300410742030002040c10701843e0029001c2000300340d050711400f0381040e000d1030481d08222901d900074080342d80d0341c05540d0082c42c03004080020000c266442001402c2e070b00c60203640702d080c401032002c0a0012501c020340c407805003c980e44154980003c034402000740007009141d0840c5991506000d00c41c400c1070722820b4034205c13800414800000c200071070007007050b0f06006980c1c0780340d828454101440075044030702d1104900001c01c40c0d81c0d00041c1e0501942c0c80070751803550207160f59006941c03d02c5402c0c01c2c2001907a688046001000042d0f1211b4102c0311004080c3c031201d0ba00e060002d0440700f0034000c44003c29062800b1900302032940e07200058002400b50f0000e052800c841d95207181035540018802a04000501b1900c018001c1c094a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 837081609 1250 837080359 837080381
    0x120f070308070804080412080705250e2a0c010213060f05030609070e0111070909050c090903340b070e0301020a0207051003150305030a020d0806031b12100609 70
    0x3d5a92404c15595080c10b03403140d881075a2412180302d00031424018880c0440754040c0d400004c07034101c2506103101c00c40c0d07054418a0520050081a00001c840e01030038080c81c8221348555081003120b03042c0400c004105c501c01e104014030b040a00100c5081c02c001d10007806050100009115890314020000f44091404244142000b409000b4081951669545141c0019160030280600550000101c640c20200c0c00020340b20b10544600284800b01c0b0741c031a816486c069008d880580340e1400521000d4442900e02400560041214407050f42c010034015020305558907001d402c480f41d8420342480c0c12001941aa070b051128428040d11035040b02c812031862074150000d5044c0003400c100a0340320080c5110707035800ba40d216000c85201c507110307a100c800016031858980d0110354030380c01c0c699920780240b0b5103000580300d80754140020790b0060003031612650b0024014032066910000340b1121f0a030580307400f5000300001c1e84c0194020303018002d80c016501c0070310001030050301d0324803194240ca17000200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 837082859 1250 837081609 837081617
    0x40e01050406080c0409020f15030609090f0303070f021501060e100f020c150d152c060d061b0f02010b10050924030103061a030606061605120f07030807 67
    0x420402d0703c10110b608200c05500b00d50008001c40c007400842c0c41c0f603400460f51076110480c5010700540b00e60755800781d40101307410f4400102903503900d55000d549074800300c20b644042c1e00c01e00004462512550a08030b822100740305803001c0c108803d49178242c007042a00041e003c01c80c000340380e0590781482020b0004201e0149400711621074100c4011791600e001e444903d000300c10b0044060782655108080b031320100d03c03141d000c02807105144200002d40384140522410340300400d80d2140c000c02806007076000c0002e4400e4405064680400f04445c0e41c1440384120b441c0c0b80c4403107568515081c2017411041c0040d80e40c44404c1100100ea170000c2c05c4a11141404d44611020782e07070008007540c41010303105044c00c01e07182c0701c0049010f82025038002440450341282c01e84000008004c20030701c0c1d000801d907080d40120010030300c00e01804040d150780040f1000c6410107030500038117490900140231011200c0c09107064900301542d0040d44605544051100c6000b6400000c01004040e840402c1560101040c0f42c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 837084109 1250 837082859 837082871
    0x70b0f0a02010609140901151514071514010e0103021008090f0a0c06021e150c04090c0306170606030a15020702120a0b0108120306011211180a0603110910020c030f03040e010504 78
    0x1c9c034681456005080b040c204000e004c00300f6070062078601152002904aa01c01d0500074040070712002900110030701c3c0441d0107034080001148600d83c0c207200d05a941c0100b040c81c0301500c100d03088407007420041080f4004d00c9a442c0c0d800255005000c0301d408680a1540441c0f03141c2081800b07468100c56000301c00b055012031007071403418003011600200500c0b40880c20a641e885080520005006a03000785104510700041a40300c207030598001001c440c001501c440321046010302c0c56445900459100b501341c1c2200024400203800344041200401800b03000604141080d0049200890381d0b00e2410b0003980b140c2e446100380200601101d0060030701c0030003402440070b039205038030541c007000d05070700d042c414000055810241140c0010044080f0369031000d4488100c3c00c42200d41552880c000e074002e02048201265aa21034007400c1491a07902c981203103080009400c0c05a401d1004101800314001c4030320720012a03400b442905500d0144100031921542041685031090a06910940c403607803801c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 837085359 1250 837084109 837084119
    0x8030a02070909020613060f020106050105070f060f0f02070f0b150d0b060d0b15040e0d090311031e060703140f070c03031b0f020609070b0f0a0201060914090115 71
    0x150035042c0c0c2c12905020030342500714070105205000f4050302c8071450300070a0000c240f855005000c0211804554000d1180c10354030070040d41d1030b210315030000e005a00000000401705209411103050010044000121615504140d100f286c05c0700f18111f98030020124000c007400409422580c002112800d0a10032941c00c500080b001d121208008100ca00b0f4880020210b66031400340e1407a99801c02d0740c920292400c01c103d0383d0040c0c10711fa1514495858001c10354800c840000d80e0005c03034603540d2100b10342d00341151590444c1d01c211010103a4148140d00108091280c001140c2101a00c20802019581003280c405025103440400035100d80c4000000c200c04280000e11050300704003281450400b810b0541011000f809140d503110701c0b008900700f9120b082550083d9502c0f03881129500780e0f6010748685080c9912600b280c840d00a2615003484000701186841004080b00c40e074034000021415546c03602e034402d4441d601d1400055a00c03035410003480510a0180e00f090804110440321458104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 837086609 1250 837085359 837085363
    0x9010e0c0405010807030b031027230106030206130e0a0911010c030e04060b27130c110d05031e070f050d0b0306100603060609080a020105030402060f12040b0108030a02 74
    0x24440c041c1003044d003d000c203c0017402035014000021016054a510412100141c805440142c0c0b01020b86551254404290815202402443c5a2000700b000c0000e80c03007803103a8003d200348041c04629560794440080103a407454000c102400800c0c640c558541d15200640340b810310700401d9032031503e0070000010300043c00624845003403403007428403101d015070a081c2112008560548260054500071010a01911312805400d0800b02c4c503c0d15042d850441845081040040d000d0a80080d01080c10000ca04429003056180705050302d0114400c83e0546900c03480c0010b403d9241000c07680000c04c2c842812450030040d220000c061403640402e090048000b464010010254810030101186901044155400c000300084004040f03d043d03040107202c40c07a41c10241e2003100042171070280000b032118090701000e03040368400300150110310308540054910f94801002280d001d1010000c0440018051024006501140460083c0341c6001d10f081001c084060b0803034603613a802845072035002c03680 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 837087859 1250 837086609 837086617
    0x516021908070303020c010e0a02100e0a0512120d06090f091104050405010b06040b1c09030f0f020c0d121d0a03020d050114161e080c0a14041409010e0c 67
    0x701481d50382e90384400b828120000d000d619402c900c1d5500742001c3c0d2140d01000112481401d00031244101815403020003a5100e09041c02041c1d04424000d5003041b40e45000306000014090100544a01400c03220f000300c032a60260740400613196681900388820f140d80d01c00c1e01446c040046041046040302e48410165400710150184140d44820006042110a42005c00811000f801841d141e60721380301d9000b080c0c0c21801c0401c4450f5003140d2b01c0d08a4060900849040c160191240c03845e40a2f00d200482d0380044101501095110317079051030328141c80704041110ba25000d404521038a001c0464020055102401d80303042e21005c0c410450895a6000c03081000c4039412a030342082100c1a01e0040e000d403c00e2505490400601d038100010340c048208410b0703004c05180d5880c945100c40031003c0d2540301c034100701c4c0b00005940710b001500c5100d40304000d00302e6205508140180c2c25404425204641c01508031128004005a01d01c0550412485050240404032081c13041e40c07410300d8642d002e0f401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 837089109 1250 837087859 837087863
    0x120e06031b030417042303071a1b06010b121609121a1509070c08030c090d020901060302041a210417130e06040b0102071a0c0a0605160219 61
    0xd40003012a04115014800c445000c4a4440250301c855035082e800d03600038003110800d655030030040d02d08a0a0328006c5099020b903143d44030410707500c4442705601900d0740c20019040c81031902c00224051410401c1000e50b000f002405421a910b40c00c1843e1200070030750140003480407172000c4400343c0c2403542142004c0e0030703514035084441d4040c03c3c90816036092504030340d981400030780100074844408014241d0303100b8040c00707070380b8046207890700b8008840455507035001801d10341c01480403c2c15036882034024441c1440080954000e52060780020b00e49400a81c003800101e40d0020b0204400c004d400070a030111100009108c3c01d00000c02ea007035003004080e41ca43c03000c2d60825000035040100c0d140c0781c60606103485034041d03292030703000504900308249401400303107010040002400c80c0c42d180c050000c0560041c1c0c042c001252030b02c070205080420f0782c0201310182909210030741031554100f10803500140180408103850501212841d031011a05040704119000b09074070b01d016080a08802d402a5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 837090359 1250 837089109 837089161
    0x10e0a05060a0909060906083007080f1b06100e010902031f060504060909020421051002070609170c060c03060d120f09050f030c1c020d120e0603 64
    0x5885110b0448aa401c190410f026103864800c011494861036480081030702e01c0401140c07011000e002214081000ba20101d000240040c030700c20304040b483c200545078081c441c0d014641003054540c00048550400c0281302c5500d98440010080354501b0400c1c0d80d080300c407403103101005604110504802c2d100c1401101e80c0b4030380003c089106004c0c40044003110300071080010342029212500240140c5c001c1c0305003800261455404102d810b1280b00301c03070032100107446002031200300a4400c028041300000541c5c031340c0180314003482802c01c180018400184622400200070015142080c08442140e118810026040c0298060907200040f8150840042c190a41c2c40c0d5580c80e000a125000c0b500c0c2c02018000c8100e028005e181c1c100b0b00440d8544100c1d00d03443c60701511107060000708022038101950503401091a22298103200c04600d2902140381c021a000007441e4000c20303000c1d40340c0041120305e507103507071040540c2070341c0002c0b042c0c025101103400500c0c50410f0f062103d401ca0b290286440c0340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 837091609 1250 837090359 837090367
    0x509090a051902091507082206021209060a0f02100c050403021807170405010b0d0b07170c0d0c030204050415050306010e040803070e010c120801090b0402070f17130909020f010e0a0506 81
    0x405814801c0d039207005043c001c00c00920425400c0030308c4544e800c6c45010702501c5002c0480b10240441c50540e82c2e0031b20040e014508154108108441114a080340c00003580250f440d1901d05200ca8015800c002d8850307100c655907245544144910042003e1200382c111001da000d01a8466010015000356241c1c0c0b041494240c030fa0342425030050808402c4140d200e044007005008002c0450030f10348c4901313601e0b1074641c41141906012018008101ca6079044610b042111080c0480942e0081200604070703d001800d1a48071400706d41184c0844641260240c8141c80800403032404100503800740910010329000b0f0b041c40c1c0d403807440380e0001520210074019030070500c1e98641d03c61030300b000c100e40c1c1140043c903031051021000340101d81d081c000c05290038205410411242808c4c022a5242548540561541451a00e5000d5007180709402c60305021400c2050a0344d01407050480b401070035003031000241d018803170f104001e0301220034403c0505107d10f45411000582e96a40ba40c1c0c200d035400e949650b51 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 837092859 1250 837091609 837091613
    0x10c0f12060302130518070e0a0b041802041a0d05011a1503040204021e0d05010e01080d021005090703081803060601090302031506031e0a050d0305160e010509090a051902091507 78
    0x40c92605001c0d121031047c1c00700001c500d0342c1e03100414081c1a064000b080b0480410082c0410f0f95121540441d8403410807090380010f0809500c0b4800440307461000107410320f0b0050006140030340d10072040e5101c0c0c1d140d4641d170419144110003415204012101841c809111400e1017806020003080a4030840d07011540320581c1501460445411070810041541d485249105800504080c0a88549201d0100000c520102d0014010b04d00c6a031341d8005068543c0d01c02045005003000400281e0f041c01100c00c0000011220310207001e00c60032103a030201ca03e0403168103051400f4001413407103040000b5800300b040980c50204407203018500807108040305540e8400424507104c0c20f031500d81c41d001611907050b041e004003c209918164840e0301507a60004100c042101540d4007601c0c0804140d03003000d25040020b0140385406030708041814071030b081000c03040008026540c12038420852980724000c205e520284024401316030489960218100794103080070501c04042488810b0b41e1b98000910542 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 837094109 1250 837092859 837092881
    0x15120f0f02101d060c030d0b0d080304121106060a0302060a2705040f0507020c27100e0a0e0705100e0301020703020c031b01021b060c010c0f120603021305 68
    0x20a40c001d041440920b40442c40108090700d1004221440071030804500e040d407901500300d96903081c0241c002d50501944401d4080140b111741410b5a00419407900d640000383c3c0040035511a6001d01c0c0004005466504098004450050044e245402110400106603107070781e00c040650750140e51268488059a0f400d0728000303003a000032a001001c003142a003048200b000707200103540701918103003c000d41400c030a07000d03120191411000340e040404182ca55042000c8104038081881600d4203001081891408101800383c41880180c403d049084c800454402e002a400008048003003041c03211f0400c4007a1190440d016a511a404010000403500e22508924881000043c000c55541c0322501d0301940d00e402c1018442d000380501c01c260480c051550203140794040041e009020b03401c540d5061440b09100000e101d60344a0424085944034440034850804d01e68640d840d417100360000302d03002910040c1d0503c5000990340c01c0c19001c1c00161200403840800c003a40050106c0c0540b90911200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 837095359 1250 837094109 837094133
    0xf031401061115102d030b07020307080a080106030b01020c150a120e010e0c18040602070f06090515060604031112070815010f090606171008071815120f 67
    0x3d681d00120400e10030042942403440040725084141c283d15940e00c1208808083d0301aaa03d02c00001d030610700308003007003052040070790280142c410b9a280080942e101003040d00314140d550000348200006101e0300745c00d40b01e0148078102c00d00040c0f2008101d030000803540030403281804441240803a026094500400300c46a00102001c400c0c4210585050800d00802910400100c00d2080c0001401c0608020320110351a10040c4103c0ca80341c1d0369501c03040041d50009100b00e8405005007888000b28141c1c0c0f080341c40300c5102e40085d284011480124242c54880504160300c9587c04200c2040054603803101070b0305809040c0c3e8035208a040b00070006017000c90310b502c481c00c503014040d0418400f4403039003041c0e0706803502c0d03030741340c41c0c0003503d5600160807241280140400326260107400c1401450450510764060450001c03000c40c0c82d100c840007410654140d22001d4150014105404000c000d8003924202140c070200030b403607503131505004031442d03481c1c0c5074003800091095201d44240280d0300c20070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 837096609 1250 837095359 837095383
    0x60d06110a030207150b06041a070212060a05090606010c0f0c05190609140108010603090f050106062307030822050312190515120106080604050d0f0314010611 70
    0x41d2107100074a00940070394003074003044036100740c030504010950f075041c450300805d07100240082d8149410851404070b482685a4001c07241403007030110303c0044e40c07090010f14540b428040545038900705012480301b91100a0041341e06900f00004001040c1d0f404202c103c0e0b45600028082d804189a00349104d61a82035000f054100e1702c0000b42c0c004498031404501c08494a41c1d54841481c0d550b038440404005c0701c02e00b0140050700803070040041c18803c5d0000700f852409501d80103000a541da803100d00311011580000c0110b08114185025040900d00c0c90b03a0501200100a2038800540c1d0700600c0380030001e04485141103040b81c078010004130306c1204464a5404800c036039441030b59484803101c2040841b80c2481000c1c202c05508039004040c0682e03801400c041c0c024801d03401c0301d041002440f044141c2c00041c4c945d620b29000806050400100e4000c60207400a072064a02c404001041c040780c05114900380350901c030344030700b0340b1290200190440f01d00d440e0140f1203220a903600350802c80704e00c0035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 837097859 1250 837096609 837096641
    0x15070f05060403110c01120b040f0e0c10050c0a0201030509030f1303021c150b01032d11160807020105070b04030e040f11041202030c09010909061d0303060d06 70
    0x10404105000034407034000d50098507071240b400c0c0401e400564401806050500249407140c4011241c80990000340c40c0d00c4000344003241c00640c400d8007204030b481120f80e8030307495842380e000b800440c00c201542900c107031440c1c0782141c68080c11900031551803000c80d1000741003607a01c03400100920341c00d00c1a1843c906142010590741d884000361803400b0b04940c001a4411a00f03480c00702e2107401d464410003141030344455000c40c03012a4181d444010b00040301898140750301c0300c004500c2c00d0413245071341c03801001c01125409083c024201c12412141c070300c160208400300c104618560504140700d1048032070303440100b159544100d0301c012100d0b4000e925004000c041c00405000c10560001040d88039028280d400b0440d840d0104036400c2030703401c41c00c023025070282c0800082c07000315158403615407018006002c4840c905500b01c049040b03035109038024052180e981c00100100f2103079009014540017042d0503180c5014002d040c10340c076484040c100d603205040d400002400c00c01c803600401400141070708 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 837099109 1250 837097859 837097883
    0x50a0302070f05030f330a020703090905061e0307080f0601090605040e150601090911030405060a020a0c03080a0e060702030403062a03021b0303180c090f01120303061e170a0b061507 80
    0x387c0c50294220103801c6010504160020905a4480c80360798030401c0c0040c03e405d0442c2d641c40003110501030311011150103025620700490300a004010b03e00034548044021305d215850031184030100c85041e0050303071141d03041c00503540d0100c9001a070f2402200740520b80b0206070b180e05005075a00103269202001d881c0c181122000c44000c48000b030361007240620280c4100b0b13560313030401c58124803841001c140490341850380301e070100384281c003400d030f1110980300002401e2429489007890b18000f1520b120045e400060b0174410003c0c54004c0404100d0b1440d60300ca007403940d20702c00418607128004c20004041e804104801c01c00080104044071031602810307a5031700c3c1814400080310700311382d008800c080d10031541d00300814103214500a12618580001400503400c00070102418010184254101600d801c0081400d01c190741c1003c921401049040c074145140c82441c000c40b100400d000c0032250031008181c2c0100e440001019440b03802110002c4081d00c14200c00413403800f90300000380400c1c06a80b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 837100359 1250 837099109 837099121
    0x71e03151202190503030f090d020301020301030b0115090b0d050406020d05010b370305090703200112180809060c01060906030605090303011d0a09050a0302070f05030f33 75
    0x9a411680c01d03000340c1e054103084504070050942c0100d240700e00c80e0994020420000d440182c8000f501885000800704045076007150000703400da030001e030419110350280000400420044500100f541c07015428030507242d0f45028443c021501070444603510305500c07003001078100011641101c41b1001600410400340d6140e89117000260000703044500c1900c010f0700c1c1d10701d0a03c0c040d1440c280710310b0312941d01c4100100c0350100b280030308000f40c9055894800c00d00d01000007103054003d00492080c0d40f51041c1c103450b001c0c0c0018220455a102a000c9500e0254801665402105070302011078019490300d40d1002c500c00403540d10700c11080d84034803075442c00e03401250018040c1c000f0340880740181800d20154807050a616180e200a00c60225490341800c1d054010000d00078005a02c081301d102c00080c6951203489960030408440000c0780183c100c50024000c0a0401004602521040c0c0041818000081c1d50540d00e8824402020074218020561410900001e80c110488150608907290b181052 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 837101609 1250 837100359 837100379
    0x60a170708010c0c0506130f0c03141005150d080f0408010b15090108040b0a060b04090b030d1404030305180406030311010b060f04140f1e0a0e071e0315 67
    0x54041d0310640e50a020fa0341c02102d21642403200f08580182c040c24aa44800d60340440001101c10104c2e0389a00c00055500403441d0003400354015805202007107816144400500e0901039880789030200300d4030784010b10076250f089140355802c260b02543d5520070b405640c100311a140c040c0703110494014100283c081780c180c1044d0449441c0311400d6450090221403001d140e2480d00801200900044205c0c00050100f0113407000f141c1c001c0c144020001d01c0d1501ca074840c130b10075400b9400c0b80c0283c035214158000c45050401c50703070200500c07520723081c02c00362038000c0c07402503078482d0388005400c11401107803803029800300c3c521034110a20300400c1000305035030b2450040d01d02c012410035500c05520780726944025003040011106103200c084519072402d400d120780c500e410480c2d0301d5011b8118018034080e1003191109242a03546040035484d0f00c1d004401d110400980714100d8202030382e80e00302c20781407010168000300d4180310001a08801050000f0207a03040703000300f460124500362256141d030700003a0240c40f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 837102859 1250 837101609 837101623
    0xe06040509120c071e0b0913021c02040e100b0a0c1407030c080601080d050702102c031e100209011e051918050f04020904050405060601091a0a08060a17 67
    0x4900c1004007003026440b00b40c10f00d05c06100d0320900240811030017070580f501895060140352481c0c1c0043c14409104003440540c1080c0205030592130f80024144600c000280615512550050584041904040400d4014040c1c1107018042c0181d010710001000b03c1e96801404800100085484440d0380c0e0415425802d0a84203040d00360180b207002240940d00452034100b20020364488510b0245c0355401d2020115803032807000100840302243c0140810880920003001c2c000340c0c41c0030035006110302094140320703801040c054a4a403240c1e00c0b12003044081034581c918482e80300c00680b0350000000581d0020320004400300c074000e03843e64074040c880c0c001d405052520030002c00c0285500c9c4008040c6c4406a0496030184c01001010b001c0002c1d1030701d00d030b02c10007004000c3c00150810141c40c011a007910b0040d54200c803176400040c100101c55034031400050040400745800c1100202c0360702410381a00c69a80980c0420098078002101910341806510043c1f102108017880e2004c4141c3c4142c40c0e900c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 837104109 1250 837102859 837102869
    0x2030307050322030c05010c0c030b0910230c0d060f060503070f0c0803130507080d09152c01170408090a060509032a030f0a05160e06040509120c07 65
    0xa002c07405901d0311108082c00c1c00c2030b01c0d030005c0f510140d5400c0c07a00648101580c188111569984240c000c00041c41d84c40c8051302070804a402001c1c42200518024140c2d002c5c0d210210103020805400d842200800032201d07044100040c15940d40c05088403248017a0030300e5008092291003404000450f99400b07401180304035442d0382d0b0b0001056801c42c1c11680c0340358071076000d010030b0401c1c00031800c138580700039961003083d11410803190780e0740e41e5100645c1002600f0203608041008500108000c20307800110902c941c0e07042c9001c1c21b9060f482304401120b00030b41c000d18089103c4226101160764090003548101328030094014080346001e140690050f440241d90340d00809041400143ca01e0049040e40d9002c8001005080d560b00200c1280c01c40c01741e4010000c140c00001d138603056a985061000441c0d0146071405842c0300105828541c2c038015201a00105038a4818420401e40d5001100217402c114105c60109064641d0079019260840b0314444c022107810001d503646000200150140c1198 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 837105359 1250 837104109 837104137
    0xd2c1e0c090c12011806080102090a0b13080d050a080c0a081f0e10050f010804080f0c07030f120908031602010e030114010b1809042a08150604051311011407020303070503 75
    0x203490707e030600e09030300608082c03030340002c4101011311481185c40060a1904a0503141c4010280e40d803607040e1a20000004480104200180f948441c03a40f04c2e0115600940120f1003d1074101040f80050000d40c0060034035004000040b041c41038400c9a01000300142a030b4080404a4200100700c1d001c440282d200707180c0b0410054040903503a502400e041c1e4866030700b15205038205440c0038281c1c501ca91111622000600400b0f0b00130000500110401d1405805090710004a04051001070900c00c003d400c0140d560384103001201c0201569142c42d000c055080c6082944010b03d0720100703025241031580e05c224811040300214248268201a0001203010982440340b0303001103050001d040c20545015000d10048c070112104529010f4141c1c0406114140286240d50b403442c80302c1c284141c81c0901c80303d903420203050104514140c0621900000003c84142485900e60350780300d0b10300075001d020780c140921007003620529012202a0f0b410141c000e019250388188a01c2d0a0f0303281d80c41f10028541c0c2c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 837106609 1250 837105359 837105371
    0xa170a05011508040b180a060f0b040608060108071a09040207050f06060f0a1208070f050a03020d0816080703060b0d0209190b0a03020d2c1e0c090c120118 68
    0x700b485100014004c0b0b4112104180d90b8590f070b22007440c0303c0d000074142c40082c82403065403c00075805104906401021104c0041d03822914801c01c41658901d90062820ba0b006030010300c401c020215021080300c0130f0a00000c030003030005015140d10300035a074813182d2081c40840c180d020700402142c5001f60b403047c071054814542c4c8141c100710030740540c0c09005030000e03000304003401000c461012400742c1d14021080b0720300b003030682e50315018030254044045440350003883c110000c240d0100b24000e01c9201c50309040c146032605200e0306c0c040704100200b00d01040b49480200b01d400c1d0090f84020050070101016680ea5006036050700043c2d4000c0c2a030303a0040c40c6c49010000003000c0030548409540784410b17124603088039604210b0180d00000e41c2e00340703c150b66455450030020005140501d5800c100304808014101d080064203000604140e0a040c0d100200c106140d00c00100710340c01c404c3c1c1c0072902c10941d80c0780d0402c00082030007030000d4441428001303000071038400040030394201141300e07904040c00300c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 837107859 1250 837106609 837106649
    0x30b1c12080c0a03020c010b030303042103060303080705160b010902070b0a0e0a0b0712091101030b030604230a020607080316030204030f0305070201170a0c1b050a080a170a0501 78
    0x80c41004039800c4001020500c2800f80f528401d80003004100103c03030000c02c0880c202e42c002402d580c41907030111402d40300203182d540503981c400c1803512180c80c94201002800d10303680300585652001400d06080040000d1000c1c1d5640103002c001da400c83d00300301c81c005c00790703150700484009500180f01921506d90100004031071400f5070141504407100e80001d0300d8100c40f1561303500414013000d040e040900030340d00f070040b44005a52080c03070903003405010801104508800090704540b188001c0c58080e030030000030070010618800517010100810040b030064007204403003843c10144c8c00e60340290701c0000000c00c4014001c1c2140030354050f2103590800700700e0904c01042a0100e10072803000505080c2c001001402181c0540c1c050014a40181451044280b01040f900d14a620442d00c501c8e0140e911a42001c4450f4071007204d4488d80c0d0b007241f00380c12000403a10741d60f981c0c01c030720f0703d004240c1ea0000800c001000e214050000c00e1140445100580d81001100c0b6030180c1001d0040e50070380803a807049506 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 837109109 1250 837107859 837107867
    0xe0f061c0b030723040c11030f09010e0d030c080a0c02040e0d08010e190b01111501030b060d0519020d0b01030b01050112020a0f121514360403030b1c12 67
    0x1110781c1c0401302141e1514076000600c009005007010010a2080188038600842418402012070071060300b0403030b54802c81d660000d04540c42d154016401000002441e0001981120013440d900b5000200c0c0303600d4a1104a08542d001c00441c0c00039000f6043c01c003c544c001c0f800041d00c618015940d202e0310b10903030700c484100d64129002c80c0c0024507a9141c00540345080c0d100c1d444081003a6040c5840c6a009051515080c1b41c5103141822584a82e81f0a004006001c2c0d612081608024100c41e0300c590300c00700f42c0301e155540c00d419a40d03c2068a40b0081882107507107210b01c0b1034600c0c5e030201002c4e80c99070b560300340010702d60300903c11180072a004040b01e0a58034554400c80e5240c07050354540615810401000700c51011300074864181d0b650b0380e600c07113600300700c0c103050340100408400f024002d1a20494060044041e070a549600005801c10a003004210302140241084032140c0080c4070a41d6072800c0480c05828464005074200d460580050041c0742e802c1074030307581c090003200c0f65907042201c003800319 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 837110359 1250 837109109 837109139
    0x405090708042312030915060103063b040506010e01060212030f0402120708010e070b041a07171801023c160b0306031b010e0f061c0b0307 61
    0x1080300700c41c0141e1080400079450650b003040f0035801101d020740003c9190301c0e06a4400e4400740555400f03411148400a41d502100354060400e10381031044038904030080c2071000501c541890f40d43c41044891500e002980380ca4003040ea0101010420307418541000340e1108803c7c0280c00f05500e64600114030940001140301c2c12203202074070a0310f15500d0140340e86800340d01800c100c0c0e01801d605141c42001004100c4580903103503c07030000a80401080380c09160005a6000e6905584107200810000e0800c030040c00046411071760159484003076103400c00222003445400310314200e022030400165006034103a041084420303000c844964050501800024601d900c0c0e0004a0000110350360841c44403640383d0484982100c1120f580040170102c20004d02c10a4010185485010003004440e140400080040d16042c4000710140200300000800c2c145110000d640100e5001c01880c8164031000d0442d10500c074031038240300c00395a0b0300320140003074649000024031910070301c44c01007407402042080c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 837111609 1250 837110359 837110363
    0x603020112090618030e2e32040e010b1218010b280b030415020f1207031a040e060a050a02040e131502030108060402010c021212040509070804 63
    0x201d1072070201c954403000d0b090380042100c456132110781c01940b95000d400b0005503035200b51141c11800c410042407000c0c012100d44240c47c140101103809904814058030b0000da142c05143c110340c1c1c0604240d00ca68510000708111003920841c2007003038042e039500c0d0007410541d402150403001c1c0d641e803009402c440c0c1c00380c0ca601d82d408030146004a001300d4480041600d0070045c0100214500542c3c10000d441d44200c0e4541d42c060b510464100e0003144030084c00c2901501100c45a6800c508050711400c0110400d58000071441d640003072060070081624081d603084450102d0200800d15001600901500c450741200340700354142c00c41500945004d0085011019929000701516581d04820001415010341041400b560810000c500c0201c0e51820a01c18914850100724070348491a00094080300c0203110b40c401441840103103c15140466540d810540900e440c118581c124000644c1024660200840602c03c5000040172808004044d100700c4800b100c0000881e038880c2000d81c1d20100403200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 837112859 1250 837111609 837111617
    0x9240904150b0a090f050103062706110f0a03020a0206060301270c120b090607090f0509091005090109020f2430060f0301090b01180212041101021006030201 69
    0x1d5a8040d1030140d2162646000081c00d4004241d601e00780e4104440c3d211081d002a142c81b40010b0051100d24040e660781c1c5400c4652011004595207070b611100c1c50031010042626031984d000b20004c6d120f41e82521500e00714000e030507550f41441c00340503000f507000d0624036001d0700451001601c60f28062084030110301103411040d0391121280031500c49182c0701602191210881040441c11110310550400724600c92007410300d2a0419001042c9403903c02041041003041500040c40750844101c204802c4a1058030060025182c003640c0a041018200a0032881e61401c0f01704511090150049062580252108020711404100303110400c02104a42c0c08041d001c03410154070302840710004d0507020500b07041410810b2202c0f084424007508640000040744040c07003071080f10710744103015010004040f40200550041c82d0741d42c5400076814452410011707180b110030991030344e03682c04462064058085407a424a002c4c80c1541011264007405030040c0b08a074007101c04400148210801d52743c058407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 837114109 1250 837112859 837112883
    0x1050708010e070e0102010e03130f0b0405030a0201050a0e1f090515030105100903150204030614061f020312011502070b03070903080d09050d082d0c0901020c09240904 74
    0x12041e84c540c42c1c404030f214119940c4d80201442c03c1d07024000340620070030144034100c0e100e00e02828100c0c48480d5410000502e40c04210030000c6035000181451015420b090241d142c8140c5d5400361000304948142541003251008101100060322030b0449031212151102742c1225181c0d0248000046002505882031004000500c00e51400e105260581a0545050056117440383d071601c01e42e5031500030024110340c000c40c05008002c0180645e6039101d80840c00c00c3d20500c0c0c0840002c148440346540540c0355291203503400d007010f05c04e200b150200c0d21082c0c150a150f5941c5c400c0850f840b410011000014040c0300e10100783d250800b01100c0c0110f4690b50788284d05d03421a1550f04003503120088c00640250b1f10032042c0c001440c18011030b01e401c685500d88074035602e80ba00883d001252038840c09182c0c0895440444079020281c520a50052441148540c03180c0507140140e14249400c40d05a41c0700c864641000059442d103480303282c50594144149481000b940c00b07220540006031070091811000c40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 837115359 1250 837114109 837114121
    0x60501020118150b150a092c070c082a16030c030b0c07060e031314031b0a170a0303150f0b07150203010f050f0f0a2309160201050708010e 61
    0x30300150b0413002d00a184400798008050f0407549030340b02c818803402241717082401700016070117452040324990442081d805150f24112151041c5140100f04800740326541c20301c80d091114840540307880b0503401c0d03942c86a4030000d41407103840c0c07100e8070031142440c851810120b401f44042d410a4080300d5000380b201205c141182d94920410b90024002d0b03082e0322050009002140740303800f8136051030074078802660750382c502094241003201c0b40d5008840b20200c2c0c19001f00490303d00081460240d0794414842c0c1042544000064800001e5031001e0b00100305100d201102607004150700d804140b01f07850402114030450512814003082d0722031034202450800c4204180c035903100050006600c640c1003560f28401150341c0b00c01326002030300f06500325412280148181c0c20100140081400219681088050080000350700203601d8051100421449419000114441100003412000091002c0301d1b41ca0180041103243c0c1c8000646001503003071801043c0000d009060341c506031007a8510011a47c0d40700 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 837116609 1250 837115359 837115361
    0x220609200f09090106080708060306070915050f040602010c1d0904080307020c0a0f05040f020909060f060d0c05130e07120b010207030c080d0206100803070f0f0609050106050102011815 81
    0x400500d000d080700801500003640c0e2003050850203080780f80c5607003000d400c0491009280c1c400081126010303900ca18240507513150860130000c110340204d0b050b400b60214464040b01c09000d00384100260800100c0c020480c3d0350190011020305402c1c4e6154501e00800502d01c620740003501300d140782c00c082204049400300701d1030801103a002005004a40304c19140e88003050b04140c172a4007002d14a2071409050202d85018010f0f207856404142d003d50400d0135090000d038141c4000f5041034810711580242021a40390032098648000201a080040c0020140c015100d030b0300520007840c100c00110300204400f41401380c0c180c000c124584e64000d803203c803151414018014940000d05620605500000107640084445c000d0f02511020f880c1e01e1500c1c060207864150701400750420120114014403107960000282c4104030341007046c503008140c0c0d900300006c0c41402c0782000b078203080c2042800c0b01032110540040044410030303402004000380c5201c9018040c62100401444082181007018140c651 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 837117859 1250 837116609 837116617
    0xe0a030e1912200406050312070302070803120106230304030e040f2909042a090914060606090d0807020303040b1b0f0c0607060c0e22060920 62
    0xc07000c215180c1d15910307502125180031004451122085209074201c250700101000102402e540c1409283d042c640048d4032075201d200c0c000000880411480207040c409c102185c01451190107490f5103000d04c0014a6050009000d8040403030300520207410682ea40b0092800346c0703a603e15081e804d540f1030765412175201d072128403c80c3d44280c0714400351329540b295110f10b042181030b00321010744480c010a030140b82101c142414502c50042c590400c808609070078185d03c0c1c40ca441c400b291291a0782c8210361220640c040d0000d8406a1070807402d04104041b00c4900c5000c0c440f09001c9910650390304040058910401c418160480c0c1c2a410000000b0740765400340c0000c0340b0040a0300d06141c1c0340c80c0c4244040d08122502421107071282c02d154405441408810f005190200c0179008040403900810080c4c821008000c0c8810f5a400380c0341c0c2c0c40c900c075400308003510000034041c000ca400b4481c03224a001840e0204194400c1ca8808002007820303591150313044400c2c801900e01417080c3c95020300300c1d0740e0700 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 837119109 1250 837117859 837117889
    0x7060e0913021c110411040329010e01061806140f041802030118270f1506091a030d08070909020705011a01021f2007050106090e0a030e 60
    0x4040706100e0040e650a0380340d12030680000c4a10642da480d40c107201c0d5181c0c0319240c01078000e41c5801961a00790310884110740a5941100380c0c0080c9007201d42c6102011001c01000d0342080304400b0000c541c607100380700c20305d0403200c072a07071100d5601c2c03440b5504445d01c075040e2040d100851040c074040448075040c40081c2030840e590710300c290700f8a544c43d800e080320300b5015416040780340d40c0040140801511b540e41c148400100010070840f4131400d02010003001141c0b20740b080c0b488034071100072040100080050300c0e02940050100040c1c503000a41030003a1110b40602024642442c071150b10807910f01441c8a42400001c0041071000088c210689080802400d00010030809c040c01180d083c04500091841c6441100009014851548000c0041c0c00e6508891b0454201440c0c040c245141c2400e140741c18003851000049000c14800300b10814880e05110080b40355000c1450030a20070194400030407114000814051000090055a2107640c1080010003248002e8140e49407030400d0381410940d21 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 837120359 1250 837119109 837119131
    0xa0209012304030506151002160e06040f0f0c02010b04230a0b120a0203011103060916030f090c0512070e18030f0f070c0b030915190504032007060e09 66
    0x64490704e801c0e0511100b115503640c0c20444070085411401e1420f440171103041503201a2404500b10303403807a50010b98a04c590328984c050240400c506c0c0d87c5507030100c1d403071606101c070402c4401c2c51464131038083e110841024015510b03020401c056400c107402104d00040c07215880700594004061010304044002e410740340030760f03030394001d03110f0a8580181c03a10001250800421892040f03104140c00d50b042e4080200000d14144180102519101001c58201c000c00c07001066100172040100c2c000c0500002c1000c40724100350010080c00001c944803015507030b0586034084010070b29070400d55100014814100b500502c840060003d42e00003281002054562040d00d20380500e00880ca003258003c41d0781d9030042a00002d8100c1013000d0407104200402c64008031a04600c1e042401c0307500c2d900740424054044203031100248540704c4590700580811203480b010440c50425040041050702e400800c4003a038540403140301c5c29200002802001c44900390b60300360780385003100e003813059211024002103007403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 837121609 1250 837120359 837120367
    0x30703080d0b10050d1b090501050d0e061302030709020f071401092f04060311010c110a0906030519020d0f02010c15020a031505030d0507020a09050a090204050a02090123 75
    0x80e43e00c1c41d6040c502c4080b00c1da1125191505601407100322000303c6802c0825990044124a0081d0004800d03800c64100742031058840d94042008400340c01400c610603100e028030810012513110324520045c031b0900a5003200c00035626031a00c17130200d104900301030601c8042030014400042c100304103114400ca00c0400400c0481a9036514080900d071443b050b1031a0315403503a032000101005400612401045606100b514036645900c040208100300302e6040207403d201c45424000d800040d0b002e03003e406002d59040d140e5441d03007100280300b9404201d8040c003139040442b4401d25501814003199400a1141c2c030340311900d80e21604050b0704564100d061029480070715010520301c00540144044040c00940c0e075001424000301200c1506610004482231041d003072046031030002d03000382002410f01f4001d40d0340009000045a8a0300d03640b011807443c1c00c1c0300030004103880c1d40e0401010303540300781d400b800750f61160b070007044c1079000b0348203d18001903005a1101c005524000c090b000e00c2c000d54030407450 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 837122859 1250 837121609 837121631
    0xf0414031902030304020f1e330a0f1419110a06050405070f06090b0c190c05150306060a20030d0e0715020d0f020c04090308040309050a05030703080d 66
    0x5164264014025800100070171056040a0640743c640c3c05046502d220b00034000080c0041200001c40d44c98018240c0403416401052004100f04407440a440c188240c01c10040910401d548110080e0000408850520811601450b0703040030300c42a09c2c400c6800c0c04200700900d402d180c403240000040000110a80506a00c140314000a1502980c1d002c280b40c50315080040c44e00d01142e1141c5042035269000704035a41c2e0007500c1c0c1e0107580e0500000d960359800740020b586040d84000c0c4410000e07c030302c2144800c1144041d211070490704199003680034440c0a401a682502085610b41d42005081141d4800369125203620012035902c448210f440185aa200903c0d60b08002641c0921650b64100c80e95a00740400400c0000e080101c0240a8000c1009000791110800000ca81c28040d002c1000540140244418003050740f014004025079101800e008040703260644060700450725603075020440b1f0030140200e0042e42d6000d0001c041d818034680e107042c142d910081c0441e00b440c1e41d8555a8071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 837124109 1250 837122859 837122887
    0x10902071e080d060b0f0a03050604140130021513180b18151504080d0f1808060114011403070203040618050a060f0c0c08060114090f041403 62
    0x4001d070182000d00d4603544030b10407076400c9034141d80010000d00c60511034076140c40751643c01c031a40b40300c01d403801084544815000c1000313444080e00d624403100c1403a0010078001085820400002100340d01c1001687c0c0c541d2801020f03840c001006900040c003a219500d0640b803401c002c001d4443d807110a2480707559039540c511441040e03003041c0d580031070b00c2d00900c0c042880d0054110900032044119117415040ca081031942502c6d0401415015240032601b841e0080c0341d600030b5078000d264150550700c801ca0000d00003090b040c0c00100010106c2d01c2c0408074000d00101c20901030680d107032180141096401c0c40362041c0140385d04086541001250851095060260800b40d07003d1085a00115140c0e410075101508d0050362083d106030100b0410003c0046a032407480c400100c030014106000d680c1c0c260202261009481407028000090101001554040004105049841001007880c110340820100005803600b6140000b0a4100002203008180c5400c441007000c10941304483c5000002e02e042d603 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 837125359 1250 837124109 837124163
    0x105012109050d0f14070b0711011a01110604031413030804180513150518010e06040201080c0c0601171507080a140405030a0807050405032b02060108030301090207 72
    0x4070755401044100c0c01450f040050007103413840d1410314081c14207a0824804090040c48070217403610071032201040c3c1041c09074050041c54101a4001e10100c0703180758000540004022805002400c60000a840c256000c5101030041d541a40c900c40540000c070540801c0d0b401009070040d4401e000c0c1d0340080095901d40040004001e00c84804400e101050b086004030703540107004002060200c0003000000380140110601c941a500380042c00d912601d150302012000700d104c044003903181640f41e00410100040f0a40310f14405d0340c400e10303c3d0342c81540500c521b0056090310012648048010700c600b03044031200103d03501001c81111010394021503e641079503000e460742e0000c01c242c00c082c096089034500450140e00364500e030030513031410f19540312652489680b00c50801c210030000482c0701544a181110024880102140c03180140c8405070741000e80031700810700170300d03200380000078100d40085030680c100c44c2990051400c0d070b840c0c580164069446590100d461100f007135129000c1d01c101b41401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 837126609 1250 837125359 837125363
    0x1519031b11070f0f1a12090f01110c07030b0c09090f2a041509030b10061106010609030210050403080d1e051017010608030703020321040302060105012109 68
    0x3501500e11441c1e40142000d4040e00454522414503000740700c0c2243c02c03121031007107030b110390103115800100860034242c0340501c03034446c00075440c000e05204070064005020a200c0e960700d4001c100701940801c0c2e503940d620030030207400710039081a841000403400310020b1a50200c2c9032900d041c5001003502c005a2102030448459203460103642c140500750404c68400c0c00207c109484400e8216092900c0070f1030350040b4400e034601e0400188818213414420620403005582c4402a14200e04094403201d9541c0c0150140c0303800104080d29140c4444000112a07040304c003a501c03211255030441d001c1c800352080054807507061000801000002540c1d001c0240708588941e00000307020b24801031069200d0110b09080c6101c18101000c1c070040741c01ca103500030304840c40c00003140501d2102c4510f0b0741c05482180d00050203400042000000e164021005109603171028034880024104008039014202c4180c1e00030300168044e03401880035500420010420030450311050100010a2203524141c0b0160081 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 837127859 1250 837126609 837126617
    0x12c0715030c0f05030105060315010e0d12390503070b01140f0d0c0608061206100504050c0304170d1407020c190509060d14070b07020a051519031b 65
    0x1401c030349502c614000f0029a4610380a881c6502d0100041c489000190038501644200b00080020b81e00400c1c84600c0104003070700341850043c00741400302d01503007030031802c0d8081341950305400201700c95051010842d58804001038034060b1825142243c902082d50304aa503884100f28000100742000403040c000d103542441080d0b200a803c0030b000a182802000600130080d04098900203181d0911013010b40348a0720f405001da0303451100181c080c84544050159a0154a080c02005a000c41da01c0d401d50340166000d124503100c0d09800c404901c03007201c0140c24032004280d124003035804040204020740c0001c1c0c0115441250010071103c852060b1800c00250740201c11a005a04041c404070000400e6071030010002c80c642070100307481e0b2000500c594815a1030300e54840c100040e10700c40c408248038207001c4071403003900d032840100703d0b5000b51003d9100c1d11081c5400105881c0038506800c50b07403003043e0114107001160b8100903100200040070030030305440745074001150300c02ca6084540c00b0600c4c0e40d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 837129109 1250 837127859 837127871
    0x7031805031306030b0f010e01090b071a06030708031603090f08010515030c030c010c0606090608030318060c270303030a0207060f0b0105070210181205010b0102012c071503 76
    0x40b00e4080c00c001c1d980481c080c1428054a0141d5607641b01d00c885020b8820700f0710110715a003580040b5000e2034150030035040783e04041051410300c044804030007103140a10800719156201c140c1007541d685070701c1c4070303512440d40104104100c5145085154507814031a0405002e1b00d40c07a4a80f02d003080100c0d401c000c0980c0c0d9910708100410110140e484002c48041d0081c104460811000c2510340f170300340d8080c6044c401d600019004001440d8010300040c001c0b071108100847e280e40000d0388076401907410308600050b00140d0304010784046002402107045844081c54900300a913030110b02e4408007500c0e00743c5410205541c88540303080c0002c3d0710174904c60000503665585c1c0c2c50500c5c1107850002140d4423551030982000c10301e17600032045031001601105d050311104040001107a201d2190030000c0050780e50040d0004d660000b171041e0071072683c428402841901c022800490885a00034034030415429401005070250f00041682034110501c0380540f04417580741c103210211115034100080001b030340c0d08 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 837130359 1250 837129109 837129127
    0x90203120306130902060415051605060402130c0f0c02030c04050a05070311070b07030e0a3203130302040213120f020307050d031e09032415050312030703180503 71
    0x32030001d501401d000c410800c0500c1500421000e00960140081041001322396400c694014010b942c2c0c2c40c01d81c820141c24800541c901036440c0c400685c1d0480c0500c10b03c016441c0d00b04040e010348465522690785501c0f18115520044034441a032040c03e0f0b030103006141d118851b5444500441740300308000c5c6004181c1c1e040c8500700408440d01d4a416407810b08062004000080c45400e16039041089454040743c0d481c10300034458203014140714014905000c0d07429030855811803210f424652242d10f0100c010884c00002c40c02c1d182d129414400c60000c0c896001400107281550103401d441d0140380e0000156900c60b0314100c2188d101003400d0342c40b2903130989a03c0841c0340400079031000d48800d40360118031401030340d07000e40040d41d184000b030800e050540016454512a8030010000d58000165109031601001c046010411107286108a5400d0408285000b000046a00d0403200e024005024030046601d8140b0750760400340c82e003000c054486a1105400d5111942d00ca00d03280100061a51040c0782 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 837131609 1250 837130359 837130369
    0x90309080105091b060414191809060c0c1a0a0213121704050607260406080702010605030111090405090f0618070501090515130911041a071212090203120306 69
    0x80710301300b031051104000030f221401c000100700002e12019100660340030300070410540038a201b5002410b0905203d14404100ca02c0d580065034914000c050400c02c0e50020a8100c0d00da003045c074070191010018100b84c03048075070810038850744490111001410000c004420140c014026804000054a070f240c0240a0100c50304241c2d084140d0501001c0ca0310b0700d0300011448900400c2030180859a9108d200000103c1070603074131000b4405035510304d40c0c9984413000038082070400d484450056107050030209e42410144260110424008060390030000180304000c0074201c024941c1181c2c3c05607900b000c014034070412065015503402c000c008044c6d0710090b405840d0001691044d070400c090b0501c01c1000341c03141c0e00407504807e000301d00960388004140f14840384200540c0402c0c1c1840c903290b0860510601000680241c40a0608807151820310540301c0486019280029113600c81c0da52500c4542400b8000100b10b241c041170010928403410b40020f41081111350b5038881406002080000324540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 837132859 1250 837131609 837131653
    0x1060e15070b0c13050402041d15010207170f1b0108150a050f011b0605060315010302150c0a0f0f0b070f02120d021c020904051e0402010309030908010509 68
    0x8003903446418000319071506a0842d0010300314240b8400001041d242c0f465504410202810010304295a110303a200d000542940c0d07240d0f5100403403001000803a4250020300c0e0704010716030050b4000d080380350822440543c188040d0302846050700c43c901c1046071014081c42200d0203480706010b400d41c0c51030510000b40c2412802022500d820346a0751018250740d403080d8031030080e24001d5074080200000307039005032212003865844c0190161880a10410861310313401c02ca103e10700c213609640407440c102d140d40082d04401c0c00025130044645107010f0340958094047c0094001d200102c03041c40c2e0941c0c0b1100c1041c103003107a09440c25840e800040d0705210118003525002005031070454503031145060b0003500d400a120248403003910004000c04c5400c0300303030181c0f491242841c0d40f0408032502845640025031105044602990500001071020b28050504e40d072100301c00303180e40019995650044004103826101102442003400011900325000d214071845405524010009011110b00354078034104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 837134109 1250 837132859 837132889
    0x4050c0307080114061c0f061d0a09050703020d031d1008072f010608010f0606171312080f01080c0109030b13050a08040e0105011d01050304050f0601060e 68
    0x100400c28490300c9640821100c1c1124950800000c15880b4840000c4c49032040340d0101071507404c0e11641c00380203d05940302e8019041404410005540d072610381e0b54410658960084038140e0b0a00050000ca19640019003000e2140017038905850326640055a00400c090059001580d16034200c42c0d0705514508000080307408072049000179240e803100509194005010004000c1c0201e03000301c003d050361256034001c1034014810b042400344001014000d03c12485481000c0d82028622009402d59114007c1aa140c3d039580300d4400d1040303a030003a4100301c00340007101051000c5a140c40442e001000f010b4900703125541d54101e0382404031485240d1501a00304c036040e90015090000c00d41c5c0c0000480080365804600548566030744440111642c10046c8062b00f14004c00c0111410481640300a000b41c4882c1d07850301c5400d90725040110b426411440754090941d04014510b220381d03018101440d0f10030301c01c108444000d407500741e0ba00c0c10000281d0128010070400c1e420b4002d60b04d0603a0300300c0f14601e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 837135359 1250 837134109 837134131
    0x80703060b191202010e041b080a0b060301060f090816081005090d030e01110c0f0d020f101113140102070e1003020118030c270c0c08180a03050601050405 68
    0xb80c4000e401d4200c11015100701c000140b2011540360031a4020489050709050060040001161201000310b891f9100e00842c0f001a8544001452070310b6548609454a240645000d04681c20030400350707414408a0500f0040c00303000d610002c4c1c1e0403400c000100c0d0082140580c0c040f660700e4401d216180070703858003e03020910304120402688480001726030031040414034001c1501c0c1c50700d80d05030b030042040ca08042a82c0c0c82c00250320100080016151000c0382001c02252945080c1d84000c989071603002c41804881d0b008540101d802180e0398100b41d1002086c064003514045142200d501591010b500003209041d50148242403581c060041c58001c007c0b0b18001d6941d071a00c0c6522403a9941e013400024140031251408002500c2d44401403030285900c00d600c4110280c41da03800d085001e001c044840d114010b030071007010220b030721030140100701e2206895102d400f0000340e4400d066600203202c99050f6031084551000b89607240c0c101040154041e001901282d41000240016200001c102010030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 837136609 1250 837135359 837135379
    0xc03090201120b01020c0402180a0b03042105161a040507060807020a1a15090c07051903021522030c0c0e1603110d05092506021213050a080703060b 65
    0x283d8010401b81c8090b08106c40040e034402d00c0d000510f451113442800305821105500001c6500c0c2c01442c002d500460080c0101c0040d00d0564180c040444003840c0f145002076014841300010a00020110350742d0751088141e810110290200102c6005c6d0485040d01e0b554041c1c0c42c1000403e030000e18180e008a524405807503404900c4d140d03a1030300f10007001d001c41110003400000f020304400314056005010001c1c5050514109021812800d411000080d591406103481080c448810380b142c2c00e00b07442c0d06070081c00742c03110701e810750800b40e0714000d14006100303c144c8500a02d2445200c0340241692003902c58800b0107005091100c8590403d4104161646008041c4420032518840301d600305400e9150215440344c400d00440400d019085507080d030b280c14002071180701c03540441c0d8240d5088a00303112524982c440120461885030381e00c078107405a04000ca1b03600000f10300100400c580c2040600070110260741e0404a00401903d600410302c07904140000d00400081d40144650b13520111418805 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 837137859 1250 837136609 837136631
    0xc08010f060c060e060709090c0207140405040212060901022508040b0a0c0f0c0e060415140a0807030b06090c18040230060f01031401150504090c0309020112 69
    0x4040c4240079100c24882e80700c0002e010003002da00410344040300c103c00e4412505010801522180d0b00c0d0180203112800c0603d03125903184001203100071035000c480c0100d40b0552400a103c000c0c0401fa000303a0b00040f110880c20746c408400c2218071b019407901000180d03554072440c0300344c83c1c03120f0568602e174000c0034003188000829041010350701940c0f501800240d071500110000d03103e214694030000d017415101d08110050000310101c0c48215003000c085149640e540f00c0c10002100c3d0395003103185000300721400502040900201d2500c0031030300036006005550b20380c1c09441c6010003942c011604466407204001e50741c106180c105801020024003903041260200c0814001c202420a807406280d000c12900c0c8003620000c0000c118a103200c5803000b443c9205565102044070481d20700740038841490500703003154824407891511600070510b0041507420f04071000014504c103103412040120510000c11443c2c00391091b494040529140050145c070544005400f080d1505034406080b0720b00810220 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 837139109 1250 837137859 837137879
    0x30d2a0903020609040221040809011218061815050403110616030b040603020d0c05030d050f07020607141b030709020f0d0e030f0c0601030204050606160b060f0904080a030c0801 78
    0x284c00c3c0d4111800340e221900b009003284000e100240a010030880c8005010603c40001e00401c2c140e034013030780c80400c643c074400101d206442240c80c1001c1c440010a440070041100782d800060f20184e40542410b1001e11621845a408166060300c5500e940c0c540610081503003080003401d0600350003000e0022071400155108101100c0b00c0320078141a201e500f0042b05584907804000510f40c02000c691b41549582084020880c1c18001d15029204507900e114401d8001d00554184488840000d03203020f00c16400d110403074110000071113140c241d14404040d0008240700031400c61082680b00e81042c8201801c0618002c0ca95003c0c08800b441000000c2e03001c0c1c08842182d030b0200c0c240102040b060800c1000c030340795200d01042c5182c20350011840301c1402d1000308609040b60b0013242e05115a803100d200b0040d051141d9508491911080c0a1103c00500c5940c0c100c2d511680081407140340152507800f00750701d4881250203c41c1408002803420b1165018402c07480800103070303d4007d44c698109594030f6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 837140359 1250 837139109 837139117
    0x903011a060a2d02010e15011a0903010603060905060a0b06130e132103060b0f0406081015030e062a07060915200705030a030509030d2a09030206 64
    0x2204014801000600c4800c615140c145120b040f0001041d5041200000900900b0300c46000d50076801001c40e04040480da080045040e0b800712995501224950a14480d00b68400080300d074255481c0d002c000041240c42c494a4601030207880a000c8074603099031204200d40d08050020b108480c14803544049610b04140082a01c0306070300c41405649074001c4800203008030318402444540f454000c02c1060300c0403e50a110429162002c2c0f103916141e400b420060300400051318a030340702c140804c022040c480e50240d03412080c9501848425a112a02c0b6021b903040905000302080d10f8552644101c4020002a94498850404504044c501080645a03203040000602c45590b000c41c0702824842030340d0044100e00d51042c1c0c0c4003081030354a08448041e00302c0403200141d1030344601142d04a00c1014040743c1c84264804051032510030002d0f01030b00180805045101c080c80b0130710580380300c15100d2265242d80d240a4034081c8120719143c00f19524903075140703800d004200d00482c1c02c00058131680117031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 837141609 1250 837140359 837140377
    0x170f0d0807200a020d08091905100302091203120708060906090402130b030313080f1f02250c090b060c0712080909070504050102120301060e0f0301150b0903011a06 72
    0x1840018030782c101460885183c0010b5400850080c28504000e1410014021502c007030f144444801108001804814400c0c400c03140c0106050425400c6548a40e0040041c40002007031240c1c0707103403a403005900e0f6400621130403400c0721321041404003140e040094180d0140003155070324070a2800b200460100403026000078007540760001c01e641081c0c055000004004405400c90780c50385880e206c1c0354420707107261146202038010700c01ea0302100b1002084941c0c020f0821001c0000580e480d0340c800000703600c40281a081c07441d0700c007203000701c600007010f02105e014015035840c00a281030510000840703260042952103884c08120100094402080b040101d03001c265880301c0364511414101e541703100d5424040d90003601c541c10070140e10b801078054801d0f1070084e400c40780d0b512800c2110030150300c002e000e60307030129041c840c0c042c500340b910300e070507641300b0305d024002040103140c0c11101c1003d8070f4583c0013000142404101110542400d128109101000506404012041d140071035010310500c03000d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 837142859 1250 837141609 837141647
    0x100c0b010b1c05220c1707030b060409080a0f140c0105070f02010c0e15070c0b03011403030711090a0e100902040e0c1c080f0d0903170906070c030306170f0d0807 71
    0x4d0fa00a1101e4095504010140901401d1b80034800180b00d0b9150191030008440400d40c0c2d601250301401d0500c0780b051030542c06100b01348ac0000f120070a036000c41401414008110004054080f201440000b400b58400d170030300080380e142007501c40603002c5c5504800d0f9108580c501200c60412980c860300f02500da61341030750448640034840d4250505441001c4001c0d200300864071000500c60342040c01507040b070704018016072641d8400e50801d13840b4825024050301307000c40c4020386042440c107411003a07001000104005031100c0d42450107402c011684041d803803026036502c0100254107190003502800e881403800b51003c2e4130705800044050f02803d12040310200d81c203c10790200304034402103503481c492140d912a21600c8102030381e40503202c00801100010340032040304500c0366020072403d004014241c040c000d5541d89440440d00c000c1c4c21002a820140c4030003000500c0c172014038042940c03014440107060b44640c4e11340714500d000c01100300c02013000102020050341e90b07031000b843c0301c401e204000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 837144109 1250 837142859 837142921
    0x20d180b0d09080c030903070f080d082d0709080a0c060c083c070c0302090a0212011e08031305012114190608030306100c0b010b1c05 59
    0x5a80008082ca01002800564000381c864500c5030300102078a100e14088044541c3c140d203880c11100041d050f44144002d41d40a11080c2d1000390140c215142e2105145614800316a1058100304a65140180e81c6001616a00c10304c10882d0340841c00c08041e00c403c1000341760015640d500d0001c01100c0388901003c12810450702020065800100c800c00140c44185a107004549081035401d441d8500d61500450b20200841a91032881c00542e20f02682149000030800c0ca15001c4c803580180090190251590800c0130408030601500c0950103807620181080c50040859503002c148400da0700401d4003a401401b03401d00323410b941d00c1e10702c00307a4100780b070415480f806050130043d10035005000700030028100700e80950100948a65a4881c10a0364007a040a45103540900c0440303000c1d008583c1250810800103047d418240d41d00b5000c890186170440c468403181d101e08044580c2038012200b201030008100c1c1c458210030014041d500d15802003081103040000d00c2c400025141d54160407402c2c1400c2c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 837145359 1250 837144109 837144127
    0x609010507060c1103031e01090b010806090c0409090803010509070206090d0c210e0102010605060306131d2d010c05070f0302011b03060302030f0a0b010e040c08100b01020d180b 78
    0x5414544c000410404903600e9003041304c5400b4031406d20b800700b032070400341e64000000c0603100b900039005001010f0f15201100e4840000748800e064008100d8508000b0400001841007450b05c11040001d02803402652254105420171040300000b624510445d8007401c1485458000132424072500c403d40d09002d190202d282c500051b603000d2045c03a2180c4903c003608a50201a04254086184d4200342d000f0003106441c2d50422550f40001c2d203440f500f05c03a00b03490910281010354002c0c0a0020700c842086004042442060720384107001103080c00207a1484101d0001142c00a140105034803031500a10001002d038000174403d002d01600a41886c2c1d009004005042c003e6001200c132003030066040a4442c28040007401800003440304a01034803518800200c91030b030100c0c240c6000d079801240313000d03981d1038280119211440584141d5085408a00000d0400410230401031045220040441c41c8a240c0300064242040d0b50941c0c801d0195102e6448180382210f000715050751080e02d0b00360f40f224159 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 837146609 1250 837145359 837145367
    0x10e061e06100c1a180604080f0d181112121813090c1d0c07020d15021c1a01020c01120603080304050f0f03040f030b070e060d06140609010507060c 65
    0x1007140501800700140640075481144100b0500c6001100c0e40e5011598a817258295100c0b000c403030150420703100b400ba00c1448141e0000602150002c00c4020a0707a003070103c10700d4240855408200d5803548000c041c4e52041c103000500c003004a4000002d40b080c59000c44108602e03109184490440c0b0702c16480c81d00056849401141001c01820300401146255190121110089007d00d202c1d07a04a04030b000301010b40c08030b095101d44540010741e030900f07203940d00380310f483e4404580882e048582d0024504862003a403020700700c1e800d4060201907100d400b201d9400220b4900e0a80c1c5c1840c80e544106003d51a42c0010301c1c000302c510f0a282c18265248100b0592000742003a800040240c0c00000038042030160015142d00d019074003800340c44001030b44105032540d0344291b21800f8040e094029042000c01c0441c1541a8849403508110215075861303000248240c0c8510203040d03c00b540c91800b440702e40d180394680c40f141d000507204e0901c3c104004001809a0054134401810700c1d4440c18408030061107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 837147859 1250 837146609 837146627
    0x60a0815010c0501090b041b054605100f0203030711070f06050c1009030206040b0702011d1006270f06050607350720030f010e061e0610 60
    0x400800550170076182684441c1d10071345041c1c66041450705108101c214820392207044900c0140591100007011941408441a080d41e41da80500c01c490042d840c005130b0310f00c80c20b00f031003d0300c0c10f04492810a001c000f00300c20100e1001d0100250b201030040015000800c030b81d08085a428180c20410075001094a44500303604040200c1c000c0690006a03141c0010203032141c1d0701650184c0d020304004800b030808882c8032a50240050b40400041804030b0004217015801850510010950350707807500761105030411080b0b02c0f13601e96114844400c0c0c0300c1401c0c46500c015290040900340101d0b0700d44c9505001848035861307020825035860966540b2525548100c000708400383c0b005454414a003441a00c0516042c08039804141c0ca40c4080c1c0d408900550141800308280015410000540c8070074101c181c03e0309242001070491400140340c0d0303a0070401800c96085a000206d8078155003010b10b8105107014043d1101c01408240c400250100b4062086c2c1c8503000b81c0d2100c5081c9440b80741140e035024 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 837149109 1250 837147859 837147863
    0xf0105060702121c1d03190c232e03020c0f1203190501060f120e06010b030114030c030d0806130203040c0303140a09170a060f020405030705060a0815010c 68
    0x220344c00307606500c1446040701848040c0107842e8409a0121080310140f03503040f0b440800c1c1e03d40c006544c10389482d808440540072140c028501c811182d62035502c92440503d520360788e0075030000c58912105491801404641c2a6920407044003034400e0055010054840d2002080c3c05041c0c003c01c1021096000f0850101300301c503010203d900e0254115211070007640107541c500408800584034074104d080314060541220019940d0030010998482d0468200760b0410607044007684542070100c1000307040024178068030613401d145603654503041c0014000300d42506c00600a800005805a403a40c0103d0342d5854425941001c002c02c0d580d4500164000c0203590900c200c0741e1011040c0300602009040d001c2c01d0301c1c8261903071000201111500c20190264240c40c5c00055a80542072014040c25004c3c001518490001c54240e200342c0d07905c500a84d280d208070750450383d6003c00d00f00001d25003000140000c10b019203555103020100d0400401c9a1002020003481ca0f11902c17030f00c021030344142101e1104075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 837150359 1250 837149109 837149113
    0x25050d05210f09010b060705030423090412021905030f0c03090307030f0b0f130609140118020a0b09010915021f0f0501050603010f1712030403110f060f010506070212 73
    0x11a042040790300b144810381e030010543d0b2170b060020020742016001c9410140d00300c401142000e151103217503140c0d13003244d041900000e40c01100040541e202c2c00d2401c0d010b140700c0c0000c65071207030010304001c4c46d1030b0803203c41d200840d01c1301c2d00080200303401000703c0342c059a515010b541e9900090340500d14601c19882000d4151140c0c600001c00e10015082c111606481090b02e03400c0f0b40c64100b4001c07402c0384182d1741c07484000c200c040203000258155106d005602c0c85188180204000c41080c0ca08441207072801480a400340110b000451034a0050000600740903d407490401c003189000030100d0001d4003518038006503801080561030b0080014180e00c20a0754030311004280705854050140150f00281c141c00c07810580046454070b0030106480c181c0e81e0000c1209545407800d82c808a0707041c00c2002e4610140100e800c203810145011004611403802510b404284d14482200c162410010344888450f540200c820f0002c601101100f060444208507045505e440440c00000c01011072010107803028 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 837151609 1250 837150359 837150361
    0xf040b0714070b032a04090b030a0b1509090105010b030609040f1509030810050f04020a1b05010c1209020901090c17010f0f050409020603060d210525050d0521 70
    0x3422160003c40c0725001402641003600f4000b108107544180800030031710800c20a02007840301c0c07a4154000c042d1100014200c1e00a42429211710b1140f2006403403800701004809091034a0742405070074903401c449048000c100c1503242041c03074500782c040544580c4c030a0b8980c5000c6400c0c0032907000784d45007441c0c0010300d100f0b64001d9291802e00070100428118003184194002460300b1100040c1c2404032103015210b00808543d44003040000d61041040000703000b11071616000d11032000140301c11507403081000043e10801008050511040010000e000908007258000143c480e2250941120b07000180401c40b405000011f0b42d400c0e100c1c600000d1103a00744d4000144010600c81c178101101c0303506000e0850207840b08280300944885000180d0450802c20108626040186400e101e86c1c4c021081514002c0d03138044611158030184015000007200030504070030f00158002c1220a4030080d050314188002d5999813641c480e90015901000d200010459440e08000c2c06d60041d524071004040c035100d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 837152859 1250 837151609 837151619
    0x11070501050f0414150103230304031214032818051501080f0303010e1803040f05130605031009020f03070e012d090203040206090a0810050c0f040b071407 68
    0x1406004032011348040e00b0b004010b240740140440c0d4280d00013100c502203540d50707086441c0c406169818410301c40381c150501502c04c4514405001810140d885228100c40020720018020500c5034081c40c1e000308000c1c01c00c140324030740c804414001500d9880c603540c030404980b60051400104982c81d041c20603282d102d049401041720106500414002c0b090a84c41540d0b00c90200c50358500c2081d03e0043d00340d000308014040d80a002c9640c03031b88510400c56500b11009500000d9045400c1507014081094290b0001d1046150901c1190104428464100130310341c81c4c040042e9541490b600d9240d0305540e144024403d5442c0c0001040140c040a012600201d555203000b003c115400d01c5294003a0580418108140c4180c0031000b0b1507000c1400c19000090400c00d440e002540060001c9a200604100390000358803401c031100d00130500c2e0405042c0101c00b40f09140c00b6640010301c035107000d2a04220011580d122030301500d040d41c3c0381b81200c0380c440c0b0840c03800041c000c6641040712220f205200000038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 837154109 1250 837152859 837152881
    0x105062b0218040c0807140912070303050a030b010813080a0309020406230405062d2e0f05220306020f030402010f0207080604120c0c06030204090b0d02030703061107050105 76
    0x607003010195810844c000d0120801c503201d050030307200100000c0c00c456107181d81c0c0c90654042c0a4607a0300904020b03140040c04001490300901c1d90085011440c04074035503606039054410400041c50a08000041c1c0c03828180020304650181802000e030341002c034640440500c01d91007440015400f0b0b208000b019240c60501d041c0c81c40b94020803003010380c1d800d0150010b003030500a9900560b006801070384013078074140580d80a00b0000d052503100c00c252492107003041c0d580d0040c0342d180840c1c5e040d40103407090480034a99019441c5240080901060024400c0c00c141e110f07086403450a550310084068028110b181c0c1c6030000654406040540040b86a01c01001c2d42c0d001107000b076100340ca42844140382254240e0b1540200e00c18000c0d02e4012000180c08290058440362402d01c4902c0c0441d041111640c4034407141e0203540003d000242d000c202882500c16a00c43d40d030b0010411100200c0d02c1203e680000d60f41d50603070100a04054483ca20a0f285400f035400303454915034068000e10180c500100e45daa = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 837155359 1250 837154109 837154147
    0x5060c100c11070801021216110d0c0309080f070b0310050a030602030703050f1b0904020712090609082a03120c062203020c010e03071e0f0e0105062b02 67
    0x160180fa03200040c0702038144200c03170040c2d2a80c030340851155604100d0703107122a5161320000a000c4440c50004111070207000c4441e14107801d403a030036480780440c28010000405a00082c2c0740b94010104400c000900150207421545261540c965039566803001d00486101580290741110440b2070210070410681c0246104a0a0799410800b9645500007940056030584000340403100c00450a180441000d00514400074090009450113502c4c5e40d03145200c00c90741c82c0910000b103071044e090003091b50201260f001864107030000e00750070242c2100c10050b949000c215a140d50100c1d07030346550075242070012080c83d0000c0c2d0003982d2500c03403009000b91034401c11505204418014200c07a01d440021900010420390194010081c00704050015103000d204514502e81c0744c45402c8000846c95800030003c3c03420021746401031211464125100c18014460300b05003086003041c00140070340c1d2582826281d400c00072040055a160504007140244081d030340c10071034054000150740c00c061214540308 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 837156609 1250 837155359 837155387
    0x80d0309060b0a030309120c0509160201050a1b081e011d22123e030a0221130909050c0316050d0c08010606031401140a05060c100c 58
    0xe021907902d15042020401032400000c003c200c0f07101003441100a050125045640b0030f0848000103070712600058800d5004480c046014800d071569448555828010030f600411560002e01001380c443c24800302c8010b00e1000034007040754803000900d840c400140d030303220344541c3e072030000000e940c440c2c1900105507141180b891102c41c41c1c4000c5a2900c6d1200b03414450581c08003506100c11001d0b60301c00708101c42e2403000108000c603904020702c0c00c001513154910300282c180c20030075034912080c1c2444401d05454484401c0e43e00144107429a9540220382c4081d00403203034452020055421907070350524040e858100030b00c40d04100010032411017580c401c0b50041d008800300d407623101402c02019034030040c0600420190740c41c0c00041000c4e080440380d030a0690312416140790f54070303140c00d007560031192268409030000e0380b07602c48840c0080d1062501405030025294920240f41082e020038900c004612459008a1002031075000c1c600b400e1143c40f50804218006200709450140b000300111072040003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 837157859 1250 837156609 837156611
    0xe0a1a010e1e0103030813051204090c0e0f0120030304050a02150a0e130608060405070501032025051609050a060e1308040b040b041a040503060a0e07080d030906 71
    0x302c1c0841e0b980222480c42920714031840822603095075011600c0b10405000b0035032110b4125059000200c1c01d00106c143c80c503000c45c0140d1501e1034803a0800075142c1c070b080c80c1000d01c43c400710500c2203500d400900221101c82800c1c0b1042031600c43c8911118001c1404002c1214000403040c0803c101012540b841102d0089610510b880042c00e5080500e1150020040100d000d90f0032022050074142c3c140c00c410301d0b00700301c00560580c0e10320300c5a0401e402103500701c1d4603403c000e2081c401503800d8030901345507102c68000e00301c03501c0c82e440500003d0300c24018801580c0100142c0c161b0000301c100d60341d0707400aa00a040d176050b940410000e046813034190003015046800c140014050140d58400c22045900b02c0c0c51546460b00e4907070147c1c50404079540b0581e40d20380200700101d81c280c0c8050041006100c4044080d94662a2401c0e402e40e81c003c500b10034408220400040241c0e035000511070317800816070000011100b190070383d5603141020f01e80c882c00c05070184811408400f50540c0c0031014550051038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 837159109 1250 837157859 837157861
    0x34020f0d052b17060310090302030903030408070f091103010e15040f0207050d031a0d080d050903041a03070e0906040914010b09060f18070216091d07030201050d0e0a1a010e 76
    0x2000120f009080742d180b5059071084c0040340111003690081b41c01c090180c0103136885c0048020100c0c1c2140e100d50880c109690100900b00f082d00420817800004241104040014003c4040032021610040c4070b03060902003c4004178012030350100c040002c2240c014010081503240c03d104034065000071170151f0f454050100e004002502074040d00003540300410031052003441010030411050025034065483ca0340a025021004e1643c3c814140150b82c407100035501e41e481c00903107003451001000403407a091030038002e0048842c1c11840403564100e0031107600c00309542e0103000c00e00901c40800058030160480c81d5090700c100c410742c45209248015501c4641942e650018812824150724007190480281810300100300c940d2018503410032002d105540d414086200540754000f5150051071280da07994607100c40030710060903601c00043c0048042d00c0000d02e15000641540216890406283d0300c0c1c2d20103d040078814030800c90360742c1e0300411034a0f0700000100400c100342c0090140b024190f503554 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 837160359 1250 837159109 837159137
    0x11e0c0809070612090b010f08100c02060a0f020d240506120604021606060303051306031b0302160506010f0e060102030c0c1c020634020f0d052b 64
    0x104015104244440c000c2219524000c4202c0e10590040e6a009407145e03503040010004400c1c2500302c0c004e11001400c070201030b0510500034200f80c4442c40d04010180b43c0b8010598091f0085552940680d010300c00007000400e03000c107603011703101e08011203071102c1c60402c1076141c011541201d44c0c101c006d481c05041049031901e06201d050b200700b070300040034030141e0300014055250640041c041c032040d06480400c01c50071950b0b45410750301ca83d00100d000c224041030480d40b0790402d8400318002d2541d49802e00c2041039903a102c50701841d542d2000010943c000034045c030a0f410029000361803a601074100e0b0099039492000e0504904035004d030903d0038117040c01085241d0b20000c2035418400314140030b130400718480c40801c075034110300b8241100240c409025010150341c403440508201c8002d0101300c124210101c0e029402000510004031004151503407141c00740c0c48005000650031410340d454501e0101c01c0c1040d900d0503401ca48081c45c1e01f84000f4150b50034a00c007141100c074aa1991b25141c000d20314203 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 837161609 1250 837160359 837160367
    0x15070b18070605090904030c0506070302120c04060c260f1e0a020303011701060b0a030b1206090a02041a030d180e01032f09070f0917060720011e0c 65
    0x14810709000520500000c8041c0c58001e5417140c020740329051006840640f43d40345400d000c0704865040100340d001c43d02c00049031103a13013119030001018244624040c1070410141c120104041e000d0014032401c0c101c00210000b1810061451a0041c4800d85801c03001d04510b520341e0224840c0d0400717410380e00c16543c080001e00709480b40381740540c01a50442e070900e80d2498541d1701c1e04184040c00d640301d003400989120381d9402080241c2e20b655011405085030b0060020400218010342030b194421000c1185020001c102494002d6040740d004c07031b28030100310704003081d2114161059890300480201000301074000f10718014032501101d61580d219525000103819010911003e010389401402c841201c008a11419035000160b50030114080702500124208660844810010603202d20307003002c2003030300308006c40c00405000007a16046c6e07005c42480c82e1581c0c00540740d00d0510901803450340410a404584103030020301007000300f01200c5140040d0848014062900d503e0910300343c413040c502032007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 837162859 1250 837161609 837161623
    0xe014a10080c0a0b040e071e050a1107180b0402121006020f03030c1605030d0c0503011802030103171b060403030f0c0807090317040905090604030201060510120b15070b18 75
    0x308458106845c0140c00c40c00650000d1020080102003100c102a890901c03d100e22802d16607074071180c482ca0116009400028002d02f49011540951001c00902c045c400d01101030328900341c0040b440744500000705019001c0c0205181c031114054007040290042d14161104442c46a405c0782c0007214400d07021500e0784415a42d80900260800c88074100502c9000b48145951042c0110307841c01a0394141305c001c94000c07480c5400060380000040040c5070b03018007018203100d0440f80461455240d42c0e601d0300c0380c5d40852086c030611800490481c1800081c111034807001c411b000150703242031405150050080c211490081852440c0c54102c0ca9503d00c0740d400d0511a42d250345401d0045400e545851400c00c10807029004086401c210110b10580725004190081e00d81c100148050b0a1900d80a42522080e070001070141c40d40c1180310b1801340d4042028204424212030004100031801c4c0802d5080c20701010203c224800001e0070410051482a43d9205d88502526054005105490151a624 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 837164109 1250 837162859 837162869
    0x342050d0b09150f040308040215032e08071403010912020d1d010e0108090c06071a0a022a01090b040305130e0610081302030d08010e014a10080c0a 65
    0x24131400040001c0d02481c4030325005400101039000c404608030a0b84450b0340101c50411200c1d600d044450000c0310030011100100035122103112505041003076169079070509104000e2003003500c80c115091910298020b881d1a0b40003001e10303c0c070152901d80696642d18140300c000001e9070307070b52990b00311060f12440d601c41204140d4034a40d0302c03c246001103500c00c40180024107130b401344203a03030403141d5558401050880d2051950700340030030011442a811090080180f450386004000001220f8101d003001007180d860903100704454080504c085004140401e001000134024106120505820402420000c1303120030f901c00c6c9150b120000807841d508260380c01e41d000080d84c003115030100d01500c41140d1104030100c803001d403594146c00080c60710140403800f00104000c03d00500078961054003c5000d00100c880c013000d10b0001d000d88a00500f01300e0344001e00c06c90118440e8050020001d06070304240c91843c00380c50b003070404203801c952040d0306214200c0700340f003104c03803040183c10036011620480c0c0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 837165359 1250 837164109 837164131
    0x9130e0a03090f050d110117070f08010905090c120304180621020132071a0703020313320c01021510051504090e060105010342050d0b0915 61
    0x85c100d07643c140002800c03403070081c180040c07040101d14aa07a8154110700c588a0340e5a101ca4440f0781200191010070180c1182a00c01d00b82010040c002e40e002800304203d200aa50321040e43d52480f98030b030b045004a41004034020740041b01490760311499000041511519801c551401400f44800c90300392140090081c04160745000c02280000f01340c1d00101c40d028000c2da90a909424000c2c0c4140d51340c01940122800306c602e205045500c1e4041802940c0320026080440ca14109200450381442041c0001410503169902c2d468000500500c61035140c440c0ca09545148900307232003290f0301c8808802e296030040c0328403400000c040b500e08100360f000319900f04004524904020a204000701d42c18400d20040707074108000a51305005104101c111444107010f4072555044c03100060176a50a111140f04410100c00880c210401c02a118082c518010500c0f40c600300d034280c40030125190342d80c00542c0c421070700b181c080c0c148000350034800d102c0c0f54060b06840c4508282680d00c0c00c0c14000350b0b808000c41c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 837166609 1250 837165359 837165379
    0x5040f060c1a090d0503091203010b070b06030a0503120709080303100905150f060c01180614060a0509070e0111031314010c080a1b060603050a050c040e0c0609130e0a03090f05 77
    0xb401a002587c01401e1181500c110450b00d5128102d5540203a104211a40b400075110050042d010400780d00407034120701800d0351180ca078079140e5a85c041d90340200840c40c0c010000c50720040c09501d03075100038401d03d0b050303e4482c500310b09101101d98280c0b041621b014100170024030250b06114844d1040e60004010754810b42c0500c0170310665411180d956010ba640e036140508100000d80155001c40b4855003001c42c40289610311108552806001c00c1e0055243c0707081070185944244401d540440e091400c50307801043e50004a80040d081c4a00054030700000419103042110000c40c1c4094480401e40041100381c07042c011074200d41f10b444041e00c829000d00c02c000e8124031466065200071074801400159958a031920780032960b1030b85c8204c0300395000103454400c0180620180700d02c601c2c1100c0400444102444083e01d440058194512405002507010306036982d602d09082c4152000d41d0401c8040e070303c0700c00070f83c1c0c505606034140c021a40c01e040018103690145000019110007030160114 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 837167859 1250 837166609 837166633
    0xb09100e1c1101090f0b04050d09060c0204020901231e13050d0510050c040306050708060105040504230a0506130e03070308150907050406031d0d05070305040f060c1a09 74
    0xa4980c0c032590482c6540b100c00c02c0000c141c044820100d4035000b4290301e1000d0a00303240192620b10320095813420300c00c558070100009038200300301e5a80300382c050302c02580e00c140180041364280b014840720f90040204c00070f8280440d50700406030400301090014611101d0040c250003e050007400c0c08000d150b03640e01c0c030603c40340c181500000c0e5494810001c460385140000e81034011355400f2550004541000f00d420030a00c41c09000e8148c11141c5802c040c180f40c00d02138002030032803007180142800386885495041030352140c00000000c00e18900445110307401c0491101d4041e000c140c8440384903138490481c1e00e1080384107201c1e404125007040c00443c9800701c2a9416a0301707241c000c06054009440b1811980141c0700c14101a2040c1c4059407896078a5041c00c0018048a61000340d04012281d182e11589580300700183e900000f446508010b0b032128070ba031804441030302c1150010103000307508140000e0810b0b04440a02c204511512140b002c90080c00c0c1d600c079000304201c0c2d45003c00d80c1304040303406d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 837169109 1250 837167859 837167867
    0x7110c0406080a06200f1e090a090e1002071b15050301060e06090303120a15030803060d080906120106020d1d0d0606122402032505070b09100e1c 64
    0x3c0041c400352400800032800705200712950450098501046e10006000d01c11002e071b0040006903030800b030006410008290045001c800e190b001d14a1001d1355400041d05127001084419007400498400f955141d0710b40c83c1000554400b48403095084105948c0407a040303590710f14001d034010350340d5541030860f1b1030000308603040702003410307550340081081005c5003a0340c82c140300901007103503200182c0340d013400c1c01c1c01100111506c80c4440e91015515803810720002d5134000440f504814100c0f80b50f6080e0140f4201f84906110f640040390b40004000b901001001c900403405040303501f981c0a0b10310a105841090740d8011081030b44025444c5507a040d552a132824084022499003e00d400240c410b07142c07402c0c0c03800c50b0141072054982d150400c107803554580155102908044440304e081d4214204080f01252122000b0503418800000005119409110f401a03960260304280b40b0285814100c0606071a561420391240001c1e040c8121000e50410000d0301c45d100c01c0c640724207150412410381c0219 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 837170359 1250 837169109 837169121
    0x4060b041d04020d1a09121606020c030d05010e0a0c020d0516171309060f08070506030a150603090203010e0705011b151409071a030a05180607110c0406080a06 70
    0xb44d10010507450a4041070140c03010700d0303c1d0004040644c81c5030406002c03040c6000140c6150980e580c0c801c1210702d0003a2030b51101045201d81c01140942c83d03203107e13011282075000e000100401d440c036140c0006680b9100d4001c05002e02d0746940d08015203a4468400c0b62610300c020300b00404981d00300700003c440b1040d100034010883c010b4001020340702c9030320031a18180d40070202c4000b964501301c0090180c081c10344100001011040303015900e080c540401a9102da0080c46604d2280c440800061512201900302201c0d110403610303440301c0c19480c1d0602400030b00c1c4890041e8007a600e01240c4003d00b207000900b0704150f0304141c45040c0c210001e414288001e80c3d1074041240c2800440003002e000040900500507408400008280240f8107040f055180860b1544041c040182012403001c3c90720b1790504a94000e0003607440401e1680e10813103400c1c1c1e030840802d03090700e40340f0440c02008801c0760f00110f27090307072080c4100507112507465290030041a030307056000e0085160044d5101000083c0d07954014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 837171609 1250 837170359 837170363
    0xa120c051207051b2508060a05100b1309050105040e061602030c0102040321020307080a120b220f06050f100e1507030201150806070f090f090b04060b041d04 69
    0x80d46440d40c04901c6145082252100301e4103588110175601100100c0300140010b0b01c400c1c004032081034500804261340303d00141201c410b6582d224041a907500481000310302030b01081c081036541c0c0d402010400015011485000c480f40c4c540300000c10755103094094080200c501d07a000b0a46034403100224480040c000c154001907100c00c001c0160070728001e00203000118040d40c00220b0801c101c00c25004040010f5007000d0464008110400c000342c1c42005a60395044207242040b0b6541d64441400010304459060a0713014113551500c0a06680b1701c2168035a000b0303000300501c081030500300000c05403081070250300e500c034601d50000d00d92428440012845901d4071329001c10031900c0302001c10328a01d01d4060728420b02d040064018281074090264010b480010300301c03458020b1804500c2c07030f02c03808050700003400c20200c403171001c201d28410741000d0050010761140c4690307155580303070030001041c4003440c4600a42c1094400120b0340b08400a8400710340381d41042c0e8000312800289010131603402402 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 837172859 1250 837171609 837171617
    0x1113080105061e10021609020304140102070c03060506060f030c18030705010906050904020d0501030b0103050613120c1703070225081207170f03190902030d11070512030a120c051207 80
    0x6c150b400035104022004001d501e000582c0da044c01d0038540000c81500d0315441c085d031700410005d000103903015008422650400c1c4002220748402d00000c10612034007a11408903100070082c00211a41e5900802c00800000c411060403e0400185a2140814440d0b2804a4984042001403a000360002e010850b40180010b1800310014012011076400303030020740f00511034bc00140104107080001e44c4e00b02c11084480119406140e41e101c1961030010f140001f0888031001010400064441d8008040c00080d122074130f900c0c1000000f5522800105410780c0302100e0b90756041c01e07100d00540c0d5000c0d13440040150035202d407160202038407640060f20403204140310030201141c0c5000c04010744900040400d80070341c0c0e404c000e0000b80e504001c411000903298900303101100141d8000500d503800f0380c0716090031582c6800c4004602d09141030303540403030f07000707604880054058600072008041103482615844901c68404094100311030180241074081001086075440a00000e4400c81d4401182e1130 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 837174109 1250 837172859 837172873
    0x70801081e010b060d291e1809240c040e0601050f0703030c0e030316150608150103020301060b180d060f1409010b2b061113080105061e1002 62
    0x400c40700c0d440305078405c0d222541d440341c8200e6402d0310044805401409041201e50224040000e000415510300c01c01d0a00c1d60355940524507100d8071403501110740c058555101c28a00300c01004e031503407003102611659100f918132400c2c0c43d002e07590400d0f0041030054646030400d402d100c0041d80000010b80080d050242c10303c0a9142030090b0401401228469a40410091000903015141020540d4140e204e60010700c050782d00340661a07901e40509801846a41c040028941c80382c0003000980c1103085540902c0c1c40c480d802c1d1264001d0607040764070a9008001c0f0305e580d103440d240c143c0500e0110000e400c2d5030f500468802d2620b0410300d0343c0c7da030140f80c0001d0340d0710039a9000400c5441c103160704081590024100054110280310b01940394205440061240c101003a2507200150800e10b04a8640c42e034000e80320912609500407003000e81c008101a03031703500c08142001083d056a00c61701c10036600340000a101ca08020032004000000c4031300b040308684640041100244004c0555400c6100c0c540c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 837175359 1250 837174109 837174131
    0xf1d0d0f060c030b0d03080a09110d050c10080106020616020102120711120903030d09060b0a1805060420070615090f0e03340b07090509070801081e01 66
    0x25940c6006105010005800040307000140940e6204000c1922405203894002d0100b038001216030303808224000006240c0f1114070b440300e100844d0540c010707044039203540c900003000030000e00032020341d43c1100ca102d41c5d03414100045400c10b009001e13200040e04400003150f5860401e200c030807080682c1d4000907040001681c0c42c01080281120a44009484001e0302291200e0038083c41440843d0221218540424903001c40c1d91b9200700e00c140b88155a6801d80f03038050010680c811906c02c2c10040501c1ca8003595511601ca0240d424071600d82c403c0d00d42400318405141030312804c7c0d0344106448008140152084800c84580c107c0c1da41505c00d00e031034100e4030300d90409004d9104041c0000741c000045400310170501004848207118203220560040181500440300c000c250222440d011006080b0440c0103a00240201c1070080001c01100461080c8030100c1c1e045009401503910960b010f01e080d65400e00d084134050001c2c4103001d419000050505102c002a900501c0c04c0d80c41c3d2000410024541 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 837176609 1250 837175359 837175373
    0xb0307020a05011815110307111c08010608130c030807110d140d05041202060913061211030c13020307020c09040614011e09150329070f1d0d 62
    0x8040044e601440030724031a0070041410385400410f502d00000b00403004004a80241c203120262815041c030040708402031001408000346c0160ba598036040c0119040c2090024001d040c2c00c0c084d43c40442d60301000902d400d811800d6514150f03821589182d2203500d142c95030051588000c46c19140c82c02001401c640b03c0d1985101c141140d8450070f402440c03441c0300c2214500702203400e255507080000400c010006d01c00b01005988249404460385596296810002200c1101da40400039240c2d042900c0020880d001c008440d03102800343c0c10040354405010105500c0301910280b483c1e0245c5200510301d0084581d6026582c800c00500407922001c0c03d02c8001409210100d8044903640d807200308021266906846541c018413101740070790a0340d095007510414401d864081c02e90981d036104084080d111841d002c141c0296040401c2104103192242221a04041102100c080d130070b90001007810315108182e0240c1d61100b9a89100c1c00001110f0703200105880e5400951740304a030018910701107101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 837177859 1250 837176609 837176621
    0x60b0103021204030207030512040f0e0c04030c080304091d03030411030c120610120b0106030c0210110901020f06010f0e0a0e150115021903030b011815031a06040b0307020a0501 78
    0x4e40c0003016203c0c59440c0851520031107600b61410840e080c0802c0000820221040701500c3c1e0101d6407606556444511200c1030083d0b074000380c91113207605400150400044010011780340070b071006100b1f0501c501d11007482501e20212446040c0c2c410000107001c0341c07401e00005003803440182a200300085200019010114030204403440390444020b0040d10780100c003156000745183c1105414501a51b2511451140b0511800003815192102e0741c0000b0700c01e02404c4580700c4945401c1000044035540641560840340303102e40075100304521400803080020307165040701d0008003e501c0d054200503440b1240407000d40900031003a12034203150b140d81c9040c0080c2403880300780c034052004c940c0b4008100040711060ba60150540d00400359141414078a403400055403605802d0100740d1f4600f440040310b11080c1c0d0300c0d8040006c2284030010550b0b08034044030f050006001e940902c8450503080d10b525911900441745540110100010800c107403508000e0355211031070340142c5140c5109525420300f5601 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 837179109 1250 837177859 837177863
    0x1080a091b050405130201170a0917120702070e0a0b0d08040e090d08070210051e040c09060602030c0a020f19080c090106030b013e07151b060b0103021204 68
    0x44800040c000b42c1000d00c5520381c0300781d029003e00306007882130b00040d111050030421000f0f100200070002d4184452a040395401c00e60003144040c2c0307102c2180389c0c504c2641010003400040100c00000c28000c2c0d1000a00c0001d0301d141c00c000f0405130710760000c9000100110020560049071400c1c904010544410103800140b24029417104d1f1031030a68081401c000300c44490710244043d02e000d100340954005500145004201c1001456407a400c4030301d1400c1d8041c04a10004001d18030801080010070708503c822140d03040c200b8000d5070b8848405076201c1c054898010a650301c1610100098070f4140d25074004088007a0600f00c1e140d00100c1502e10710005500302c503205511001e40400300d401c009008600400340e03407408100c140a1680000c00008070400c4100311360010710305803281c4a0366a842c507440e900e1004a02c00c41002d04a9032561102d000d0700c03400c000000400041c1400030300810b584c4090301a900b0241941c43c03202c1d43c2c0c0d10028611100d2050402d94280b2290713141e00f6503440707880e008034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 837180359 1250 837179109 837179153
    0x50d1112070e061c0902120f0c0a0909030206040b040809150901080c211015030506030c03150a050c04090c3204030204020c0307020a0303091509031101080a09 70
    0xc80e01c0d880180001081d060454050b120030440c205422600105120350407070131081c08180845540001200c640c880001003e8a00800403080042c4d02d00180c4850040b1040d500b20b02e06030fa690108404032a800c000150140e004040010002080251000c0c0c0c440d03c503404550400c40d02601103021000c00d010000c46460001480c60940d40c1c02c21042540301c00a0365250740f900c0014180124a102803203410142e200081f404101001411020200070302010404c840b00c554102d2002009842c003614411300078094044d50049606000c962800060400b1104400f95115503007480020070008000c0075007002c041c807012130302a03414003c141c1c0d10700c04c41c4d903402c01d03044051031298988030300780742c50300702d170f000300c855079001002c8860144c404407a0100e500503168134600c00c00d1421441b58080080d4031001802c401300401d40c00001c5101a51911804030000090410b815034100c506400090687c00d210310b0001d0456104030b4102d40d0088075240c0102d00102c182c1c3d0340909101880d100b0582c90 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 837181609 1250 837180359 837180361
    0x6030601300b13260a030903090819020a050f06160501090b01170c03010e19020a0302060c0d0207140901030b060105091329061801090b0705030403140a050607050d1112 74
    0x3c0024201c04004030748110106205811013101c50030610710501c1016014162207800010905000381e088030300810500c800d0383c030380c2c43e10089048903142d4042b03000c0344519603051f40490300b414030944002c0c40c180d01030000ea01d4030444080700410703001000c1c03003100d403036480e002c4190010304800c500c0d0340217201817814801c5e0041c0c00c15500e41001d9982c081c032802607162a80d408000c0b07100140c1c040d0b074400f41c00198100b0414900105888201c1a040690007540018082e0300d1188009000690360784281e0903501c0ea20b4450803128000050b10443c9503114456400610101e90344045403a00148141070041c5010522000b003000b07100b9600c900300c0318565801482c0000840403440902c107401c60041d40c90260000350010300940118185d5410007040c0144c4124a40d0069803003c0182c118407440300c3c0c58051034a02a80d490340310340400c856071904104010b140e11300c0042c40e4038103180d01c4405040166100182110076030811480d50000d01d4492803d000c2d000401c000924600085400e00042 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 837182859 1250 837181609 837181613
    0x803030105041113092c100f0b031c080f0705070813170c03060606070c0e130f061a01080415050901111602100503071b02030a021c0b06030601300b13 66
    0x1c1b03010b005190700780091076072541d0078000300086245802049802c10000e10300400c000c2040041541c1c202098242c8500380b400c1c040001900078006080000342c2d194a8030703688409201c1d205003030039200d01d00411014000345000407010005404c885a00c07a9170301d256107903104a444031861030282780307003080c0d001a584183c4504003441150b60010b0103440062074010300c3c3d070710000026910b00c5070400308103102021410002c0300b4000000000d410074160011320000e810108000c0111801918031198940540006540a00007092240b9000a12240f41865100c0300e0006410014600340055503100b850040c0f140c030402c003904030420941d940210001180c410700400c50f03c2600d2100c2405414403c0184c0203500980341d00082100c226481c09441017031020030315082222100952060120900e1404505c0d01c0b1040b0001d64042c628805180e19000c040c15281c007828010184220030b141e90100058102641800c42407841c21a000c9031040b985e212000146001c0e50700010540d541031440c02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 837184109 1250 837182859 837182891
    0xc06290907050301080c01051821010e0d122d150801270507030c030308061903030e010e06070b0903090108070516030e0409060509060610020601080303010504111309 73
    0x80c0c044102c2c1442440c550503d00e0241e910709520f81c549041000000b082e030300901700000240c010138806400340c241041030030345000d51001e2002660b00250320302107110401140000d01c00b81078141d5601c50300c00c6591a0f81c0705201400e801198020260003507904091101d17800c2d02c904041902210300001e5009034031500e200c082881c0d03400b80545078100184800d01d20301c000b0f241800c00d4040058129419014a090350070408254005003c0d150314040020078190801d0006220f5401200d901c00b0b031a403140c2c10401c2d4000617000c05000a02e001c80c03a03100300d50044801c4444144010400d0341440a1951202c0b46001c04565480c4282c101292020895800101d0182c004020b418220700b404116004010100c6144070050304000019680c005503071a95031243c00e01e1343d005a81030003246030a10410707a41d501c0541e255405000024561101c030307840455241d040e58980409585107903c2c0204110142c01c82004800b007030682000606e03206004905190001d180348000440d541d0000c0e07402030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 837185359 1250 837184109 837184111
    0xe0306090304090b040510140a15020d090e0702070311030c1201020d06050a030b07050f072306092a0609030304030308040c05040c021c03020d060f080706020f0d0c062909 75
    0x14005c134141401d1010b017204096a035001d540c520078000684462420010301c001c00e40b94408601e141c1c0d0340751040d0459502059400002c5001d0316412101661800150b1903c68111a81001604004c00610005000c0d64030a461f82030024100ca42090340ca0340000e1030302100c4515404540c0d40085c903e0742882d900c1c02004000c0404941820035185141c403110811180140124208174000540c041344070456020388803002d40207000c107000c503c145400d0b2485c0d0034070903c04203240d206442c00500880341c0020308610f80760014408404c4035124021f5145e60108000c034041c0c6c0014180000390040d103081010780000c40c001d540740320301414241040b00408140341c0145005a0404202001c90b07600054210b035000c510b0304401501104101049000b800f038414002c8840341440400244925032600d004180c1e10400280c0e60b0250390346105071303507444c900389001009421021407003405501540c1000e01090240390082090008406010420703c02c0c103400108a00307151007012142d081001d161 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 837186609 1250 837185359 837185381
    0x9060311030604050a0605220f020f060f070f020d02060c031201080706140901110616110c03060f070c0605010e0103050115050a09021303050d050c1006050904030c030e030609030409 80
    0xa40b5031828107403100381c1c071404041c0300504803d4130785004c119040700401201200e500c044985045026603844d000c42d000f0000502070348500c075600081001480c2c54000c5440300e20302040c0c45c52400800faa140044250307030050690f403104c0d2130340412003d40c0750314008104001038040135580d5030aa09841c00903620068000014540c4031311414003001d43c0005410207034000c41c07610301d9110103861004a407000000c1407603110314001c1c1003e0208451201203051014001500c41c01d0700940c00300005039440b500144010f5050744000081000a150800442d8200c444d610348040d16001988a14080e601c00307034400000400614010030600c1030a1081445400c4c441041041c2d0500c3d01c40090a80c62090241c03d65140e800200d2a0400070705080392402158090107803100e0410070100a40303a034100300b000c40400d016800c00c00400680ea841a032056030340c002c000b0052511503480c12104400d410400700d0511820300c030540400d5608018041c400c002060003160f0741d6091404c44006c0e1200c007400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 837187859 1250 837186609 837186613
    0x408071e02060a120b0307090b03071d040f170309070f05091b0d1811010801050d030203030a2313021002030a0e0415051801030209011205030901180f0906031103 71
    0x12040c0181e80b424200e500042e8203182850118000b00c10100080049400540d810701c50500001003240c41500051080e90f821804e8800c0541d903a001d0a010304620b2600b030b00c56091010025002408205109022a0140904550244100c1c00009041c0d10548051504e940550310800c0351002c03c004640250506551500d0242460510030001143c0400341842607031000c070703800003010403d40c800f007032500c011919a0070416141c00c0510041600ca410180001c074810004105400d124030810b2203194541e00440ca035a07100c1c0e003040700600180c69584481e04055030000c0c0c848482e44441030044280340000d1040603079a204101c40380c0b00700240d0300c066410901100083e44c0d005a547c00e400e8030165000308030582014207028180701c154220365884548020040000002c800030340341a0381c07081d01c10b2400d590320f54058055030b2254206c000c01940c0300300310700d80003944111071209500c40000348505080307032101d52004c0c0961068011282003566400c08006004081251800c441c4d01640 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 837189109 1250 837187859 837187913
    0x70e010203070b06030c030703060b15190c03034a15040c090e16080a0804031407150201090b0a050f0c030705090619081e060d03030f05040807 63
    0x40040d44a00420101030115a4030b40009409600e050112106401c0000c0646800c192246444001170285081150252802d240e0a404802c00c01e0112003080202100070300c0c007510010b808507011412940c00b10101a00d03000b030b001c00310000f034104200f0709a081e00d0414030182c0b030300031a94007551610015010022145641c41c0c694101103100c4c01306e0154100440d07140d60342c07400d051603e200030303500ca80300c20b5140409905040e88003244405900e0003403004c0030300003503407a5011555401500d0002d010100100b1082001903204802d6140e241c180700d00303813002d142e502e5103822032a01112341c41d0000340c1d456800c00020800c1408007240d021800d04000c2246041c040d0004c00340040007441340001943c00004120600d0040058070402400101440d0392084214a6180340550905451002c94131f65070108010a400d0b404405040850020150740c65a83c0010000010f80208054080c556180a502205007a90040d184124018580035555040602d400890f41d50600100c41030305010300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 837190359 1250 837189109 837189137
    0x9050601030b240c1504050f0d08092a03070603050118020408060103080f0c07060f201213090f0207120512130c120b01140409020f060703030221090607 67
    0x104080301e00107402d0f19151288140ba2a59103031100c0086503d141e00c01c104100404c10000091024203090520180c8040c6a0300a1041e9410302041e01c01007910380040c0e45507007415a1035455400700a41d6036032009a41000000440d0071b040d00b5070006000243c0361001400605c2e0b1007819404040901d02c411403501f807030001e80d152a0b10b4107000080401038001103a68100409206070b80c0c06a10b002e050302d4107542e0707502d00034050b40d4500500070042100062250b812014005006040074034980c007a01d0150910701040e0b11991002996004c00340740b003007011518844a206260b06022180001640c030f0180e8201954a11603888070031082150801080c0601544041841c0e00b1903c107600314801003d8a107065190b459050b00455aa41712480c0400c0030b2240e0ba84215040b51024018410040718080a000554019003000b079080b03c12404904041d00b0040002c0c00494001d18005090110000050503802060190000d0301c0402c0d0040c000b0100c010311600d03400050783e05040800350706003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 837191609 1250 837190359 837190399
    0x70f030e0d050d05040201030207080d0207020112020306010c3507062d090501180803060f10050702060f0903070f06090b040315090302280302010b0f09190f0609050601030b 76
    0x8540140b540a440310041406c5900940588030b445510808030364075500e020328014001e4001c010240d000490080d080075450000e882202d00881040c0d460103d000003d07102c2c010040c40c0000d035004409000c511401c1c521082466104a03041007410150740c0b00c1c52811703c0700c15281940a050485040c8440090789164611601011300281480125a0040500740207004041d40c0d042c1c4a005914101e80c82e0401408030000e510070318003110000151a40c1e1002c1c0000c1c01a40c42211020a030304000a4002d4a841c2c80680740c01c0201c960b5444c034103000f4001003418500c595020b070300c001c50440d805225003034104507804003030691070070b00a0074a40355480750100c50b920315128099140da00c410000a051082c8144030769503140603566210b04031110600c4000d0104500c0030380041d40780c4441044c107850824a2551400d030010080086900c2c3d612123850303001000c5041c0450280d07584001c001011050049000030200c28500080074601b4000250a03a03440d10b418600ca601c2c211901840002a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 837192859 1250 837191609 837191617
    0x1060602010606120c0e10090b12040213140703020f090406080706120e0307020103021b010c050309100b0d03030c0c0f05031201080a0c060e130213030537020612070f030e0d05 77
    0x4115121f141c24841000f055035058020b4004850300072000581054202c0110403042c007840c400d071404404c98004006074400c6441e00001c00000703000300b4000c62070440c8290013800e500340350300e00030358a0102d0f0180001c007220303001e03031203160b0381d8021200030094113030001d100c4146021000b40901c070310a0040349030b50720f82c800d40c10001d052607408134003074010748240b0004416800c100002041480000d0704090031540040399107203418402c045030840407091502911f201e071180500211070800c2c2580e019005031050b07131400c9003082000800100496400d6460700900c2e802107001c1c50369401003510114440718140c0000c00c650f130001c0e400100003a0000307010021034500b0310700f100340c4a1800c0001000380b5203100e40e01c00740a0010500700382c03900941d0070b41012244980219101900b00700030310030314064141e00c0c07034801e00c1300044101c001000c243c80210083d440140304610f070041e86c4807192035045080d03e40c54000398601032131624140d054410100345204020040c003100e1420035000340070f841 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 837194109 1250 837192859 837192887
    0x3080745120305030c0d050702071a070803061c39030206120a06090603031814090406020a09050d050c0a0b0327010e150a2405040b1201060602010606120c 68
    0x120020002e503205104901ba2020fa10780900c0c18003d901303140768000d581e20303001e005a90070648010f42c040c035088102c03003c589042d940400c0aa0441c0d1b00c2004104000e400358200c041c59001c4d9540709000900d4846901d0210106001840c985010083d504800440660102c60040c0c059201c1072007d030795090142c030b01d40d10103502c0c040c1da80c1d0b640c600e50102800e500d45c003441d066414010080f00305900032040f850300f141c201c06100303852540c41d41001d45507810602220f030820101c0c00440c000c213005400801c00c40702a800c010410710341c0c840c04100d00d10644102503540d90041e182c541600d1901d004104001c0602076045425428a07100030100400d4034a0342c510580d440c1071041c0d1306036101303401101100b0049000d60f43c1c0210040c50701444240100e0707248101070701c0c0280410040d0404c00b0045036180320591f81c50f0500d804e04c42400000c102e26003000354002213078400d21200107024059140941015400070401604d0108050a00010011140300003800c1103c80980c00d80d101e00d45c203520030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 837195359 1250 837194109 837194117
    0x90219140a0b0d0e01140114031c0903030f0e0613150809030a0c0c12060917040311041814010204061b120f05270a0b16030807451203 59
    0x40000031641c0101030002c006c407a601e03000c000019080c560b8451184154200b40d054400c0e181e0091036003088030002d881c010f40410aa40803d01c086032140f09044060305a90078058401c1c240440091025000b2004072500c5542c103540c240244240542c00b40100d00103400c003542e503814031101081e01c900a4071044001c02c80c2c2c1000040a104407001c072503000f0004440380c102110314030704041000c0c103a040c0056440100c800c0d1300501d0701c1c10280881c0c00301c81d00500b003410b20903000020030026243c0385080c0ca6102099800b410046000c0c6c6103009055448034000603a11464410f019220000c410310081c0c03c001c0d105a03032004240042c10540702200c2e07070f1038540d070022070030303c02520300d402031000312001421201954110540e41e19035480e00b0a40071164061000d640c0c10008031103104a500c2030402c0c048205001c0d0000380a07410b100d40207821428522101c2a101400b1002e03510700541c2c849000040ca03d034240c828200b440c201445500c1c010302c5c0c1d802d060030035100040039280031400400b00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 837196609 1250 837195359 837195371
    0x1b0b090a0b070f11190308071a09060a091a1305010b01030c0503190e1f0612150c12020f07120905060a0c0501020d0f0902030c0613050405040501090219140a0b0d 71
    0x1a50320000c03070440020807680c0d00d28045d603ca0601c40443e81103503200315400f0b5044121010000300125800f8420850607005040b542e903109604005048001c4003110340c158603503503802c0c20007854100c1c1c0d44500c0c1c980d1421800c1e0200750400d24255504c41038698141450004e407495810350081c01c807a4046070600e250815202d00c84d941000511683c0c0215116000d005c030b0b02d00214443c000b50207841425000180580354035554007069903000918004c00130420060b0f03215007061941c1112101c1c00b06400d01e040713071101e00345c0703600e0603070b0310000019441c0900042c03191f0810020f81c0040c10308290501e08241c00700d0400001c212644110481ca50034801c2907100501003040940403920010340e0060180202000422359030f0160840d04022446170242c01140e6000d810910195000c05008140280480c0c0c500380610009140140c000c4d286952516004401350300ca6056644803000d01c510101c0416203007034060440740205070f0302d0303034031480e1141010080c050030042584d41c0010101400980c0d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 837197859 1250 837196609 837196643
    0xe0a1d0f09100e21070b07021513062417120f0309010609021602031b01020d270b03010e0c040501020606040f1b020c030f010905191b0b090a0b070f 65
    0x30707107a0f404e444004800840c0600d040c1c580c1058003d009101d00c00c105660369070300c42c04c000707070388542c603031050500d4070303503071940002d50140400790300071015401408001400421481c0841e540515000100900c034500791040124075030380303000454940e641002500c40010520941e004070711503210018240d0071f011001ca1402d090070f521400040c4040c03e000c65890b122401c03005ca040380300c85400da11038001c2d840750340d0398a02c51800039228120140e01504580d8058082500c9980c0d00c0440743c901000040c9240141c110204417440c043d118194100b40c0721740c9058400701c81908001c01d40c0e14803d070240320810290741c0011f50260491401c44e0085000007081465400030103450811824402c0c451130101a482d07004200b11200f40015000c2d034201d018240011401d83d000f031140141641e00c006403200d07500000390344506129200da003222404800c0384400314031500c0d003a0080440b141c00010070302c40510300300c490306000700113602c001c0d801d240b402e07221414101d40e1481d001d00049004424400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 837199109 1250 837197859 837197863
    0x9060b07240e1501050612010b0c0102040b030f0402030705030f060412050d0c030f051305191106070b070801050a030b0610050f04030f0b09030313060c0e0a1d0f09100e 74
    0xc504101d0308410412404a041c446541d0050000d04081e00d680e03030b0700081000c1c204841250b00340081c0c01d0f074000c0c140e4605481c80505034085081c4a045560074000070904c05c6c640c0b00114052004c99415090506050040605041e41548410300c2035000c200090b2080300b012078581d038400e80008000e9221100104190b07150f10665012928291804002c24206600740d4840120a8900d80b410860341d034452000d82445054600080c01940c031400036002c0d84080548401101c07841080c0042040d203040000c292030f90040e00f0111a1301803030300300704082c0361350200714140103110440351050182c1c0323503441d007410f0702c80b000d42141e02601014010301001030082c02241c401411610f01d190762160b880c01d0100c0503d64803442100c508442c0001b103030110390f0010039240036030084412090070301c495598103001806981c090005104008540c00382658920300d0340c034014090701c0070307040c4c00b4028481d07031642080d17000344104103d2440754103200c0e41040010341c09042d000100710003d40c1030180710a641c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 837200359 1250 837199109 837199163
    0x804080a03150e07020c01031e05041509080415020319030c02151006020c10020613060b0a1511011415030f03040f060f031a0f0f030f031309060b07 65
    0x100b241d1a04140004100c640511103a1280c0000d03800c0c1c80c0c00c007844100440694018034061481c44054400c0803001d62840d52003590054070034068a20800310190300c071820b40709043d009a95900c40814204170310020903070661340c4100c0700e1000d1494034400740800c1c105524690f03104030402d81e80c0c0e5503942605000b0003003420b21400c01500894540b405001e107200c8542c090083c400107005205105a403420000c41c04c00440d859500940b5095507080080c002c4210b044005448050711070012482940340c1c003100202400d10906231413030280d255030380a000541c0c2042d50b0846a0325110703005010140c4120019000811911230040c0c000d0280c0020307151a0002c2003040090000080010704403514101d004102d5085417a40006504524400e808a40e4040d159002008411111248034a80b46030001280d40f00289000048400640800d14000d1041d080070700507407001030501c0801c45840e18100c020301070000e0910406040c800300b071440307000703203c002030200445891b101e120f0300c4440e64007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 837201609 1250 837200359 837200381
    0x50301170a021201020301050a06020616110a1703040314090a050909030d02040e060127050402160f110a141509012a0b010b09030d0c082a0601080a030804080a03 71
    0x16040e55903071448218004d500c00e1289130320527064260001400d90022800921a002d1121403a40f11051600180d4003080c42c9918800d4902800b01c0c040d002442c3c14000c000e003041c41d40e1500340c9030b1a0a15004d000e5107001074500413011404e2148407950340d5050780318029113000380c41c500321645900c41c0840c6540920800f14901034004103004c120840d9602120348141380990303c100181011002c503039200141007001c9910541503c038140b0582c1820f800501d4441c442001200c10b620700b0743c903100a4040d440000300c80e1552500f01001161030200c941401900100400c0c034000a21000056000721a108149810324004035031444941e01410300c3c0d5200285200c00e405840c1c043c10ac40034407071181260103c0b40f603103c04002140016070320341500c058800c0503004002e05000c2c0c2a095840d0a410041200c86031010045214200703450403040000c0c012003840c0c0e10142c524102c099091240c143c1056000ba400b4040c4c25010aa00460154100350851062a510280641c0807409000d407a409 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 837202859 1250 837201609 837201619
    0xd0623100311070605090615060a180306050a0b12010e0d080a090206130603140f0606092404030501060b1602190504050112050606181b090301060303020a05070806040201050301170a02 81
    0x15000744580354011703070712960004098854994503064601203034555035030a02d411100c10310544403024046c04a003101511260071040e5101d54036036079130040d60002c442d0030220b1074035591002540c6c10300c40010b480d0400900001d1082031220b000c16a40c40410506940030841803002192003142c0030b9011440c0307650040c1c005a51428000030700f000c03001262040b100080c2c13a0070084011520b06000c8980151080006240161150350811040341c00008041c0e50004c1d1034084010545d00c0c070070000140381c050020803a10fa910b1400c0a600f12002e9600c07c0f0503c50040007450b0100c511883c044880c0e07581180d1001d201e4100d000d003100c4450042d00242c1d009803801300081003401890b059224114803400864007580c0c0da52080c440d21a43d0f00c02c10001c18864403000c01d04014981c540310301c030301028447c000d003000e01c1000004d0943c0c0c900e9105a000d43c000704450024400e00380b1007007001d06200b1004141c1030420b075000820902c414411600418604002e03448080340605c1541e404680043c2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 837204109 1250 837202859 837202867
    0x30515370c0e100e0604050d020118090c2006010b0a200a14030a090902160506040c0501110601080c01180308180a05010c0203100f200d0623100311 65
    0x31020b8211010684000c2c40340d445103101941c0180302c0c1a02d0b00c41d100c0040d0545041500d4482848640c0151180c120b0610100305048000c00380710a040e4001441060030201d1003ca01d1000500900c0c42401400c085588281140348103400000e18141141c0c4050010350f80d45628180807034003004800705080e11142500044030b90f145002600722138190140802d54107410b00103403100d80e01c0c0b203039645040101d01320420820090300250f0107003020b8506244051482407442d550182841c0c0c0485044880d81c10030b400078000e40d40d210501902c02104e980040c100703541050030103a80c8080d081c0c040350400c08982085600780413800401d60065904c080c0942e1551411380c050b00791020b4207040c09024000d500300c0015158440c02e03c0340070094014002d42180c0c15003504c0322000d880030841003220151030340d1031413000c0c0140025009000108a82194079030b01000c0c1c0003030654040707510445a001d0303181e074141100c3c020459181d104020031110303800d4682105105501a1201040c4000c000308041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 837205359 1250 837204109 837204131
    0xc08030412020705100f140d09051c020304030b010e0606040f060e0f040605101404030803040308040b0106020a08040e180d0302090a1a2b1503051537 66
    0x501c04428a10154082d00c03400c1340c0b02d109001481008000b2040052035420001003881e015004d15214481c040401e54a800c6c4c02c9400074003504e410032030440d015442820303c01c840360305c1003902254050052000d585803a16544a07450088018000e20084400313a02c04138405607190001c450081a0000380d64442540d02c40001d0040c3c62030308225401086d84003040745417850248035181c2500e0008008448507444450200c816080c140c466035001c840410011010900e1b00700a90f00c100d1080e628611a45003902c0c0c004020a81a40300b8419903014010602c0002e501800359829909014070180940c2c2c6c0b0401b680300b00d150401d0021700103008a1a07100d41444e171580003410301d8801624294801a84c0f031701604a60b58406a520700020400c2c81607002040329034082c0842c0f0b00120791010301c07142c440b11800b000c4503040d100004103024203c50420400c142400740f890207601082482000d46080581050042c5460103d03116800280c44100620142e0030031490000c801140c0030000031030a1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 837206609 1250 837205359 837205373
    0x30c1c1505010e0601080103080a030f2004031a16080901020909092103010f0b0c0a1a0604232e09020403060e070f090917071b0506120609070c080304 66
    0xb802001e403c92103400002c0c000b035020740050f60480390300040452070134202070300490060005016000c0b003d40c0b51412004034294110144510214041d4141c2c0d07903d2451a04005004134103429000100d03a88040120803034001d0707460702d682140e50400c500e045e030b10254010f00a10401e01810740c000c0c5020300340f002d41c2c00001000c400582c40d480783c0021700c2c0040f4988d0f07201400309100e05504031008120507c403c0c4408005001d081460380101c50700090165a4201c1e01408440801c11280c400381c1042034501d040d005100d4280ea0303200c54005901440040d43c0802140144850f4000d120701400041815000314451404c5420780589285151161f170901c002c2e5005210698040d400e010681102d02004503201044071717440c5181000252504840b000600340303101c030643c0d2101c0c41101c1c01c40c465502c0801821030500c2801001142d2051520380c00501c41d141d0030041c019113007030201135014003421001c16000901140c035484a40d54800e01190070f270008100041070b1f0100801840300304030784 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 837207859 1250 837206609 837206611
    0xd02030c0705060906190b280e18100501030f0b060a090204120507060305060d061116050c03070608010b040905130501020a0203130e04020d080a090f0f030209060f030c1c1505 77
    0xc1d50f00c1c2010b034580c83c80c00c00c200303892110b46d007994094032080340f065549440480c808e44254042415003021a5550001942d00c0f03022100040d000140342044644982c040c8049081c0104442040100d54103503150f0040416505a00421045e28800818035681c0c0d40e092502c0104290300c03040d5511500c1e240391341210194076008540600c80d841c0081640c0c0d000b4061a8400c04029040c804442826207544001d0a1500e00200ba0700408201400c2800e009010740c1c4d8a06005034000c00d078101d4000241032a1400d2584418100011071005110000042c0c08490440d60090004629078441c101c0100844800601c02060b5600c00209006c1d0650044040c25802c509811110240c642c0d800d545542c0340400c0f60001d504c0035402e211200001c1e040c5001c1c08060f4001e01c1e180c1030361501c0b206c03500a1918283c12a0050840201d420021880d001c0c954503030005090307411724224410200403a503183c1000300030620821580d032441c0c05400c1c0d05411540c00d6a08007921852541c0041c03514402808 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 837209109 1250 837207859 837207871
    0x5010b041406040302150d090c030b0f091b040b060f120609010806070c03030c020c0a08100b04180602092e0f020c010e01140c030c0f0706020a080d02030c0705060906 73
    0x201c28210821038502841500e007100d401500031101815418403c05c0c107540420300e03000780144e0390105407011440c601000c8018512410314542241401c0840a03000c980080c1880103590105480003001c0301a400708070480501620045545001d07000040d2180c01104644c10901c0340100380d40002101040758a0b004001c15900c0c135601e0b989904a0a4035000700701c4182c00401e09400e14080040d02c242d00500036802941b0640e5880044580002c1c4040080e0b8009100d6900c5841070010191103803240e004d5030039086404100d41000700d0250b40400c40200ca0243c8566030100e820086a01d5032583c50307680d6200c087c06415100b68402000c6200000c0304c0d01000024400c11072902036a000041801d401c0b1016181c0d0001a2044001152032240717842c07032041032000078004c45090780403c10203020043c2d000d03030140c490030748805500c62500c4c0c03281c0d100c0c00c1190310544e4290f02140c9000201c8480c6001420301698a40d00c1c4003a401080c8980580244135200e40410006080c1e404107866008113 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 837210359 1250 837209109 837209129
    0x1d060706020d0507030e03030129070203010c03051801090f3908010b1509040504140115030515070c060f02090a0806060102070e091504020d021906120606050a200105010b04 76
    0x1011b031607031940e40b40401d005120101002c030503501c615010609415850540310142c40c1d02d001c44587c0800c0c25504108000c5010131f0700c90f01404680d620007034841303070400c054070000c0004942c04d840340707285c4031840c0c0c1e000360101544100690f0030b04c0d01c4040750003580820070030030000c500c01d00e60300f031016808600c0b81c140a03500e4403003d98402d00c1e05007200c11001c841c48916a02340b141800400c4002c0402400840d480c080501107074160140a0007401c582813120009043e22900d5030415605224a62070810b1940072000d040142c1a0f0b004400800070a130440f10001e403864424107044024480c80304016484039103014002180500061118481c0b80281d0039248210707901d42400350800000d5401191a800850551682c0f034845a0029482030000f0f2060303d050b8002d40200c1c044a814003680d500250303481405101c5140c02003041d80c040c40440404100403490101c00134228010b0700070300010080180032044120354049884031080f40000002c1102d56515150950154003901c41c07a4804 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 837211609 1250 837210359 837210371
    0x3070f03030206090f0705010c03031505090709031109071b05011e0608102a0210020f0901080c0f030103291f1208030a0504080c19140109031d060706020d050703 71
    0x505e0010480070116001a180d0606096070b0380e60a8001e41007840c03484180d0304d110b000c00136040d9107400c07040e03000720455180c00171034506504100d410b039030009100d5401210040207005c0500d03484045503c000c000d2901813025503801d8a45036014107600e0001703218120421181d106408201e510003021101d5400890b00205a089011010b641290450800c40c01454000821800a100b07040640e0030803841507134a01003903580b07104201d0b00f001a28416496010560206550b0031051684e00301c41c5c03007404a0305044428420b8010b920050000402c0e41c0407980c1c2d4007a800c036008041c1c0002454002010451b80b800e1042e000004001c83e22442d0321041c0c414000410242000a820300c20303411802e5545103541e01e500c0940644000b030000c032925002007003184030001c014000c2014450004403c1c4482014904180310030004c00307040600c041c2d141410031b1001039001030950390005500345001010000650000344036015220016065600008074407032080700981c0036030f200f030034151810010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 837212859 1250 837211609 837211633
    0x10f0515030613120e09180c0118090b22090209061005071106090604080a050d210902011107351504020f0a032f0a1403070f0303020609 60
    0x500c9500383d5040ea0341c000d102084401040440810b8108100a401c00703400d5154a81e0105e03540340c008549001244038200c0c04400c40300c00520448904407803d20344000c0d095100c40720881250581d1003600300b1240d899403444895110f036801c0c08100d40b15120b080608008109e44400641490f2400707d100c0c00c039001c0012100e10b0032403070300c0f1600d111640c0c4a40c1021a039507541200882c0a040c2603074444024081c4a90540c0c40c10b000344054003842001c0c00661696140041c6446034402d02d0f0800d002800000711a000000001540540d03e03c87c80810034810900040e201c4031104c040f4400340380248080030500c5886a607420301480300685c00b0340c0f042103180c0b80003031039182d071000385448e0b0b9001000b41034404408044101d4209000600c0c0083c0340c481400064042180ca500840d0760540c41c0200c00d032840d000c000c0146403810b0104907034032352840b418006201100b140c00f07018400c40307203a40b03c4034443d10100305040c00350505000c0e010a540e1681400f0350f44141c100c1d103500d002d108507146212 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 837214109 1250 837212859 837212863
    0x103111207140913020a2903190b0f04020f120108030307051603120f0e0124090c030f150806160c0807052506020c0105091c0c08010f051503 62
    0x2045440d100c6003040805254002c20402c3c1d1400703400003003060551110803004d07030b65141c2c5c400700520403222102001e0107401012400c0c80c070881c4001d0110300c800e208024034025200f1b29040c440030740c3c400005400240c440040c0c540a21289030681091011178001e010150503002002007820034020000c45a0742e0703061007580e0b0f100813207110300007403401c2c4410300d08413903000d54441e0f400d1300c603040c10300c00d0f2284600704908660b0b514030941415601c0b1880901080703800c0c821460074042c0c2e110300f0069514440e00741c02c0b80d01c0413403040301c5050781e072051841c400500c2648a0f01c0c1c1142c0500042c8000380f1003607814032091003039026020f00c9004100210b0308104000414450f01c140d84e4850103038184198980c0000c0350007602c000d0781c0714061044400c401305420700c01c01c201c4000d1025542d04c002d051220080c541484096000e040c01070420400029644190001d1400c1c40f03450700500c00e4818515008003440651703408604250b00b003d100c0d1790050100d400103449051020000f048e00213500c41010307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 837215359 1250 837214109 837214123
    0x1030c12261b1911030f010f0212070e0102070e07030914060604050105010804051c050f0304120906020115050d030e0306090a020f180f0601090f0602030304060e1621060501031112 79
    0x50f07241d203a1082080041c10205a9103803484004094030040c52003842c1d0182500c0940c861031881690000300c2200300450202001d40202d501d00d41042c00c070303148800203559403000e070158091540502000030180351180d00b00c522000c3d0b103d900448664618942240d450000380c0d24030380302d42d081c000003142551040da0342910407030308030000302584480000ba9011502011120a041280420520000743c0918008501951043c2c2030040340c42c025140003084450700f504510116410441800c01c0306104a805000390380085402ca544240c1500c2c0507212841a19403c9815000342d1082007410400818a8140035000307035a00c6100090b402c08008251400d42444c0030b0903159034000c5a40c59042d003a0790b03a840b15060428030310b919202c0720300318600200399101000590002040104200950050b040001c0b600e41c014684450400c1820007030a01c10300902d0005124000d09070300001c01c43c0181d04000390000e10410840d42c607810b000c04d60100d81405d003805a03150712001007080310006400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 837216609 1250 837215359 837215383
    0x70302030d020304020307030812091e0a020126040b0906130218070c080301081014010509070c0602130b0406030e34050a0b0a1701030c12261b 63
    0x95071a050103401d501000b9000a0001c2c0e81521071210b0200c0060030b10b40007030010b00186410305040b450460b242a00d48019040c0344800c1c2c5069025020240d03200180c00781106609007000200c0d070041c2d170b0406084401322841038000d00ca4013000e00043c810010200c41c0281d0342c0a043e40d12503641c000850540480f149002500b0a004d9003840b076801201c11481074100000349444066140b054846090580081e00246500e402031010101e000c0c034940f0404c0d08400a40035240c2032503140c1800500c004000816400078401404140070411034294102e4504901004001c903445407203850b0001c0c42d4103c1e01a05020070700c0c0203102841d01200084503840c600a00d003044d810041004160851510007401c084030b111980a408501c40c1c0d03400243c0c00103401020b041130f864114402008010344507010b0405126031010005202140710710f07085800303481c92090300503005020380c0381c448501505c0004054840300602043c44910401400030150f407803d000405034200105040c40b0740750050a584 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 837217859 1250 837216609 837216613
    0x30212030918090a142a0f010f0219051b01030516031e050a09030915020304031b12050703060c05040803071407050a0920120411030708100f11070302 66
    0x390200030700d25425400d03440f108410aa82e01000e2540c0d40713a9800841803c4050245c20126072401e080300c9004140304107415079811901080301c8000416101200c16005038104942c011050070000c0c0200841c2000e00c600d41881d1150304201d0510f1500c40e007a03442e100c421400400002c918641c417a00429008149810030340c40740a140800550090101840d807070803460b041ca40945a0301c04600c6018800c090841c07020440000c41c0c9002045080d0b2604134500b818a600700b0f003a5955030000641c1d0a40350710100840030794044186880e0b1211055100c81c246200e044900700030841c012415000700d034480c000c180010010f0507000d130703800c4c0121f01402d50298024007009011a05000e00d180c0d5400d0f003407003654075180e19000030804020342070300014001c40e240d155200281102600100c00141040d100b20b0a0102c1c10440384020940584007500e0510070907030016032039506000c0f0500408210301100d80c0f1404003000c11007c3c2218001c0320140714981641c81c14150ba0410803500a40c3d45540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 837219109 1250 837217859 837217879
    0x5120d12020a02030336061b071a0a110a1d0405150d06110a18050f01050a121e0b030f06040507181b03091103010b06041401030b030d090302120309 65
    0x1014841b0107000b200000f5800303242e0b1000c815a0141400701e82c5648288801ba01c000d1601523408080b0b031342c01071006c9100031300400c10100400c4c1c442c03000400035003210040060940740c0800e4200503004d0a107000d890204000b95000034203400c003580d500031030510001e0181104101c4204400c07645c0844486050f0951811440c03074514060702c1d08806d1a100300000a510f00f0b031007400030115005040c056010450f200e81c0140c0c98410050440020801150005202400c40000030014000d440750b680521405030030650300e480031500702000300611039054160010140c40c6c40c01c05803400c81100c60090040340c106100d924804581c441c4200c1d003010040c80517503d8410700442001b240a851a1450741d0f0701c0c0c0c068001f0300e50494030540c2d04540d684c0410480c03294141441102910075526200e41c1c0f606a45285070341310360041d40c0403100000420b100704a860380040e00504046400c465141c0200c2520300d03403031500215400b058034003d864100d5020051003210307550f8031030075040e580c2c007130701001e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 837220359 1250 837219109 837219121
    0x18030d111b090c09030102120a0c0207150509060702040b04090c0512070b16050312010f05120c010906030209040e121e0403030c061d030703081b0a1407050705120d12020a020303 78
    0xf00140442e0101500061415041d500c0694200400b0360b418000d90340c40d4803074021080d904002d448044c00d110b415001103000c1c41f0f840640144244c02055010f440c0c0440c081081d9901d036400f8101088020f0402e00909050b450300e00d0a003196400b40521903842c8240d0401990400038980d010380782101215807a01101024403541c2c1040454102c0721884200b245510b010001e03070000e4024601d4041940d566424402081407200c0c000001c40340c0c5901580c0c510400781ea000c00300ca4201e80c05810300680d81c0302000041000360040f1100c105131840303910394a01940c003101e00242100324111501c00c80d4080c8480001c4145c0c0b01d01d01c8040e002585020a203000310300c0c1a0302c00c44800c8440f601c200c2d8400c01d8015841d05680000030181c2c08600400b04115443c1c19103000758403078010307107a00e60b441c0c08103224016100012910103000800008117645007003010800410717024260040004d20a07007441c0107020303611074840007280300042844001006000f91030003aa100161240c028606660342c0d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 837221609 1250 837220359 837220381
    0xd120329060d1b0c020103110909071107170309041406090f1906080a03030507020c01121a061306020c040b0a050f0102071a12061f0518030d111b09 65
    0x2a906100390b456480044200305411101ca0200316041500c495040c0182800094211810300611840401d400c0021f1a200d685084c60340d0f84c85900381c1043d001e604260080036240000540040c0c0c03031096a41e00b1407550035000000341007040c0c0104c9050268080d88049144128429030308241c100d0f421001060b460003405960a41c40984030505a041c18903078261503080d00c1455222462a8010710f040e03506143d03060117140e62050300c50009000c2181c1d014002083c0c0c4a103403903044401a034820085180900021405643d4503004250a03100e028081465840501034400c1c2c40151240543c2a0584d04081c0203d4940c20300040c4030f995240e00d090148018803400d159000d0450180d0303400490300101450b0780e0f50480a15140c1c9644440e0001c4140200240181403148652203180c1c1044090703800d0701d0031f240741140c0c6151142d1107a1500d10180071f0441010703002541409007011541d00a50b01c074043c0b10440c0c060400310381002d20940c140000310f040640a01c1d4200070400009034600d039103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 837222859 1250 837221609 837221617
    0x1e09080a08090a0c1203030b0f0a0506070f120818071503020c0a0b0a0203090f070305060c1e0a05070c05060a020c04051e1801360f020d12032906 64
    0x902d0b020754096210695400d281030b0103a03080b40405080705070a450a144d031500c103150700c002041d0b40b40e40c940316000300040d461603200c2c0b050500c5901300213941010441c0c803c400408040e030140e000e006100340c00d07001514041c0101c540e86880c01c0051181d408213080011500121022b4490245030b122041c178044000e03602644200120340b20700c03004440003400d10450f40d8483c9a450744010b80300d04002c40182c2c2030103000c0700c40008540c860741d800c0c00460404620701e0340050745c01007121383c2e400403030004440d0903840c665810b2000001082c2502020b41140007404c8492040000400741c545607030402003d40104c6042c840107900817880c01c03100b4202680100d4222441c450f00840656101e0b002000940701103422490f04c2001c0150014402c3d824025060b802880c00c2c40a02800d544110210207074a0803c0c51240d20302c8078580001c144501160300305401a00035103480c20300001424018420485000207400180c90310840000c2c542a45c00c0080ca01e81c81c11080c0c0180d004080b082140d1900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 837224109 1250 837222859 837222871
    0xa210509181509040c05090a2d230c1b1f18030806090c0c12070606051512040303020d09030806010f020d0f0806031204060c031403040b0f040f06020c011e09080a08 72
    0x150b140b80080082800c0c01c10791030100030111051040ca0200e9149070242d46d080e20500203d000d01103000c000d1949035088280d0b20034841c1d552180ca40d507a0b4ce021440c42d0a4101c170b020500c0c00307042104800c510b03600c1c01007001d0440c4480184903a1354803035020b004100c031040c000f82c00101c01d00007180c2c1170f1401010640d080000c4803549420090001c40480c1440203044840c000007400050240400800d409420020314044907903d8060840c1280c081c090312541c032080302290740550000d41010f000343e040c0c07249280030890400c0348100524024015400c15036086000c20080c00c10451203500c00500b0251403112562405c070060b010800070b80c0e003030001501039680b500131f04401440d1340d031016014200134101a0fa0341552503400d8200541440c0d5048007601402804000f0807010032a0b0500044c0c000c81c9510141c813140d5246d040444200f8019100241020700000e26150340c082c0540000e03180a450045a00d40a00c0440c860000c442030104020014941817110354000ca0092076541d038008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 837225359 1250 837224109 837224111
    0x215031f0f0e040209070c0519150605090c0a1403100503010b101e0c0f03080f09060915070201020715050604060b271315090e0a210509181509040c05090a 68
    0x1070b03550b032380351802c094010f140009040c0082e0800d5040c4209207841c005040702061003000b0403428030000c540ea0840003412102445400160514494400c442c2c040500c088080c0451301c0e0304092441190354641d602c142446582041c1c81c109440c5004a0000a6032a080d00c500401002085000d04415803102825043c0442102044081420f41d5402c109082c446e50b0381000c28074000305240312052018101e403c0c9940074504104034440300081c0181d50b45c0c004030b560945070380e03806d00880c0684a200d2004010188a694001800040d070700013a000d4501110240402d42d142d101166460090301034002144583e01c070340140d0421085515588501c001d0301405004003111940c41c19994000c960707c0c051180c040003006451420301c20305103010810000382428024507154105442d0000b6004200420000b5450410038000c00848680301d0001e09421400c00d48813075442e00404040740e0302c8818880c510a81c61541c50010740d0a031250354455100d050003410107060000841005050007141 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 837226609 1250 837225359 837225377
    0x41e1104030c090903020f06010602030f03150d030905010f2303100302060a1d01092405190c0203060a060e070309030315031415010b040902070215031f0f0e04020907 73
    0x10403460106000a403e03000004a4264107518009107084111000e20301c40b40c0100005000c0d195000c000c456440c480b40201c29186d844081d900a10f50b41d103c0e095540c404003112500c010141c0103c40003007110350903200d00c01c0c200d0740b03130301c0551b46c4d903d05005140d0780398004441e6a0320ba5020070003443c1c02c007541c400140f40c0355440342d02164440d406120100013244103690700e0110b00714018009610004207181507080d562038075045080303140030030b800081c805c00400071090045101d48207407502c1f0010ba0301204002040010040c0c020300c00c0d0300099000f40251000962a0200340c02003c04440c407001442d2155501e07824100c00500350010110700701500e8002428488184000c040301450280c1e162042c030900e0703c2d21b01032400070b81e80d074800c050030b113480c00400101c6812010b0742c04403415484007596600c2e40c0d100007280903016521401c001d410200c18040c510788840419090744e89128280c1d45496202c0b9a00380441c58a0b02c603070303203400901400003401410108500c503086055410300000c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 837227859 1250 837226609 837226613
    0x906060b030c13080a15090f050712031106010609031b0f030606050108060108040b150a080d05090a081b04091e050c010e010c020f06160b090d0905041e110403 70
    0x40758800c0d902c01c41408000b25605030b008040310b4460000708500360040c0b1800c480380d60740750590740314043c200c5205903888040780c1c1400780708000301070440e51080a8411f56a12201940c0c0c0c0041e0006040d00000c4860130b5003110074800240d807905035040b0703445007070240c0d00e1680c6035100034000b00d1039400341c103094100014014440056440145110301804241e0034100300005084c0030000784030300c0c1008007070414800416105801030340c20280040c10312005c003400700e01056603188a607000e0710311482103c1d52000207960260142ca0100c00850301007100581d80d040503540e402d90b40000c40c0d030082c10b04006564a00d85079129031041840381d0004840d00044d8000f0310500111a00c4c2a10170f0b402c40c0c0e02262056038088009c02c041442400e00e50000c1001b50041250845940da0f810701459001450b0011030680503100d40400394000c000c070095140802c01d49461720002682180801c09100c0040781c035181c64007480344400e88001e280f414010904c41c8181c041c0081e0121210781c03503410000480 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 837229109 1250 837227859 837227879
    0x30f0c040e091c080618221202071203020601150e06070b07030612230307021c0c0b0339040b090a051504030809040204050406080f1c09030303090606 66
    0x44921940d80242c03001003404040585240c010851001c01c10424a003088607559411078003001110380000130b0007961f0b6820710420003003420326919401100080b1900810000d0844200401e403031144c0c04c1d9603105584803078008028150342d01c0100542c00040045c05007400c038506000c0306d9030b4980303032110b000c00a00000c20b0300c541c000b07001030350240840b10802000d50740600074080280a40c959840f1000241c3d100c0048201044440c03074200091280b13440c1448030200260f03070015800030420000c95078061507000e401140c24030f0858031042c08440000b010350584064070311400801500b0b03600c00301120312250a200c20a0210455500c80e039071a906655007c4020344003070548014040d580f40498000c02c0000c0003180d00c00c40c4a401c1e4000000000400f03079040d101103a0b8000385186d1030300191130014010340503903001190850700d0401e0000f007140c40020030210b9642d040060b10075400701c0c04031501030700c0480c0c1ea00c80b01090302580d0820010b07200e030380202580c6001da00000b40c400d464084100f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 837230215 1106 837229109 837229111
    0x80105070311032802090a0816051c0605100f080114090c03070e04110d061a030f0606010e0312030718150f082805100501030b06030f0c040e 62
    0xd82d100f04180c0591b803000c84018240002c1c541c03103440d260360700d10244440b205010140000082d150a0030510070003510030341c0d510400382201b1900c54a0241201502c80707030380705501c2d1200280c013480c503504420240c80c8210001c01c034111510007200c00c07940064401601ca4001c3c12000c1750950300000c0c40380c11100c02c010261401e95a908050001044100440d900309510310308000c04c0001960014001c102147c070b40103200002c480901d991100070400c007000550100d800701e41c056009140750a54000000d04507500008040390612280d08140c5d9a480880d09e50b00c4083d400c0484854070901030148100403101a40301828000e000b540240c00700380c148400040404d0300480042c141895a4088841c020740c40c00142021400400e4121401020300c840080046950b62280c0181c01d20b2100003000035003141c0320385994840d14000a05130000d01d80042000003100b0386100500f03 = true := by decide +kernel

theorem cover : BRFrame.Cov 837050359 837230215 := by
  have h0 := BRFrame.cov_init 837050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 837050359 ≤ n) (h2 : n < 837230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
