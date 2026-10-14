-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1287
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:10:52.332986+00:00
-- url     : https://prove2.me/submissions/8e05a71f-1e88-44fe-bdbe-d6d18581e6da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 231294964 ≤ n < 231474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 231296214 1250 231294964 231294967
    0x40308010e252f01150e060d030e3a11100219050304050a090e1c020a02030f0f0f0304080a03080601090305030706021b0105040b220b011223060c 64
    0x208192166003842900ca208509402c00007000f40740c190504002e02d9811040741d4030b4003215812a82601190b10216000381500a42d90348464003013140d00008210214240070000c045100d1503280e0041c004009040d000003071107074580078882104442185021189600702c408a030100081038a034040c03c030b00794107a8280c108001c403c13506074981802c240700b5902040c4160340300c0041010001c02401611029540f1038211139564003006c003520040d41610011340c01c00880d190010b5070710482003681c142c8510466580104030b030042400d20804840302c41b15a001562103c207010002c20900020340c03841c0004514091030301c20429210322500038000d041140c41400701700301d40e01c600d403410087c5400405a03a9502d50520f0114029800700e1520111250300e0005021480c2040c42424811a040350001d061940d070b00d0031650f0544107205001e464104002d0850b008aa203566104d4041c02c82c4031011014427085d4107000f40c004000b000c10141d6a121036040d500412401305125400020810015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 231297464 1250 231296214 231296281
    0x909020c0304050a090605011701140d020a09050f0f011a0706020306010302070c0e060918030304020f0616050619020a090b0a020c13050a050a0c02031803150c03040308010e 76
    0x35040d40314652000e9440401034802260040e903617030101046505c242c94004440340304020a81406a00344600c01a00c4e00c410b0080c1c90364102154104540352001b410b00c095a0349542014003150410b682d000c034280d001904120324030b99640c507114090103003c01030000070308031140032160714410008004d00407038020000c00c1c942c0c0d01980548003895800f0f0030381090103488003042a8116000c6031168410b84a82c8082070048210540c0c41c1982c40c8090090b45c0366546d035400b44104051450b000ca5007280303081000e0b103100013680300b103001c0c0d241c405c0c1d028101c1810080c00303220082003d400311300c1d41184100441d906079a001311400b400c03640c0306010940c0310304045800740d0601070b00700c05035900b00302c20741540c03090340000780e2044c2c1c81035103108001c00240c2c85130700e400021665010406005648100032051402c48600042c1d0182c040040031507046007a0000c500d12110401d689420b00d5460100c14481019040841c1d06d01601c46640d5a40380c0303180c05000001c0d10000040300b040c084441800d02f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 231298714 1250 231297464 231297487
    0xe031c141603060b090d030318021905010e04020a0e09090a0c14010f0207061407080409020c03040303110303060109051c12091d01030b01050f120708010903080a0c090902 75
    0x958000150622640c40c0341107044038208480341c2841000091900601003500c2e0020b0f003c0d42c5903035101500c0c12004400d00d58040d80180400d0f0384071910320f191021803038016900d04201004c10800102d0302443d8518010000d4094890103241c944254018480358421582c0a402d440d0000340841d60a0070301e0300c60034451070610680c1d400107003c1c44c200070008201000613940b441d006410a80c2e40b5001942c1307541040340c4851840c040c41001400c0f1040c400c180f41110300c05807800c0750150340104e01d002d5803015024100e9100b480803400c641c1010804105058100f50b81060703000c00300025501d546041c1000820400d12406120b10030072210100324805168098407500055119071900d148507003a001c013500e00101c0d4404d4101202c1c88410a0001a401c0c50200c0d0403070707074003034031942031a4200002c01000c85403011015800040700c1013200d5840c41c4c100503110080c40700340000548940f4a04000340001030041c20300000300d0900310030800940e03220014030126401171100584604032042c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 231299964 1250 231298714 231298721
    0xc05093001050403020102071109091c090906030f0201171005130b06130e0109020c1504110306010902090f0402070f1202100c080907080708030d0c0203210f01050102010e031c 77
    0xe000e18a0741c6410304100400d50150300503d03001b8010910003181040c484100880030390111291205c030f4100803907128006c00c80722884101c421603030034006015500d8071000411a0210740c0705031001d040d072400c0300c02996040303980304401c040d42c0180005245449141024011101e2148034001c481d81c0303050300c08000480d07110042d1003100610855036010001e1511454031043c0c06407480c05100340d400024044154800c803540000c0070300103080321103000441c0c0d000e0030500070026200203081103d04000741e0b500b0b202280c081d041c4580b00503118034454040c0441d06042ca081e01e0b015510410402000c642c1c48003030031001c554040300b4000c051000150807410410009603c0709054200580710390f16a4210414520800511040700e4809540354002c6581355040d2089581c6900200102c088245c130070b4110700b025400500403071b0300d03000ca442803040740e91100c400e1044c00000541c007445002c0038000900380c01840f003480248030945401443ca0740340e20035a5160035288010000f4412000c40541 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 231301214 1250 231299964 231300049
    0x306040c0b0c030723070602300d051e060402040b070b0604110d0b03121e0307140d0605011107060e01180506040b2a060103080c03131502010c0509 65
    0x44260744054407078081240c5e4070350742052244e4074091110041034141c4006800030006504c85444000140000c0f80e1101102e20030045c1d00d207958080107401d002188600405000c0c1145404503802c05050440c0c1c9600c01e2000790181d0f129500420040210500010985900c5130304444122065201d01002500900f001e5210846285010032010b0101225900c03004040b1001e4040d10120b5a06140d061410710445e4104119a4035110a18803402d1030140650f50080d66800e101000d50f00c034051b8080c164000802811810f03494030780c144002e5034480c8030300004192180040049034104a4080e01342303030141351260704008001c040c00140ea50b4101980d8020032018000d25650351b200e550400140d84101d54549540c80c64001c1340360700300740c80d2012103205000e5038064440d50b400c6a4881045902001a6640d1480140038044c0b110031007000700c00090604030800c0141ca0108440642501c2e07003860b10100340441840510029240c6082612040c0c4807602102011403034405201151981ca8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 231302464 1250 231301214 231301223
    0x4060c050c1203090106060e030607050304030228150507080f090102070b16090b0f0703051c1d011d03180114070309030b010b03071704051f1a0306040c0b0c0307 71
    0x12030310b4140d841c210303008601406413007001b408829140c0909582e100000c80c48a60160710600000b59140c0c4980080c0d0b410921920540d100c00045003c100030700c010022200042400d070b28500410410350300e10308446240c0d03800c1c01b4001c1e40b509140203490500000c1c56115070b945e0710030020b03400700300a504803040c02e030340700544e0081800c003035445142c550404040c54000c141c801102242074000141030b03031a00798a00c200c40703180054580e0116450b821002e0802843c0f0452110840303054030601a5410060716050503242da031074108880e5013503403030700c2c5404a8550303850010501c009002000310b50039002d240428a640010080c01200d8224101501042401005c200a020164440070303000807a409801c0310001ea903200ea032400514070050350010040340800d00c4414182c403030745005c2940140264190b50a45080350043c02c50740c1c00c02c8500c0c42c0300355524000f483c82c00c4442c410240740c81d0780581c01406070303140907038030402d8100d02809960041180450540902e0400b0000c844105510 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 231303714 1250 231302464 231302473
    0x105040801020a120c090e0103150b130c020c0a120b040804030b0f01080d030b0a06080907030203030f0912010c0c170c030d0c030506010c03080a110409110a17040b04060c050c 77
    0x90340b00100140b61130b1070010226400c0180946050f0302c1011032009941d200c81008102d0f91840d95034842050030802070190031a15003403106420750301d00311a200001d80c518808142e180c40c9400c020b0078428030903036603031007040e03080002e00902c5c52104a0548041d81b080001d44036846504103c1c0b050702031030384000c11884050080141a039030b040074aa049031008000c4841d5100d08234415404c2d01c1200840d1750300001aa05d04010f4944a071b00c405812507984c00940c0c034055202e4022a040d58004058501790040000e60321085050040c07003c40ba0f030704064000c2040981d030300e9008010204801014007640310042c02c1c40e04c02401da008407000c100c0e54104503695040020422400340c4864172840002c685004009505540030301d07004000164103540d40c0003103540d00c143c410000d200300b9a500301c1c243c00c00c1c08003107403030762407803040d20348080d0f0a0200c0354441003015170041810046102e826500c528580502c800181501b0056400c90f1740308030086501c1c0c0460000b200c80c1d010700320121005115 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 231304964 1250 231303714 231303727
    0x50a02100f06030b0a02030717070c0609050c120102041202040203070908010926160602130e0f04050601081b01050927090c01090f0b0309070308180f0907020c0f010504080102 77
    0x222a0b10070001c40b849800001000e6949124100407800304850b80c00200f01c202c0e004182103400150710383e90005050401481c0254a034443d1002c43d08400030444503540200707410b072814500001114416840000254601810160590b01424001100a00458010000c1080207000da651800030f000540d00030031807a011801c21140e903801a04100c910010440060010681d824040303d4003000088a08078100c852661b82100075440720380007100b032603012040895400da900e0310140c0149140c494004881c00d0506103242415010383c0030a450703070b0182141040088024088803020842420700648071490600407a01105074540c1c01201060030502107c950346004421a0040050030704950042c00c5d1b00006456030046800382516480c00304104020400c0681c3c004c55020003000140d0340b540c0c0e940e681d01002c031b0f040f0744500101c030010740e825004942400b848d40034810a0446000308036003070008002e51155003400a03c1d00070003000b01240c138a640a04102d50081040c10002c655851 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 231306214 1250 231304964 231304991
    0x9050d0503070f09050f010e060f1314030a050a060e0a060507051b160320060406410a030b030303150108010503070b0a050c07051c060b1f050a0210 65
    0x784120381c00b00104074180f40c00700491344141081d100781c42c00502202c032100008401034800c04e0080349020b51154080200c0c50080401c0030140c200c8501c0071100e042d400341003800c00c0c0034680c0403075001802940102050390100d040043c2520710990821030016101e0040301e011410802c031600c001c0c140c5400c6c1024044000d40c400014408481a1800120324045010038151902d448280f000380e01e030880e42041c808250b4103194000401d440350034071440782c0101c0c004a4a6600207903c0040480e4440d41c0c0b5000c00c00c1006c4124000711452900707034046584418000140070203803519099141c3c00422034400003402035021080c03042004049031b07100e00c1c0c010b1040c26912018450103000074010f0700002518100050000207440912a0b21400d0010743c140c210b071640c01510030740459124a1500155944030310300003200c0d40b402c40d0840c4450412504010080d12810030903907000b0780c2c5440000382d504c40d41c0c10402c03100040780e04e06295542446a422450f20b00c5400034024198070b808803444065 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 231307464 1250 231306214 231306217
    0x90a0f110405090f04030e040f0204050d0b100b0906040b0a020c15091207030206090409020114070c15020c0a090f0603020909030301030b0702030708071704030803090105010504061e120609050d05 86
    0x441e821103003c1c1c400c1c0d0794003000c088040740a484c001e01041204000209910382a0070031300a8400d40c80c80182080c0c0e0380e074002440a48800340c103440056807031060001c21209070301c2a101270280182d810345002039507030201b08541301d184940300c6510300c0400ca5800881c03090081c8601d280000b031403000401540c90410850340c3c00100680c1c0300d0344400219042d8040d000c41d00e8011690018100b6080207081000c0c000134010300f2404a04201d00c070410008401403102c0900000da000c1d48030032050900300302c2a89100034119003450f00795032005070000032070713540c8032605016a100c001010810f0045c7d9210391001d40015013000354041c8441c01004074900e80080503604076070180c405210a43c4810600f41d0f101d12885c80098100d02e410402580032424980440f4192a400c03481e45260542e81d848590051f0020b076082d40040e510303040104064075050181c0c00c050040704050001030100e08038000c22107070652256071408000040d80105200c3c0550080c102241c0003010342d080300c2c56441c00185070f03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 231308714 1250 231307464 231307469
    0x206041d09010b0d020f060d1404030804020301140115030e0c04060b2d04151b06020a020d090b1b01110c0303010e0a0605060318120a0c110409030905090a0f1104 71
    0xd580b078000d00d20503070703d0300c1c0b2260b000b280e401620071b403013101424051102650114100f042c42945900d13043c6945001042e111f0b02c00d5010740d80c0c101203410075104160a440c5240c03ea040804448401403022601d04601922050100c0c02d0002e00b0130400e148190500160302030070fa9202d0703d030010001e0559020f400903c40c407240001c160100c0340b00f0b40c0f0000000c010014102e4035242c820300c4140803003160a0030341450401c0c6403c050f400c0d032003042c42090020006e0a000c40392550041142d0a14540411001d0164141410801c0c4520306044020000d4042d000c0d241c0e90420848403a11040c0d0002e60050003181d400064031580c804004046d950340358030a100310202c08515400080d6030013594800e000c2968801003005245441d0a600d01c0c500486881100805004002242ea4035000c03540041140003450f845016441410342441e4281e02c00411840b0b000d2410a491100001d070321189901c00d40d40100c0d0300d4a882d0321411500c100503d600303028800c0c1c1500c0d004030110703401d184c2c2024204 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 231309964 1250 231308714 231308731
    0xd240b090a0b030c07170706050109020c0f070819030c02030a05010c110118060f14010801060f051f0c0507180b0f04140403081308030a02071a01030c060c0206041d 72
    0x30001e503075046040803403004844000180f0f04c280a0880000d042010001003843c82c01d201504002d11521010100c1e502a4040d500c02c1d540001c224015050610170220b048064102130064140790483c070a40b00c3d8504c502c102c44d4030302e0000e81c040030140200b00100c00300c1e4010b812990080a9440c040303000340012220000031031400c0c0030151a080c814040ca4009640e42c16038420440c015a44034000741035000e104072050354aa0004406000300c0c0c4250740d000380f04260000c148a03113040b010103603807050b64228600500d00d841d01c001c3c61401011014141d6121443c103000c0502c8a4180300d42841903a40040103c00c400020b6000c1569843d040710805880031505030403403403074180410003211042d40000342007451100019022138010001c980c0d004103001608006201c042d038480c50154001c441141103280d02080080502641116110300220801800300240d41107450300825548248502000c01c0500000f0301c0c00c5444000a0701c5c0241516012220a0002c0c03029100e4180001c0340c4412 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 231311214 1250 231309964 231309979
    0x310080f030403170d15050406090b0109030f02031903080603070b0343051306030603050a080706090803040b060f0402040b040b031807080a030e150d240b09 69
    0x244224020811a88888191008510b010b1079540c6500d41044000841d0b0081036060000309083c0301c0b5401182860002c0445200d100e60401080108a9110341c01c516a1286007414076601a6080b80c040015079400c03614100d078004640c400a40381140103009143c0d8000c11050b00420980c0010580340147c0e070480a0300c00e620b1b210000040d850100322042007201c0e902c610003c01110340410356261807500b42e5901c03608044424038002c80c802484030b20600042001400f0140300c90b6082d559006080507150a014481c82c545500c3c8e581c3e5103011024010800010f036040400c0940e50000b44a180d001c800d00d6200d240c1030800c80d6501d031040303845c14091120503001306030510b81f030302c01c4a0a42e00e2a16226080c0303424543d1420301908014154201462881c02c0c0007040501001075000901d4014002c0200603483c4c6401130880741c0d83c81c85076014100800c501b20708603c1e0141034803c0d408441d100085c4101c480c01840c00407440c05071601c401c0c14920b89000c00c410005000820350808240c6054 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 231312464 1250 231311214 231311219
    0x3070306180b0c070f0201030c030b090106120b06070c030803070201090209040f140c0901210f060522080403030503130c0312030b0d05070e04080409060803190e0906012307080310 79
    0x702203842401c400425174800c0421810040d07000f54400e1a41e10014540010341400c40350102d03030001270a070060004610041c050132580c0f07020340603002c219034040c2e4402d821302c0c0c02a07440da616000c1901000700807040c00f100007a6014400d5208142240c0c0040c0310b6021802c0606080504092880054817030540e10a00d5100750280010300500c01d1101401a1800360302c2d10031008a620518203071001c201d165000a0b001143c021036030b00b4100381c041c03c1c000899081c9001c0c0065908501d0034000d0b031b800c4104c450480824410010b4400300c90701070418603030341e903210107041030241640c182c010103407c0c2a00020080c80940594080186d04a80b010000b041038031003001440c0e0400080181980d202d808103000204d201660990444d100b0888030341080c5e01e59603e0400d80d500390704032682c00c3e84042920700790811003007200120785d54903040280c4046c0303003a000700c2d00a800040100f07040c480318074510314040c201158a214084180c0620a44842c40c0e8907142081d54030680f510325a24800f008003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 231313714 1250 231312464 231312481
    0x210c030813021e0315040b0609060d0803071431092705030910020f07090905030d090302031b0a060506030f060415060f080a0501060b030601020c0f03070306180b 71
    0x14010341c40d00140740071484289030210302800141c8222294041c002c500c03d4840345c44010b8105030081d8031451440150f444c0510501c40301400040c811881600310b150040d0114441d01d003100d0b040344041ca00b5110044240c0c0c28139500d48188000751001e100d035881620700617141007441e40308140500220440b8580d480041130705030780e0750b1441034084002000c062401d08040c50241d1002c00d2092050720b080c0320f101030014030b036038003094040800358216101c030700c050204c24040740c400b034080c84404000c01d400640782c1039039034003600d640d000b5010f035513204040a142c02041a1480b0601094400d214100d449040607150040602c04031540f03070030f01021446038600807898031400a460002801c0c3c0f6038a5440e2000008801410a0103141d031351007020410207000a14900078100303a0700100300702031051600608413140307540b140900c02028014895161fa011030a0040094111000a4204900c2000a05003d80340d44000c01403480c00f1860440d800d039201c40841e00901441a0800c0755403031900 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 231314964 1250 231313714 231313741
    0x3310c14012001230108070504050f04030e0a05040c030b03060c181c1b05030d09060813030306081005040309060201090c05061804050702030c1603050c0d210c0308 72
    0x1000e0740801e090908440000c440744582440201c0c0d1000045100210800f0540881108004000d0f640c4031040c0103002d1b082042001d14010142920200000c0c40c040444030400180a040281042801490112551307a004080005020001c0c810006e40d140d6007400307401807203005e0405029004410028407030030001002d91320f242c00d600c08400c0e44807030341404020040c031084040e00e00c1190032500013004522118161034521808180300c892139410700d41090300d00491495481d082000700d40c4280a441d0b80007904903008203080451040012075440c1c03d40240c1170b41d40281c842da21800b0300d0500c04403600d82120380074902a4881c900500d0b20344a0483c00e8614a250140509050050800150400000409480d24121640340c1004c184000103001d036141558018010f9001140d0300d48005003c0c00009140146150343d80c0c2030625566400c1c2c3c45808200049105080719000c10089c042912050700307858007040b00e050740c1d035a021000503100c071140305400e0f400201d034807000440280c000390 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 231316214 1250 231314964 231314999
    0x60803070c0902031801020d05190e071502150901091106131203140c071703070320030c0a0302030d050a06061b0507080d030b10020106051503310c 65
    0x7032010020509001c21200650300103010241308042524606016140a00c09000b00b11080d41002c2480d00780b260b070b4030803a210fa80140301e0007686003105060300c103170002403201e007203a900400300743c210b0806a9003a410513030080605040200034900b00070000c101035000c4a4228401c11034a802c1c0210281440003502036583c841d071740860016418403413014040041c60000e0f02ca441d001d000010200c1030101680c01002802d01c1c0d50740f1802062040c4801c0100700e06800c1c0c201030055082036000e840042400001099040048141c0c00c02900c0480c0140f040b0340822005a0459001c13020074507000b0341d26880701000d402c07460701c0c240c0410554541070089404030f52455850480d1080f102c02d4080c40d02005480c202da881c4560040054644000d00521042c505540c40000344015102c05001d2488002500c007411a40b40003070a10095590a2000c0100b003101408030b51070b40e480300540c951a00d001b44000c1d1009030900c8406444500d1140601d65580c0310b003040f08101603955680c000d5448440f0f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 231317464 1250 231316214 231316223
    0x40506011a280909020c0d0c02060403050106080a03083304140a02040306060503160e090304080303180c011404052803061b090608010b030903070b09060a06080307 72
    0x400140714400465184011a48500c40c607106100c0c81c0b80304521020003480c550040052007510b55036801001c0c690042224240541c5010a801d64064980044c003448a00f4491212610025901e07040c00752070285500000800440f81c035003003001c0d600d44561608500003070034400020301c100959500c444008405122882030381040f62041c0c3c800102d100c0c45c03280c04c141d807040c030040700085280072207000d460081c1c1d006030303100e0540c05d000060720096003150303020340d00c1400d208024100c400713072071011a1124080040d8503107981c10054103512a43d130200703085100c040248294152064801400c1e4a2440101c4203441200401901c0340f90126034202d24442c0248030400c181d0a007041d65080b942c07011041c00f0b4815040450756020400075400558180e0340d40c1840b0381d9011108101c025000000341084c4c2c950074940000200440310501400040070310100103c0c03880d80c0100143c0d214103910000f030700520b191800045030b842c034003160700032819030070520b000861020200444e0040c1c0c0c0c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 231318714 1250 231317464 231317473
    0x50d170106030203190903090513110405100207180501170a320a1a011d0105010e0f030a03030b0319020d0206090d05060103051b04020a0c06091b0b1309050405 70
    0x1c0c100160001c0d04010030344950102041d00f0011001e1051041c1988a442500c808920f141000700703029010110a400600d890b18044400560300000010b9400710759085941000c9105010801c90422a640d44000c410018943c180c900040b980d0704020f050314a805480700300840c070342501d19a42c0c1404c0e84007800d0b49003c855010351101c240e02c01040702d8000c01a421501100761156149031506c0007070705481c100010812090791503284a038250050441c89194182d01404840f031441070a4188201810b01590b1074101c02161030f206607252111034002c0503505054000e083c080e010302007145189200340148400050120f000c04040e11909030060804514000e8076403c0c051540d211004c0d995100420308292400600c0402003a4042d5114101410441c255010705440d8902d00c00810392050b40180202c0880c6548071401490554021300e002c02c42480340e0401281c0070070b04290341c18098820900100385020700c42c4c000c1c0404038645421a10725961a1104411180c1c2580c00501a0b0007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 231319964 1250 231318714 231318719
    0x140103060b070b06011103131a030405060f070306240e010305360703050312010807050f01050304110312040303090803040b03040b0405030903010207110306060a03030906031a04090303020403050d1701 88
    0x206990184d02c5003042c14080b0198050481c568a1a04112221868454132500c02e01c62541c010f1031105001d004186410304606003a6903660b191100242034404058452001502087c820380090f4003c05540c112134290240e400300c0c5502214000701c05401003200c03113103c000954400e21506100385203142c02d10b01072004208029444041c0d01c2e907060000900c2902103001c2e500c00348208401144141e0045d0350703451030f81031800c00c48201603000c4000750f08052003c200079110f820f0391f900c1d1038109207040d540c3d0340d80e117103840e1002071903080030640c152280581880b03007064003400400c243c0e4000c0d1a000e079400e075102856070f901d11a6002c2d0700c4403008188042400100c8000400b0b800a02c114207481c14100c2200c0480d007203810101f4242d82400708010000d0007030800307100013908140309a5031200b20700d003182c4020b040c00c0050710441f07040507901c0a4220180710b5090002640c9240140280146003070741c18020065040b9000650f9640100e07140d130b5030650b0003241141d40000d03034000c1c5100c3c00da1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 231321214 1250 231319964 231319973
    0x180b0d120c0206213709060c0503040311070501020c091f140103110c030901050c0a050105190501170c0105180a15030b0607050705090a020403020603130303050c120f060a030803010b04140103060b07 87
    0x140308682a13410a4540c6c09540c005242c070301800020748243d0b95030030b8403417419080c010b196008070400255950801a8240003990340441c2005011000781c400c2d5034580c9038240707410442e04291049900c00c2da8140c001081d952400040302e440071000b66028032210340c0040b4006c03d244620341c0c500c1c4039a4010002901c495000b40003800205200340107840c900100c41d15480e0a4580442d142030700903010f85410286940f1502c070b4280900301c0b00c007503890200d030103001103683d46203001da600d03051142c04074064a0490020503242c6a581c1c0c0a0314007030758075540313018140f45090040005000719041142400700e60074084151082560480300030b003802460601402060100a01005a5603408200100150b2030304002180245280000050052101d050080484a0191001e14101401c0140c09100d0008000076504154900b0143c1c2c640e0301e412000940031000b03640300a20454000c000010004aa6030280007200c08680746800c6003203601c3e00440840e0b0040c09030780c48100c014086400440c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 231322464 1250 231321214 231321301
    0x20d0201020a21021603120c02030709061706011203050316090b0c03071a1e090703020301050c1e040513180c090204180b0d120c020621 60
    0x5401070054800ca48916200c900e408a1000f8408440c910f02d040050b540c29410401c1e03440e020030079000125810b00796500c1203440d14521404400304415141030806568041c00100010a4030300010001c080d5111103942a82c4c48030340c250a0b15019a500000d548443d08207001855031f0f265440340d01c1d5641300c8540365124401c903001031080140100b00071420244c0c1c4401414040002d1000710303112101840c04070b1184621a0361001c05c0b0114105015443c1a69144251002c00058000c02030303940d211062481c1908651000e90b1542c2041c0074007551042000041c40000b5604142c0e00b0310403540c19410005100c3c500c00d082e0003e6000b0a201c0030141d0395070004182d4000900000701c0d43d080d5480e030203100003882e000b090440354002070405c07a0401e003512003c0841000a4180325400c00400001c190a140308800b07010300320110748803000b240c851040f0710022540188440e07107503051a060490072401c40580d1702044007404001c00c4141c010f2035060f510503104200400145c50f0801e5011030310 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 231323714 1250 231322464 231322489
    0x90901030f03090312050903370203010e100e1002070b0a0b0f1306090c03060b070f020102071802040302010e060306030a120e15030a05061c02043c0e0d0c02 69
    0x10003508043c003000151241c030350100d44001d2540ca076070725011840201818601005000d80210b92009203041c40400f0181c44070001e01c428240c244009581400820701600040c800c443c0c440c09092030107402c0410582c4245000d01180d42181c0c1030054100700c2004901c05c1090280a160600d00000c0c000c0c0342d10740000c892044d001e01509038406161012030504408007684803035190311450144500c50b090b21890740e68100b1032805000301c600e000c5140740d0b240700d0500003801c00ce039509503901c190b900810900000340040c6600740c0c00004004000c078002d4000d4007049000500d400c410382c0e03107890040c060704e01902004004c6c00540300279a80304034116407280d22781411711884151051159884d0054400e1080007000c1503603503890410004011100d0007081c1070712840c5100305808034240342c0070074810303180e5048d58001010303008400102d010070071b0440e8002e0410001c0c020030f000341540070400031401054036028031042036200603040e140d0454440b144d00281458500318054a000da004924 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 231324964 1250 231323714 231323717
    0x70806071119020904020d020405070e0f03070311100e030d0c02040f1119270e09120a0f030f020c010c0305060139061401030c0503150f10050603070c17090901030f03 73
    0x1f1402d006601250a0724412a20f030350102d0040c00d0400340307900307044264950208084015005032411562031821001540c007400380202d0b05a40042502401a82e03c00d0518a004084404801c03a02c00005d051442d1108102d001301d013886640d405400142c00340e2116035082110b920f052490092010074a0280c407003100701081000342045c2a07101c0007400440c081451242034250903420482c51080211000c1c281c4e500c0c5510140c40c8496584228055440c030000700e240080a405c007640088000e08201103004d00325a1001403801c0c10740c0e00541c4000700d401c0c0c1d542c034144491381e03d010054a0b0513000300d2503800d80c0c166038015030104009101c1e58003100218582c121101c0780340307612041c04845002e0340181c0c0c2180c90800600900403108050001008120014450554081d1690384c2e0440c003d421404120a03c0c80803c00013117021181001a01e000b410031522441c0080c001080310246c540309450340024040d148a08801c0721044980030200030340303840302c1d5900c1d40d66001514101c100082c5c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 231326214 1250 231324964 231324979
    0xc0f0e010e1302070b06030607080c0714060f22030207050d020d0b010311010206090a0206070b060d0f06050126030406050307051e0414011b0201050901050c07080607111902090402 79
    0x7090781d03507041a40d40c503141071a200142c6480c400d00c0c148602c82005000b6a00c82d61141c030402c1903803070313118508940c861407041816440c0c07055440c118481c0143d50b905002540250b01c01c01c62403c280721495881000c9070402170382030010012210b404072140170030140040c2c00401040c4442c3c141107843c00c880350300c090701e0a42c0523079840c0c9540084070804c1e04201d50300026584810101d60341007200310b4000603204040c0c000f00d2907960000d2600d101e00400100103200d060001001707946c8250f44103070142e4000c11440e0f203001d003504c0c10f0301c002c180c01d000314445a07040101190030843c40b03a1203019420714030360085103000d0074079100352041e810003000c11081007420000e0310010700a0f0b1040304400e40388000c0309506c59091280b42180078810311000d90402c6202402d01c050040494444003030349030203003440c5695041c180e0040b2501d10405039402040d22900c42c002039000700009000f40708400caa83c1c0c03d4551480046401d0f21000c010003c10705008481d0040d2000d03190442da2190414030040040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 231327464 1250 231326214 231326237
    0x90506181008120a090f0f1a0d05180f030c03030a2004080a060605090c09120f16050a05041506080a060e090303060a0e131e0209010b0a120c0f0e01 65
    0x4600e00540d5544483c03601d2000701e0a808282c0d00110700e41e001d481b03520b900720342642c108201c140c030b00d842511442500e110300b5000c06010442003812251105031846040c8181e24081402000c00030f1183c905c40c40c41d10442c000d0304400c2c0c0001c025200d0448580c07026614580f500303074410f4090040c0d10003c030261400e42c41c2c4072614100e04001403009203000310150052200c1414400100c8006601040c0500400000c120810850711f04a4150369811600d640d81109601c28040c5451980c2c03111104510030f4400e05107058498014200440344201d480340c4ca200d0721541848240c5401280c90707200102c01180a0020900540c1807980c031500281300003c417640e07502d031542d5100c04242c0d40c0030a00e4000105104d1182001c030b0440703000c3c1c001c2000440e100c4c00c0030324402c0a00c4010b580c02800c0005800b203d007001388072500c3c061000d19001000c803052035071100c003144551ba0280007020017203000c5d071141c000503500a000e445140c2d0304913102c0038400d0300c1e41682075130500c1ca0700c00308038100072111104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 231328714 1250 231327464 231327479
    0x12041407030515010618030b0709030c080a0b1501090e04030e030102030412200606040f14010303050319050603060411031509010204051903020d1704030b0f040c0905061810 76
    0xd000290300600003801c035a08801a0035541c8001a045903040111088602c1c0c89500f08403821000c507a4000480e0311584e82d84807040391070114540009160107071410000905d028001071004a60b8040d01e181e1003540c503114030402c0c1c00d00c400c4001c9408038158640070044445001b41540d80580281030013261010300c01c00103401ca034000c4400f118400d520449881c20264440703000f846080c21180982c924096040e4a95030300c0f40700074441c0744035035200c0030070702121007441d001a10950507083d480442c9503140e1601405580044a0740d10b199903803c000c0042258032401010300075503010b00035100ea9140c40d2215911032180a0a40da0180f0580e140c0340c0c01d140d00403031644e00c1480c140e00010380b80d50400c0100b101c48a03507800c1034103402c0c0c00c1060610240e620f841561007450317404051070340c030706030390780340d920de55004652000d000c10b041042040440558240040e10440c420407d1890841c0c40c0c120380d2040ba1001d650042d04030320754103a20701e41481c02601c06038100000c2003a210a90350707100700 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 231329964 1250 231328714 231328723
    0xf02060c060a0203071e2307080403050106060305060105030c03040f2103061703070312020310120b070909091a0a021314030f190f060b0402040e0405060c030c120414 73
    0x100b000d4425800810003030001e600c101c144080715039140c0714090006180390024030041040c880702c00e032182078401c6030003840141d0084400c015400301c400f07925190b0f2818038600070941445440b0102e800d0000007002e542c46502168410310348501e265007551140d03140c00c012003202c00300464507251500d203000d60342c9400e0080001a6a0699000b1807045e06000e011100c40c1d91900030090755503c1030240341c0010340c010840c82400d000d02c58006803a5680c01c0d4515004904541c0400030044129400d0001d100c11040158803880850b1030b02551590350b40c0a078000c88140e564040c1006100c503010610032100b103407003540c0040c48000e0140c10010032001c2820304000942c4032520b0245441c0040607103040c00e100d21501201954060803002b425480040c82c40341c00d959005021a0765020745000b00010b95124040214000d04215203940d101c0130a0111110b003a1f50989032031241c800018400791149013102d203c0c0209950483c100100241c01402000d806001121903000d18034441317400100170003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 231331214 1250 231329964 231329971
    0x60409050a0605060f1204020a1502030a080606070b011202012001020903010b190e04240b01110105061302090607020d0809010807031a01050a051905180316030f02060c06 75
    0x440008460405520310412034034a54012130140909201c9908900030301700599104d030050300303407060b02e96660b44005101e19845400c0311b8150701207a25a500030581c0080640210081070700c0ea28508c0d10b80c641002001d0080071401003503504050018041e42a800b2040d80305544181810301502020f1001c5030315032041180b2107081c1e80c1d4081220b08040c40d0901410300710100580d00190011284041c2105000030340c090b081c003029259002c6420001e150600d43e2095980454010607070300200402c20182c1001b03500d5a0000b003800504101c21201803288501400c0020720310344408141000f034802a4000b8242c140d4002018000d00700035032180c403070b6407041911071081c0b6507582071102d0026040341d0700644840100351074440d4064143c140d01d803c8000c040c0c400d00740075403a01544c1004580302e00c6514083c0030808080501071008907008406001c62001c02c1031441c010221540c00c1c107542d080b10080d1103e0f5018242401c0011070f8030f6000441800340082c160707600e00003010024506c0c0c40d1082d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 231332464 1250 231331214 231331229
    0x40207050d1e21020915030405070614181e060c01020304031119020904060902041409120930070f05040f14040212070f080106091409070306020f04050604 68
    0x103440d000c4410110700c0c500d00642c040b800d000c000d0031506070707401e0304444021414030308a80c0e000072101c8499440e200300c100b000078545000c030381d2803800c2e19016450b01024411200490644c08038081034200940070340b0b030060b00309108a02206002030410241c500118214804101e681448195903150030004210340c0301200005030b80c0703041a10f402803d0204881c40f5498540080c00141d00740014103c8140080390101c0385c204454131641880001803801120080d4042c3c80d04000402d098981380400b03100b00044425500c0e16001905e40c0301c00c5129400c407540e403244081e6000351a200e140b0040003650418a0103240f0f450302c4114031985002c007103401409500400754002c10007883c0c9809240311606640000f44020304504010b0700801602510007403141c00b001400d5042c460080120400812803498002242962a01124020705075030003140003041c00c000b4030951440c402482c941c0903422181c01010180e2840e21580003c2d00300001c1d011080008000010341075a460300a00040d045a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 231333714 1250 231332464 231332477
    0x305090a060207050d03030b0f0603091e011517012309070605040e0705070f05060a14091507180509040c0603050a0c081810020f03041a060604060e040207050d 70
    0x15441000840300d800da22200442d480654248256142c501d000404981d245c00c011560b1586d600c00a0080420300400d03a800c5040801017010050000501000d120001c4103610710b587d12012500b0300340da60880007031410240d101c80400c00b0500e099240e000700d55500c40009503040c1c1d6040e55101d00808c901008070444600300900c84014010300a000051500d805c205250516145204405230306c010308501c01c1c400041124000d00440e18200c1400c03a034060156005403410141c40e000400000480c1c0707800e00643c800007002d80d480011240c07010012003d80360415a1844404c40c1d40c0b20341c100c5820084100103c000810b521031442c10760065200e030a403118200d00f8100300408984005020f80b940342d0410308034958840d0428001034000340510154040b51034129102032900c941e010300500410b100281c3e00c1e074140f1400010354051481000c011707003042071825115180c03440c29207505034400010042000900d000354001c110200d0040e0016041c881c907500c07000d013031902d00c19020022646 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 231334964 1250 231333714 231333727
    0xa11010f1e060e150f0306090d09090209061806071202060711010b0a050f06070c030606090b0307060203160204090b040f110103022a12041401020c0603150409080405030102070305 79
    0x1812504207820a060541040180d160800c2c241d22160042c11030740d250a40c1002501c1d41e500c803420003d10b28030019085503501d0808107085075039440c411000c280083c0801d03a02040c1a00315000700c4641040040c005414450806a40420070b0500c15499a21603c2000a10000b680300035111192408030703009002e441c43c2c034020113014180007041c0d005559141c85191803440e51280c0c0c1110a84400386c0d60f08060300214004180d1a03c20b002002d01401c143e150000100051500241c080c1c0d99080ea062100320a132406141c1c0d80c00c2315008860140e003092005488801e4003d4589a030207000400103d50304134145c4804112103007d41e0b041e91a0710b024450002403200303070b60000100702400e103421480c0c10350042c0060005407528003444402c9040d4000c000c0c0100040020520482041910b981d95a69420b41009103e840c0801341e80540105001c0410034644482a60f125070041810b1845c082010810003005007204038007190310a01c10300020896031003d2001c0c100291207a21116038800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 231336214 1250 231334964 231334991
    0xf060314180a0b0a020d14090705090609010306020304060b04110a030614061204051216050d02010603081206040e0d02010e0708070f0b030709120305071a0103080307050a11010f 78
    0x8100801000481c6488410300d14210800900034000507003052841d072882c3c40c1c06514401a2094a1010400314100300b10403031a160300340c00903405000c44500315003c0941e2242400b200075000c6450b40c0c3c0c04003040780100040340b0203400031907115102e01800109803420340001001c071820860681190b00300407901612003509445010081c0c006003503507001d00c17601c07040003510394414070796110003144041c4003048c204441003091070060412844825150803090b003114290140203d81604c6502c0b071400129000ca00600c544800d0b81e82041003a40b4140850a82c60719400001d0400760f0096590320f1180392812050000c0390045510341e0010886440c00c5d89190306c0c0c950260054112a003048408205000c0802e031854100c6801782041600c80d030702d1000c1610185500c1c0e005020320b01d542d900707101c10141e000c001420107510401c18a846203001099400c030019090000074501d86d010808140030030701541c00340460891620348150700c415511181400d41d10340c5610700c3c1489480b1501c000442 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 231337464 1250 231336214 231336251
    0x7030c0e090c0a061d030703050d0f1107050409050f0601090506030727200a08011809030e122104140d03050706053309070c110603070302040f0603 65
    0xc4400c40003070802c0c1c0710a00014000102c544203031001d0000e41040c03840e1600e02400640410400182601c082683c0c904103203465144280c044000200303040501046980036005551802c40d105000f003000c41d05003414030004003c8030b81c09503000c0c4968202c0102c2c6480810045003e0000030300082042e04020f030a151070487c40e5001484000070340031001a0441c10b6030603240b80900c2c03820303022a42002640c1c203010032801308900000c68000004401c80300941041c48141200c60700e501000ba8060965a008101c4e030301180010006200c2c2c00b1100d1071481e01c0300e000c5181c44510400d0314000c3e41000c490440c009602001100309002c0800d080142816151800e05081c0b010b8640c5618000d0170740d001000343c410f4280040010750b030b540200d10b500a0744276100c4801100315041f140c00522000111030f0036400580428841c40c8014002801184241d4101014980c440b84e240380581c1001d0402c403842e00028881d5080550070b12000400a44030044400200b00e10303103001400e51304075044111078 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 231338714 1250 231337464 231337471
    0xc030706030e06040b060a030203070305030703080f04050c01120e010e0a12050424030b090403080406050c090a090b120d0f0f031e0e0c0927060c090907020f07030c0e 73
    0x51500d01002c00d40300b84000300c0c1d010352181c3e1000c420311313a580e80c0385e001412a1285400194162040100c08070400000000504071076019032a40c101950b1038101025002c01c044030010070300d400c07524034540d03654001d40d10140024115000495a00307864440c95007100e0401d002000310780c3c01180380302d003408100f0344444d4907120385207803031442c0c6400c02c50029146080c5413909181038505003c18001d5522990281000c1d03070004200705860309050030005c104401c00d490540d00d692812010a684159010846151240140c18005060316240140005000c0d038818035400520b000d803810b00e031040c14403401045481c140c86450000321265030081040e56400544818985400a45c4583c0c0f19103100f056200703e0244008108003403601001400d1400391801d0b980c00c042c400c414480b0415402070a4030000c8150080000042c0c61280c545a071044140c070b001006400030843d44030603007800a00d00b5805480c1c1c0c012200e0700d00c2560031480c07a14056500648019005200c107101d840c102c1260582c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 231339964 1250 231338714 231338717
    0xa080a0b12030924040b0c0109050a03030614040e0c120a080301030c15050c100b030c040f0e0d08040c1419060e040b060a08012d0902090316150c080d020c0c030706 72
    0x20381002e15804040c962065016000b00d0910100311f07416010425000f514840d540302003590b951020924000d000707045640500b03409200f007a1820701d51401e062050010580a01004105007a043c40910424807204844140c80d4042d890009000c9a88000114001c5108064246281e03181861241c20b00d6465510b08040120030842042d40700310024201c0d940c25481c036400201240c1600011b0702d050f00c5845825041410b029081040c050b550b8850a4542c200705c040e5010800161070031034014400321802814540e40543c01d12034016041c01d1000d0380c51000c0c140c40402d027103211a046c104105d036440b40300051902008850301707041c103000d0070285110642d4983d04040f100000600200c205000e0742d05803100c48080e0803801e081d80d02c031284080210110402d40c03c0c0c0c848004d14041c1d4000c060040c080e210b44100b40404503156280c40301201c0800b02002286500140d0842c0c00f03200e4210b040d10b10070420f210051091060f8030003041c82841c1a0002c1c0074007025081854204200c5a01020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 231341214 1250 231339964 231340009
    0x2010605031b01120b03010c0c0507060e180402041d0102031f03050d1409040606020102030405060c04050d03030c0e061810022a03030c0a0c1d0c0a080a0b120309 71
    0x41e00700a075010480e465402400e00d401c01d03549403183c1d0707002451060005e42c0d25600307125003110441d40055500e04542d004400352010359858400c281c0e40300a4846645801000e8113120b000c1c0304880e6030003030fa003281c8010b002261110b50049010140380551044c4403a5942c000140300384900018581800d0420b00403e0044803881c41d190747e80c4480e000c412050601202640d008040d40092044508040005104200d40341d254038000303000b500101c03400c40c0c5034800e020120b8403010000041ea0100e0300c00070b01021100d507003580d0850140120003044002d1010843d0480c5107a51400050041c800c03802100c4005540ca1204001400211100303d009641058101098070016100b66048040b50b00762000c102c0d40c22040801d14510490f02055110700803400c984040111407000d000441d04101d01440c40b164507002e400100c40c10a40c0c2e005031560f01002004107160081d02c0c10f907403041c0e29042c0021100d2034940030132090011010013107150303003001034014240d1502203408210200c03081c8092 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 231342464 1250 231341214 231341233
    0x30309090e0c060a03180506010b07110402040302030c0121060311040b04090b0a0b01050f0c06071202090a060806040b040e0c040f0504020a031e0606060c020109060807170c040b07120201060503 85
    0x60004e01c680c0c1d1903070040580300d14a0b0042132000024000d103c0741d00008984866035105070f50080c9401c2410211590f801d6200803158a02d80303070094500f900d40045c064142103880030010b5030085e11180744044a110f03400d4082450314010702c145402140500c00d0001d0100c640c2c000c0004540041302d4a42c0f003240f4100c40304010801c2150f00a07030182c8101b8000910420800c01a00c1300c0c059001c540700e8020000131007401140e404541c05000c0ca0f070710788801c900440080460401d030b000700014907410000c000010031100307100c4da4440d9085107000c1c00c00500b0078202c034041000c0e01c1d607981c0007035030703543c04284580031900b054850100b0031001410b0801907814954001034000d400e41c80050000c1c00351180700300c2034213010890b8841565004800700001c0b40d54072009010010740310301c02d90206000302e02c00102c9030f01030880700344250440d03968841040c41109110b900b5010140444c0b0f000e920034040440d0900500d001029043e01510380c48140c40060b44000742946c42a4001134020b40240100c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 231343714 1250 231342464 231342469
    0x1063c1215030206250c050a0f0605030f071b06051501170c0a02010e060403110d0c03020d0f1809140a110f0d0f050f040c060203031504180203030301030309090e0c 72
    0x996080d2581203e000341e4485c0e403884010780c01c940b8690b2040e2210481c014900c2040b1042c403031181218810744548a0702c1d80d41d92010700308107041c0c1c418200821401c10008468000c800300e1142d11450f6410100400f040b680b1b101d5003800c0e1071090881e4415514414400328118100b40c01c001040246050841a40403104007511710b4005012404407031b40205030b25104030300070740010600f402c40c2c90890b5000c2c03500342401000405480c03c590340c02e0184010f0103500501c101003140727040ba0141c004100c102504103044a034060590700107810001c0040c40d8241c400d4030700389418010980c400d4086a10072148100c0090540050100e0b001c4c01d15040e624500e01c848401940c03050110890140e0b1075a038042401030180c2000500c00318960301d0036042001504850a909000b00d00900310300800325101e41d0b00b03076601e110964413a0490300301106010228600740c1c0011105144210390142e042078180d0205e441c40e0000c0e0400c030049200c1500900c10450584a203204a4070010020489112082c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 231344964 1250 231343714 231343751
    0x170106210b0603010209062b020a0c02010e01020a12030e061503070b03070e04060303080f09210d0f060e090f0c06040302010804050c0d060c0f0201060e01063c12 71
    0xe005102680d41030009599903401c0d410345985160142c0f0441e55404228111103801181050b90559540d082020a407910800d1081c0da85400c1644c455400038145a001035800001026000d0304600ca404a140005103c2c05140009844142c40c04595480c4401456082680081020f18010500140c03110365550003d4264115200c074880c0e242d507501c0b058800c440b9400221400c94205040c60301c00002c0641c00070400c0e210f0000c8064481c41900c80c8031845485860f40400000c18240c0034010442aa01c0840200b0b00d604003034500040b00c41040c10314405a402650240072421401c40070000045003d00545041d00250700140c40208101000901640218000070381003281c40c10005040103420880c4041c0750303000900c40902e03031450303203042c1e8050101d90070000d001581c85c40070b400c0814014080e0500744c0c0c060040c2c01e54640e0034000c00700d9403d42c100104003101c0c01d0401e0304000031150040f0100104052052a001d50540301401510744010003042c030fa081e62418210000d90300280306c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 231346214 1250 231344964 231345029
    0x10020a0f0e0a0e0606040909030503240a180b0a03110102061602190804030f152403020409050123010e0c0a051603051905030f06010503190905011401170106 69
    0x802003c03060701d42001142e65070003250404c0e0380c0c880c6499410b0080c990010042d52190101100260456800400006607032200c15800c46d0805c0b134543c010720080710014100100c0340c034840c000003000768180d00028008c40880d4410344200f0040310620880c2d59046c0f00080c1d08c2003030f540100c04801280240259240341c194042d41c108012064281c007004501400c48000b990010401903240446080000307003100950310340059103140c0740600f000c4981100c41c182c0c0e400c03a815901d010b103501d540c003032001415202e00112115542c441c0d000e06a0405550319100380780405000e80103a6040080d0184504000384c48600440018082c48904a48c81000c46558400140c0d4130701e00390249150948075030140b41140c514000e0b180c1c00654005502c4809548a1a070b036900d02882354035440015581440191119180f00115180020310716505d07030002c0349068442c000000e00c0b0426076070700484200d0281c01408984c2c3c0d442100b00c5074200240a9140a002c1c2986016024501c2594122000c601c04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 231347464 1250 231346214 231346229
    0x8060c07140a060606080601030f06050f0d0c03020d031706040204030f030e010c05030a020307151401230301090b160314060103110c030d0e0d0216030213090510020a0f0e0a 76
    0x410310301140321042c8214440b180d4004002e100d295121880038101c0c40d8202c5d041800a803810611034440d42d5507018030f83c202c400180c03c01990107080810b00c030842060800079180700e450703041d0020040e10750050000c00580a90780c5c075103140c0c6044c540001000ec01030400740c42940103001c10302c04581c0b007500d043c224907454117051840740b000c0340069810031010000a801404042152150541c02000600c00e0505c40e002c0d040b002c00d29113002008880ba8950088901b0b0300c032038018000c8003880032071899100001800401d0049945d400a820750f684040100c1c0ca110300d103014040c11040c03d0041072440700c91814203204118258180003000003006180c1410581c442c1002c20030f40760305074110344024a0580c1a40d5490706c9885100700980800d00201e05a481410308a02e2018404684896074001c421a0303447c0030f07461502044040c000103090300055036501c00144c2d0004004001005401890800240c2c80d01c00d0008080c0c4401d03100440502030101c160704449865680070085030a55051 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 231348714 1250 231347464 231347483
    0x402030607140a0c0201021f0b030d03061a03071119020909060402010206150f04110301032114091513081e0a080c010902061b1002042103030f022208060c07 69
    0x9400100c0c50500389517071840b407460007030748016801190358102d500b40c42703410350072541c07a0031001d9011001c4540c5846202c1550300c0548101c0030550645000350b8000c540ca1800007115403a18a00c50b090410000584078028020b10b1034204605241b121158000c1001d0040d142038030307183d00040e40b5060020020480c1a0071050308851030350322140113041d100c0700500100310b002d056407010041d5500070300068840521541b034103040d01c1c1131403400c120030740065030b29600c014554118041f407a40000351029404580d4814005008400e103000c3d100f4117078103803e010401c0e40343c100340f40c4c10817145145004540e1049039030300c0b50740755001070340040380c44d030222542c2d65540f0a284854010151808001d40c004000115102004080c00258030400324600990310b01c0f101d20680a4100c0c0300b00e1081da034012411050202c1140c0d100f56540c01e52500904000c00c1101019002c00206e0340135214604120381400c100e00c0301614002509005041424001e16240c1810554882e45001d4404024100c801 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 231349964 1250 231348714 231348737
    0x6050405101206120501020304140c03120706060e07020a1b0b16050a0203030f0a03050109061d09070e011d01080c1c0c0302040c030e010b010c080315010221030402030607140a 77
    0x8440e07014100901c0d020249480300e1040b458018082c1d48152819143c2e00b10312b5400307202c07640000c2101c8541504c0100101003030581010069000c2d08464015621190359440000c0c2c885c403680c0c05a441800a94050700000609260441c04d4408100100c6042040e0b50000d1003c3c030609011105142d0041d1240e814140142c41c02524000200074000e40501000c90b2008982c0141c0001e0b0400052584050110340c0e2038031002412140d46214003400030300e0240c0480086135030f1400154100d1300e00c2c8203494149866004401841400f039001c1800c0c2c00880000c1170003040b8041c9018050800344001e40202c000c6000003ca091020118954582030300c42d041104004600e02e0500007903501420500048250394405402410360980d0030300d1650909465908941c4240313401125030340c0c0030301e00740e003540c803022070b02c503581d0310310000b00e80c10343c468180c0781000c004980a60b621202d640c0110305940e8a8648103045c01e00c000030784003030180940748100b1006131840f102078942d20146442d11050f0940b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 231351214 1250 231349964 231349997
    0x140c0d02090301020703090f080303190504030507050105010f06120506030c0f13060303120605180c0901090803040b0c0d08090a02060306060d050a050f15010801051c0b090c03070605040510 83
    0x41141c10455040d071000454004064000002c802150346c642d03c4011010b640349413282d140d10048411001c0a040112061024282d9500068003c2e0003490b185040580e60341d240d40c01c4910a030441a4624081201080b4583d44940b03e0303840542e403248140000c1c109040070a9513000c00c090075510a0084403503800940c0c030707400c1e9900d01540b00c66070103010307aaa69013009031190009100e0f8008041c14910041503600741107035a00d20038480260201e807140e40c3d640040a0907000341d80740c581004900c0388006801c006c204003400c0178041940482d5a40c00140258a2070310400816800500441c0340400040c0100425441240c43d0107580300d41d0381e9500c000000300340e44512100f107100740c0d16000510207568001e61196119084442444900740c448904950a00700c1030910345002a40c0c250050186003442494142c12604010844090143c2556a0110200201c0302c4001030b620030600808103140070003240009141d00d091291070705003400d0204440c0b910180700380c0d0034017482045a00c50306 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 231352464 1250 231351214 231351217
    0x3021506010512101a03190b0a050301020403140f0606010207030303020703020316050f100b13090c0509070f1e050a081b040b070303052d04050309041505011101140c0d02 75
    0x98010f400c0d62012440c101404c8450b1442c00c2c0504450b001c61914120036078400f100c216406444c980309440149944002c82034050f095000031540c1100f040030000503580c42c240003400c0510301c98050801c59082c860881450960440d0f0044030f9503000409001007660082409000d40741c142c500940d03100484c1c00c082e03245102c0c11080c1286050214600c0052200200b44154101810800d4a4400c130060402d6001d907a01943d800d64003800308820110a503082b9400300c000c0c01d01c2140b4403030382c40b5941c00001c0c10100c2d0455a101c08180d5082500c016268018036031814121803d00203440410303030200090090145010b01c0080c460800003007803141c000c90260103140d00c00e40c00a030342c0d07458030b07281d00319103d404c40c10040f000b00c2d0502002c02c0c0d42c01415581c00f48006a0f1401c140d880d04003481300007203101805001910700b40002c000605450320b540c051415425900b8208803801460000014041d5006c403654407002c0e4582404452103042080020760881115442c040c2c0b00e24603800808000e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 231353714 1250 231352464 231352477
    0x50406080c1210080d03060609050d03030b09040b061002070e0402040914060a0606030b030307080f03040317011e050102010905060f090709140609011e031b030204020307030509120403030215060105 87
    0x21090310702c2c1001441454140000b040da140b00c4150350384052008400e0f01515128003580b4041076407401b0611407420803503002d1085a00925010804c10600d201240b100749080e941510b01c841c0140400c440d42c03e0140503180e4007203041c4000c040041c074010074a1a4840701510083c82076031100404801d04c802c1300c1404000b2050f190544e451400d01e600c1d0b0200030300c030380d02c100400b281c14a03654085510b000710903105e040d50000e4603603180070320b0050002220742c0010011024801c040949950400300004018040c240310480409503084140f0300c40c20300440380d0b1046045a0401e000000000c0303021034455004074101c10044119220083d026050480582203105028600036500a1400c0248842030140d00c040d101c20186036202d48104800c40311101e200094071b00070b85c1007040022041d000d066420b8108080304038110780c0700e13800541603900a07258800000d48401c14040038820034040210050308881c81286094516500651200104903440c1c4071070b400c1d500090301d10b9001d0f100300c502 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 231354964 1250 231353714 231353737
    0x80c030316021605150d1b09050301060b1c050709080a0302280203060705090604120f030e041e2301030b1008061b03060f03010c1d0907050406080c 65
    0xc903440e01d05000e1038910140039040c001403007950501071050034101e40550985802402c141c106420744840c80c038442c3d001410710300ea07550740c0707030403c0f005103005a4080c0d841b00242d40e0f500700d009140100f0182541c1c0301b9000310354002820002104044900f07034150250044240c004105a030700c07014142c032007264651001030107000e058401c03800c0690124400c00007290401c1400510b103511810840c20500c43c442c02074160340f03d00081034501d8003a90140c00317002c00040143d8605902d80300c1d483d102c52001d05044072400d411800c403004064000d00034244501c001d8504001d002d0f21890303643c40810302001e1b4250703c15a0b0701702a051440c0da0101d010071004481005100d9035035a8a040744a0500494110192000403040031032500e01c04201c0e1405558070b0503405401c2c0500a455003d640d00c040c0403141c0c0204030300c4102c2510f890a00488243c0e2602c0e8484841509420340058051240c40d284644141810341c1088036058010f403c0c1c4094038228600a801503a0310f600c511507a119021166a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 231356214 1250 231354964 231354967
    0x912050a05120c1b0603061e1906170c16170318072112050c1e011d0a06020a0c150f0c020a03020d050901090e0a0209041805070e04080c03 61
    0x240e00b600040003030880f403150004580341c0100c0c142e1030113241c03c041e0b540c0a90295003000407e07041d00d41000d00314401c0b510140388070f005040440004424040d41403070b00d03529822644003000786942042e03140c2c0448890380443d00b464a4039031904880341c800d62041280d00903000075405c081c07000540d1044580e52102600541d00e05040c0c81b114a0000c48070000c280d107115020011960054420240c0e40986207100c18800c0c02459170f03100981c80200d005100204101886000c5601008014410480c0002140c4078040d40360f0014941c290707050320f03940078100d224807000c001c1c1d000390010303460841503080b10005071200700418089500c0d809160f00500310440f0218030803800300301d65001506034403194a0404c00c41003000c00507a1100348880000e80540c010020744204e246c0120010200f00c141450712a80080e11407968a8807403409840c80d004441d40482d54000d5810184600165140e601e0740003290180c0b20350340c503540c0310014000c0741244400640032404005c0e460064036502030030002902d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 231357464 1250 231356214 231356233
    0x7200106050901271802031c02060709030203060c0c16150f030506030624040920012f071208090a241407050601030f0b0f0105010912050a05 62
    0x15019204500400d031259100704000541c400c2d0b401e9002c104104c6829a5100042946110b0743c0185441e030024000c00072480b01e0600185c0d000d00c044282ca060321895110603040b4100005c0c41e18000918020138000416030910260768001007144d4030030900341d0000c1e80e070350000c008181040d00c00401d0300300141002c40040745900b03006040700d1494145650381001c10362250000c40550340151001501500640003080c142400c0201c3c0e009094060303c9000b210501c10008282100c0e60031030181d4040c0f028564420007200c18001c01c21800f030302460710300c40e04100820300305031070300a2038104810460801c11420265009005040080c4202d000503d0b4804090074421002d60106c08042d10407041480003049100402d100d01941c0581d00b1580858041d0110b025142d0101560508415003814410305d00054420051980618400c036074482016106d444c08203002d51001d40b40048402210006104d1643e000030588110b801c0f803000001801c1c0c2d00e00705942061018880603140d4018203104 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 231358714 1250 231357464 231357527
    0xd080c0c061b0d02060402182703091e2803050102040b0c010c0306060207090b0105091203091e0f06030402061c1d070b04090e10050a090b090105041a07 67
    0x200380e14490102603c910b0240040204d8079008101d800a42c040703401c600702e4042c641d54070203541c3c2c0902c000400d4481c207591003c06507007056a130a41554076510010725000b05050505404450300420006800070745101800146079a54400d01c7e003220107800c083ca031084090704800350009640110003159900e840c6c1881c10001c0d400841401000d600f800501c0d00c20034401d2290304200d4900394043d00b1160300703043c10400a413604c500010704210091200c03150030b503144045012240c00c554019503031010300c5018400359100d900080101e0f0b003100190003005403290814a16040c00840d102a901e940e2440003c2c5d1a0003029003042c154114200b14010886696020003003050700c0c41d00310300b018a0241c59003580e9007818000c00016800500c02006040c0c21070301300300c03030f00042e960540340300d141035000f42c0080300c500300c0341c5041071512801110144a41111403070b41141102d40203104d50f20700781e00e5040c0520000301161114250301c0c00010415440b0f00303110014480c0d50508003081d00a00d864 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 231359964 1250 231358714 231358747
    0x1305060a1d01171603140109080c010c030507050301030f030f051216020f070b040902070c1703040f050901240201020408070e04140c09070302070302070e010605070606140d080c0c06 80
    0x3401d43c0c076441400504860180014080b885a60420701980300a030465940d500c0440b80a00c03076003159034a4124000014921501070540c4a14580001418030004030005044d03403006061351091007000c00044c4003003515401d600d140140c25040c9040c044241d00c40c1107030f080c403550442104629010082c445624642c4090301d090303034120307401c446040043c80203c0d902c40070a442a0180f9490401c02044800000e402800d010350091401340c040d80c0e070314100c0300004841800c1920580d000010188168440b90801e140a8a4103a540c10349644c1400143c0c96580c000b000380702c82602c04c0f0340f18401040d00c00d404441c05040e141c41a1209c080d070f10003100344100c00640703013105c100c2c45810300546044400100b075488500014100d400c40d440705481a00254898402a02180a07003500407810a1036510618003d141036502d0036622030b0941005000c480b0a90401070b20000d0032803406c1c4044d6194482c644146070880c60a07540c51900d0240b071031034402010a1303207400250100f80078014410905 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 231361214 1250 231359964 231359969
    0x311280b06031204030201030b030f06010e10060e0f0105160c0801020901260c0307090f0e090f0d091e0909051e070b2b0e0f0c010903021305060a1d01 66
    0x1004030009481e00c1003050307200d009000403610908002c0c0010000f662280e00404070121014040d103842900e221110350030004246c0040007200410740901c00c48081c0c07801c0c1390000b80036516012500141502c00100385c04c003986606c604010010400d00207030140a0394000c003099100d40ba56030341e10741d02c0c9038680c042d4210014660119404904094401c06090209200a010030040d148580d950150b5811150030251101c1c041102840d00401c06038400200180075056850040c1e10601c0e1060a02c5e240040301d1440310703030540044090807003003900800c0410a4442500e000c02071400c005980717200c0d50303a2960105000c2414080c021003441008a000c5040011a00740f81d9404048142481d83d12034161081c0c4440d0b007010018032080b1481803138034144801d01540862400780342505803a003562409000e078080b58020301c0c0324040c4444204208101c08000303080602e1494503640028107114104a00c90442c0ca85a8001a8550f510781341e4882c050b0103916541201000480e000c010396841c00d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 231362464 1250 231361214 231361223
    0x90b030709050c09090720010501031101050711010503090312010b07060509070b0405040f0b100206270601030615050307090b1809030714120c010203040b01050d030507031128 77
    0x10404100c1c1c035441d018940c81600c48142d00780c902a0241d0510000150090014003045480301c7c0100d80041103c0a110308202000008034507541141000e903891020400d02c035040c0441080b05a000410721090380f1450142400c290b42c80b44c0e10501442e0951080820312560245100000b05058075410050071751540102400c0145075a003007035099407050140940c00c1d181c0c6d0113100400803403420360000007407441e120f800420560402c002160700c4941c81c25640d8090b81024040000c15059440218114452803422100c00c1080010341506c1e11018000a004140c56580903007820316040801d5000307000c003404484d001e60307540c3e60a01c01442080c0361a4899035806241d1041c0031001000c01c0d0040e401030014501c0c3c552159140baa40c554a0424003d25024202061070100440009402c0c000300490016135170740351a00d040030b41e1010582010f03220708150003545021070b40c0502a911030b1541428030700d020400c01883c07186072603025882c20044006105158030108184c2c00c9180999104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 231363714 1250 231362464 231362473
    0x1e070f060e012a06021218010213050f06040f08030c07080c0906040e0a0822050a030503031602160303030204060e0f011d040e03031006020d050a2115090b03 69
    0x390082121110780d549411030003e03401c0081803403481e600d840d40c0c0a032600c0f9400e6403003144000fa03075040181c1e0000140c003581c000d040b108114114021400d611000301d140d0740218640054080c01030412101401200c0c015510300311802500d44070081141c000d050b00980c0f200d4400e03580c180b81030b030f00c1d803016001c0c541c980204040060803480c000750318000048020300c02d500568524050200509090780c2c0e070030181c03146401c0c0c1004642c4034801040c41542c148420703240c2d45400035042104d800d15a0103030b4055030010f4002c0012500c080256500300258001c40c1003044000d0740101d1400390078980f414914803050b2000000c140e015070060007201e00686902600301207401c00c01551902404c0114003142100403007402c030340f070508204251840000c100007074000d0340c0d420451440d0800c4a1704400d00010607001e0010039010040c01ea00c5004a2620900e0000c0c0b405006140512011300c0d80e4514001c0f06c0000780000301900000b00b5421080c0d01c2c1024596a03595903c09084200340b000d02a005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 231364964 1250 231363714 231363719
    0x180d02010903080615160804060e1806150408010c080a06090203160509031f060e0c03070c23030a020d080114180604140112020a0b0c06181e070f 64
    0x41c05115085a0940c4920382955107a03030034800b140f0b815000da88500c200c204800d19400b04040c030090401401450150b8959090a90103403814404070b003510706c1410308400182171080380c1e141032603001200b9207161804010310b040c001d203240516003245850b542403640c03011b9459480480d0601c02c1d001d07a00305002d050782c1c2c3c450030012440203864101c845141220352603c0c03140103c004051120000e01140c2d03240e40340d42c2d0890071692aa00c00183d500d602c6440030000c105424400301c0d000342d580b0604500c2c5003800071000c1c00c851a014801402d03001c4014420700d000f14100901d40e514140c2d04107070396484141c0131009494814401118000c40c44c40000810150b440d0700000503003c2d0040e010020040b0b10400711230810000600480d40240c41d518008402d00c0030038a014001c0501d12180000a4401d01c100152a0140c0d08000358410090180c0720100d2000a034290300310a86420001e51000d1011150f03007010541444254550615107004500000000e121800c5920882001174040e4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 231366214 1250 231364964 231364967
    0x7050114071d0f01360806010605040915050604060e010215070c141207050307030e0303280e1906030e0a080f03090c0a06030207020108070c020a060318060203180d 72
    0x10450400c6001114900c02c450b603504052416502074107050400c42001011440c04400d8542298990b060841080401502c1d507007006041d00e0242c11000c010f08060342c101341c0700500d00c2c001d6100d107002c81c644a0581c080c0000e2000b0000018000140c410707a50b035515484094003028000030054018418044410096441c2591050140c00190740d1100c9010f0b5030380700c50742e980203100041c030001d0180748400751100c407290004114042c80740014503107403500e500300904602c002d980700900a40003007000002c1075100c1c0d1040809007580510031001d59100303290032101034103240d0515070031100142d14001a03200c050000421544683d50901840c07001491864441c0d10816004110880501513480600203081c007455106100d1030440d40e55240c00c100280903050f19901841c0402d5002558400f956444540e072540040d0034200314070792540c0e40d40031401030402403042d80205699030b800c117008171100c550444030060704400d09644a0030401202008540e040040c01c6252040070080d80815 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 231367464 1250 231366214 231366227
    0xb01050f0d02060d1d011517010c1b030309150213050f0319050a0b0a0c0816020d0e01020c090f06031e03040306180503030403030b0108010b2704020705030705011407 73
    0x803507000e80f01a05140140d84c008001c1c0c20712003908290301071483d90400200c0004d100e80e500302c402c47e0014560703041c40c00142068031152213803080c41c02e0741010499043c0030740000c00c0f151f220020f0a9980d4a4490504040340100025200201090f02c119019402d007440d980180500e200704c0c4030716085050703549042020005a112046405030030054940b100c440042c0d10040829008034203a403082c4025945160100c07008454102d016a520114000e0360307584600034a5000b443c020b248d64030440c2c50b64001c3d44d1600026003610170002c130b602c18a2120791080c44115075014000c0c01400381402c00e44004070398003030200c500174041d00c02c00f02070081030341c5d04060309000345100c04040d40c60542581c803000041c3c6051000c4d0f4004007c0b040624000800400c0210301c235600075a000200e1550340d000040401c0c906034000e1919101c00d01031b290031110004495000e0a91a91484480b00b544c40b0101d40680035002c0c0c050312501002c905282400b4064000f0b100012112400403400e584801068440c0f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 231368714 1250 231367464 231367489
    0x212090622090b0111062d04080309061012060507020708102f0403080a0e150c06010605030108030a030e01060504020a050c100203011d06131d0709110f160507030b01050f 75
    0x194454001f1030041011490104400d5490450760300c10a4403000f00d10105031070a460840e2013100000800200984c00d0040c1743c1c000807030110901d285441d2010b4680d80004882000e0300c1995654040742040d13008004903001410703014155038994888000b10700040c803a021004034040300a002c0c41d00c1d00086902c8085800d00d14600490509056803642c4189401c041100c0c024814004803040c12a83c1e07110751240381c0755080001079500c41c8451601030030140b06030300c06002d2050620060041c0c51012080e1003a440c0903150014080038a4802603024041c16403201d42c0080c40000e04a06035a80907005007030f251040012500c1444a40c951182248000d12500c61803050400c44440010250540c840c0c2040c001042c03407101e141d0900c2c2e0301040780d20500150b429210020a0429250720500000004000c1d1782d0b01008070000e201c885214502c40d1808400001030700180140e0700b401c1540d414029941c2280886c3c2c03280e501c038a00081c103140d080c000d40d440782d815224000114500070744034014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 231369964 1250 231368714 231368747
    0x909010b0a0315090503030103140d030516050c01140a02190c03020a02010f030b090a020405011704020d0204110f03010b090a09090c0b0307090305010e010204060f020604030212090622090b01 84
    0x10719840c0d0340b9001010b400c010a114046a00c0300b07005808100100090740c0a980580351406000441c503588501e01900701000b101414200000c010480ca282140c40400000c141030440c0d42d03d118440c060700400001c3d030f01f03c200c0c0c144001402004040c41e4080d041e0074107092313040c280c00c0340314040580d2001400c82004005900c1400d815005502ca00002a5030342244d040c04243c0042040010b6250701c004c03034860140d1a80861b08000560788100d0312050720445590400150809802282480a09101c0a03000e9601c41d0101c00c41035040c0e100f180c29510414907040e49950711403c0b00c0b8582e0340092007492042c0800342c03020860041600c02c0700070855000ca010300c101403519802c1481500700401d40d40520004030703c0040814800e00650340c6220000c000180e0b150305014020300014000100402107501c00e0040100203a00001c00c456040d040010040d22224030100041081c4540c800c24880d01c904810307500415088059003105480d2001401e0007010b207590011182c070040b0038407046 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 231371214 1250 231369964 231369979
    0x17101d0703024e0f07030f14030a0f0905040b1804050c06130608013309170304091d060a09020621070807081608040c03050102070b01030303150506040608060109030c140909010b 78
    0x2c0003072070401547d0400707032107032010449400f8001c00c1181142c11108030b100c0428034a00030603c1d41503100c1c18000103810112020800400b004010070511a1202e42e0185400c1d107200100f414482c080120307084414000b0091076440c48102a18442c0d040c6a1081e540459503420000c95601c400410f511040f403610f162a643c4801c002220315800700d2644d80d01414401000c0d00072516420345d81c980e00c00300c040900256600c0346000108000c0307500460903d101698a021040c00100c000b041d0103810802101c0d020030248103500000301a88204041c1019880c1c201c0350044010718050804c503c28510b9440e078203240d41d40c140007030303a01810888610508142c40d41080c602c1c0360144c610301d03030000d024444414410384c41f07544440c2203a024520965501184400400805a00d0b00801c02080d00c15401d00d41c2207483d20010906601aa0151006200385400001c1040c2d21a4084100454102c90348034112aa681c01750080400c040505031b001e001000c002605146050086041200c80074101e0b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 231372464 1250 231371214 231371219
    0x3050a030b0a080616021b1c06060e0a050a1a0102070510020f0d0201060807090c0530190b01080103110607050717101d0703024e0f07 59
    0x2100185111241c1903449032540340d01140c0c09a041051a10902c461084c180d1200d41005000c1d15280151110603c003417151481c81c2000c0e01c0f01c2c101d500843c100c45550b08c0740d86140f454108050003450300b114100c00c80010030024401c0c00d40d0441401100c03003010800c21300900c0480c240c0c0c640c2890380d0460140c0e01025080205050102003c0b400e0081da1040d03074503000d151842c035420035540c162070350b0050b0344408041c80614000c0c041003006014014040008103414640944540648d11503605004c0c04000c0c110049041c1201e2441d0341c41d0384030030765261403905074601e062296034802c1440b5010310307110050026501a00c0407a041c0c035041424071103500702e100c0802ca50343d4000c103011603482c080d0030300002e04554030a00d0442004a1074024007c031005102001c1d049821a00031a0003001022017034164092000c10b0b00415660195900442c1101c1c11100648c602510020104506014002c20b1409180030095404244528100d007119030178001001d03684940c58101e81042d03400c038034000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 231373714 1250 231372464 231372467
    0x9060302160b0910051e010e0f010603050c070203190b13080d0c050f04060801030209070519081b0c0307060b030f06070e0102010f0c110f0303150607020a0b0f040e09010903050a 78
    0x2815807007810407003260312650321a001c4d00c0640d00203036a128800c0105070000ca400e4034111500f640940a405841001e51500d012514039600b01071144400b410f40d00e0000c41c00b015840411940042d0b005000c544001c0c00c01c0c60382e5048640054006e460001d89803010402042030303009603100840d04a00b5940c18020000340f0343d80200b07500690481030200030090301d2022150003020344020001d5485600056145005108003588018a01003c100080090440c3e82c41c0b40d198418200c0401d141c41600e6603107100800c070309115035440c5922802000300303012854110002c014074500d4403c0d04140480040030040c581c2e59241d0f00e042e801c00d6004000010503007032151501c101d00c240e0508c00450400721360807440e412031303540925020004216803000801e40b03404100c80ea482c070142d68019851841c2c03000c42e01c21a1072584c5401c62158070b0010789501555124544c4401a02055100135071b11f080851b24103d40368403d1189101201c1c01e5800070319920741c103204a44095405884442c1b9010340c13480f0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 231374964 1250 231373714 231373733
    0x90105041707050d0510050a05070503161202190e03010c080708040c0509130317061e010201110d0504030f0c15090203030d0c030203180c100807050f0c0309010906030216 75
    0xa407284921030701d40d0004180e0382d40c1911582090080300517010b501c03040440201074400041072170800b01d00701800c0c05600c640c007400701da911241c400d02c080c0c0b840c0008070040303440306e07020060448054004510140701050181407101040720a40722118040400e000741402d86201c642d48001050341003000600440c003514886501521032400b10000d581c40d00c0000d4640310342070f1303660b00014000483c000d04040d009112031101c020300c11180902c1d0f2030120000344e02c03a075101d031020a001d0762041d003418242e4000d400c04c900d01c0800b400c03441c1e01e4504188440c0c0040c6012642500014542121302d0341c84c90140036148009504508051004140c2111350000341404e040c3c120b03058031080100d080412014480e0700c082145070340d00903a590a041510000142071001140c0e4143c0000c0c0110300a41e58880300310b80c14408a05043e02141d48004054600b0f000703403101d000b02c0010005882c2c01012021000707008100c030980b25075031000e03280c100480882c014800442603181200d0340001c0420558070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 231376214 1250 231374964 231374999
    0x50f0d1218031505150105070f02010302090f0306040b0403170108060601051606090c0e0a020c0601051203040807030308040302070906081e0708070303111209030a0b222609010504 79
    0x44840c0a507030700c2e034035980c0f09081c5408030b02c2100d0781e4001303000201c5140241e80e9201c0743d00f4680301d0304062980d100d0728221041000004e0500d58000ba2403d566128850310055400c001410368800c0d20b80350800070001c007011201100010301d104042414600826200e0f8180c0b0103c0700107103642e5590100665aa81c404440c101c0c0f210498100700c40002c00358000d26060302d11610101c1074292030080c01492151001c2d00c0000f030717035005100711000c405c0005550f17411107804850038a03000101d030425a0562103160485103890043c0320b000b005150700400031500451081e821a00720b96601c50002003100c4150040c0b0b52207402180380000343ea0b03c0b640100000c0400c10060303c55035640d80c50b05070328080c129030003200440e140400c2816842000c0c40360002e00040042c0d224074018074480040c2d05c44c0480c1c07000819a168400205091280f42410080790709030030030204600802600b401c0c0c820100c55121407030007400701403010090440700000d480d000c3c0b00c182c482d1400c260401c48251803828030031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 231377464 1250 231376214 231376247
    0x60403020a030f140706020a11010204050d02130b090106090e070302030112110127140f090f0a06031e0501050615090105070303020903030f0403120914150d0c020601050f0d12 77
    0x201321050809601034000c00a00384204801070781d0b005116030160020020505024080c0d105004c10009900d80b20001c080e5198110746848241d282d0441d5400241081500690002c5600002140040e000031200013a68182e2001e200c1d243e0720844110103030310007401a40c0000628000482c0042e03882290008107410504240c401d40030303241c0062428501070641401c90b15859502000907840b0101395070780b22202940e0151506507860041410984061f12002d150700c071480c0003420395a515403009000d954001805000b200c1c1a00001ca981c00028a0564140d40f900f0f02246d19454101d409200780855160001d04140d002c000665064001800513018160204130020300d59074140001c045031a440804035842d031703055003001d050b08101241c0880078094405030504c2030003944010b13044441070890b203000001c0c2d5044040d8205004141d5110303030340313070034003141e10605c0e90040707601c0341a1030003994030420000303041080103980c0c08120000340040044180301c3c42e000c1c1c03140106200c0c05042 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 231378714 1250 231377464 231377477
    0xa090f03050f09180711010509070e041403030405211201140a05031204080106080f03090d0303020d2901030b010518040917070b07030204050616050c12150108060403020a030f 77
    0x2443c0841d11081c0c03031080b0350700e940c1c82041c204480c0135000441200d01510903402048507141c85a009076407650075000340e49500c80da010011f000c224800d1040e8921107200700940e512810b280c50a690340d4955075200c00a0100a0980030350700d20400801d42e0350506280003001c150b640391580c1d03040f140030001d40c100e4100c8001079020603141c4082000014401c0a60b130104d907030754509206107084500540016510f41c100c59600e00d0b4000340001034491000c011a00540c100307045c0d140c00c0d4001d1041e40c031204203013414060940c01c803840340c2148910001ea070b01c6c6807100326204500110304503011110b015000c01c205000540919400324910300c3c0841d400b800004490302d207911400407110101c0c043c0030038202e0029402040000d00351507d07420040609041d0b00300342c1814009810344c098100410260700409400009001d0300f00006000c2d00d90180007101c0c070040b5a01226150001007034200311100820740000b810200000340c0a02c50703501030b03004d0007540301e0558044030021119599003040161 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 231379964 1250 231378714 231378727
    0x201504290a0b010e0f0f06162414011701091403130b19030902030a170c010c0f050301050d05120d0605040b030c0108040213020c031b0607020f0607140d090507030b0a090f03050f 78
    0x184108d015105004580030002920300c104940c084600544204505c14144000311001d00d01c400d485c24195030f50900303200c03400d41c40d038440d080c014902c081020b003d119010440c0e01d00c000002c07008000c4081403c501ca010b4986030020392450b80320b107881d00346101a26400e09151244646d00100e607161006043e90030021094841e0301c04188200c00742c1000101c006821707004990248541d120030341903802c1840c0c100391250f502070040d02052040c6401075840b68031903c2000018841c0140320603041084548850002250703d0040065000e820f0245151102c1e07030095190014011000304416984c10809948a80c28404122440812003210640030f2040f001001014070190052100e840d980449582112401d585420000790041d819034210010075141c6107000700c1e0030f40d4405d0203414051548100303481a03044a21a0b196154901d0346000300c40b80c01c0040200304501100d009500c080ca258441d0747c840b20440f0415007005000c038240201c0880004e018401422195040152107410080d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 231381214 1250 231379964 231379987
    0x1e0f03090b0106021608010b0315060409060e070f0602010b130b0102070b07060b0406051c12020a1e0b0f10061b0f0b0601201504290a0b010e0f0f06 65
    0x7002030b00004096000340a5135080108200700340c0004011410080c44a28407120100ba1a15841c40003024009a04000540d80b52030b02d4202c103100507800a01080141e407802c0003103482d060700d40584d08082d549d400001802500c140500207104000038100170301c2840032048100201501400ca5055009109000800c3d00024024203c600e018040c0030540d0400001040125401908440d2041c00c940f102c0a14000c032000c0e0300d0b81c443d98046150502e0701000c0301c0030380c90503065000041c08036800d41d40040c43e501a8841149080e4400c41e8034180b2900c400d001e009031480210f4100d8400740094108002941c8110724085a4000304024031a581000d601c4500051500481c296480040c117401e200c072550307205d81f51002c3c030050780d9446030285c0e448620340c80d1074095412101e40c0804100020030700780054140400781901e007910726003041e4018694800744081007150001991494440d05803181d5018140180180c0e03401000f1443c003410f10410001041e202c011348641100d81880a81c0001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 231382464 1250 231381214 231381233
    0x170d06031b0513092004020906070503090a0906030b0c280507050601060206100b090406120f11010c020604061808030a11061302090402010807020a02030109211e0f0309 74
    0x14050703a8450303640d4140b505100c0d29a10310314401d201c40340f62006981c08603400c40c0c80c0310000c0d1200510305129036040b80c00503000c2e0140b40700159100c400020074108000000004101c080c4003030b9004869544d840b0030081c216000c500c070141c2114840c00019200328840c1000b003032740c00d003414611381402c150400c1d1058010301c2070381c0190218100107074140900c02c04205050041000784000c01c0c0f82d00d084c0b190182032131210300c10005081c1001c03500324901d40d680d402c41c0018107110048031940d20aa402c12030780003c4c0020090b50f11525030010441c565215600646050340c01500031481c01d0315000d012a83e0b0f1004903050200c5003008100031505510520050103800ca856031105052440030b002c050800d8030140100c81c1d1003200341010401a22003a2201d5406a02400c16204684e500c00e0164201074580d0310003541035207880d503205c041011114554005040058401c1200d92403020196280c17071400d0480300c080003c81e52417642c0c6a00c2251000440c0890b46000701b4124072603074070380144 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 231383714 1250 231382464 231382493
    0x1802090604050907090915060216140f010201020f070305091509090f250906121803030b0d150f05070c030c1407030b0115020115060906030c090b0c0114090a170d0603 73
    0x44841f803030000c200095040160010a240300400000c0540c6480c003400721034400d140c0ca103401580305040910031603001390b058850203151407513420368820300c51800400561008050038801e00d0704050144680e02d440083c0c03650210f02901c03020300d40d244c049102900e82402000d114541c00095135103020300410300e00703408550407030741c0b50300108904110014168440108200c034243e49006698908031b044030745481d0b00e03141c040c103000503050300140214101840f5130300054282d40a40c1039104002040341e110101005850710108141d48501208407034000d08068054001032003140f10f00007051a981c00240102c4c01d0320201c481c202e40c0c076640c07602d0b012000d91100e030800da0705110080402d90203001d2040c00b07600300c0041c000341e1400c0c800f015280c0411802140c08050b80c440894030400e0140c040304020b4090054400d403500701000c01d03240a0020b015503c105400b203040032600035400010700002441e40091411081c0d000c000d040d0201e50081403034100081e41f41d40c40000800c4907054650b05 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 231384964 1250 231383714 231383741
    0xc0603040c2706080f0303040204090804050a0f080105060d08070b090f10050a0606080402031f110711030c010305060a06080406090807050d090506070309050d05120d0618020906040509070909 84
    0x191070640b00c1540403a0f41079808003030b060b003000101d0b819420707011040780c1e8020b40c100d600044a0100341041c65641c082c6030489904071482e4000440c5964034424400308032059400207001c01c1e5600400c0c071410254207071004144403024482000041c002403c0c0701c1c0e11030345102c200d41d00b100808142d01d1605000c40140c82c2c840c2d80d80d505020001401d0300595020340b909090036880f504141d80880e645501940404030903200603a03610b216000340350440003010524081c25a21640d2608112030300c40d424121b128841d101c0e140080340c455020303001d058070a01c4024680c111041c6445016180320740c00800c121444c0d40d44d00829000a00440c02404000e8081d0004101c0b4084c0c00e503016151000640285210b40000c0c4801000203520540c20703000d13900b06891540c1c012401c2e10740b142c42c000440b000c0160b90013021480740080f40c2183d124408a13100d900d00302c6102d5205116a80403482034680d05a0031410401c02440b503410115501500440d0303d1a12a42c441e0703a441040c4200c13070380c1589101 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 231386214 1250 231384964 231385019
    0xf050c07050606030106080303070c0c1802030a0515060f070c2303061302030303042901180c090b1e0c0316060b0105030f01151103040b0a0f02030c0c0603040c 70
    0x2410310034108500d81e40320400313078000c1003a107003004415986c134000104000d08004400001c03404019039824081c00800700c00210120014809109001a4100302e9280d08014039110000e2002282d08a9280c1e47d1840603103260303c0c04d2500610700c10fa503445404c06480c0841150000181040551009030013101d4104203110035200320010141001c030061300c0c1c1603800d0105128200540e502004484c1c0103903000d104062a00b100c044081c581c0994175080c44000102103000040f400c603103840c1d27280503a620004c10014007610b0907040eaa281030314001c0d1102044284400840d0108269203000d1030102084c4113400c00401705120781c0b856000030303020100d01c081c104c044c904101160091510a5400f401d20604516040007100b042680500c00c9005500940d0101c1c005103000b034000c00344110012081d82d5545846402c16647c1c3c5e80860301000c00520070300c2e07510001030320100540c0c02001e603071005041d135200f220702085225000503105641d01d0050110002e11070210024400c04074411a0009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 231387464 1250 231386214 231386227
    0x181303050c031e0405010f0c1e060605040e01150605040e0406110f04150e0f10030902010e0d06050912030403230405090103121202031009050a0f060b0c06100b070311010f050c 77
    0x10b00d0000c003000308005014041001f60300240150580c488550501901c205020900740ac251010b06041c1c1d104c15009890011103843c41007040d0050340f6828034540e241c4414a5503139008840f40c0c0705501c240300d80350601c43c012900049240e00580308140b500c80055040030292441200f0541c45603110a920040320303141c500b00560403420800320410201ca015955858001c085580f0641000c001c60400daa0791103007008680c0950b09e805560800a400c51103d40c41c1860060f004000944882c41c540c8a208030004d0010700100449110b55407641d2139080264002d1080c00058040301c88074100f00d0424080032400791200703403c40b4000c40c007070b145d03002e0011381c150380280054081c0c02c52506141e004000300170b182000004043c00315110380da000200b641d138188103030009185100205e4465810841c1c001a40c1c41d40102402c44070f5500401e543c0c007625030b0b00703140591031054401d00322541001d101543c04640103880311076100e1407031070020400b051120905011160111072030581c803980810ba0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 231388714 1250 231387464 231387467
    0x12120403021903050a0503060a03060f02070606050f011e05070203060708070f09080304180b031e060c09030c0603060118080f0d02010506060f0c0a0f0b06181303050c031e040501 78
    0x40c05400424402d282c1030940c0c5440003460352140540c20810700c003000010800030380780d1402c0340005641007501040081ca2042c00ea00296004400c04d5500908215011445140025810100d00f6050712151240c3c1984104c0074141404c40d10390742c007031000606c810000750320240a010f200f03410640ea0440103141041001c0c110f02c03040900c15007000b80488051040c2e036400411507081c0c0b407500b850a18181c0c845002c01010f400b07814051a01800303040c1c00030300c22181c440580c03100f080c5460f0076100c2e01d64a031248d03a807140c0201039442e07138550311442e1415000d0034000e00558001c0018500803036200c2134283c0510400120360f0080c1c00f0343c0d010b0f10b28a0150703c0c06002c00c8150240c0343c40207104d10308203080011464010f002244441050004203504a10410008007401d41c1d0301006c12140c0141500340400e035510200c6601c1e000e000440003c45400b0300100009100311003040030707041c0c40f0794561011101034002c118000390603c002c200ca40700210141e50022100c8111581965403541032200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 231389964 1250 231388714 231388723
    0x20a02040c05160b090109060906050723030f0c0f0a1706010c05060609070e0a030302010b0414071704031112130b2d0f030703020903010b010906020d0c051212040302 73
    0x15081080010301c141d080c2e51514010104106820010030307044c984450300c17010700501c039005008084e01d2a00c2c0b004010000140c0120f44034001c90349884484020080307050b0040d4841c5805000004402c000084035000d540d010281c0106840c880075043c41240d00c1162860f07481310707017036901080c0e08030280d01100f1107062805a024500386407030300c02030209549441d51402d0241080b0310400103400040e40180c444c1e000c46e414403030002c00200700d203603032130038040d0081105c010201e0003141082070400c946042030030400e00a0203155900f600707600980100b84030500c1b01500131010400301110341c00924000f0020814403a00c080c804999800e80449207118000d01507100c0d103201103082c02401e004040030490004050124460b41c05400d00c0c0020310300062094603985940080040140b180841e07040e4080c2a203524264000c0140c0705000c0015203504116200d2040183d0000c523650520a20a205981082d40b1031811942200c03110680c402c40c0f03811800341c003048844d9842c10002031550402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 231391214 1250 231389964 231389981
    0xa052a10020a0e040b0d0f03170a02070f20030303090312090703211707030e0c0f1507020f060c011e050108030909090312090c13020f16020607060507020a0204 70
    0x11400c42c41c000c07048801030b24801d6038203072003403049643c1c404503840d5403544ca40700511640c0c46150340b0701b16509450050509280320f0100d014a08403c00000c18122440c4211000c0b03a802000d21180403060740e88000440c0315258800030b810396007000c04c1d260b5840400185003e6100800519210700c0003407403040301200010042201035012060070004120052188062000c5810340c0702e044000d4600162a11210f85182051203082d0f0010409020360582c0440000c09040c001d5689800071001000f110428404405c0c0d40504034143c800102101e140c010000350303201825403000c20b8140c04c00a02d41c1d4110303203210706499444242d982001c4003600380003a109024000308102c1c950500e01e0090b170384d01448800c00e019065400214062000c10010340b03641d50840001c030841d41c1b0704000810b1f210b0200030121801001c110180202e240800d009640c034943e8030760081c40c1082034407070842140d10081d120a0382c020700c081104001092141c011184180c002d5001032104500510600044401c0031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 231392464 1250 231391214 231391243
    0x7030605011503020711040c1b050606100f0f0302090111010204030507140a030503040501031a0306100303021b060304110103060b12010f050a080307020f01350a0506150a052a 77
    0x4008140003d0f040c6d085110a440007070700c000032810311000d404d0718088690072400d0035034000368005908104002070349612810003900c2081d040454160282c81036001103200c0000304020141041d0914032903406400000c0051400c4800b007039039440c1540c06c81e4099042521a074201140a000f0f541c080105065100c400b80da0f40f03042c040ca1a12074a032039008500500307040640b2003212038152004051a00152800107060b54202d061840c80421410103921049000d0301542030601e04000780100c03003900c1c0c2ca50242a480c81e55445542d81c112651141c0e43d061b061540e20100814994082805001d100200c0b00d0007070328650500d01c403441c180101b64003d500c1550190028000c018012065504c0c480d4190f5841403100300740401a5030034030300300462403401120094095502e2044001c444650900340390680810384607030180b5000e451045505607004600c1c0f0600001d00c200c1c47d00101001c2c582d9103042d07410301d00320040080140f4001c60351102002200c50a10500c00418401588602c004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 231393714 1250 231392464 231392467
    0xc120e03160b0906060a0e0114130e0c040b1f080903070b0907030c05100c020405180303070e0f1e0915041a180420040605042a020604170a030e0703060501150302 71
    0x2800189280147d05004020740740d04000c00022031519240901415152041c50902c00c4c40c001e141d88030390303c40f101844d06d07116506100c000e04190420722502c0c1c4032501c4002d243e4030a204100c009a5004001501c00209840b04014a001140c81c80e4a068051b6030418064030f0310b146182030403000803845820441c880c0310300f0115210015000641c0c040841d50580e804980f40d61541c00441040d140807040d46d03032502002080001d06640300c0110802c1c500d0485001d0180030b561424003141e82c0180c1c805680480d690640d0148600d4200b503819405800310b402c0c00c81805030b2001040540e003c04d011002d080801521305402c1340342c4404104a43c80088495540e03e00d041d85400028100e01c10820000c04050382e02002940c9494000c3d45c0a08005002401030081284030000c08450076907407454012034503295140102d1000c2651802150456580051401144440040750703100780419424180e0b00c42f10705070049414009200290b00415001506615003181010016070950840080520 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 231394964 1250 231393714 231393719
    0x1e08060f01060c0201180e071d0f0d080c160e0108061614090901030c030c06051204030806210a03080901020702060f070305040315020a120c120e03160b0906060a 71
    0x8068030814119002d600d0540c204219500042c0c4115003030120640c4103025002000ca070250840c14618000c2e40c4503036a40681c407034002e04c00f06004c0e17440d044403940554040281c03d03052900c40450a1600e00800703c032460002e1602e01c181c42d010060030f5014101842500410030550b108040e5801410100c1c090900c0d850585000641009030700d00800c240180c0000115020180c0c1c401c0e00e0820502518000155840742440c05580e101407004460400303040101190f024452015103c10721820b094040b01a1540c1d85c05845100b40202850303001810405c141a205c031407210940001030002018010f030f0314231401c008004550080450101c1c3c0c2c0100000d074016215141201c003000b005810203074482070710340f501300c1d40d0307108550000d004030303010b03603820414100350f03600800b00c2296603110102c0b0f50340300300d24400a44110015800100c0d0011b40d251002000da6002100680340071030079240382c5040c905210105210f0035a080c0c402040020400c00740c2d200401c0003030381107501121000003151 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 231396214 1250 231394964 231394981
    0x1a01050703021f0204091805010b030a0203060f0a020f0a18060305090c0108150607120e220207210504080c06070f17040315020a080601090305121606061e0806 70
    0x44040006611150400c3e07150a10901298103640280c901484240070208025100130000024641c00f41c500354a420132034a40c502d800030300e042c0c540b07038007402805d03c03640c907041d940c12001030003825454071503020421079400142d2140200306078030190719480010516809d03450328890700f0360094024549000d0074004940c00c0002c01c50b00c3d9031802d1030040042e90f150210320b1540284220915008040030510404001d281d820610121301c850383e0780c100340c0c510f0400f0030020341daa072014030306225010642116043d181e5001040014001c000b0103503900c003c1140c7e0b42c030f403800040070203002850100d400d00c045002032100b002585000c0360118200303449602d59400141c07010300c00501400c1900e03d41031414030038a00f039800441d08590140c031522044507c0001070360101c1c00180c002228140020140d40c054825003098031703000002046c0980b13000781c80007040e51040e5412a90b00c45680c1070000000da00d406008054925181c1c12507081d0b55401c8401c41540c42c1d034000c0d094641104d020008280c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 231397464 1250 231396214 231396223
    0xf090e070630050106050a080f01050904021e0a0e060307080102091305060d080a090e01081c0807020a020a090b0a1208070b0c0702060a021c0c02031f110a031a0105070302 75
    0xb850102c840c000c9511044203102d020400500200d81507030801000141094014014002940ca140c44d0040d003541e51908c4414884000d01605510188002c00f05015040007180c4100c500549410210750b40c079408000b4140415030390180400c00510003c200c0c1509040c443c220040c11980000d60802c1c2c08080050207601900c00d512000e5a0303a5030004044d95500c02c07240030201e4018149998a0042c400c00824070107283c01410b6011452301c000250012000881aa0051543c90803002030144000101e80140020b80000218480c403a88007000da95406075110061080440c0000e1001c0c1200500180d00003591001ca502c0703016a61070b10210b02800100c9034040e0b0300120448043d40d0782008100c1601802102a400200219118580c00d4000800030310321480d504505004105420b4100d80700c3e9050341c1d000b905508107a0030881426019090001e805408004c045006204d2003140e2030300e40c0051844000080e11940d540104010801c42010404e0003840d10624007407403903c0c0690799 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 231398714 1250 231397464 231397487
    0x7030206030117030f0c0c180c0703030f15061e0e01080c030703020f07060e0c0a080706051b24060d12050702120102030907050a050301050103030801050d0602070501060f090e0706 79
    0x100001d1109141c01c40c00f0030300c01c850320384808400b12500e0350f002a107910341e03624800100ca0f0054880d0140700e100007001c007400c0c51050380140c3d07480d4682811582c04a0107085218400c20103161600c0c0a08034840035005540081c1006544521102c01c04d1803201044810404085043c804010303040b0000d640d101c00029030002c4903084455507074a814108800a00c0b403082030130880c00d0b01292100c2040015080b103510542c010049406d48800b2001300710b508a49482010050760104400700710150260000d0100e10007212288403001c1503201d44103007417195041e040b1104070100d507081c2070b503940d050103420380001c016141d045407900c055690148040446040300144200411071000f1075403840c030000240e50080c0025900c80c20805641581c5148078043e00e4031804042d4404201800c0c148201412a134040d5180d5001d40d2900c414452160301c07900b010b0b03401507003c000d80c1020070424026070b00100000c407030581c400e40c904400442150b00341803184100c4d40000340c0c204040d583c40b41d40d1145 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 231399964 1250 231398714 231398729
    0x20c100e0f010617121305060706020d0e010501060219060612030c03090b090a050105032a030907050303030f0406050907030f0809010f03020a0806060a0909060e070e0109030b01031106040b0c0c0a08070302060301 93
    0x262100e1b10001045070f040180d020a0f405000015a5010403440d43c02403d0711803080502030040e49408000103098485c24041e620050740601c041d185004815105019800d000e444001015078880aa280c13640d041c144054020420b080c100004055004032554020100ba541c2c603422f08040c800040c00500b410700c1a941000008808195040c070103401000071800d00c9a1095200240d0703034a0124640c2046801040c140038401e0002044c0c00c0100480344110600d28031402207644556450b0020400a000340f5506e116811010001664002c0e18040c00703400b454140c0d13229a02c4500040c000041c20b480c074400c150040c481c21181c50b801c00b66a40d0464401c071307082a160035404c0400c50b418042540f040d10700909080c03000404403c90002ca50190740c55941e912000540507006452424261100900340a406c0c401000071856007010055200001021103140c00da0740d00306000c00340c008951400c815000a031040849240c201c25400c000c00505015254152071500040c84070b000522880c032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 231401214 1250 231399964 231399967
    0x41b0f09050c0c0a0c050102010c140301050904050f0d050702030c0a0b1b030d0204090b040b0a031a07051201140906030106180509070e040f11040203010506030a020c100e0f01061712 80
    0x40c90300b00d12a003650071920382e400031140b0340609070404051401d6684a11800b43d440d2013003d01c012803007001c0c1d6240100003c070525196910300320602c0090040108140e6150180e00f140d800030380020302c0010b0403149180d41e0240c640d1100c2c010142413103580d10f00c507480380c214080d04024000052003942d10001c45598806180f03010301100c4d6046200d10071643d41510300c00180450f111180b60720010a001042d9020482c03103d001d000c4c0700b181c4845000c00381200c42c60b42d00b420319003000ea8582c6a40000300d8a4218200010507580d088840d0086c0c0200c184420010070110b5070f801e00c3e61700540e208030704030000e004217490725610000071246e80300300b05191a281c200041604008200c044000c105904c40302c3d0031803405051200b01030340c440008840a82110010695034a054000d0364160395004080b5491505e0b00394190009500550b80c0366190b01411b00400501074003807142e8203941c006940602092122036602d1350071580700c3d402140c0108082c08440d8044007000409241440c07000140d05e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 231402464 1250 231401214 231401221
    0xb06010c020114190311130e090a08041205060a0b1c08090307240c02100f03091502091936020d09031418090c0c06010e041b0f0905 58
    0x4940d42d4150f40041502e0385000540361007684030309034242000f03030020342e410001c2e11480c4102e1245881031105244103174004001c03d0040c410390030403850300401078004072a4100419550000307903400c00e07405540511256003035030003401f005000550348101a400200401410f0100240003017854005003d02c1555103008482005552011103100c0072005088500040c0c2e6800b010701147e150600803580341d03c10310300d04440c9502900b44050b406600802c071007004c5a481c1800c440031202d102d45c48040548070b00100000c60820180c84141c082c0c00100940e941d100c3d4014880150103950401d408803c24413010000030104000e104400b0f100100c000d0303640f880244a10584080e1a40c1a202c15840040c0c985040d07020740e03204103c25846074441203901081e144008145020741c03060700030040105c1201c03030914685080108e070310907035000e41a070610380039208051905000760407038514454017601340002e01c0034011803100e200644d4111a103419090040400040381244281d00000f138860700031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 231403714 1250 231402464 231402467
    0xc0b0a060503030c06060a1509150c06020a020c0405071701180b0a090e0d05030925080d0804020a08072402030d091a0c03100b090a0504020a110c0603040b06010c0201 73
    0x680050400400f120380755034242c140503171191000e640103440b0720810313400023403030b400e02110401d0030303080315110348000d07500c1c0c800da00400e8a440e0003280c08210390004072500151462018002100c81580240303025079602c8140030407904090002424042c24000320103840e040c0c0c401c22815680ca441c0b40403500c0b5941003210300900f503010310650340308140d0b41c1d0114808206070b20030507402c039016080314001c1c07400040c2a90180b00a4440340c01c180c00c400e400702803e500740c82ea0300c04036805025a202c40c16594035a05402d0118030b0840c500003a0390300341440258039060f1054800b50003071702c028110003894100d10142058206e060004040b18403005418400d0081c030030f60b0036900d1810414001d940c40b51412444451080e8074100352120610040344003030200704190391144642e40c90348101d0a0506440c90600d400ca01a17959100681090104072500c460010346014030407520790141c1c0c46803000c2e490303003040402352159014100078000c100101d600c8400c0b1a030003000a0800c02c40280d0319000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 231404964 1250 231403714 231403721
    0x302130b0402040b030f0f04021008040302070504110901110118240f020405100201090215130b13051e010503010b030604151e0e090d03050711010e07050a090203070c0b0a 75
    0x3065600502c003140004002c01000c0056128401500c0e80036003039a190042c0300f4124400341c6001e500500e41c03c0035a941c8074010b055032504030380240101c4900303e5441c40041c0554070b00d002c10b40031141307002c43c06400715600304070610000b0803598000e000500c00c1001c504001c0c00e41308805000411603480030400c0c3c0c00d03008000d01c0481c2d65688240b1580010740c85801c082e6119200d451700400b041070442ca040380c0b040c030480180950040941550400000d000c140b940c20516440c540d0350100c0e400040c0018029005003190101d201009400c075103004104000b45040d0a02240128442d1500c201182c0e404812241510240c400701c64a0b9240c3c040420010690103a03030760034505c80d050000c01c554280b80b00c0c3c80700c400020304600c07683c65200c40b2030941f006801c0e207003640107900c01426185124084c2d00a00c0d03100402d480d041201c10044820242981c224203031545494108000c1400310742000c1302c1c0f0101900f0700601c290b165060400c40240900b031407a10140c0308610380300100c1c1c2443d840d900b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 231406214 1250 231404964 231404981
    0x90c0912010609061503020903100b0117040605100803070b0106080a0b060307180b040501050f0702030a02090412120509060610051903050109050a1b0503100b0a02010f051f030213 79
    0x38001c000380c98884154030010411400748000c0e050007071030030362501c41c800d000711040410302401400081800350340a030003070300e140000181448480070b80c0c1c204030100c40f03050078419400742c07401045505104504c0d690302090f0340c21200d50368108002c0340003c0b03110316a035941100c03070034074201c07881355500c07501c0130000c044034018141e22440c00014898403da22598a5a03107006a04481801544d80e40b5620100d104a20074907010030014042100e40c828044050098140007034240c03440f400059002424108040304c0c1102d6400d01c21000c0e046155002c0030100041005101c100440d00b891042c807030380c90800407d03061160303421003200010140310b6410340f04070f08000c0c442c42c12028107190001d00517203001d0003450314240c40e00300002e4001807180220310b005031040903002e07180f00303111400321403d900085c494194102030f6840001c0c0b14540768010500d0b5903c550000856000000190050718006409248032100340c0d41c0c6034420701d144405010440e80e04503050440d040c104004040544a40c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 231407464 1250 231406214 231406249
    0x40306060605030901110405010c02060d060b04031202010e060f010e04020a0806010902180409380403080a0e0607050a050c07080307051f0504030c0609020d02191a09090c09 76
    0x100d000203607150050003440c09036030700100a0000d900703e940c450b2814012441010f0000f8182104c10004d401c0020091014000141012410b80e4407810340010650003680102c401c0364100307800309649a820302c603504120a00700c014085038105030003002c103203031070600840341c030070084002190440d91211401030090184006840f403030340e0340324440e1000750440d2360511410a0849203200080c90144a2100c0c980da00081071421078812918216494404044120260080310907a50310003e00b00c02d5184a80e05c00d594070320061406d00500000d503460480b55000e1507110b1b5062100361a004816181003000e075181c030b01d032292200349403507150607108d40c000400c500002038078030107000000c45c0c03030501c10003e00a07140c0054030694900341100c00840d00070700000d00da01c100000240c0984c000c041401d000901e43e5500784200c2c0c000500c03280000c01d4402d08580c1044040041c2c080d8803003040c4440d40c4400141e400d0544c2c3c50007154850000410b01b010a040004a49119039034540d445010030400c0f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 231408714 1250 231407464 231407471
    0x2615090406050702240c031b0d060f0e07170702031b0703021908030415110d08040b0603070612050603070b0f0c070b0412121209080304020901120b01030b040503040306 74
    0x1608100780181802d03500d8000601990100340700c00d00040c0d1130780944a403004080c1d0703076950b102c981034480d641020700711a8861240020380c000c102d1400002c0d042401c02e10030001030745c600c4c1001820039078002d81d0000b060420300310b04200c0740c0c3d50040070402c40c0d0840862801030702d41c2c442908a040d48903202821801c58401b05204041220029481098910a1360201c620340351100c103c400c0c01c2c52500c0741e0300480e4000c010501101c8801001c1910f982c001e41003900c0401c040d9010503007080c10b01410400000c1164003000f0030701840008541d00301e10b054020305140d50815000130407841d02c100510038003549a030041081a102000102c000b007803851451034950384001c5801d400c0c3d6000c080c40041d1486031250110b2550804012941240c2820b840110084005c1c0d0ba1200c1c1c240481d101c00040c0801182e444040ca10f0500035004900d1168400e0b81c1d0761301d401d104020841506801201c103020300c2040d02c0d8000307007040c50700300d05498000c40040c0d260b44d22840c0c0a0302d18840c03500010b026506 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 231409964 1250 231408714 231408721
    0x50402040213031a0603010203040f03180b030a1b050a0203070f020d080c030d06140604050d05010e010f1e050c120406020702060a0804021e06040b090d0203030a050c0706261509 78
    0x182240c4401e00c8004d00362805203076031604030130182030340816503019005000d009190000203003c0d4251a11181c0c40e20f1101455039540c1c50001c07426081140c1019003503844034101d92100c00348491991505c0690300303000b0f052503d2040000c0d5a40117540c801000d071504032408405540d102084009000e900007401551018514503040c0c60fa0440d045c0110748030b007080e0011440c5551007403680e00822000d080705041c00c0c900800c01082065113101621035550750f44650070803a60070700030040c000030300380c4000c5140122000c00c40c080e4041d00004440052074030062111344000103044030034040a0504080755601c1e2810120001d204180e002940108000b41e4032496642101030b85201d14000c0703404501d0305200010961840300464140d607449034003040301b03104207103000780580034420010b41010882d80c1203602091459000d4507071310740491004900c00310f10140400042d80604150314001c105181e0f8200d803088084400540300f0902c0030154002418100007550710b072105100106001403505 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 231411214 1250 231409964 231409973
    0x3031b030806060906041a120f010305060a09030509090106091d0c041203090f030606090f020c0c0111010608070b0711060f04050603070e1e01030615020c280b0406020607111005040204021303 84
    0x14026002e10328a1018100052401c49d41c500030503040b0707500314020713010316594401311100030309000e1011428000103000b101881e45840305224042d03c0e19844155485040030800c450250440c1c3e6040899041c001c00c110460030701c0d4054500701d41c0d00e06403070a0316110900e001d03220381c102070300001e0240a02910020a200f0241c101108403014281d0070440c00c12801c604400303034419034811030700366840f00c005102954410141a1009408000001081501c50314120305000701ca07030261000c0301000c5100010f00c40010001c0c10701e55001c07120a850300c5015052800302d4066071145911a0780044000781c4041d00030187c0c1c0b0811a80242500942c5654000c10103a10f00501395540c000b916011001c20b4480c100700c0000d011030b4040e00280058000307a01000113080c604a501500c2c404e035a00ca0b019080343e4205480c0240c00d1031807800c0c0c0c885007000c1000749000c800070000d0040284a0030091107581022a8011840d04408d2010915a41d50b001080182c0708040400c144c00b00e80d03200000521 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 231412464 1250 231411214 231411217
    0xd0e030d0c261c0b040506010f12150602060402090f0601090b0703031508010e010501050907090b07020a05030111041401140712110f030706050a051005121501060903031b030806060906041a 83
    0x1030010f4401000014020b009100c101c6404132444da005c2010521504086030140319901031981d0f841402007440c003940c81d0280e103019140c0d80400c026a0102041c801189050070965074000d5010032048001d00e81000000c00032815440b4030280c50000064200a00d4425004881a20420240c60580583d1008001d000f801c40d84510007580d407800c00080360307d01e000f1100034010b0105270f445078140340c11300c92348080562200030100d074040d209001c001010748080c01340a000365001403850751a5840e100f00792031001c2c10b011045040200c10300c00400200441004c2d220110303044202480004401603003514080c410360034100c40342c490071003507d600c100000010503515102d180140302507140c641c0d400090321400c0e01ca84038640c460034824441e034100030002804104c1e18500321081404070304550b210001c4203820100000c0c2460b40284107164010b0081c41404102e0440d0b05c1c48000d040c2c0f0010420000a03040c00c3c070501c000202010705a554800b5a0094040a03031541c0c030400c410500050075 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 231413714 1250 231412464 231412507
    0x304150806030f07080c010e060c07090902121f09061d06070e01090b0d090c1206060509150a030b0603070503160503010b1804060507091203020d0e030d0c26 69
    0xe0b1207640000f00d01c107240400c103142240c4030310740104110303180300b0015110310f00c188400940140c8244490800d10204001420040040140001d0065240d00501654070342031404889607900206140e40d150152015428030007030000300010742e0111900d003000182a08a00d048551144403440616414000c146036016180070b45400c1c122400d03850040d60103246620500303000a40030301400c0b04254a9400c0b030441107104000c000007040d10703808445480b052502040e2042503a0711418800c905108c0252600000110045a02c080d406000175035000b1580c040181900c940c03030042629601d00b00402409820b000341564148081100811840c0500e40b040c24032035030a02107901024100444440c2d000131503140300805983d2030391101c5000e0003002e001c04040100000000403074200030300089403107502c03e50141c5420700324820014558844141694801d40103c00395541c0f15810401103660309500002910071034403c1102c0c858030543c0108a065041d20000d00100403c445000010b070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 231414964 1250 231413714 231413719
    0x22050708090c010c0602031008030307030c0207141c0203010204090c0e03011d0601060e010c020607060f0f05100501080405010b0a03260a050313020a0810090c050303130e07020304150806 82
    0x44503034501c581030340e4a5014800250100f00d01112000118440f90011603200c1440d120300c0d402d0b80c4e078030400d1901e1a84101c0c1c400000a6599280c01d00b804d0703041c00741d00020400540354a428201c00800a4a145001c0003440e014403000041203045403400e40543d402010323007080800682d00385140180074041d201e40700c20700c42c0d4038003094400d288442004580f028003070000200302581c2000000d0f40c1c00340301002680d040c80310292060005954010081811900c24180483d645415400103809d41d81080f80b1480f6042c209410013600245000345441101c0c424608a0165165410540e004180c041ca00a4000c803540e03201001340500e4a10301b04012091110700c00303828010f400b02d200603004e5005038030001002000421908685130141c05a158001040c012000e50b40c1e880d110b240050509040d03241071340710304810091140c002e885400801d82a80070b14030f014001da107900400c20180c00307807018084a450100701a54400c00c02c3c0c40141440d040b004e0103e00002c100039000b040120344651 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 231416214 1250 231414964 231414977
    0x518010c0c0603270b0c030a06052706010c350d0c0f180522090606090f02070c12140a0503090906040905070b0307050d06181404030c06020306220507 66
    0x40604c120390604001071904410078503600d850320300002a0301d6101a250075072064842e5030229195540c401c41d1154a40207107410344101140000021000c00014103460610454500850120700300c0358500c4610041c52500562007030341c003050000080452421b45200740341c04200a04a4580daa002940701241c1da112500c50303c400c248200e5440010641c180d1044e003656404201c0b5003400042c0040307107400c28002c20060038420002c4000c4400401c401d48626888107401c2042699511840d450420307410070961910b840d6031114580c031000740c400c01c9120741c4c0320840d0000340492003949810b41c1554006880580c03041c0e007001d03070303a980041026074411000a4041071203498a40305070321420307a220000d000000d00d401c0d840c171311642004010f0f03020b126003003000001590340341c4541c0001d0440b141c191017002d00d144082e10100c41c0440284990700c070445040c0004a40c0050440340c80c2540664056a04d5940c00c011640d03141122a18802080000b071151645a0a030380007544900740f03655424 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 231417464 1250 231416214 231416261
    0x11701061a12040303020c010c02060601030e0f03120702120f03160504031e020411042409060210091e0803060405091902090a021b0f010e030a0518010c0c0603 70
    0x1494154000c095081c0c100c1e07001c21481184a10004003035a2041c0281001400e20b1556441c031420b6902032607204005800c8a01001030303940e003500c01e05040c51400c0f0000d120800143da1210b03601d20404507041200003040c030001d0f03500e5100b00440d109030680c5400194030b5000002000c40503070030507503054180d11000c00084507010f10074800c0e01e040700d0700000032805400b20322440000c0e156000c070040c0d8003d601e41e0f00b104c0d11004841e00030002403801e103a581803032200302c040c40351602c15044118010000405010841d80d40c1c009059005282c0112000603002100d16041da1302c0d0b0f10b81030842d00011500c0d1081002d0080749005140f055a090340d017400283d95000005417581800001108503c0081070341314090b081181900340c0c0b1a0000800625000303900c00313a50300341003c3c0b0043d00e86691006114543d0b40030203005075a000b60301c0d64019030801c082404090410b0140da0f00800c84004400490840c2da8030a000260104d034200140c420b056888140040203010312600021b104419811207 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 231418714 1250 231417464 231417479
    0x19030803011a031501050705012c06090d0f0f0504030b04060605011b050303070c0204020417010504021c1a04080d0c050307030c0503060a060c0f06020f120105091b0319020301170106 80
    0x86074404e0000e00c00750300e01c005540d001034070320340c1203410300b40c5403990790310031004049003550802c9014140d545000000c400c0445001c504e440d0300204141c006400003210412102c1d007040c50310005c110581824244900d140b0011140c50150b5840a020b0041d81d40a00007031000c55448401694802c0e40d919800b03240d80450900b840c60b101d40c006055900410004840510411000106510041000d80307802d58540c860b01980f0700d1261800d215940da030003800214589508000d2050b1075510120307019222a44a60010740e03a0220350040c0702e01118009000c0141031001c030381440e414810100000b07001d20b107008080d90401c54214001c245400c041d1a0a80d001d0819603100b01c1000340001e40040c100710003200c1444005074121003400c10317070300d1180c001001d50000d440320751030801140c0d40711160f440e20041c0702e06040e40454028a890000e104194000c1d541600311587c50035242c1d0350701e07240c04100120340c2034901644410f4034400f000102c0d42e2100a100651403928502c02030283c1500d0300782 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 231419964 1250 231418714 231418717
    0x907110105071206083705100e010c08130b04020d0204090f110109080c101106150a0b03130b090f01060611060c03061f120207030509031020030619030803011a 70
    0x91a0140254903003072520961800510b4030801508006d000c48041590f602d40392903a07000f54080700d5500c662080c24503a00c01d10078044015068a0002d6403410440300c041c1e103241c50b00c1409030403d44401c000030255291001c0800d06141c1c0074004114040d42c6082c02c0c80d442201400440f9501c01c42c0b11880d45540c846c0b2030034010351380d1031409003964501040c1040101c1c03004a200344148028045e48550392441408150320420a2002d41e039030b40d84900c000c000d0035081c640c0211303042c80002c2c001d0184240d86124a000c10320707072001401c0c0407500c400784038510302851050001090341c202500800d6956000020b034400400322411038400c0d48601c20101258081140d03c0da401c80b02c20201880c0503031442c1071921810445d41041c0d01003040c426042c4050303910240d001d0340499800561010b56050400c00c170680510624001c220352420503854420481c403146a80f617108402001290f5260b44410030012003d68048080d51042d54910701b5415642003481404488510f103010103440071054070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 231421214 1250 231419964 231419983
    0x80115081212130503031014010203041809030c0501020a0f1b0506071b0813030317010803040b090a1d0f0a4a0c0301110711090711010507120608 64
    0x140490300b0110400c086020818008101c0991107403c3c5003003001260060004502031034100108184d00c038200301c100480302c801c000344a4119070040004021180d004da0a040c4125007007100412000110f0400b268400500000500b41d54400100301b407441342c0100c16901002c445841d6140740400c2501500241c5400320409030182d000000041c115600c10364200204a03403000900051507c00e480d95001500508512404080f1500041c010305801420703b09064034002001d61107503040c0709003541c50380201d10801c00c0d402c901143d680856a10245c50704043d2659000054810400c9400c01f07807111030035500220402c00040105030b4080b482e0151030382900b00220344003000303085028006100c1800308100702c1742026042c08506c1521001406070745900314000105503c0c2d040f901007500b140e0300c2c2c00c146021034500300035050000b544126201c101110480741c850081e62b0300b41c07050b40c6442c42100c02e5001c951925040140058000290110b11925003904001844e02d695505076600d180c1d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 231422464 1250 231421214 231421243
    0x20301062a030c030c06050906040212030a0f1202040302040213030b0903070c0b0a0306330912080a0201090b0a090b06090105010e0d0219030c08010c0207030c18140108011508 77
    0x4000307001c042805040035005003480380c40d2440e410b003016125a42151000d43d12240a90480d2042c00b0540c94250740f400c00001080019519204006802a108990710a20348080c0a46003010703862081560b41134030300550b0043c01c25591088541050203854182d4002119901300f13000120b0001ca0000040e90f0109600650314014181032101c062003c1c0c00204500c01015262003004c104180c0160341c8a000a0341e4128030000a183d001d20040b00210200c4d19a0800c188084208030144a25000300860b5070400b01065441b528000c080b4050840c1c0306003e003282c41c0c41c50030310544d003019500130300d00345002d40030b01c08264030381e001040a03a040030301c2081c0c00200300030202c0c030305450444501c903451403000340492010540320707112284124036a40142e030b541c80751502c03c116020b82806000701e44405480500383c00c0307046a840310301b80b0a003401840f105110350b40c13400d02007684940c09481a0229a0000041580d45414460103800d80c1504805450f409040004052100044202c20721002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 231423714 1250 231422464 231422537
    0x10e0d11030703051614010b090f1b030c071406190b0108150a08010f020901020705100f080a0f0906060915050924090c030702060c03010308030406020a0302090a060302030106 77
    0x2580742125683c001000d17582880350500c4401c0002030103a4441015401030310300121f000420382e001c0191701c0c140140103014000c0542c04012001c0302d0307952080d41003010702610540300c1c0c41e90000c01d01c542c0540c1c0380c018200404005076400720100080d02c18861603002e10308150010759000c2d4201030707070b014110060100703014801156481880000202c0407090280003904220340d209100d5094410160508041603800224240c1035641400b00c2d02c081c00096800007000002018000c1c0001d00c1045140c0411408401040b960910307904011440d0f0000030b410b00c001005070030620020031541c85400001441c0900d4542c01d42d40303442c840411100003c16080807035481005403440d02a081801e4a00514002a03440440d0340b410403290041242c030b41c18507100d2800c1c000180c9410070140c40034800d00c2081c030040000581c4601203940c0564441d0001d85c981e451400c013a0068001c40c0e60b0b41d5406a80000003062081d0305501541c1200c40541e52070b01400d4003880e07118081c1c4c008050403640582c6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 231424964 1250 231423714 231423727
    0x80610031505060705010b220e06010308030c090a09050f0105210d050c0102090402120a050601140a0e0a0302030a051c030e070b07080702120d0801140108041103030904020a02010e0d1103 82
    0x8219003c3c0101314056400401c414020000180e102488003e16481141d02d6500c1400030054a00c0352303801070441040101415415503c1b00d100c140070042210003003541c000b4040d0915100c1e04c41c82402001c07020300c20300c21030524031481d400f000800d00905001d1001143c21030600c40c40e103847c00c43c00d100d01c000a8a64907055007403c0311141c0c0070015106280d9000c20108072507464a01c020001069940390046250900f44200d0b41136400142130725040208100070b00282000d20400c48080051508090f010061101d001c990900d10981c0040c0d8140071700807481d801d100307000c500e1480b80025104c1d0400807024209040e0100c1d0554480b00f5030952001e1800e1001e201d4603001030000d6401503108a08140e140d82c0003d42800500100c441e064000000a058081d007210045014000304600f01c0804190303400001c02c1c2c804003c1020f4401004001080c0c0240c5043c4103d4002d404050015503640c0c0c84120f010380039011680c000a407904c0f4500022121034840c01440b8130055101000e94500700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 231426214 1250 231424964 231424969
    0x40f0612030c020a1d09010f060e0f0907030b07020303040302010b01020d270e18121c1e0f060305060609060619030b0a1d07080411010f03090b0106080610031505 71
    0x20b002c0001260401d8401101003143c1070402d6550b841d030610030125400d01d20704140100c0c02c0d2004600c4480c101801c007007060110400081d020766024620700c4034140c06580f079000581c80c0c0b4070103900c040c041c24103a5050005150340800218030a03802500280800381288004a0b611310701810b0046c001803040e5240308403e82110011000e850042001d0004140ca540e00407100e5401034883c520144032404008403440c5082c07001e03585842000700901d04241e080a0342c41000c500040c0d080d2200c81ea80d050b031001c6022100380f2888080b40c80d05082010284181c1c403d001400e150206603907038420700000542c8e42c85c1c02151544102000b034a558104604242c3d5411040380400070303030084c1500c2e2080c1e406151650031408006058030006901d0400281344d4072212494080c10b03042c2080080c4003000040340340e68491100401d0b080c80e0164000c810010100d000b0071000c20000c007080200340c0000740c1283d01001181c01120211128004017111305403c0c1c04030356000301c046c01c1c5891034007010481071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 231427464 1250 231426214 231426227
    0x2070612090516081005010806190e012c0606030a06090507081603120809121c0f050f060915100e040c08010828060903051207050306040f061203 64
    0x24404010081400745555444508101c94580a01e480280742a030400c2086000c1007006400c2c1020003081040307505083d01240c880304000c10000c280710366900b4400c0c200300305a20040d4100c0c8218020401e40f03c05411010041110f0280e01c3c0d0a07521070440d243c2c0103070f00070800354042d20b00100200308042c2c5070381e0b441005e89404401900c160250b984002034024040c04400d180020300b9000001050a41ca17200c99501d640140c441d0400c071305d940c1049103015001072f0100c4006001c0c1080b540307400e48915401450040742d80c82540103400c08100007040c0309250480381c000c2c1d01502c0c0c000d4155450009000d100c110031240000c3d61920744403800c1107402c1c441c1006201007200d2501c036071440c0a80c8041000d68507071540d043d001800c1c030001089441c070305100d8240404400c09071500650022072421210145074440074004507695883d00042500400481d1204690179100946d81d01c1c00a01c05070054100300c40282c000d5003015801c14055100b80f007840300b82c131700400103200c00d00060b440c1280c40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 231428714 1250 231427464 231427487
    0x22030c0f080a060e070b0f091009060813110d060e010b030a0201090306020a050d020c1e06092802180106030c0e130e01090b01090902010e03030c07050613031b09150501020706 77
    0x29008900d804a1b4203030344040107180c24043c00080d55550340700300091101c1540302d5800c0340d04001d00c0c0b95013800440c1d40004599046180b1400040c213a0315541480c4481000d0f01d100160700920104125007003101e1500525201003500c4003c01c2803a00c0c0900381521100b051030700900090f440f400030700009143d603000e0a140c09403454047d003460141d54220b012644500e86145032a07000307a8944001218056000071a01c1d01c000241002d03003031241d042c5640d80303484c005150403081545011550050b075044842c40d041d400070860202a0024140381404020a004403c000783c2007c400c4030205001d05030704000340c6000740c8100031010074041da4500401c0c8400c80040326540f109030080c00b0803040e016150203092540400200c01d00b241c400500b00c5042102c00c40e000e604240501014480301103005c4044076403d440c0166a0760a0a01c1010aa40e042e0030080031001115030800c0413440070482e8005a03158602e00300300c0400103001180500c5424400c95005900500c400d0104d14442c41e9403010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 231429964 1250 231428714 231428741
    0x3060c1905180d03082406091011031201080f07060e0f19031101020c010329032109093d0f030506161707080402010522030c0f080a06 59
    0x300700e0400c1c00101840c25208056000031103074424400300b03964010646d22407685044250b1034a07040440416107074058468400d104040311040880c10070b00424180127a401c000c010b681e80c072059101c240600d0b2100b8040e80d2590f210f81d040c21441103900240980548041e511a81d8032424050104900806141e600c107411042d05d44030303803c1745081105032001861007030042600c1d86010b42c000910f011103e1400c1d604150804001c0000c0350f8030a10804c0c0b0758620100c2c0d1300003015030600030900d071002d80010924031060030075407030305004008005080091805c07141001c484d15000c1422842e03058690550001c6242c4102c00c0b400082c5514101a0300541100a50005a0780d4042c0b54481e52140d071007900c80c2d070404d00800c540c1e8801c1c0250040303203c00c1414480403c02d0604528412503000500c00300a002410010500351381c068801d540c2c1c45410100c0c1100c000390307598080c00b452903052104849000480720041380c00140c81d2580401c2d612418010000c04c030175520303524060240d182c04004d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 231431214 1250 231429964 231429997
    0x6091509090c02011409010c0c06090501090f201206072111070c051906260106030b010f02060c0f090d0605070504030b0a02040302010e0f0102070e01080c03060c1905 73
    0x1d2518002c0c0541c2a080515070000a0b205411170220503500c080102042003607458260303a00229a00521407907042c42d044400010401460f203042401403450314000303801d0b01007018802c0e042000b010142c0c411b00040c100a8007181040708180b2014140141c0e079503d02341c100c14001010030b445507412103001d08001c481075000d000004411411900ea0001140ac4042d0002d117000501040307841c0040240300660324030401505d0315a1104402ca164003a03082080090380303030142c04011210303078200c4400c0407400b8007107156922507001e0020708090345c642e400b25111703c0f0320810090010848034030a41d0070b0210075180411454110030340f40e000300b42499002c0c09c02c0c2c0c1032002003401e91040c140b1484251720340395030b60344c114101054032901c020040c4120a004010500060740e001c0441c06003880b0aa400700065581000140e080c002242c00004c0ca01641100000703603560006500e030000b407000d605581460b01d5500c40012144920b5007112100c3d5505202c1045461248004104010103c060700 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 231432464 1250 231431214 231431219
    0x4121d010f0309080c0102040914090322050619030e0c09180a06020301060201020c0715020309220515010f080f270d091805090604060b1206040b0411090106091509 72
    0xf810250001d105c0408282c1d03000c2011711101407103100d1100c3c10a400c400700060752403c14505942c0b0301c2104109210b51149100011003425214400c034058074005000b40d0300c444081303032500c1c42c20140b0202c6d900007900342070720711502c59008a03817010500f00c007038280b41c499035645804007900801400079048a1161219000106000b440510b0103441d299001680d2240d0343c20303a132858150560800c64aa0511703035410300020f07800100b01c3e40c087c0300640d01400c020040005c1c44160080c00041010f40d40c0c10401000000402d0180d9040c029000b41c0303507070000c9045e21204558001040b40d00d030880004003004628041405003540505205c0c1402e1724803030720303a805489410f00f0315000c0e41b140800c01508090010322032140000f4410410450700b003001d850b080c10321030f90f10100504041d003015a41c0d1070b0048582c40c5e207c1c0e8031075400f000d9002c442c014241482c0400d012401220182c0d500c0f14007980c1c071042c51030501c0146040310b000e40d80756038006061940d0302e0b4011243d1400f81041c0080403400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 231433714 1250 231432464 231432473
    0x70507020d020f031510030302150702060a0b0d02030a14100b0603041401090c030302010b01080a05151e030d0c060e0105040b0106050d09061a091b0f092704121d010f0309 75
    0x20b842c41b60320b00c0b80040ca1030a20b103140103403810b1400304445400c20115800c000c206980000c1c0e01c1e9001014540104110703c039000881c0240598400203501030203801080b005108070201443c101c4405002102c0c043c410440300801140e41c03140d4126800881000407e000ca02e030020f0300c84508004c1c1300009055001030382c0340149036a5583c0118091b035114a000c4102e0b60b00074481c0303613200c0352841007131000c0d24200a9200d04e800c00360242906c1116821100c0e06070382c0c20b0304201e01c503030800541190070030540c3c0d070303405042840c1c81300303003180c01d28205540c0604044041c00303405d001d15804960320400e81d081000a480940000601c0c8405642d00e1a168020581a006504241c41d030300d1030201c2c1084920052005200b002025400e40030b03200064a1a40d0300361100315520448030762100c81e01e4101d220300164402e0001007145035841c2140034908448031a0341c00460041e441200340c000d03600e12a15080d500000e501c4509800e240e031800c202081540103400768884800289000100491580e95 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 231434964 1250 231433714 231433753
    0x1d0901050114040b131b0807050307050304030f090f08030d05010506040302010e10030e0a140c0d0c0b0a050706050109020c0706020f1b18090c0406090e0c15161a070507020d020f03 79
    0x61245040150004600700140c121807d1074001042d468014910314007040060014400540010100441115030b00b080c0c5110301d41c410090101c410300782040b50346c5c034205156a1b421000004121602d80b01c00001e091504004850403283d041c1c40f988417895004080005860200400500781525018030440c00d040a2100c041d0052288410382d040301a2255101d103020b07400036a05e8060f03010344030032070701050214041c6802c440c0580807080d520003c074401102c0710300503214002d04070303814400085081801500030b403c400515000f102c42c0550758000807a5201d1082804e0b4846400c000715404080281e401d010b80c014402400750701400740d4040c1e00d81c8840d08210b880b04a5600014a044c6161070203000340300041c4218a410701080b43c48003561078071210025541c071700c2500c4004240013030381d0a0005841521403c241043c2100b4181c0c100109449070311048240750030401e10005a100b401101070b54003142d005480d00d0752408140d030a204080e05200740a991500c503e0301d488040140058 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 231436214 1250 231434964 231434981
    0xe0a05030a09180504020f060901020a06020c070e060d0308010b090a0b03041b080d0815040b030a0b040201030c0908100903030f02042402070501080c03070e0a1d0901050114040b13 79
    0x240c4510109207442c042010304141014280e040c40c0c00c0038148401b6a840100c040070111040300c80c0395880b01140d0041c1d1520141004c01800c540c00030803611000900424210101c889410b001034032640da100401c8100701401d0700080101d0701b2200103200244040c0050400d02c04013603c280d560b140c560f401300506402c21102140c0d81c65550f00e01212004402c0010801413529000400540d00014406401003400521100400f405071a9114981d80e03541c1100d0092640941074407040c1e442ca003070034010b24204850680c0400c1c2003070100070040f48250002c0f0212005c41c2c01134040344040d140504041c015813141542016103c2c2d80584c10003115200607c02402407405040c044000010118034030102140c0038000c3d5048180d00b0800b50360010000340e801401c1040782d0b43d680d9141c81d0123641d0003c43c1c4036099040403031311030041000c0510211142a42615000400d640c0d55458001d50a848c8240220a261802c020200b405c43c01d00c0c0d000a0300c402e00051107850400c20a02800b0700721103006 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 231437464 1250 231436214 231436217
    0x4050904140c06090307140f0907020d030c0e0108040f0f17040504060b09060714030d0c050715050c0a0315091a120303220204090b040311190203100e0a05030a 70
    0x4200107a05941c10045240501d0b82a1001420107070b848000039162035651040c5620190700041041c074503a6142009034502000420380e83c0242040c0c50300a50f00d82400030f00f071000c03d203400f0701c0c1c242490150011b5801980140c0d6940309958031a924543c070308007198000caa40d550a02d80c80720000d0048040d018208180203031154955161034100025142e00b81e1280525103000c124090355030300c3c1d010440d003d46070011502004545400350041c075620680b10020f0400c0d01d094034040b850343c0e0002c02003400e1130203a501c55008035041c0820b1300c00c0360802c1d103a82140c030804001b5004060b0003500801c08a0b4119984503001076039410410b000d540300019400d003880500302036404685007000c104000040c00e5001941186010390b140e0751106141c0344c04140070074220104031708656407508110700d290342c0080000d40070304151070b02801800c14011029500d016444088045035041000b40300301c02c3d0001c000740140554400800020090003005400c240075080304100803840420003081a44550b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 231438714 1250 231437464 231437483
    0x61f12050f0601121a120f100204090b100906030b01030b12030a0810211103010f1505030102091c050a1707060c0806060d05070302160f0213020f03040f050304050904 73
    0x3002c00108525501c0203400c410034074001d6610403a203080040f214101d0004e40b0f6000c1400c8400840c0340c90309a00c0d12103c031952007400741840006013107030090000c8424002003800b60039522420000d40340d4250b181800041c151303a1041043c1c1e440307030b007103851915018100010650080000f007511050003060128160707000188140665030300c0486182d01034080c006105285040942070102004003540c100c1082600101080034452000025011080018000c1000203a41e421a01c0078226504849005008101c40001d403400d041c0221102840700408258084040d18107600359141000790a503400e00c100300e803050000f0201100d604010080104084c1ca0340b8144c5065025500c0900c0880200300c1490140841503c511080c4c0350034245a1300c021a1580e0380800880090203040b0000b0000302c0101ca0090a00c02038143c032990369402070b02c0101406441c40c0010003a07104000003c41c0300c40c0d0800004003c038074802c010140c00d620034400e4a24007030b07640e00051a070780d030155030a0f10030402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 231439964 1250 231438714 231438721
    0x1215060203071e050a1103010f0515010210060b0a0503040f06020a050304200d03051e0f2104020d0f03020f1002180d02011e0509100e01090b03061f12050f 68
    0x1000038450364940f509600b01c0c4015000c5a40c4c140d1500780301d007001048030410031140407080d43c0a40045050140c5610100007500d0000c0c074200c10a1011103585015004108000c0c0d4601c0d500c0c010001239842d0310689616002c1c080008450b03a90005005503a0114000078a00c000f6100b030009214088940d5940d90f124180741c10100b44d10814080101212000b40c0c2e6650f200d0340300e003c81802c2603501420078503100ca072032018440188010980d130514140c0002400409204500060420549507090040031100c0b06d5501c01c1d0940320030b0b80c1c0603600c40d40d48000075000401d0b00e40c010a200c1e1081c4107a41d00e4a4000d02d100d4036168030801d901d5503454000c00c3e803c0e05100700340d10200301060103c5160010704283d4001030545100c849403100025150b00c0300c891458000d4044036100d03c40644440d80401d001f4000030b10070b5042c08459800100000e8000031031846550689010381c20040004c00003515200b619448619558000f405118841441d00c031408a54400d4038800c85552a0421242c82c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 231441214 1250 231439964 231439973
    0x40b0403170f010e0c0c0604080a02070608060319080d14012c04020603060102160314062401052a010501030c0816051504030b01060324060203070201121506020307 72
    0x14042034a4401007044040040e40b00742c8081d01811208068542c1e038154544090301d400038406d03100000e00760310440e000d0004222a480043c951322900c0d80c01d40d403016844060849402500381d41503640359001191100100c407107070041d0048548641c0e9880d18058200d0600c200780c8010241800f105059480108064500d056501c942c100000c00d015071451508665071201c1500170780041c0c00741d50080002203050b40200a4805400c140d410035112181c0e0383d1a03c4620070489001c0a0818001c11020446001d813001d030844084951290402000200b01d0044a290700104510300725400a030f40301d05010100520f4200c15000254004100303503055040014800032a0380c85680079500001c507400410b03510b07a54400540b0022070304040c8507510f0000d001110302890b08003400414001000062a50705940410303d0008031000740840c1d001c2e400000740701c1e61000d1240401503001000020300561042082c2a44000390300400107404120304400c0c410807200e50081d0b0050703800002c2c0e813011720 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 231442464 1250 231441214 231441227
    0x20a0302010b04141f080f0c03150103030234081005010803091318050d020a061a0619030f0e0102040e1f0501120e0102070c05090609010b0a14070b040b0403 69
    0x801c0c1900c051140c44c005006032005032000030040441c44e440031140720000442240750000404104003100c103400c0b02d41e07402e0380d02c1e9551601403d11030f1150070303105540c0301c64240d4100d049a8145e000b40240329044440400000380d480d001c100e0240008020304501003445075224050300700400103080c01e080c5000500104c03441a04a00007541c420b01c110b0340981c0c2c80c0e0110f482c4551300e0a2010401c040404802e19090300321341001441c0303001d00c141880344150f0008403189024000d0001740141559481c060030702240400c000c0e500590104180e086900c1c1503107902018500c5880d00080300ca098943c1ca4040f9802401c041c0b1080e5000501008260144801540c102465410f035410641d80c40503240d401448901c1098180007103100513690a038000d82c031460000d01300c40000c4d96034040ca880c110010b8041806007034400d1b640301b004610103003040340003107050b14070031020103291072480102980c0780040c142c15008503e104200c5100012003644d0f80b41d000e14443c1d01d8034006404c1c14500649034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 231443714 1250 231442464 231442481
    0x705100506091f030b0a0905210d0203090f0a05031b0606060409090302030f04030602030a060b0705070e060a1e0603180308070e0d0519060f02090109050f040e0d020a030201 76
    0x5400d090500505555500040740c020b4901c1c002080041e0200744290440c01c450360020b41002c055000300103c00d0701ca41c008000192040c0e094039640c01a480c540c0c0602003c49500310303000c40080c0318110780000564020f6404c01d080078221001c514003241c807180b400a412004032201c1c0c2010454a030442c0c1c4041c146448080004040d0a00d4502a00450a24084e81c8078040150307440f00003820505000303000310380c200403221020590b82c94030380c1052000703544250740080c1081d243c1b010010300d6802c004141d40040703a112002d064400c0c941076011000c120007409055101c00c04480000d000d0361010541c1c8442d4801e00101e542003481c1c241c01404462031000899554100384007440b00007a400050250b000010f81000034065038000d010441c04120803000400d240b0034600f042320404510400008580d108650501903050040382e807009170301640030994085a42e801080c403591506038000c1408001c09080040e21100d10440e041c07400140440020158000901d81410315a0a0007031928 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 231444964 1250 231443714 231443743
    0x20306060f0303032e172e0c030615031a09010b07080f0906070b060301060605090a09020309030903030301030b01030b0c0a14070203070513060e0115091e0305060106050705 76
    0xc000e031180c1c000c2500d0307110082c0040260100741107405400022141400c3c00705520301041000c0507100c0c0c0c410302c282c0240e0403586000380310b14a21103c20300e01040084010b410034145070004010b905c021032002c2d00034000303800c00303050b1104030219142c01c82004c44142c41070990307030204261207103480c0200b101c0546445140a04089001400311a5248040b9803026a2111540751f0320185042c1c501003a0041030513140d40030314009444018032043c50039190003060214003c02030b845d500d07070f019200e62107038141460700314511010800c41000994091980300b0100c10a880c60125117100003815a4000d80080f9000c4900000500601c110b0781c450a030b004890506491400d8240c0401400c0e00304040031b14001444009081811910107104040041401a007041c500520b54040c0801404080c041d4408802d50f1000000e04000360704001404442d482d100c01c92107506100040302d104040100e413076612217a40c03000200103001004014003d2600790341d400e8950002e45082e60801440083d0b100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 231446214 1250 231444964 231444979
    0x31003030f1110290d0f0614010b0415090302010207092309031903020f03040f031b060605012303041106040f06020d0e040c0e09280c18080705130209030303040f02030606 75
    0x44c0c0d031290841026200d4100c010314840740054035100001c0c111002d000e02303603540c50200020b020280c0c070000d0401e803009259807030b060042080b412541c50005100103801a0b1005600f040186130a522094803401605116805152402d41c201c504000959115000d50320020380200c0c00342942501c2a0200510315040d0710300044031003c180d4a000c0a0005408020209881400c1600880c0340641c55900711038481003882460034404001d084034400c050200705074400c0f80b51030f141c401da400515960704644060554030345803507400ca20819441903d0b0440803c10010420745540c0b0101001002c42c0e074000c00c1582e000b2080100451034000700d66005604081d00308510540055525010f0441664805560b98070210886685241c5402c0c10080440c0c0d401c0004000b0001c1d008809403151548406012003008011401c5100f074511640c4655000800709120b82d00d041100035580102040b0007608080b06280000e0942e4415201120003000191064045040a0192310b038030000446400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 231447464 1250 231446214 231446291
    0x807050604030f0b0c0c1605150408060c25080306030c040e0c0f03010222290a0804020a2102150301080a06021c0e060906090102031003030f1110 64
    0x9004156020014403801c4040002000c945d090390a442ca90300f00c8a084070f03016403400d541c090001ca680d009003401141040191407820071171340220303030450b4103400040080c0d560b070401d901d501c0c0c0c2000b0f01c0c0107404640f000300c0f8403540d08001015881980604452a40c03800e2140401d032800880002140c01581028803021002c50045122400500203071040020511030400003402846a001100d084107441507040c403401802c00e03080e005035061050720019001c50344000f018164036540c132089030305c0b104100d00300c0e085100b051125040351000c1d20368500d16071595103400e8206c0c11003001501c2503422800ca20706600d0840d00712440e0542501d030349455541881230007511880d158001424468000849000708200d1030801600118514010480c1d040c0192000707450b1107080e100382c0d5543c07043c103002c581c6001d418801c9034003c4040010b04000a869550152071140d002c03110340c002d0010443c241400303000180490755000214800004040039046180c1040003d101109050303000b591255 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 231448714 1250 231447464 231447473
    0x180d030b06090409020312030907030c0b0c0d0c17030123040b010e041a060406080f070f090e070302120c032410030504051608010504020a08010b1305090c0d0c080705060403 76
    0x8540d803040043e60003003806071140c004a4a8501960701206220600200b04005c403103002c00e0110560744504608500700d55110540a017600402c41001600d400111000341114012400e400c22988a210410740c180c02010084840c1c2d0001d82c000070000a036010300a40501304900d80e4500444100d40070045080e040700003d0201c459240790a01881da1488406130142034100e010301c880100403d03039a9196155a0002c14200c403c0d180c02d44c0c0c1e14858000b00303c019004200d55201c25046070380d020a010303e0032601070f00c40c03100a8a031505042c2d081001c4440503c0c440c120f5032089403c5140ba95490800046c041030140004030840300b6001000d002c6400369640b650107001c0c8620500e4045400d480b40d0802a00300101120158020a1507640006280c60103402961245008031f0f5a510807981c0c60701010300366110300078a00e5200000e110750180c0203070710398405500130035020100c512403e00c641c00306900020303440003a5404403500340c08000300c030010044040074000659040b41450b1559030f4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 231449964 1250 231448714 231448717
    0x4080901091d010e092a030d0815040b013e01061809080c060907260a021002030912060402091005010207030305070f1208090f0309130b0406050306180d030b06 70
    0x1601d00b0140e624404210382c44000c0004070480d1800c4007180078886d4080c0b15000d420521269600e00901900c0c02440d401c0b40580c450758030a0b0b40d00c1242d2100004044108030080030b6283c01c950510002000462440c800743d11814006003402c503808a8400004907000b000c141000030000c140c0e81851801c4c800300c1c0e0310f20b0314103100141321000810040d0181c913041d010ba0007210808000c4e4852103040226892000650200b107510440310422070610b05144541c0c80803180541544940c0680303c4403006041801221120001c1da20549050680700400620390a00f074107651000ca60043c028802980342080c40250400942c1400d01c81d0a0b103003000107501c2d0301c460b10000e8244007010403440b0034050212136000025601c40840b9031500d04084001d041d4120540f40300155102e40000070140b0300e000011240000700c0240302c00d500c82910340780b0350702400003c1c3c021038005440d5040080e641d18104910342c0928455600b94650101007201c00d458681c402003848d04040c20305d8030201845e1542c10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 231451214 1250 231449964 231449969
    0x71505040302040b1201020c060f010807121209051005040810060503070b131a0414030a051f020f030702061603140105010c060b03060405072903280504080901091d01 73
    0x40d008240a1303801d00014030350b2122581100080e50002800c0c820940010401c42e00c2085482030a8040d40d890740ca2480e80c0391224000c0566950807502c050000c0341500344499040b42ca140352440300d89071940d01143c80c03501600c0d100b0021070700c0801c0900c40a0014001c3c2c43c01828666410000a40b81c440080d81c1c41c400c43c0f050544280d800901c60354181182200c001c081c04126040508450007a100000544e001d403044255890f8440d0710034207240780204400e00c00d9600712000340081680608a02c0390104080184408107600f0000f1661002514014500c5400150043d01417880c01e04028440105240074000400d49030004004082185090044c1520390070701e441400000c80740360140040c05868040c950610420040000304080041c900058502d039402011080c44014205007001c1550403507100300582c00e000140300e0484c0c07010040c1e101d0500c0311034160304c4403c4043c2e17002241d0301603034161600c480000c0c10140550b00007203d0700041c8003000c80c90006825032043c6000400060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 231452464 1250 231451214 231451219
    0x608120310060809030706020a1e1d120a020a03060902190605031f170f01110a0806040207030309020a0f03210c030f091e0e280522050609071505040302 67
    0x3c0b00403448848080050300c03183c1c1c0d0300581c01c640d43d60050394054030282d1651403103542c884c000c2241c1d01042d8411445c120941d50729440d174940c0f0700703481010040c0c130802e00c481c1c5d1144e601c030385044840940c1e00c402d200300c021800b0300170018052045005008010707000402c0a41d0b015801c51003003101c994001c084035840303014000600748507035401d180071482051513400340f400c503000d02070049103e880101d0386c40603200865000f00f0214200d079002e0340d000e004060041c404101c6240000c1c2d40340c1000c0d0002e1120720310070b00e80020341d81c0660340010350582950b00102180307044454241308000300000a01c003011080c0c0030004200314592002010282901001010012034040c50340d0114001e05848020704118a2141443d04951014840b020900d20541001156200c08207508411805458003460070240504401ca00000392a40c007500c0080d00742007000400f8404000740d21111204001c6182c8a04060403c40c100610090314018035604992280d0510300e0405900d80d030005c08480031680c0c103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 231453714 1250 231452464 231452477
    0x60e0624160c05090411090f06010e19030803090d120203100513110d0207030314150d050c030706090311150306040c030b0303030f040b011401050d18020a060201060812031006 77
    0x582c6031402c0d09011503030003d900442c00f00300340020008101613010ba400c4059400c9460743e6030b00c42e240c42d56a041524424089000e20240c81414100a10b0002c402240a0104c0103c7c070794a80d201000355004951054094201450942c9102c0d13118450440e0300e00010425411070401c01c07010402039085202d040c3c4281058814009091081c0d00100a85030601c502c268540d4000c02401303002c0c1d404082e040f00064a0514910030707074001c0b140294000c410380a0181d100d125403a00f402041c000e84201951a4880c60070310350166a01041030f000501103503659003070890702d1490901c0c00b000c0c514404c03521441512000c0410b084615069035403142080b9400f0410344180e1909a0061205400c0036816020000c20848010340400380c060165100f1030007400580c1c0d039103915074032609295a181c0c0c00038504010405030465550001c00c0f44450040400f41012010707070000c2e01c0742c40250b01a0001d40d449000801000009010342d0403c02d200b030500b5455850007904126080354580604001d0000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 231454964 1250 231453714 231453757
    0x60206062e09090608010504171303050a050a02042304030302090609090c0405030c0108040809131404060509010606020102090102120c120f0306031c0806100210060e0624 75
    0x19101c4141400c21106441220403108a00081880545005000308181030450001d030107001446071754403c075004142172803c6071850034501d210340e001074040d88440d940c3e142e0200c082903050080c95070543c07046000384103c246901c180405c5c1d900400d44241140c030f00c42080445c6c540b1203640750f03504c00d90602c1d0059940300d820001520f45d02a089c2c04541001c003541c10000310400e400010015100110212030142201000454108000b1034000700705000074070051050f8240700040c007600d08070b0740a002c510390203010000c0b0107641c4d080b901503500e652a1028420601000e210f1900601200c1c40203600c1c22903580300203566411070404206044100060300d581052041c0400c10307012058401c6941d580e041d01651084540094031060710078014841c810749840c0420385600d21444068075030f00c426580f003008002c00200a0500c1d1002d5014034001c0b10080340180c401c0101400742080b0540b00c5003051024040484020164480e803070031200d108580e0803500d5400c0c0d0b2071a48850310101c04c00032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 231456214 1250 231454964 231454999
    0x30b0d1410060f08010b0409020102031204080708160b07020606030307150605030d1d01080709030f0f051905011a06030415090c060903020907031e0905160602210406020606 76
    0x207031540c060800c124608400030a400b044076003210110303101c26000b407003603c5c4200204801c40b82c40c080000d000d64420800540c10180b1380d0000c562090141e501c0c4c1d070511900e0f440f15051035114404100c03413901201001d00802000c40b00c0a90000c0c018402400640307483da0119560344920b0302d020f054030080b001e003013043c10ba05810482c003800c00038050314000c1e4044800a40304140c000302d040e000301000c905401065200c2c1440c50b1090045689901d141891a00c4912480c44000c1003a58485000704004000c1102085251442442801c08c00303080031060a126085501811030710080c0202d004000d040f0382d0740da009903504160007509620106d5135034582440186007902c0010034100d555080003030740c0ba4001c40d15108030390095801d000c0380e50310751130704404445080410845007220092800010611a4403000046100d10220381c442e0800400000d01c144480e840070700160300c0307007407103961110f8a1071035202c2401e4030a0513542014209500139495040081486010f1103501c0c1800300703400c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 231457464 1250 231456214 231456223
    0xa060e03030c0d0504031203050601020703020d031b1b09060b12092e0b0d0c0315090606120203010b0102060405030a140f0715111e0f07020303040b120601030b0d14 72
    0x104052011500f40c0b0048502c00780890704244000e95003104840c180c41d048078003900a80780b245005901801182c0e0460382002800600c0030b005400f00031500008681000141011014150285100c460701c1c050004201504071042c1d004003500c0c5045c1754041140000c0038064451641000100fa00700740c0d941c1b50070a00c0c102d84403400b100b441030b076020804584907070b964048410305a001d42c1481440d8280003031105200401c40c2c010440d0035124000c00100307404285038540c5c0b0703180c1040410a0380054035800d045d14880d401c100c0380d02c0f15110111007189000d1040b0380c42144280042c20043c6030030b8850548074016425031009100b910b40d10380c2440039101d0110348401c0e500c40d00c20313510383c2d02c1750410080c105030000d05508901c1c42d2180e000004017205d000d440b501180910091003c800800000c0000d41020440b1208582c5c144814001a40c1c140003510142040b05410340d00c0b00c616041c91100c048010f0302c242d040c103140548080c41c0303403242e414404006801070b10901c1c00391000309025140 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 231458714 1250 231457464 231457477
    0x80f030402120a0308100e011503200d0209030f12030a0504060209062a060912130306110c01050a06180b0d0212010b031006060915090801050a0b12010b0a060e0303 72
    0x5000303c0300d80f002010741084031a401020020040030300c4903142c0414080c945028029a08203218440c072900f91942b2030303005144584d240c1c09078607804004004584116400841c4036003c0c15402181d00c580c1801c1c1080040c1e004400800102369101040004248034800600140040340e220000601802055012900181c002078061581c5620354040080040d00c1140341c54100305404900e1030b02d001000a0840c0143d070140082d01c1c1304102d90161031516072107451411400d50300940008003088492044844003a1007000700ea90b0380000c404e01a0031102c009000035081464140c09001c42003014100060403195030200107001c096500002d29120b12155000790b2007500c441002159440640049035903003401d80c2100c2c5203105006441041d62a103000b01800a00a0701c004c000d40c080361583c2c100d0030462402c000c01180c0e1214442400c0d20412501d0f0000d00d07880341c40b4413183c0d081c01003510480c6648040200403540d2088005590b40c0706500c100070030800c03260030441340c503903060084821 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 231459964 1250 231458714 231458749
    0xf130b0901030803041a04051b010201060f060f020f03031303030b01200106090609180201030b060408070303020309090105010201020903070b030c090604140f0607421a0d080f030402 80
    0x2029a960f2405803c0c581c1300704d6003203403401c2801c003400e0000d41c2e04103c0319002d1507005010349502d00340c202c0701c240c0032489503011030304540d2141000200c01c400c1019010180000eaa0b43c8011000e003188041d1804c5113482e81201d60b58010400c02081c1204000780b8101c1581c036150110389a811440100c500f220f0307440480003c0007200d030038a094540158041c40c100c41d1404418171106688100440840b0101008000182401d20308080103600c280d002020300400140360600303054440c00032600e0010340340c00031405070340700081e104410714100280d0341c0142400d10095203000201030110781c968115200d080d540750400b2010501c0d400d1004d003541d441d068041c0c05a9102d580d55a460540440f000d102c4a0007560144020403072130500808680000f0342081074460300303600c0f4030030710842c0c11209040a24959140c20442c076405603400d070011551812080045641580c055509202004c40040244070303141d0028a000001d01030000d94142070101c13240d0b41e4990340c172800030656034160340d0714000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 231461214 1250 231459964 231459979
    0x31a0a110c010b09100605031906120303050a1107020607200402130e010e09190303110a0804021003020c0714060c01090c030c05030c1305070c12120f02090f130b 71
    0x624101c0150f00c10000240103d80e403040640707070038404603480007542c020800010380410005202e201000d0080315036021111001a006540c0c000c800c0c000721182030100c000a03281c00600c8260780080c00369018000c00c94031200c1c5460a5035000409501c0350401c0180f141074004900c1040c1e200000300c03641c0b61040a00295502c1094010785d00a02e1002e014041000f2001000814a41ea088108501c904107003001801d0740742c10b0a800310021084854100d08240e1102302210a6203840c1d400340401c040241c590400a007403902c10000c142d800216803504040c81031008440d140300000d0000219520b48882207403410074a000310380c140c803462041402c6507003000300d00720410011840d16000c13070307004000c1d40307084984590070552100b212200e4264000300803409042405419480b45400c043c0b14180134602441558520322001014045da00214042401801c45c0c4800c6010b45e101d14170040d581180303800c0160000814412000510320302030f0095850384d000c02c08059100d10043c11000340003c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 231462464 1250 231461214 231461227
    0x1030f0b0312070c0b0a02030a08042603010602010e0a150e0a0501090503040e0c0a0504051309020a030605190203040f08130e01081b010206070e0f0307030b01081c09031a0a11 77
    0x9262a80303c9034049032862400140010505030120596118034010380c081c40c902400f0720303003c4501c0e180c003030000e03518896249204c0c0c02c00c4617200768407040704032003101c0b003070701c0350b00d0840042e00b104c0075411018041c2e080008060f0000d505014904641007507038500240318000c81c03050b0751074050390f008010201c0d1b180c1701004050100020190089a82109441e05035a5820441a42c10f0041d10080da01040091005008502c1c1022205d500c4580c5c50340c001a43e542c0e00c1e0002076185085a00c207454266660047c454a505c1c82e4004401d0b03c2200d040540c80c5003843c0d038a6044040f00717200050104a4041100c0490440c011442c2d00100041029526196183c2c081e8a80300c0100d010148541044a140c1e49155400841d80038452940c40c1c803a0340b01c01c0c1900e418808880c1c4c4101c43c0982c180110b00380400080c0710b9a2a140c040c106203001020714800c0761440224100c44504030341c3c2132012040303040002030034480b90a40760a007066886011500c807c100b000152003540b0898804a0011420 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 231463714 1250 231462464 231462493
    0xc010207080d0b06040828050a0c05040b0409020d02130e07080f0c0114032a07051b1f03091109040305130b041203030902060c0303071701080111070201030f0b03 71
    0x6081c41e04202c60042203400c90080400000d03100e00d22443d40701da0000c803006d1081402008031980c2c401c41080280e8038150ba06d03950305081c0a0f40884c211f82140080c0390a00c2241081e100d00350038801c00f6141003050b403803160001141d0007030f40300c0024450150390100100c5600c1541001200200134011100095141c0e110700c0e1303d407642074103141e500d03100d01610154070350b1156000c010800a40000b043c91503c4010740b4144100c240351a003041415815410707503022500c1c100401c00540103a0151050412128054807015140d2100f1071181411518000754603910b00040f24105240e401d0005030180240780c0001c9489100309687c0c0e100800c4402c0009054110008003e0041c114070703404161629015040030038010b0380150a101803400c0405400a80a5413140081c1800141710500b84000311608500e15401112200002210700c014070509250b00070300344d8007400301140284210a00980e071103400d4007504102904254880c517002c600c1d8041c5a004074190880038040c0d54805c42406076 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 231464964 1250 231463714 231463717
    0x108010501122f07030e030a12270801060e0637090501120203060f041106070516091e0204030f0b130b0f07020d08040203060112080c010c0309031409150a03020c01020708 75
    0x59001c10006d60740e00c4003500e4041a1500e40c00d90120182c0c003001c07000001101c0c1912031041200c110411600c03040300f1121200c5007500100164400803c0e86400e142114988082c0030748920f001c2d80003c0749004220000d9010308040195102d4100110042d0f094151072101c0035901800039079241c9000801e000740410390384106a8003d40890704580c0300d061041e10050f0b02110080c050080010401f2034515089004111150240d0704803038203039444041282c04e8450552103451150b039952200d001405406003882820a18680114205441c0d500e0340c650000007880000c0c0101002000121038081c22a40210907a800c201150703010f1400011074404403070280c0340d0703001500c5080c000e0328031184a58041d6200c1e5a01074050034041c3d00c3e0503620b01150100a070100c454003018400150400024451701c0710402d0203580116044c1c1c120b040c05004911825503c8031280001c02450105448040740a40c0c680070712301c41d1540c0d032048020308030000d0117003108007040c03035000107445024089442c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 231466214 1250 231464964 231464977
    0x90c0e0a060311130e01051e090406050c07020306010f0f05060705100507110118030e0303091c03030b090c090114040501200c03070906080601050a030b070c1b030302030a0e0108010501122f 83
    0x191450f0702401c0074083c005141c3d42d415004c680c01903027840028002241c503000660424480000141010440c0e40000d0070088260000c03207440300205401c01108030100304e4600105016610549461690b072510780d101c82c4080c1e000d03000030b41c5400106045030703c034460b003408240109000f00200003401000c4002a11041c038180e0002c1e082280c1d4121616011007100c650f1a0700401c1ca8240c400c04540c2c003403c2c0403504000b40c003490755420790500b2648612004078070034141c0058072940c80842074005481c1e02d440411526000300d05020134082640c2003852564002d10b55233175540d81c8002c011840d450902002221505800390b5040015003500300d40050b0103882d510010341d58180c2e02c900a01c00100081c0c0700c0607015000e01800b03e56154011800c0002250041c0000d02c8800000d0402100e4003506900c00c17001644001110350f0225440a41c0512945092801e180c1035450000004c00d8405c542039514002d03603441c880802030910030820302051205002c0c96110845000009003c11340010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 231467464 1250 231466214 231466219
    0x120e10021f0b03030405090a021303051e01050f0f09070b13090f050f0601051b0102030f16090f090c021c0c0506010e010b1608090910090c0e0a060311130e0105 70
    0x1200341c092600c16010341c81c1980400303002036082620304401c010040c20080c001d0141594200851101440c11f0510781c0c0103103006400030b0660319070301102891058007051916006900d00030a101c0d003015004c8540c2d40100b400000322120340c5034544041e0074508541e0003030b1000d10002030002280165235100c1001c9450f0b625080144150102010041c0d400031154081d0b83c02211300050720640c080d0001c1c140d45c003001c3c09041e0804012910030b900b26803082d0303041e00420002004001003000d0750000001003040620700f0251440c5000c18018040880e8001c20f0445ca031030310100c0361141d20800c80018200742e01c0c030290740c00c1442708001618026004100b50b070940101d40001c80d41a85000001d8101c550702c12215182240b10301e4802100119410107c483c00800c0201d6030480e50340c116100c0c00f454038441c101c20301604e0304482004540d1145081c40521003101040c0e0325603079503140340c0340464416080110b8448010007090146208000c9207410450a0000100b248520200b125040c1c8506 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 231468714 1250 231467464 231467503
    0xc03120c081801060830030405010504061d0a02120a0c260609070510110102070624140f0f0603090105271b0a0909080702031506030703120e1002 64
    0x803901850907560135016081440c0e00c211302003040c01c424261a801c85584196000801c2d800c155404030071940b0a80741a60f1a80d129414017060004620400405130500402c07070000021030041592a40c140940181c03003a2003a100c2100c1e501403c0c4148900c0303a034048000201c250720b03245200015140314040c5070b80c3c0f0540d00691690641c0002e20039016030980c20040018502e82001c000311260056000c0041060450030142075000c00d0000e403c885128840204000100c0002158010051114400741c4000704034200280e40c4d0400d00200003440c1907440719524040000400e584880960701c03075401070400410041c050303006602090044c0610040e0070f8481000d0706a240e558100070888003510f400068120803510028603600407001c0e005844003204903583d050345011107416090585015100252050862800303100a102d04c00c0d00303a076820358500b01340000ca903991005000090003808402c403840100e500072082180e0420004140c44800b80703201c0d500944036013010780d84007403c445 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 231469964 1250 231468714 231468751
    0xc08030c0f1002090a1802120108010506040c030209060904090c03080a0f0e01030b0f0409050c060301060e01141612171017070e1b0f1209060f0c07030c03120c08 71
    0x42d40201c940329040200754011032414103400019140e10300f0070354411260300304074080300304c120b080e1658000c1c030b40c4000010b1030303241600a101c2030340c5038103031540c00300361040051400680d28507082e10f41404055400040000c240d182200c803544c980d41000d0308040d00802c0b6200d400d03034400c40d240010082556009001c150b400010740903645d80000d801e9000d21120ba200341d03542055480003040d0340c000d0045413002501038000c50002d41c000c0e00080002161084000070f21b5800c44404030000c0380d600f00141c0782200001e80540c030030300d001400a040e0a000bc25612105104416061102d1000d4541d001141407280c82201401d01038032843c184180c3c14101c9014510b000f02d14981140d00d813111a8215544180e005034904455080e281d90b4181c0501030042d020000201034801342c0041135a100c030504217807080d00e19014000f80007810f28220714041110569030042922042d035810f04011000f4086481c06480e06007035020081445454026640012644080b1311401031707111594260b42e128 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 231471214 1250 231469964 231469993
    0x807020d0e0d0f080717030c090402070f142a2407082a01140408031305060a0507030605030a030207060c060b041811060a021b180a0f0501061d0108040c08030c0f 71
    0x200720f03090b9003216005e0100700c6c2030780ac15130004d0400714400c0250700a5001103903140c26a1b076040c071200100a41c8140016270155280c680f1120b145030152010b001c9031162032001416500b5011052100a202000020340000799a025902c000750f0180d50b00346c843c041c11140c02d11104240d100385200b01d40e01620290706490602c100641100c100c00319205a40e2a601e40a4803a400a046011a02005240a80428001c0c071600b4000c561f501c4010989042442e0000d05651079500b041e03119070030562101000a07000184101161070506103000940075a00b06400100580c81c060f0b5001424140f01d511500000014003500030b200e80011130032a030b0014284a51390160503200001340e0700080d42c1012072030300c0511041401100414108220b02041401c00c00340c0c1e0250b8901648585a0220215212240c09014050b00c1c0314500740395403100e80203900c04100d00c0845054103001d000c3c8045401d1200f071545035809803580108807030303440d404001426594200340c7c1c2403100e180180003a82f00e500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 231472464 1250 231471214 231471217
    0x31713061106040b0c16150c02240a1e0b030105070212180406030512070302190f0602030601020a060e0705240f030a0b041a100807020d0e0d0f080717 66
    0xc401c040051032a80d5496540d40e0250740003170084408450207100b0000c1540188103e0780702984100c1c01200d0395002400748500384d40306582081d00303540100a00f030351811800340d45113034000b0914900b03002645403890148010054508000d01907030008500d11b400c10381c0c030b030840000c083c4198002c0029644201d4206e03102d00e040c80c520f00e6807400c100022080140c0e8002c200080f03000c0180000398003682d9a541d03030b2510000c0c8822808203070700031843d6804d164052085510a03400c0000daa000b4049569601581035903803000205026808404206540d02c2007041c01a2254000c400b04400402d4140382c41d5121f8003441180d00c510040c0c240c2d00c00303858002d0b51203110b800c44106414200440302914034400c0c2c000a014031030071075541503110340c20303a01d41c050319544500110401041074000d00601107175150b0541203105210103001480311844e4001500400482c1c28905180c19035807680000c1e40c1303003084080c0a8480030780c1034404024008000001c01e080b51007915208034480620141d000c09 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 231473714 1250 231472464 231472487
    0xb18041415060d03020f0d0e10020105010e131e0311010b0301020702030c090403020a1e021c030f0f0203040e0906090106051801050d0201171302040b0a03240603171306 74
    0x90510080442c20700e0400e05864401d0714843d0040d42c01203460f050609181588066080380014054101c101040c14066042858074040744000d1201d5810b004480d814020054680c240c5110f0800c4d4403400d024012039210008410384d41d4031940100c0c18180100404503000381c0f80215460200d49103042d03e01482140c002903805006010f04042c010104881210010411b40c250301400c40384000283c500300d010141c590007c800d80d20220304a00600126a8604407191030400e611081100801c0d080290011820ba892824000004600740128194040c07540884910303040e20003400381022011443c14802d03074610008104880d03456003040181407a0094514440d65800014000360400014110720a130060506004503031420003076005000c401c9508802d485481541101140b90078041d03000c4034481203880b9106541940c0343e10f82c51030f1b0304411b0030070b0342c1c100e0151103441006603421030001980c001d10610848440c0001200c0f06a2009508460302c050500e00405c0d03143c0110500c291 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 231474820 1106 231473714 231473743
    0x1404030f081006050d0504140a0308180606010801230a0e0a0f05060f04020d1526070b0409021b100204090e0102040510080a0b180414 59
    0x3861074003504040d01045503800412203650302000765030941c4d4a50314002030310345861508642e00103c18010110074083c03050080f0a042d007003100c4903c144c1d0700d40c481c0c0614960b000c0881d42c80b004110b420320701045041300184203001011450300c1d90f40d642040005040d855210009408070308550103032600700c4000d404c1260502903806419094420194144162b003006070019440399111540c5601031580481c900b07118030700c00d801c41c46403400290444810030703480705800c0000c24080700b103820800e8240c00864201c1030300000d5200841d000d040c034490400e810000b002e0044d6005c02c01804d1240701c0300d110250000300900007140d07a000e940d0001a0b0b9249001241002d07166520342061803644140303c1000180c507107070b81d55004c1010500d4003100664807041084001c00f108600c0541103100804c0000e00b07110000915805140520b8002c040c5029100b62950390342900031070f00320b = true := by decide +kernel

theorem cover : BRFrame.Cov 231294964 231474820 := by
  have h0 := BRFrame.cov_init 231294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 231294964 ≤ n) (h2 : n < 231474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
