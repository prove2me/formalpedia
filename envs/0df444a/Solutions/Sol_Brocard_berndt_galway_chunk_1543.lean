-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1543
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:29:40.186925+00:00
-- url     : https://prove2.me/submissions/af8c2639-2735-4234-98bb-f165aae84199

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 277338129 ≤ n < 277517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 277339379 1250 277338129 277338133
    0x10302160209100b0301120507140d08031302043803030a120b210f070e01050d06090503070303050f01080a080304300f0e01030603020907031805010603121e02 70
    0x15150050409410340b030380002c00101d0a1109544807000d1441076042640070313004a041842000f03080c41030500080b0043e01411101220b038240e1003020640d40c4e440307104000e1926200000003200c007003031820302640d100d500900910015280c4c4071000b51f60ba4100510b0103292180000d4020241172000040303240150280146080c404100c8060b940e802c940b20911583c50b480d8640d240040c3d544801c540071102011540140005050f000c1c5450324080c0c0e194020030b5030041100348100d482d1058403d045071411617015101c20101d1400707102400f50020010240e10000c281d160815805400c11b0788660f079030040c460b649aa0301d0035402ea58050440c0c011701402c0c820001709000ca104c5034000c01d01b80c00d8503240c1440c00207010360b042103401441c00074000010b0190150605032307980200d080200c0c503400d1800b0301c82c0904507000200121000b40581c0b050551360003940c4030b03107010b8507100b044164010001f04451780d602c1c20504d9520001d80b40070701c0012099a00900c4071a1946800d070109511580 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 277340629 1250 277339379 277339417
    0x31206090216080714060c070308010e060307140102011104030c030506090303220311100c080603010c0e041a0d0807050601090c0804110f100e040f14040609060b0d0809030c010302 79
    0x283d16101e03070f01001c025030f06102e040d071030480e4404007004024014017560081c40ea803183c0c9801c0042c40f140040e008410030303109407018048270396000a80581900d901d100340e8540310042d140142e00400380c0710000b43e2607a1001c04d0000c140703c00c80c03450004480c0030344250781041d641d40207084d4486c07100f20b0305141317868500b080196000c42955040303c9014030900380a580f130000401000c0c9800800c884c0400c0864031401070f99071140d44500ba568104200360002d0201c200c811602811031002400c036280511340e1a407040790328028095003554a6040945078440300d11503414100890750207404140c0d0039200f04e81c00000c2518982c400d8003102d0a403a074030034010b40c5031551246e01c800803c00703400c0d5101c0c40096146a07140e540c00c54a0300840700680f00c0445618010062100b80c44010800319221450007079140400320130445031b983c2c410f61209000404041d54a4401c0003030141003001500700c48144415030070032001034020603180c0001c07401c49000212010044040c0c0c451040d0100b04000c0d560 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 277341879 1250 277340629 277340633
    0x105010512010207122f0616020c010c021201020909090304090e0303010605030415060e0a02070b0f0601090623130602190804301b080d2f0604031206090216 69
    0x546030002c0c802e03081055600c2017202c00341c0354020403081306e02061503130405d406120229410300940c0c0c01c49038250000d40f050010010001e005d1121480340a8050715800c50001c01e000c50030350494074041c2c4010a507407003a051a0901e10754079003190183c42e200034a00080503000001c00001d403412119182e4070945199116a0f071a07000c081c0f030308403a42c1401c0e10759001040007a201c40c11144200150140140c5410380c0d0300f0041c14028000e40300310300c045000d401740a11a60301041c1c40003038503e10308140c00d040c0c610041d1141070448601c2c854000030030105659880c940090010012079106600b181e0400c0308a01850301d01d41d52013807008011070310400041000e00c1c44440c5040044003e8400036108402100f0380c40c800d1020080d0450f80310515424580140c500056590058007030100181164100c4c864040c00e044181000816aa1040400c0b0599204498516945d0700a01c0d020750340f4070308140c40d000d0040c100703103e0100806410043d01180e00091031090740d841411740304094442840603 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 277343129 1250 277341879 277341887
    0xa050f01091116060b0301181709010207030c0305031c1505040b010504030b09060412140a030504020609030307230c0f0918060c0a1403040f022e02010501051201020712 74
    0x641d07800c0341c1d9070b8401d10019180d6000142c0207000350b8059400810412a660109401c482c640220103041d59242a41e4002050060304d134026002e141000d4165a106454010b0340740a0281d07000070f000c003208440c003004021020018150143c14003142e0207002e0490007c40041d6280c41e226214000441001040185415000f0600800060510b9481c02e91240c4850a040c601101c49038056403058090000300001c0001b1103d01290600c0e10064603201100c01e02d802d4850200312004040e214404101599140b02c21141890b00003011079a5071211440c1505181c7e0203550030702c090305076161b046040781c1c002151003070111b40300801030740382c0102175400c0121010002e8600c29081680b4085901e044008111290165160010b00d6403501c584050081c031020b86980d01c604401014030600001540d03480c1c0d14820703903504031001103880182816455070304005c4160b20f180303038420003482140d00b901035004a040c0d400940c1e0405e2a5002040c1e4107090780303d50480102240030665a00b000c0b10b1007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 277344379 1250 277343129 277343141
    0x1106040b100807030c151416021c060c0f05040501020d050c0106120f17070c0306180804090e0c030106030b0117070b1c051803041a09040e0d080a050f0109 68
    0x40c01140500503210b440c41c0d0300c0c19406410407143ca842010b030038403010f064508501c042010503d07205001c806440c190130198003a4008010340000320080480856071051541000000403481401d0500c02c80e08040020304207200c1c010011613143c46854240b0792003039085900780c44060b0007c10500c2c400200480d810350003062604507035561514045000ba65801000300420b00076041525602d4003800d03d0b200c20134400d20021040a010480c2c000001e0f40c41c0c164004507900810005845a078030207842c4085102c694004000210025010407080026845404004210021074200741081d0382418226122804007804000313078031004220200610441100400a03030007680c00450780ca0406d09040d070061032618013458030300240d510b1440750700c0c8141c40e4003c8001c1a2245541c0800b09a161641b08600074200034480180d10f4140000c01c90045a41c00d60b00944108244021140c04546075141c038100c0c68001582e1002084405d241e5000c0c4501500c054003256509901c0c1a010390002c1030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 277345629 1250 277344379 277344391
    0x605030c19050d030207030c060305160c05150f0118020720010504030f0507090c05091012020c0f030301080d1d0f0a03060203090109111905041d0a0f0b01061106040b 73
    0x10004801290070780f124021002550300c290000d0060505518142c004034500c2e8008208140c580740400401c0c18404d03510f414000d0090030014083e40351030030b200781808505501000b2080c98142805640200e401466048030426419841e4001c0740720000b606034461814043c00d03c5495040900440943c0382207000d02507014103115240039034907a121046083d01c80c1059030241c0101c3d004000038030b07460084900001d414a84986040c108100243d10003102c10072460420846a0498042010590440d2549001c0030700300c0342b20000010b002a5607034402d018245850061050090080380146184880e030402c1c099100481d96950043c0404044581d40c1c042d4070240103d00040451950302c0114002e00189001080c2a4014105500c05011000c8002c0c06910741904800004034804a601d054403070071100825030894004200c910743e00401403113044d074081c80c502201040b44510307031098014070503903002a45a9864405036039401080d00c500d00e05070003080005002441e96001c0030383c800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 277346879 1250 277345629 277345669
    0x30603030405330406051c0b040609050105030712020d24090303090b090f101a030708240103110904061506051c0e120a0309080a1709010605030c 64
    0x765a8000048689200d07415a1680c42c04000d843c00c03002140003404608550780481032490245011401803030b47c0b1410340c8842d41c4241070015041c5040300750700903200081d030040c400c0c01040d0321682898020b01003842243e03c6441232600025081c1e100980d440f900640050202d5205002c9459a0034918511280d540c40c080403d244000d8850701440380e100024001d40e0b0005041d02649056160030a000d008544141d0003c1021442c0c9100010041002250520003286c0302c1400706880060f50b21094905034140520900884c0c80c0c400041c001c8451074202005030002d8100702c5001c04d21101c00e000c0540440c02a40c0b030704829003008450b498100d403203200c001501c40760b1070100f0f4040c0c40c1707160010700000740c000440c4203107010b50b00ca22956941d04030008018130030b0035070b1100c0e640c0e0074154503030303015000045440c83c0514041d50004c580990040340b0b0655401c01004020007507c1030b450700c1340c40c00712410f020601003001441034074155200a07009200908411040143c020701c2c96816101071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 277348129 1250 277346879 277346887
    0xd120b15070f0206040b040806060306060307090c170109050f07141204080702030a082113240203010e04060e0a0f020405060f1818150103020402310501021c0801090203060303 77
    0x5131a24030003003004200c01e19116444a08194032541044009070a007407081d41700009200c19541c0110b4104225034080100081ca460030f01020390302460103400b210f074103039184000028504601e8000300d1103603540e0301d89604544d03a2254155504040082c1070003092406202c000420b4040300180f9802c03600134042c240c201405c3d42e00080c5030190281c0101c4200070007080c41104490709501241d6a5035a5440080700c51504404103200c80d040840090000028189503a00c4148000d43d450700c801c410a9056590350b0b1030b41d00382c11100c0d81c152403c844603841d11620040c001d0021650802641e44110303801d044182940800c00940707809485141c1c044000891101d050f502e07409009010103032100004218030345010204000700d4a06000110b60300300c1c9602c0507010a030001c4d01415207a04a40041e102c40302a0041d850200420a8105001918500c01e94003d0f100c3c0d02c42c1402c0721026400c485040c2c0d40b003800c081142450512000101d140c0c18010b102021403078002c0c43e0701c81c00c003404a80c18 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 277349379 1250 277348129 277348133
    0xc0203071a271609060308120a0b0607060603030f032a02010e03070308010f1202100503090703020913021516020f040902190e06060a0c02040b0109170d120b15070f 72
    0x2814002d880d07002c680c42800300901201e44000600001c100d0030390b08000d01891602c0300c00c12842800e005081d02d412160015a0b0901180e00966400e04040c002c0c80d11460549403110042c062804280c1c045040c08900f0342c00c1034424081d01c00a085e50103400c00e120300303070055004c0b00c618000004074195526980c560300400da0070030240c04458026542d80a540d45403031060385060000350844c440e0030303589248a0001d030300e6042d45252000281c1c503000369a43e849140360b5040600c0d40e00025401640a424802e2032000b10b4003104103e8000c940c019085810540001c2107889540001e05005551190040241c40d100c0305d601400342002e080032440621070b40c00140791442c620619030030026011818015490502c150030b91200c0180c0d03400d840e1806901016008074500390000f0301c180c4d01c1d940c0c499181d901c9003900b00b00414504030780200001c1c4025119807181c0c0c2c01003120000440c403242904400d1220f00901805400250807580c001c0c1900038501d01c0e0303611800041d0345640c0800b8034100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 277350629 1250 277349379 277349431
    0x2060405220c0203090a09060b04030305031f060c020108060a0f050f0d150c1d010c02060d02070b040305180904080d11040b031306052a0307020a1505010501030c0203071a 75
    0x70b0189540e400780d55116510310401c4084482c3c3d412034880141b9210092100d0180041101d0070b59800d03003000350b03c80d0703102d092007168240c142a48a852050f1104000ba80c00d401820024085200b622a07016580d201c906200b82d02c145417040c0195284c001404000d01e041050742081040006080620b040c1d0094645140c00f8903190050061182d40d509113402c1c10b54000906070011030003000703040a48010000080078804289400783c0700c1c010008252600d04480c0c0d0490307140036403040001500d45400e00b0302825907080b064138040b02d4481d10043d5415880c041c00d80c5407181380c2c071070030990400e00211102d5004045ea60314100080c54104404a000410180030314860390088074142180780003868100c0c00d0b00c2002c2c00b09440180b1051511110306840303030300080004500d452494895480c4d800072454400382ca0000b80001303040f601c2400c041a115008103050703070f4003030f20140320381d0184c0c52040303a40740f003146406092a54110504d0340b04900302103044c0d0b0010b800380700703000c848032040c09920 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 277351879 1250 277350629 277350641
    0x426060f070c021f080105090f0a0c170907050f0a0501082d01030b010f0b09060910140d150b0306181e0109020307020606121216140d02010e0a0206040522 68
    0x152400d1413a280840400d6101d075116015210980d0f006109041c0010074119501c0081c100c08640d64480007400c2c4107030b02c210224508034004e40340340243e50402058a03504c0d03041c18021903000e0058150398843d1402c003504808100c4006a440d82ca280d69000d21842e0017001203000149101080f902046041104903241030285008014203c0554500126074244201c5944030107030505c010301c443d00b0540c6e02c01050306c0301322206980c00c144260344910201d451049541c0c80403030820f07001c03e81100c520850752184414510071905280155142c00c45074105000441d0210340c041e80c02c3c01da1464000d41b0000e51a040118404100740000a000c24100c00a000b40c016200e8140d004c402c100007268104282c90b0000400d4641c00e40021000c2d13009a15601c09100302c114440c80040d10392981c406000c401c0c0052604841510301c1075098075026510b80d082c8041c0f110044d03081c0501d8091708440071891101795940104507503e130610701024403154003202c5050171002d140c0703895140c0b2041c90500843e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 277353129 1250 277351879 277351909
    0x60806040b0d15051012020d0501110a110f070806060607060b1309150507050301091e0c020f06070e010c110103021605030306010f051303060b060c0709020426060f070c02 75
    0x20040781805204040c04a130030040050b00550743c4001e0421603680e14401141800e50155880700b416023650401a0140c0074000c003c004401c000a60988030740c0c0c0c046150103c00c01c035401030311480b402c0604010b40d208664082c415064020f400866010f103000310081c88014812600410711902d41d00008010b4001c1c0d503921203456403103881500401107042c00b028490364892000300424182040000c005010500418490590701da83c40c8907101c201407900d4942e80442d4505100c004803020009403200113041846249202e00000306402038080d0302c100c84a80010b945690008456803201002c0c5a010580c040c1031507402c002180e8201c10400c00e4001d0103018000031507490408500040c08907030913a0907d0100081030022420980d080d4440b0f000316a0031010106000c0001740010f10729102e00c41a40840d881040c00004100b01b954001c0c1c81100d880010b00051b2b01031001038400c030b00c080c01e0124a81c50b003150303000944041c84042f000da00000c441c5402c245a002c60307408540260042500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 277354379 1250 277353129 277353143
    0x3040303030c03050c03040b0609060f0307030c03060e060c031308070b13020f0109030b04020402180604270c0507141002071b08010c090e060d02040c030b030d0e0604060806040b0d 79
    0x1403410b55505800303142d803c125120383d0a407031490541c0f2a07952802000d401c0510407011030000c1442d80d524140751780c040040040c140e52040740c0d01e01c1c020586013094401201d0440c2010b170315042200011030f4580c410b0342d00315102e40c81c554414942e60302c0d80442603400c9840c50003e11203240414031600096120341031116208064034604c2c01040900c944401415042041001003032000400300c40c40c0b030b03070860381c103035070158895003a80e4487c0042c02000700300701d1b003008011600040c01c6000d0a481841034101403524000109803031035013402c1c1c41c0362019403400701c0c0d0308000e0f030800180800c01d40d15900caa0001982c86810340b1030b18800607031b0700c102825501c03009286c0c8a04001a2a00e103054000d03d00c60700204084c41407048085c0030140980702d585000d00c20900080c1c99500c981041070f516940c0104200b000e510071400140c0285a4401d1280c028410300409940c810b0044002c00300e0307850010803807400c1c241307040341c101d4501000508064100761144010001a07c44e00c29500c07a55118440e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 277355629 1250 277354379 277354391
    0x308011e1802030a0b040c0f0c060612050a0c0501020c06030c0a03060503070603150b0a09030f050102160f0b162f0a0308040210050f1206120f0607090605040e07110f0304030303 78
    0x915401550b885c80c80d010702c22450004003600190b000b0b0182503840105090506c01c054203800d00c0c100400441d8480304560b2200c41c070704420041c1c04140504aa80301c3c4074040c1c44603031030f0001207944807100f44400d90082c90800c085000c00d940d18003d040003c044e0321740456801d0312000480c0c107060382c03a8441e1022903156904103504409402c4020080c001071a9810b081800e041001003140c501444050280d0400480e0b8909000c4d0a404480885110540100f4240f2051030040e484038100c94042d10b82c03030003c0d004034003c1c103503c682002414144c0d80e41c1e2641202a5081c04c0741414a0740c50008440e414852900c1200e00240250030750f250298403141100d10b0140140680e2481100600d0200034080040001d00c450f4103069800c810803440c80c4200c05d6440d08081040c0b0384d20b00d40c2620042c454103064490807080014803034895062550781480c003641c0c4103416140c2d809140503121a2640d00030008601310701c1103104a0300c1c844001c00301c600e81c06c080e04200307045500a400079000203840d54 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 277356879 1250 277355629 277355641
    0x1020c0718061d010506130f1410021b01050901090503060c0a080f19111204050703050705040c05040504050403020703080f0a030b0105071a0a0b06160b060d0308011e180203 76
    0xb1041078010249480005070041c00c0b01050a0300e084140150f9104100c04111004440310009034003000e0402000420a510f403100c80041c440c184501d0300d036200d03240423404006040c1c03022034100003e07200d0460b13148815041030b0040d6080d400c0ba0320098100107280c50000380aa0781007001354010402500c540340d940d08402d10042c110790f4000e0030589040d05040501c49000303000b41e103030b142c1070058180020b0241440a00c2c802c00344640300d4208810b0002c0000d200a0000100756901203a10620881b0480341c2d5810030f07c02034076130b0721054174080342c42440b0402040c241501b21380da22500c42e1041d5140c1d141c40c2d035602076480c0c210000d4500380e88804a014081c5c150180709041c0c41401c242400b0342014440e58454220140c020250415019902c0111b92180c1007030700038041d40e12004100b5500c44051000007614241801c0c0160388840c2d100f008105d85040c61403054445a4056a82c240142e00b4541001242c035048201e40c18040805400055110011040c0c10220164000c01607940d042c51 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 277358129 1250 277356879 277356881
    0x80c010603110f030a02030d0f0e0a03110108010f1d06030703060c020f4c0606020d140304111c021309050d02011a1210050103050a0308090c010f05070501020c0718 72
    0x10070f0554000e502c00b00c1d0010250790b00050740d002510b014549241d66100d1160708a40e082c401300e07407207504a00078900102c1000416038070700e16108030aa07681c0407280c1c0d072560004902d00440c4121003803030014080c003160088652034a5540300e60040d00300e070100c554a031741c2c0108441030090030343c0050b001280d0072030500d4030500043c100041002a0b0040c4281e0300d01109440e07181c0381d108119106c0c03c3e00004001201c1e403d01e200602d0441410400c1200d9858034080d4031902191042000141010080c0b1403801020094a01594004030100e9043e000c0f40d060000301006030301c3c04e01d00945010901001a40d4005680000704c01040d000700e0f40100914100780703402032a801c100b05590400c050080c4445c111850340e0248242100c01001080c1c0c1c0b60346490030071101c5d103e00101c05003018008000c1c0140001c0c00c20070644a603070b0b0701081e0364600009940700d6080c400528001150a000703107885034460300103086a607016800041c903000302c503041e0a00c0c0003050361052001c0e10008180c0d0f24a60a1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 277359379 1250 277358129 277358149
    0x503150105091602030901120b12010203011514040302010305190213050a12050c1909050916080d080c07030512040309030b06010c0201081b36040e03090904080c01060311 75
    0x1a40c0c030380c041003060a00013a4030b030700801600a04120040c02c003c214844e464021600e00140a4034044806920103092030103580240117440c03d109010510083d40340c82030290402d0b42038181036940c100707402c40c5d0046014140150031018200020b0390f101200c07940ba071008100741d01c00d901500d0f2070380c2e14040074000d20700d9544c1d10510104c1d62000004012071008107541103441803c0f030300c203103503d4051108202c0c40f0a40c3d8000c140428a80f80402c075000b2000110456060b0644060070040790ba1480394a80e105054417503140060103290224824240e07210280249901c00d0030aa81401070000d540c012140e81158140d0020354441400c000707008008030000d800c0042803a140380c0c803480503000a8222800605164601c4407a100c640350081203400540f0810341980c40a2044411510340b000d880030703030b55000205103e0141e511003045141c14400e410f4a00c1d1414051403c240784070b410000c60403402041070301c00b0780c401c1107000c203003210a10804000d180b207003180100d184048400d002030841 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 277360629 1250 277359379 277359391
    0x2f070605071b05060d0509010e0f061e01060c11030a080708090112421712040608010506030601090302060301090c090e040b0c0a020f06070c03080a14150307050315010509 75
    0x480420705010030344900d0225003850705d8100002ca09500c03004555801001040040c5056000d08112540405008512640034240780d074000510329020340d1402451640c04e20504012655104a51001139901022400d90f0000242501c03a10200d680300d500340c0d0307805038000306e484071800156128a9a080b420328902c00c0c9049804011015410690710414840c41928842005065020040440e51048012381c034550103505158802d50341c05c00540f24010340309070307032456004a403480039040700c1020903501212483c0e81e440c09240d2809007841400d41c4090021410015641c9001c4056114840258000c3c008180000b4520031540c1e0000c00200480d0802254821001c00388008113104400341c940010f0702c00c0080d507558280c644280d2078002840c40700c0ea07403801580c0400c801d1582054045e9182402912041c80664031004080100c3d284c4000e00d02107042c4603004100003140c9620400503a80d006000c851f006a1140000303403a00889890159000c41200014071043c28205030a0342c0200c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 277361879 1250 277360629 277360673
    0x9040c031a040c0902070204060b040b0909070c0f02010e270a0e12030c03060d0510090b0702010e1c05040e0f040201030b010c0309060503060604030209040b04060b0d032f07060507 79
    0x400d0690b02c03d03039081c00a00c1040c1110b40c010900342d040d513403982e100100400280f1891641c03a666900424000c0c0c100c4000c181c41020030f01c001480d0103004411508449502a00880c401d108640c0199400c45e0070a0a40b500700c43c1100c0d0800009020305140040c1d1007040e4a146203516081e841501950018200034490b03420201d40505c00c9502c81c01560b0308108103141d125140e589040100e0f95460740c4420240c1284a00404000d000b80c140c1c1c821b241d21801980007082c5580d51203416800d0b516aa10004a60380c09500929034100035414107854890542c0750480c500b030359800e01e10142500654208500d04251400d000c00c540e054491004e0250081c20403010301d071059200901010034900c500c00c00e00c0000000034034a41c0d43c10084401465000f0710700d4500d4180307820074400b425003c55080358206d1400d00c1c0380e40586030442c070130400507905076114841680c1c240c0d0452506080f4150302800d0030304a81c6a91495501480f214020304865980c16882d503c0c642800f208000d40e25400040362 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 277363129 1250 277361879 277361881
    0x30b1005010503040b070e0a03080901080c04270e0124080601180b360901021c1e0603050d08070e01050a030911032a0303091f090509040c031a 63
    0x1a40c01c00181d079403054101802000d030b5940c11909558403031600031f280c0d51010740101c0200c10000e09101a00740c5040c00ea035801c1c0d80c0c1d40d1f02044000f881c4214020003000d0600c144000604d03420544c4080800740300c0c81008946908840d605900b95040d95080c5030310042c001003d030035440c841d00b8145000b84442da0041c080c6501d00000c241c01841340c6070924200c961207160403101c1e03807500c181144000070314420400c4a00500040f080744102c0a04030030540200c50303000310754804814000c1d82c04451104210224ac0f00040181100038030300e00070b860540c0c5a11040400100c641031154000850180f00505900b07514150020070068009044c40d00388244c0d61280900c60740e101c820f842e1443d5141c100082e444940c2d0416004c0c640d81603058681c144581d1021449210074070f40c102d0101c02c00130b0112010601c1031401c060b202c0c0a003408807a044074140c4680c1001d2028419082800c64140c10414030650300d65001c590544808c44080d1034240343e9203001c0041042e00a001020a4403484030b030f1001e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 277364379 1250 277363129 277363139
    0x5180f0a0302061812070801180f02010f110a030509130b15070201030b030304090225050a0308090a060c09081603050303040b040c0b03070f1710180213090b01231e041e030b10 77
    0x10051480200be41080783c1502c07204061b500603001d0f004500c01c5803080310301014483c50000c0455203e105458020840300721072071030074400f0b8042e090405074024080c10022040310000d8070141c0007c1d006030304050b1101400070207601c040c8000c00140c410414003503981c5001c070b610206071401d1404d5051803543c13002003650110745c01140500326942d0519103d906038075210b0b0242d01c0c000071144060122440c200c0c60503002d681010340481190500010703140780407079520000d03150181d10300c00540103400070400640007446440006038810320500d0b1040300340340c58000005c0190021194000400d580d04050f11246812940c1c0b43c4110301003d200d032541d40380240d403501c00303c0302e00d12846a01503544030a0401e4540d05405507080e80c55181085002a95207102c01405800550b241c1070110360961482c119802040340001400c0f040f00c10114900340e08001540000d1905241303086c940f0350244404600c004001000719603c0c2060840c01c3d04081c11810010140100501600a00301100e407040103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 277365629 1250 277364379 277364393
    0x4171e0a080304151b0e010c08040b130803040612060b0403050c15190c1a070c12030b10030504060608061608041a040305180f0a030206181207080118 66
    0x901980c4000c0700c6031243c6651030003401c109180c81c050900a810301451550600340c11041c42d280d4100382ea51000003403210801950b940760a140301801e50241080f040c0503490720540104840600407542441199403203a82c603085402a81200d80041d1041659850400003402048082e040c0030481c0c5241900c0d65075070503a1004070305081030207540e00002013145000c0543c19111107050040c005150301c4402a0000d01c001c01c1c0400840c1c114110f406007102c0d07248800c034018440d442035155504040102d494500c07170079849011000825490302c00c0c1c5e5880743c82e038050705100c280711501c011840c4d081c9850300038291045a00180800d0b40400308001c3d4100c0d5405481c90009014100408241c850381001d1034846404200300600b54082d8050008040e4014003c1030740c2506070821b028850407a0040000101c0e501e0705c11540091a03000500251610034010004806c0801c5d03c82c1040104001046160791b40d00c4500d07002d0381003040c042100010a01600140c1c910605070b8046d21421555441c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 277366879 1250 277365629 277365643
    0xc1409040906090c08100e010209010c080f070c0b0306010e120d0c0203010212010b0712020601080601030204050711010e010c0908060402060304080c07030803100f140d060209011404171e 82
    0x34800d507181c20030941403000c2a030110f926650400002103c1980726810542d656800d034040344803083c54a0003c11030444188240c800383c400594484070740442d507403141c040075040203540319040f0008010110004248030300c00c0d030090021404180d103c2c40c14000140c442c3c19113458080c082d03401c441200402920100d40040032035042c0c00d0900202c484c6001107030090140c2c490034068040103c0000c1001041600541003c5204007448100200c20b50000c0362075038404e202d8141c55034440d00062005103010380001d0303489060713031504000315902407020900b55000c600c12500165074400b41e228540b98403446800181815400410300d07401c06034049195032200601c064076000e004a14480c80034020702c0104002c40d00041c10b513449080600026a140c0f4591194048141c2c0050000540b1f480241010104510041031184100c0c1c5917181d280203503024204031410420880f412180042d0510040c01c06014500450070440201062461600c070300700000310301d0840082642c03c54800c000801d9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 277368129 1250 277366879 277366897
    0x6030f0c090c071b0519030b070e0105250c14060706020c0c0a0f050f0d230c030f0709180c0308070c052e080603070306110c0610090c14 60
    0x10007180da42c2d4180c404039401000c0c40104655503000ca040d030f19904c2d0a4910003580c90844002c144840100c0092103510124407006052008140003d16280c0c0501001911101d0605001e460040030700c0e01d48024010903040d41400c20300c3e002c0c02000317200c1d10041d50b80c013410f000c2c440841250070b4940000c00e81d0140c1c0000501382030300040d40c41ca0741602440825149080981520080794459031800340000e80e60061a010381d016040303a170424540005001e035500d0708812410400f820320800c1d150308030032841240103148100c019004c610385003000068036040b00b040181c4051424640080250340b814406203c2ea8014540c003d40451900303c001001c6992000100f603441c1940e1410715548015607001d50352014507141c6c0c0b81c8800f1144162107d0915225481807020000c44030300f520384050543d0401d4050340020301c14400222039500464102850f840300d5420403000e030540c0c6c2d01e01102180c8070307000054404410000302140b4058000ca102c190b0403c4180c5d031034480c82502d41c0380038001e84 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 277369379 1250 277368129 277368139
    0x8070201020c190501110c0601031101020c100305060d0b01090903031b0207050d0501060504050709060807090e150105090402130812030c0328090c06021e0d03020c15010608070806030f0c 82
    0x40701000b000350310101d03104220301e06c00e80c5c6580c802c5c08510345600c800d20083d600201007440b05000ea61000c41e00502130040184400400c240150b8110001c11f001002385802408119810b004564003122150080a44400104070170145103001400d441249446043c04000d00350420219500441c040c003c1d03c2041ea0944038903042c41c20103038050f00680d0300864000e4034082c14080c58079032203481c1d1401c1c0c0703650f80c8a440c0c02c0c1e280c1d520101c40c080064800c405045002c1c5000c512229043d00c981045182c0500d006401c00c4000380004040340d02c0560341103900b00c0b0740c0f0f00400a400062220048102c2041e8055013940740500642d4501d02c001410f41c504881c00462036914011110754012203202c5090b820040da450350b00e0a5034140c00f15005000251082d840c0320140104506116041012000701900c070b51003480c0780a0b0042d41109803103520a010ba07604004102e80f500d08940d000700b02c40d66656405003010180a00000c030701410490003500304c4038001c0c0e00c9100000d2249400c10040e55 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 277370629 1250 277369379 277369423
    0x30a020a090b0d0f030504050a060819020d02040305120706180803040f0f1505071107081906060e090106090c0e100810090f0605030606030109020d080306040f060b0a08070201020c 79
    0x400a01d40c50f504240080c075000366440f084040c50341c8a80a0400d0b80d0003650821221611800c0644204004075120400d094004031034100070795154026028000584c180542403503100c0d6106814520502d000100c0c0c0c0002140110a220a0b400740b080700c0482c0c08094020302d40c95880e140c69601c00100090700000f4100c02120800007807001d0410103d8002290001c51054000c00c2009000152180c4000544500780700b2024000898880f045034840c200602071408489031240b0034001e503507803d40b2000e546020004032550402221071150300a040009401828800f5120486070012070345003c02c05113050b81e8019440c0d1110403440406503080034000c0346d0b03454007262454032003504600660313424000146da200000341c100300c0c00e0350000c80656000b0340d42c110600d822039451020180d03010f06201842c2c401302d10703010000c54000b00c0c042d101054120f82400e904042e642150320071071038017100096094500d0380c088501d98011300307284000d61908000c510401c0d0b0760030440043c40d1865040d40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 277371879 1250 277370629 277370651
    0x1e0306031c0806010f020c0622150f080a0908040314010f020a0c030206012c0a02070611030402090703140714070515010614041d060103140c090a05030a020a09 70
    0x4280c0c03129030a9401c921a00801c41c0400038184036043d10743c0c60102c0c1e003000314040700e175001268400100c40b001d860241000400800c20000300b04607096641945034070100850343d0140f0607022880c1c004035484050303d40c590118024100c6100401d0b01000d546041201400142480c04507400c680d000341c0203107006110815158010449280e0000b4440c1c400504017a4698105519071690b40c041d40039200ac40ea41d030070300c603072800510386400760903150340300c0144810a125905044e0081641c800050801000d0342d82d080441d0074030340c00483c04081c040304000842c036114001c258050268038091005031101c0a00002042000e4500c01c103009486d02e4481c8100707801c1080d00d940c240c1003130484000c07954a00e40b040c50070f0420b007c0c0d1800a403c1248640413042124200c40403038606c0c00e02c55024640701c2c910030101d0f20000d00041d04060301d0300240c1c441d5800542170700b030084801495180c3d89003105e0302013000780ca42a50109000381c10448042025a40316403080c02220b04100010800040035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 277373129 1250 277371879 277371883
    0x50702070e07210c050c160515030c0d091a0702070f06050a09090b010215010b0409110307020c040903140705010e0616090e06120604050a020f0a031e1b08160b1e030603 74
    0x510301b03110311441000d500d0501c02d07801240540841d001584c818a4141e02010160402e200c125244646901d080002101c0100e0590010710800c1c01481c04120503011500050307442c0d017084d00d00d280141d01480040c00200c0d49a01c803940240701c0da0070007600d09001c1c81d001a001041c24401d445c0201d0b83c0704005002640244810a840403200b02119041c0d0303112100980300350041d000f948d02d264908030320300040c02004030440703000f0200d0340c0007040700d54020010440500102481103003086002081e20b40e05422840180050034030440002c141001103078201403030420010032a00c0340480e0b8000c86144c158005c0d01400580c7c00007a580d190643d940000b00d1002808041100c1c51031083c07400b08010702102240e00884144225070660031221b812040041110070b0340000340811111031140c00c00c0903546003418440a204243c481c1c3d80c070112842240070003074541d106000d25084035070380038071800e0801c5460001c3c100b00c00c0c405050144400c1440b000c0d06413810390750003021002000c200e080c0e8007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 277374379 1250 277373129 277373137
    0x809120c011a010c0f110f1509040c021f02180607050303010e0f04020603220204020408010b01080105031c050f07120906030b03010c020d0c020d06050702070e07210c05 74
    0x4144446652812a00c54050003030000280c121040000001142503940c49000140d2101c3e400c80c0c4040d0103100c441d1a658418411380e089030b5803000c00444100ca00c0d441e01100c07507075882d20b200c10064941c00700c041070000341c0703034031119031021904241032a88076a02003003424400d0f0700c00500c005880360009011524202034594421740c0c08103002c14000700f0010000b00950507104031030b168040742e4891310050301101405580c002c2d0700c401c09000084400100c002d054800103621440c03400800310300d0b00414220303030007900800f00320394403118600c1142d60440010380c01031006900a002c2401140c1400051440000c20700d03040001c005045082203801000761024590050a0110094680d50002e00750701094422000441e09100c2246030342c0c501807044502aa045070050302c0103119500085406520b031322412640000407130030a07808151706228841c404c07030740340d002401d40b0313424040d040f01c80507001440c81040004801d2200e4034142c140360984c1c1c8c42c0e00290004107052005280035039039406 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 277375629 1250 277374379 277374403
    0x6061c02030705060c03030103050709091110021905070501020f0a05070614120703050a0f0b0108190905100903020f0a11060a0c051504021509010509060304240507090f150809 77
    0x1001302c3e030303515142408002141241c3c2b1070703411200000d079a070a01000341c035400000548881016040c00200d0308005a01c00b09034a480e205a80c00d034028403210310406078001205541c141c0c406202031089580401104c3c0d80055a5401004819243c0d50b500b0740e16469401114200320088070014240880001507a01403828603511001da40f500d260010001e013412110751415a0808058041c143c120b446071240486041e9943d00460761001d040c1000c001450710006105c0d6591811280408c000340440708800f000404003185003c0b03e13090003841e0000702c0700480100d030001400f4400140d1607004200c0300d04800e40c1ca0f07a0315628059012b0310a200740007070140940c000c45803c0c140143c04079010600c50383c4219114540041600702802146c000c2088440c08141c08004a0300c0310b18251303001e5607020703101c0c01800c0801a100103040c42e00d002102480d80d00c41351101d040c0850250800f0b10100500344120a030280e151034070259450b0b40741c8890055062016240224000710320502c40e20440342 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 277376879 1250 277375629 277375639
    0xc03020903030a030e07060c02031005190e03070219050604061214130201090902031b030405010f021c0506040b01052215021e07060801051e090f04110306061c02030705 74
    0x4810807001130003404142c09031009074000e414001c1020f40c002d49028041c2034018004051311581c90480c0401080060407051a440da2070f140c96a2007106030003056480e0140780060f54945500340f0620032820f01014014481c10311501c000e0280342c640c10709031421a10246480c0c2c060350118054100103200c1c8080a038450b8509004015050200c01400d01c030143c400c1ea40d206145543c0c1c0b5004040307003c155080505001c4000000b025442000c000c1d41c0c015009000000c0d00700c3c6208441d5007281e0243e101158020b0540c50080e2078010240700f020351000007036505014065808000070054421034002036501c00b03c041c2c0030b0315000f4818000390040c0c05010765410240b50041d4000c0d540d89400588503803600e01e0030fa11b10807011000b090300300c2110382c0d94171003240356403d000c02c0002084074840d00100c2128030b41032061140d070341d0100141c086c9030320441c0d01b0751741d05140c14940520580401e4540c00381d8040c0040c4191500c030031941804030705206019801041c4184002428401250712080d444 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 277378129 1250 277376879 277376887
    0x30f03021c06051206060108012c0106020c011202090603040204050703090606090605040e150c03071404060c020f0102030c1e07050607051501050108040c0501031a040f090b130c05040c0302090303 86
    0x4890700d078031140507144111407400c50945010440e41d070728901200c2080c001040c6030010003e082000100240080c030804e10189a1003501d402d544880c5000d074081001a0f101c0d074245111540c0140c84017186468400086d85080b6401020074800e22005c0c0c0000d008a036a4000180c1142c4294016455a5030025090000f80e540352100000342c16a07009240c45541b408000680c0208002100c43c402800340b8860aa69a0f0707080340c42510341c100178a41c1c824404844a24000c02c160b41d001080a0075907034944201001250040c4880758402440007030541d40100310119403034000207403030400d440d484040442c031032160300e01e06030400055a0000f0713008080464102c1c10010b01280c07000315045111240a0260384c5c5800440740120300351805880f4a517031034028015035200f40c04c080002c01c4210304586444240c0d00106040383c1400c0010300345240d40e0000a410006240034590f08100f030344078203020162064881142c8098640309880c0306650b141ca00c81e10086c004e0701034a01c0d030b180003020340703440d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 277379379 1250 277378129 277378177
    0xb0d02190e03070b210406150e01080d0512150307090e030d0b040606051e04050d0b06040507020304230a120f0c090504030c02010c020409021c1506060c030f0302 71
    0x2070641d060080070b202e8058020081855090f103c240d030303400251014182c031042d00b0302d643d03070340c11000c060001d5a013580c480002062486c200003140008040420940000d503250080c1c0c60309082900d080081003050410032501c000f604080343d01d40000310003100c0b404004450700043e28045250307001e0442c42d42090444104030754040040c00d54408081030034400305030b41c0340801040321406d0007030b80081102804000603100c0d14491843c5843c000c0c501107440d2544482c00941c0101c10040101c0380820418108821401c1501855400040e140001d5003014105008500000c0d000ba0042711206c2d01d81c0311002d60b070340e100c1824500030600e003c0300c0c0f04520350b0303070801092000c1580004c0c1d942003803200000a00900c01e11a040c0b01d580c15a4418584059543c01196000c580f4031041e40d02a4a030f268000140e035403c1081c0800003090347c00140000140c1c0f4107880c019011041608480d49040ca0401c070f0300c1d0700719126954169041c60900a5047d140fa0140d009000f560300c0d0320310417010039002802c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 277380629 1250 277379379 277379387
    0x40213181b06030e0106050303031f090504060203090d080426040b0a0c050d0801180203060d02030d08060f030f121c0c091a0a140901121104050103060509100b0d0219 73
    0x5403450b40da0f09212800300c04020b83e090703840e2880303810342541c8108001103400034202c1c040705010200fa4400300043c2c0e0359002c00420b840c0103450a5030515400800c1c01900c880c10007040000040742e0406030010b150070707103801c05162300302801228512404045000380000c11001c5501038188001714507140c0180c03060051942d6140081100c552051079002e03400305008000b000d0480e01209020001c01c4004030001010b03400c0030300001c0d00241501e04000c01a03030709015850f000b400136980c0001c1e41c641001001141c0a10303540c031901981016480c2e00c0301c0e20010a0040c01580070400e202e070b980d40210305201c1e0128807442d022469910f0504440c1180394800b00850881d560001c0e054802d800b4010600418852100800d0100340220940c008480707444000e8030b004401410a8043d1303840c841c415400382c1e404400c0172030781c41d040001d0510041d80c05108640107048162140529443c000f0000e0820342c105020380da01c421004584003941968030b404542e9440056032408410255403400a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 277381879 1250 277380629 277380683
    0x3051f09090b070504080c0d03030605061821061305160303081603020412150f090f0c060509012007120302061b0c030706050c040306020423010804021318 68
    0x55030064004080fa06851065041d507040d0303010b01002d000001605020400c000380c001c84100d003819154180000d4581d200d2000c0c0a44021071003015201c605144200440d03492940d0854401c200340031450b9148000010f0302507172002982e40745074160421410840d02e01090011243d4041e0405071010080580c400b1025001703d00c0b5400840c03044500e28000d8040c3d0103613005003140b40b0004ca0848010900da1b00c5039107075103060501c001860b4640e00140000740d0b44100383c20745519903c8082c940070000d982d045200104118501142440c400e5000248546501404440100000c61141120304070510004c1c5c001d02005540c0d6082c50020316002c3c2d2624030481e0090461a80c0300701c1341070a46051000c407181d1070f0441b00514500601540c44500818000d000001c15810621000c40000c0f040c0c8010000b03491108140840f861010502d408440101d080d0b160400c110b0500303010041c2c403100800701e04802001c0012a41c1500341c00c4c90301d8045444a0080d02e2210022003c070200c4242c46282c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 277383129 1250 277381879 277381883
    0x40f06051909030f080d1d070f0b120c0c01020c071403160b033106240303090e0919110a0503030403080d0c020f030c010b01170402030604020103051f0909 68
    0x2075104030040100588440040388000303000305004032103207000030315070000400e4606407403400000c0c0c0402060417500038094041e10503845a0190318180401031010900500508080c1d448030b01d0f03c2c0d1640548140b6400c044c0611a03446000b00741c180c0070b442d00703405403031082480d84200c0305519a10f1080010b5681c1c02615903000b4010500d42039104010700c21000f069a04410480b031840d00c1d00144040340d12094121180000007640d202d40d03200c0c4080e0114240ba5000c2c020209202803060000425010104a0b018000d0040c42080000a401c0f490060480710510024122651800000c41c01c000811050961400c0390101010400080300070900424806441148506856106143e920f1081d400080c04640e002d0084502c00401500640d50500d000c2c41036490f2590109240d51440d001411440f0b01c0b039450310840411968403a143c00d17030244141c21300c044181055004a1780360700d8060310203410980c0780d000007911040c869604c0b41c2c5014012110340701140c0e0341c00103d4020140d403082 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 277384379 1250 277383129 277383157
    0xa0b0a060609091515050c060906090607171515120901050a061d0901090507030303060e0c190806010e18040515060a150210060303120e01020f0909060402040f0605 72
    0x101003007103a62841021384501038214140002c40c20008000c0300178010503006000c00100b0000a200d8a409103d0b181c05541407100812090901d09091418020010321003000c018410342119481007054221680004442c2000b83c2c2402031f40c13000c12015000381c21480c2c4d0784040051000322001960391814480c020040080040d034a6400140c42030300c10300c0c841c01003030712041c2100c1c52942600641c21070304981d1001c00015100038550b00c0038200f20069109130b02181d40c540003008511042501d660b03210051200192800e881d42e00e201c80900b01480d40e0004210349900044c540d039010315100000f542c40200140c0b466606403011404c07203101110304032040d00a242122038060030420b0340c0c600400e4002c00c7c0c0d5500304c2c10304003603900c005000440b81c0114841d690307250b03c000d561845030030083d50190b0380b00d05032400c85141c21404c0c1c0e6148e0484000c942c1c81000700c0148900103201f607800c0142c04445501840c0c0710440020068051500444200c503050903000a200d078000c0004c004410100e08 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 277385629 1250 277384379 277384397
    0x109120c030e010e01022109040c121803141c021c060e040f14071203030f051005060f1e0d020309070b0f0a0804030c0501050103051e060903090108090a0b0a0606 71
    0x44400101c244c203c14050792184079600742c080000c05072002181500119541811002c1c0002401e07a40050340ba5400300702401000d04d4040028060f032848524076500940940c076a542d001003000143c0722507032800710340100d0098500705070020194548203513420195284c5000509407481c45000c00e54403454586040800188200074242c400c1c0b085400c030200c0210302c01c0e84d45543e00341400600700d00b1024003568101043c1d51000d8441c440c43c0900a50300094400d04200300b040466001a05500300360030b200c00100444ea40d881c085884004003218402d80310300d14034550a00c0340c0c0f00744000e4565050041090746a80c5a00c0e4082c501c980c01c0341c0115407581307541b4000c181d400c1c4030308045082c030004100840ca40d21405520090f07009442450020440b040e6900c0321400c442c002c1e00107c0c0c10380c0100d00b1208080030f0701000e80c00c0d00714140002d09101c0c2031400b0b581b07a883c8a4000080d040c03280381d00008103602028070140d400a500300c0e07010841b5140540e40740c1d0003000c0e14011800410a140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 277386879 1250 277385629 277385657
    0x51006030c020714040e10110910020c090a0b01020c12030307021204060c0206070206040315090210030c09090504080903060103050601051c020303030403032a03050f06030c03070608090109120c03 86
    0x43d49011183d220500d400304a12040070b11002e4205482032a18601c0703090490208101035118040b00c003001c4050a17500c2c4e0504c4000c00c290300384805000e13400c5500c0940c0c0f0311a00c1c1d80b190f003c0d6400102c000c0000881021401c0141d00344003000900d281d00410040d80240345a0011008510034419507081d610002030301e1000080030301550045600240b10070103100c006040000040c08150b000a0610f4182580c82d56003107142d5000030007012001d170300e999144c03086041c0544c4510b81d851013400d0074407800313001440003003245480b4456071400d04e88900120302840b100c0c1085030a84040a000e9804a40c0c51742042942d40c542886401c4c06080c12005210090101c444640c0c10b981c1d000b4080d52554440d43c070101c0180604281c10324140542c0c3e500744034910442410050003640780e4034041032a281043d12101d03001401441a8000e0300800e12528241d68003085140964203d27042540c80340d116000d205004004000c1b008100f8504000900b01140c0c00c00010503210744a03035100c41c0201290 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 277388129 1250 277386879 277386883
    0x1d0d0c05160326161208010806151c02040212010f06050403080d15080f071e14120f06180d031116060b10090e0f040507060302030601020a06051006030c02 68
    0x500c00586030f80000981d42502c4408141e003903c110714051102c50034803c1504800d4281d0121680072100781655007030100300e403a08400c0150040c400e61001c1c0229140010079000344c0304030024003600c2140300041c1a40b28490400c114100190007900841d21078503214a03160312a8001e000703040c46120403100000380940705e48210b0b000d49a2107010b841c2494a031150300c4001d00782140c5460000307142e2013404100c9110070401880010b000c5402000d006107030520032106052503d441c0e500501c110070007800640716a4003e070161607070680711010000204500203042a0b5075003a800b48501400050004040500c1010045104c400742500c0111080031030aa08940041c042c14817007002c00e1242044c00241e65120004050107000c011450307902c04d400040310750020105110114448100c14440d000780b200c00e181e40a4155988a07034036041070740729035540f15504c0c071500007016000030000e60664401d0003510b451035403000381804141060080f00340041d00d02c2c064000000c0c58000070420407480 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 277389379 1250 277388129 277388173
    0x80601090207030c0803070c170417120a0f0507140c27010614120c04090513030504230303030a0b0f0402041a0307030e06070206060a0603060308030a1d0d0c05 70
    0x410b854002c1e42200c40d903178000d0726420041c10a0107018035240c001c400309400095003206840046415079440703040c242131040750816420a907502da440383c030003420f10614030300c216125581c0d9401c001c040c40034101d804444c14403a0300801410b43c0c901c10b40e4508030306000650090b445d0700c221004402c04050205c01e00703c1101c1c1c0c80d078408181075030400401450b402501440b000602601300c1c64036045c0e414142080024086e50340f1703c07005a0005d4100b00d690858403645030000c20740c0c0c22070b01c00000b15490040450142e4064101e151854580c0d0359a040031032030300c0211020010303080e280c992411513484001414480e643d075015205003040805145458800c41f801e90312129034154580c840103100507c283c0004000c1c6003810750310040301c0507a800070450184a604c00b130f4000c00746031070a4001d0260030791541d0701c60801e150500c03009000054a61007525440102568001110b03014502c0300c10111100c010407007a10b02910189040c00c5034010180001f8a01480c1222025601500f0300884480 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 277390629 1250 277389379 277389383
    0x2100605010c08031f0b070b0f16210230100f060c020310150f0504060323120c031b0601030503040e10030204050c07020118050105030a0207061b0801080601090207 72
    0x1d000c02c0000e0024401410303008211704000401c0c00550740750400e044159102e480182d4644608004014101083c10481548015810554003130840401005801c280ca60b40b200c1d240c05418100324086200203034182c0c1c1404e00c0445102c002280d01618621800c0d5003030a1031503600c8503440c00a1a010040d061a40c03c6503412f00c1000c112a04d405e80840304509810300c100da0500400d000f80d107122100c3c2c00303142902c070a16900010340320300e0704503100712a03840c1d0f0303003c5da00a5090107010400b01c2d41500042d071300d0780e1400c844240d240c4400340c1040c1c04c1008030032200000c1d01d030100382002029000005880c1c509115003600d1f000340c1d000504995103481c24800109280c0c000c010034000199220364650300a0261100925115141e60000341a140c0031140c90045090100d111001c1d903a1103642c0c0c1d14408100c0020088084c10200020007901c002040c03440681d0300010517008000039030784185820020102030b200c500f501090300411034a42032082140701e00c07424001140584080c801c41e1103442d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 277391879 1250 277390629 277390643
    0x30603020f0103021305150a020d110607030902060915041a190507020a171f0b0306040b072304030501061a18040b030307050f01060807210501061502100605010c 71
    0x4400704004401035882900109031344014040e00040c80c1e22128402c401a50441c1e84440e2260345280c030007450f00d4180d000010030400c000400030b08a030404504207401c000fa81c079010442c8079190020404a110b48280302c0c2e04112040a6080c0c102a000042e00c1582c070140e20101014043c444010424010f0380d192035041c0000e420791103031140c019002000c0c014409009025034503903c1d40c84500c429055031b240304064000150100403a0060843c001d01510200c504004210b8070350080b980e20100104000d143d0b0a40c00040740020303002d034030341d9504980c2d45801c00100500401c124200798100f407100711015820032070023080c10071325044003540d0740c44003080d0103040c0b0307080e8040e0b03000c2d41020841c2075800541d22004440c0585044c00249806070142c0700400725070b4600c9a000e0300b11000b50f80060150b400800b000d101d410080301060040c01030910301d50401d0380a03401c0c80c9005210780e601004050400c2c0c44e900500c6c4d5000708401c1411265402c2c00c005495039000151001c0d80d515800074240 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 277393129 1250 277391879 277391899
    0x201050d02090d1208060f012f030f07060e0d210506010909060b1c06120201030207060b09090d02060a0507051c06080d0e1306080a020607060e150108010c03060302 72
    0x46100354054001000b00a00001e002e1001c0c1e2a03107504440c00500a00001d9881820480541030010884040c4102031030000b00b0001c0341c184c0c0740d421050703d0044042e580d10001000240d850104251181007500c04802591780c442854203400600007044a0160b5024000c0c00b001518020000c021314078402c4041001c081c1d88119828000300303070041409060024034000800c440c861442070780c02401c1c80408085d542c1c0000783d6030928030074804824101040c24180140024400e00350320402490742800c01680f90006e41c81c040d40681a150011600700000504102c2d8105000500c00c40300b1032680c0031b0304e015031902d04405090f180200d620a021a43c00c0220500d070103101c6003105d00841451000044641c0c58602071410b20340003c14060010b44036196a000c1d0707151588103080c0710150100c04200d00b0b490007450503190300b04070748080d00c141d0020449030207020058104084e141e50b041c041d03e40400500860182e19442070164504c03542c4cc0c403010102e031034040d200d4002500d400800c900c0807 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 277394379 1250 277393129 277393147
    0x10050109020a110321101509140d03051611040f1b030203060a060809011b0201020c0705030307020d0321050a0c030b030c090f070504090e010b030132060d0b0906010510020a020105 79
    0x2501d80a0180002c1040c00342002903141810008070036103c40d20f660700f1540c01e14007000789d04100340d09090240f0031010307800d4600c0000c1e0403004990820390b844251040002c02400d01d8040d1310302a420b002c2d0000d00303045007401405002d9014000c904c101c624031814100280c04214200c0c0011144250032518202d4140b20250050005039404602c990004c41c5403a514004c0e90100d615245002d0090307034021860746c84400e028032401c80500b80680046042c200d00350001043d503c0800c10180a026030350069601c0700048142d081a2101d45801c01d12550602800010061089101c00c200080c40c0104110300c52401045a07010003000500a40060f00c0311424a54500341c042c10709410702004010016654255025240b51400090000110341c0043e009048c25150701e20754440c1c02c54034a45450070041320481106511b240d248450800550380c03000815500803508038042c00c030110361810032007c0e6400280b824161030b41a80e040c2211803044105a03562110307000002e010600a000040e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 277395629 1250 277394379 277394437
    0x20d11070e13080703020c030f1605100521190209060910030b0d150501080303010f06030905010204051503040c090c050d2f07031116060e0310050109020a1103 70
    0x34102c11510000000340b5102da4904045912404003200960083c450400d00c600d411701c60540c080d801c0341e0213080241c1c41e542070003044440c14003a2510400c0c0b1140d807060410301c030300306a440104020702c0c02001242c40c040340c211004003c80f082008041c2c1d54188072407081c070f07900a59043e1a800741001e82481a030900300090400e0001e0344404250740c2e02c0c00074040d0b80d104507241c1c1486008625003c000e1201140c02010350350141c0002045a00c100010030240203c108500102c1d03040d45030019521486180c9140640f00e941e1226911100e490303031000e00c0040180045005911a0740d035050f103180d994420324244c0710304003000004244140074038010184140c00004214400344042c408408211521a40003020710703200c0d0700d0085010a81d01c0415030041045e071305025001c0700074020102492480501c0c0c443c180128801c001019881241a0710200b14410704089190414449581c46001c0e01c0000d40012401b440060b01e180004040043c002c03003204d0100560040400400c411503103665 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 277396879 1250 277395629 277395631
    0x809010f11061305010b0a080703030809030708030f071e050301050402090406030807050c0910050f04022508090418080301031716060c0306060503090d0f090f03060c020d11070e 78
    0x48140a0801c0e05411103000c14090a8400c2002201010301a895820924211110450300b0760149011100a210041e0005280c00407243d01d440c004c20386542e00c250340380c1107000e861401010448003200340a81d420300b2203082489882d4a586035074100c031200340f030820703400e01c02c007400c4000c01c0082006004d5030410740c004140600010300003080c050fa0380e40d2525200d6011610641d5160001c6200400614140c5d0250b504000c14500142040741020300042100010b9901c0e9446680e0001d41e4004031400d5007075040150004030102100c80c511801c008030154091803001d40320354503001d10f01000190b2440c500c1102d40e0480511170550b82940d4805003c4203c4c031400018180017440084c42c1a040c03200c0315100709118034400310b00c820b01441c01805643c43e82d00b008080c40014000c1090a03440095689503102c401c1c44c01401220064605491000c1d441c3c10180200510b078101005005003a00840c45070000c603400c813110400341c0380040b04d4403107181007074140c1d5400c030003020406066040d40072 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 277398129 1250 277396879 277396907
    0x14040e0c310b010e041401290705030a20030a0c0c080f0c0111190609030e090703091e0201020c040b15070311060705070f0b1f3305040306051306020a09090b010507080901 75
    0xc441186266107010049e42092000312a0fa40c0300003907200e4110b41c01001070020007641d905400f03400710240c2d4031580b00c2c020015907500700641000c0100500044030941d0008045960503520014018003401d9240d014500c02c85002c140c440068200c20407001510b03066000015490b41c3c2c0001083d030b29030780640740701030f000e070704110302050390080540c2c60703803425030094840d5140000c0c022000d140000c005030100c92081c1c0e5961621400c2c20151b40c0100b40300c0410002110005024902280010040038840007500d0725040c0105401040640251094a060501d00b08035a01a600d80f04122058881c42000401c5421201c2140d0f00080c4600001d80d0088080c011844405200e4026101051055071042e40103100001000a0030341c0c1c21011000d40b0090341c40c0041c900a03508801801e1032241e44001420f00c1d1baa80c000501d100c420130380e94a60580d10200541d40c5181584004241e01c546001c0c014059180420a14035580a48110b4003c6a8040c442c00d0607e041c103001580d61426413452 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 277399379 1250 277398129 277398179
    0x210e030712150f020307140c300a110d02030f0906090d0b1f1202010e09040512031509062b06060512060402100206070915030b1914040e0c310b010e041401 68
    0x2420022740500000b8102085c141d590718031071b0301e46001c10341d0b00d040c03c504034510a64204002e4131000d14240c2d0115176001005440c0596910801c40219030101d603500409003c3c800d580080c09544008070821200c0403403005000c40040f5140c0140d0000500400c02c002d01060310706421f4845410700c824035075401800380003914400f1a41c410f1080041c0e108880040740c410f0080305100c05440d1000c81c0030f03041a0291105400e110309240c01c51044800040e0491042407801100020041c25802c60300103810050620042040c900070102d1703440030155001c9119410305034030309514604c001241441502140d580e101d80b07514002248004620400001e0201070320b9410410443c0c9848000400c10025050000c3c940c0b403420401524103c20101032500c514142032910704e22003000030701041518011150666050310f203c0b00300321100184035051080010b40b901d52110540c081c3c4c0014941042a00c030200205a01c030104421601d06d440c00f07034001d00b07407400180003140000300c64070022198084 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 277400629 1250 277399379 277399453
    0x7030e0a0c06020706092715080a290912070218090703060f020403030918021b071503180f08040b07210e030712150f020307140c 57
    0x1c5025125209400c0800540d1140b00c0405c4400d500500090083c4030118071155040c50002c03a00050700d03001c1000300902c64a8020840d80f241034060800001d0000a00300c40300d513803241c40d006030444921107080180103c100400c800000305941d100388201e2006003c1c00d508522188400c007503401c202410303a04204003249203c00c842c40d202000c1c0c0550789400050031554035620b440c005440081070074040c0c00e801071104100081d00300d403440e025941c091143c042641c204004c02070090144207c009161506030040d0354040760b011840300103840ea86503c2400741c058841056007980d4003201c00c1d1340d5454144002078045840307880304070505482150060700d03069071000103203603a8100d1182030781e440e841c9140b01e03a844040c0c0310030401329407030f9401c003200e00c1c02c0c0c00c200190f16200d65100b44030303c00e60b070081d05504104803c01c6403004601070020801a401ca880c0d001d078003d4100b00c0d200300100d901c0f240c1d10180340c2801010b58000b58500e10007010072000e0030715285034074250050001c1e03810304580 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 277401879 1250 277400629 277400633
    0x509030303010e1506031e01060e130f2013050a1a09031516091212050a020a05010c0e03160f060f031508060912030f1303110a0b010f0b1207030e0a 65
    0x1710055000b001052204070b806040108640792201040e44040f041c041c51003444031407510703460080e03451190600400101c1203442c90b241b6028009500c0307660106840311142540c0d4800d4800078111000b444806c810401b43c5a9007440303426003240c0200001d110003411a040c038002c05000510381814003400380d98010f10032810704107001c0401d6a10098042041503803050700769210007580d0007054914101008400181c5411607a24242a40c1c00c007004400243d11140354000c102d110310503503009000300310b15541100028080f0000380d03004d610a0003081c1e2112000c118000012003506c04284483c0712040c548103041e43d60820301c51040c1c082c5920742078140c01c0301a4114000d80204040b00c0038049515150440c1401c01e01101c8070170244000174424408c000352031702e03003244c4d105091504a0b80c0ca0381060500707440722802c7c0c0784828000d104081e4641c00b004203684545040301c04c0e001070b26054649410403401d2901914186113171005030400003804403403094210922000c1140b00b90341028541d6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 277403129 1250 277401879 277401889
    0x903101802090c0301090c05040302090403050a1407050d0306090b01020715090f080a030e03061911070219081009050309040b120f010915090b13050f030a0801090b010509030303010e15 81
    0xc80700f03c1e480b14004001001b820f1818028076180c170405241140c54982550b0008603d0360014001508109001c2016401d2900810301ba1901881c10441d00b0b481e101e2500d015070b9940006100900002c1c1000d100250b2603240740554814a04140c01400d0b007141410040060681200343c90010000341d1500041c00091030a9a540038048100c0500010001410003a10003400d061105000b9400a02005045445840007800c0720810303c001059a1010400090240c003962502a5020081800d040c28451602d807100080310400301c00d4400d0840380e100b070003044030098440a00650420001c0c1c1c501840c141d4000c0c90701d440300a001059400801c03018a1805000c0e03080110140e40d03d4140e0000d00000b0a01da004a00c060003050112001e5541c841c2c0c403600c0c01602c001c0d0011000384048081050a00070f0348414071101044984032203e00310000c2c903020080c8200c001240c039000035460154803c0c01204e803041d10190043d46075901c1c0c6400c00c00300307030b000400320000303804000a50546a41e403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 277404379 1250 277403129 277403131
    0x20c10020703020405010e07090311061e09040605060a120203090703060606050a030f0510090b1f030b0a080f060708100801110a122a0306050d0308100902090310180209 74
    0x1290300400501e811441803008503031041e007021801c44614000c01044640c0140c810050b2540440220301c03480d5640042005406140c000c1100002c221060a03050a51100070b050040c030200e60a0024582e80d1041c45260310940c000301c400100040d0480310f0b203e00c41d030000d50b0803c0011046030401070766904e480046803c0d5420003030004000044a9203401d5060150601d078010100301000541031641100e20b50145600c20802025103403007004185986607840c0901d80d100a566061940341c0051009001302580020244141c41144000c0b628400006d5400110f606541c024107054a90003030580740611700074a0311140c1d509269001c00d01200a0041c070000740031500d81b00303403100310380000900401c074800d03180a05a4581760703184450060105a50000c1d503002291204194100c0c14102e0140009410198011000741220000c055215400a10170000726175113400141d01c880500040c0d200d80200140d00d03074040300c05d6000104165101d140c500f803841e032203200a40403683c049298a01c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 277405629 1250 277404379 277404409
    0x6081b01090e07020d09091b03180b090c011202131202030a0807030905090705091e01091211041103091209040e010c08180723030f0a0f03020114060d030f020c 70
    0x21703000600145401605000250280040512031902c800c1c0301c0800010951000030f0030981c5072128a941248605404a8115004040a01c2c40e03c1c12245095980000c410541d000076824a4004090505032098404004041480d9040d4524000d001008a6081c1000f030f42d26010700890b031000214480000d241c03191190312001e10a620344002c11462040c010700d402d0078044100304280c0d09641d500d0074118881c00c07403022001d2310000c120040311900429004801c040b41b801050f2301c14081d215075400648007045a05020000f0f40c545030344107501090324000b9103136010ba1006400884a400680041c6001400000e80c4988111049081d541005000c2c00412601e10030300251080e4400481c4503000d1480060070043d00d400100102c00795502105450740c0740320700940240fa9028445d05814402070b000316200c1034450f040050724410070200881c007546c0b03403084140d0011820b00c06244114401070212522003015282a1645480503030341d101140540c4100d84000d035608140049465 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 277406879 1250 277405629 277405633
    0x90b0d0f0e031b060c120708070306050a060806090106031b0503070c0b0708040309050321090604030b1609140906100201090b100330140903060411040b0406081b01090e0702 76
    0x101d62100390a050000c017518400900004100a00c0500c0c00721b107542c0d4001550f490509050742c1e603094214000d00e000e8000c00c0d44508900710004040c3c0d4001c4080340101000c5070f91649590340e509042d82129026040000544201c40348142140c2c0500040c0d584040b00d07082c48002ea940b80d66850401e408212040d0303000c508190148428154000e000c0c4000d80400e0300280f024000c5454003101a002c110003055400c10300040d0030403107071982d0781075800440d80606940c03803e042c001d9a0710581078001c01040b0024071420030002d2440c0325040c42c08940180940800202d40315002800f00e0b07440080b90f0300003036640f00c0c281040010002000c0340d00c0b461051012299a03821482c08040c0c030340c060074000640102258a44144680394510b600071484d072030a00d012089040794401c440e50151020442d414060441044203002600680c8901424111010003040510800304070454409004021079640500c041c50000c020710020381641d0401414028200c944d540c4c0e40844510089a402c0016 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 277408129 1250 277406879 277406917
    0x70303061d070e01110c04180203120901081e0a09030e0d0809040b03030304050d05090109170a111e01030b04020d06090c0e1f03150905091c090b0d0f0e03 68
    0x80e5900010006400c4424603203e034101704582601541c075101c003c0028402d42d940d112000100800544801c1540d0380a41a281d0f84406103400b04d07200e40080c0341003800b00b181c2d100010300e00252440c80326003d41d41070f9030400c41512050540b03001040440e2048040c440c410028044580d200244402c42038415114203546880e20f10a1000b03682c038846226020754002c0c8140000500c02140d082e6404a00c5e1500fa0789458045004032280445603120414a5a8610b0600b03a040c0380400e012440500400032006108210020301c010900c2030030b007070250b000300f0a400d15060740c8250486d9045881c010409400c1c01e1014070008120f40056101d0103407203a54640c0382a403079400890070129003000301c4801042e054800500541004400300e080f0415685000b0104900415550750000c1e0100c000304100c14a40020034540c0e541d8140c5100b00c0d0b00b100410400b001e1480382060909441040441e2400c3c283e043c003a003000382c01482800d08100362140e188414080e010805044181c1a140c0d02082e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 277409379 1250 277408129 277408141
    0x121509061e11120103080903150108070e06010c03020c09072c04050a0203090a06090204090f081b03090d03030207060e2506050f03060d03111f0b0f030a08070303061d 73
    0x102c0311000d409030740002083c40050f020b10034400308141160f4011403800d5407030032407a002038100100180307550712401c1800f001044c402d000260f50415501e146080c43d0b1a5102d500c0156540a07000b040200107a208504105c0fa40c1441150160002c1007420600c9034084d6040b040c601c050b081600101410100c2014580940746c140203883d08840c0d000411480c40c1806a0f650f030702e520781901c001d4540e0b40c40b45c0c100c20454846510844116401c0001e901d171005440c909050300b80d00c00d1482d11015510362003c00d82c07000002c400c580045100170319150003468950340640107900402426580320703942e041d18200000d0140f1504c2080301d400b1840d4149103807001050a1680540d41001e400c1207000d2010540809075034003200c1e00200d089803000711300c510519089400c0383c0c0e03180303000329140580c0001704813484048014400310070f0b03054024002d0415003410f001c4c00718a44085564182e02411031903020031402c000810f03440c0d001c0c0c900401c440c1c2d125800c81503100c3c5001151083e031030f05103042080c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 277410629 1250 277409379 277409381
    0x605011d0a0b0a0303180e0406050103150506010801120501020409060602010b100c0302071230030b030105060306010909080f0c03090a05010302090a23031e16121509061e 75
    0x58400c003603050070060b81c80b000c40803030034810903800000c0600154004900072a003401720001c005000c034545002d1945814544800500700a200c115094a01d00380c4503100085d8a0080c00e1081906079207068003680b07081429800c0c01041d01c401d450710b550030080400d418815002d03120181019400125620200f031060101c0550300842980420000302c005000007903020034640111030000d400584941100d0401403598602c45a41140c510302540c00390b441c000449400d4000030405850802c903d06040c0c06040c00c1c1c42c012038031998960440001404143c000d03501421800e400b46003518285182c61001e00190382c081040c10100e58404603ca440d1031902c5030a02300500001c0c6402e44c108800e14001c04d0089580d80680071240540c1c3d1140410591840070700700110000500711101c85c0c14003400400102c4a0001d80700e000e000c2c1c00c02e100005030540c62404102c81030b07504424104491500e0b4651440424030300154911b403101e0311a40450080e000c1c0c1d0f01100b000c510043d03104903041400384 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 277411879 1250 277410629 277410631
    0x6050a0e04030f0305040c05090a1a0f03100c0219050c1e01120b0613030602031006020105040b040605060d0b0c282307020603040b222d0605011d 64
    0x34211900c004100000f540180e610b01620500c0c14045800c0d155850301c00c0b00703a0465000160000340d110100010400d40703800861107a800100b1030035440101005114003540e903000000d8060f40b0228004051040d2540003074a6400140305846025200c41040d01105d07010160070b0340d181d44030319a90303a0740f4908400ea00b40c0c0041e00e0030116010507003040028003544281c0c0c0c2c00c00440e80d40d81c40082043c0d1200300440d02c00c4281008803852064603441c2c603000a4209450000441400c00320108002d4014820740340210b401081801595559035601c60283c8002050660040068031080001941303e60403140108890301b07502c0c0c0c55000c250815242c5000780443c1d84100945030a04a1079a80c02c00d0751a01000c503003075a0310907011460485200f140c410403070b0094004000008010a0148880303049000c1e100034610f61101098007081042c01e90011100074051143c0c1d5134a13031810014441404942420803511010440e01070389a10084908c2680034841842c0010366000640b06c01185407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 277413129 1250 277411879 277411889
    0xb070b060603130b0703060e010f091107020a0b0f0c070b0a030e060c160519061b021218030f010f0b040606050c03190516110109090b0d1707020d0606050a 68
    0x9421450150f900d200c825141070b002400030700b0f50388042004180310f0f0b0020f074064031444181455550395003400b040c0a8105214045080e4544082220414101000c032960729400a1504080504003000010203510500d6119141c150820a8800c3d190090101f00e009040c14002c0c0750f21420f01c914003405940b807480b81c1120a4002d81d040190580618040d6203841d0f1283c9101c0302000c06920b000c03807800e40d5542c0401007000b00840500100040c0c0e811245030300c1d000442921020803941c2d0260381d680e07064040d41910450900c0700c900107070a1014503905a010045c2114564801103140780d0071101c0c0141280c2c0540d403205199100d0f0304090053f034000309114540f940c50701801c0b004181d00c03405600304540107034035074060111030075118400f07490034a95400801050400079250022008074940c0c0c215000c5803a2150000d500c4240e48074800100c00060822485a4100c1da2100c080c144095003c1107a01414070100d400358847c0d200020740da030301c1001d001440a00b0001000101d680503404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 277414379 1250 277413129 277413139
    0x19090f0b01050607020d03050f0c1902030d08010f05040c12090f06150b030a020705160b0409060e04050c1003061d0f0a0b031005190c02030d0b010201270602040e010b070b06 76
    0x142c4e0040e12114440114950545070054503481c032000060060300c2840d0408003a403148802c002c3c040f00c00451840e0009108600325020101500340070740d10303e03201344501121040701c402c00700f00c5802c0a80210000e00301034640b10038100d01e9078501a0071103003c403d0560f00208090009010032070035100c0c2041030034042d003048840514000c00903489100040200b15296008200e5508010f410440005200040b8524041c050b488038042c001c1900184241282d050403d040050f003142d0000f8914000c64101d4083c120741003071720040c0701001b0440b0b080507042640d03694000944510302c3c501704001407680e9924009a0408452107501036001800c24140a40b4211400c0c5032030f98000340b4519038010b0620081655035070342d0340c07031703400d42082060b02601c07070f4103054000404503804402084940c04078982001003051010049003210080142c40101500144901076040914500710340e4040c802d0030050300c1e041e200c44102080420a91000095441c041100f40c01c218007410750035404031003910 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 277415629 1250 277414379 277414387
    0x60b010302090a09021605190302060609010506040b0a11013206010804020907210501090e0d081902070f0605041203020f03070e182a0315040519090f0b010506 70
    0x2000a2012803584a204c0109034006541482c0c3c552140103c0042d60b000780640702400240c42c010ba02844003003404900500aa4002880a01c1e142c800d041c11703500e01400060515050400c004142d9010010b00410300c107003034440b00d01081003400303020701023680d500c5608030982d42c0740900f1606404184030303010000d405400700259079903c00c1803da4032940440d451440c58031744041c10758686031440c0e415403078485001503126000056800c194101c800da40c10400040008128980d103484500c0d0000000030001030104800066202c000c920440503100010719051181d55800d5541544c08011250151100200014881000050082c06145050a6180241c8500080c040c0c0c44000c00743c2b020700048004406054031703000c00300d11084c40290020b01c440e090032113403440c40d0000401c4010710056140491074250442400f0780e0b005503071100c840d400c110602000c12024000c010140003000c0b41d580d454203c2e848a40c0603078038030140104160300d10391840d4100030701901016045a030081d10100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 277416879 1250 277415629 277415647
    0x220606020f010e010509030901050715090c030c0806072c03030c061005030610030f150f0608060106030e07050f0102032701030b040b2d040905031b300f0412060b010302 74
    0x720403252390034024601159291010324203548100c0c0841d011041d494903041d804010440842e0509094a00906c100043c46a0307070b000c2c2c156204411621140051480300c0a80c05407001c020390040290b503000600d0004075802e101080ca9901f040100c10f802e503100340d00f4809416a0110104043c0205801500c85032034110b81c2c58201100500c00102005245401c11051119200b034400c104000c2820511015188a0030300010345164040e400a9014101c000540a4060f10981c40101c5941001d042d02c2032402007003001040680ca541819404200306101c07003503070440040403c1c5660010795815801802c00010102c038100e00d54140503910b41203000c0002d9440f10141d00703680d607119298035030300f4140f2030041059402099269802c40d041821101c2080b10100c0a805a200c5c010b550340296000c1c609070995821000309000c001940c4400c0d06031800034180c4101c41101c1f07240d40c446141000c001c1030029260300039880b0349400941c0051900400c5054020f64040400034641581000616 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 277418129 1250 277416879 277416883
    0x9090c100302091e090711030f0703020c0405010506090a1701060b120f070c0f0b060a08030406050c010b04090807260316020f06040314130b041202150f09220606020f010e010509 78
    0x500030001f8071540028a0800403001c1044414940c0c80440007501e440c61445d02035561907099001034031680c240070010402e810b2a100351040544000d001419803840c1010f002000c030351407840b0f4070042d5241e11003c9180001312004141d00c1101c641e600c082031500710a2680b1404000d0260820846582240d9000c01d101042095546401c00c1410007151143d00010384d845078254003040ea140008640096000e40207405012520071480080c082c801b008401c01c01101c1c2100401801d0b10300a01500e00440c48462400903850b008104d0286485000080650303c2d030400c5900d41c100000140004024135070521070000c42c40a20300051070b90381490b030350290040401d02a080d190040220300603001490250440b0000c00a0100031540c0741c0d190003901c3c0d2411030031001603024034004402c9140000c041000c0b45c410071017502400d8200001482002280407803851400e01c1e11407036032030101100582d442828020b01082d0014050952040240d900b912410141404640d2400741084501100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 277419379 1250 277418129 277418131
    0x3080702120c150a020f06010906060f08130b13080301090605180403021e03090d0813080d0909110714060601030b03010c0905090a0213082b0203070209090c100302091e09 75
    0x201c0e000f103644980f01081c04900e00b6884040c844058890b540000900b81c07405c4d07201d4400c1d40e48a43c3d5007490005900c40039141d544082c0d400201c0d0705003007811000840d14009800c2d0b00480b941c003100b0422a2161a404c2c1150000e0f00180c07e04c1d603840c88104051714000c034111032032411a4200001614040d28080e4407010710f036440302c1c0c0c44d446d0001ca42001c0e540a0003100c80b5502e000341265610784280c14443c0ba0341d003002c131200241260002002c1490b10f00054041c140165960f40c40340c2843c10848000054200324030f10009000d130078041c41000031140102c4009041c01c100c0100a01c0c584800010103440c1c0305500d07140640d02d00001c0300c1c1500d03440141c940c00d4444c00d85030040c45840d0b100c003c0c4001e208607642403490008039503000c5508180401c01c0300d040303a0f8142440d05242034510001c200c805400040b60301503402004140018100010402d0303000c000c841c2600d6026484c031740131404101000d405c1c040041c1d4001843e149134a007200c00311200d007044a003100020641c0b178000c500b548030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 277420629 1250 277419379 277419409
    0xc010516050d0911030f010501030c14090c0c24071805060f070f051501030b0106170112020a15021f020307020613080702030d080a0f0e0d05070201020307020a03080702120c 76
    0x910b4900c10f2003803080355440d10000f40c1000d011250602c00e0908011300800c000c0c0000c9400b40d4801d140060b0142d02590f0321594104000c02e0041c8a4841c40522502d03a032007600c00e82d0391030291f40300348291104100b149883c520142159003520b458500e44c0101413441560141a00614241007404a500c41c0341c181c85000c8411a9402c5e510107003810091a44258124000d01d24031911510404080c13100140038100c074401e8000404998031030340103031100d0700d0640c0514240b203011030042150030302240d00004054009040040543c0e2100d8413817955000e10a42400503034019050f02000c81500c82c0b10340e800c00c071210310441c1541454900291035002c0546803030000d81441484c4014410080111800341c1d9004044038000d900f1a0005070044100711100c2d00150f1600c4580c6030f4042550140002c14104240500b1001414110590b00c3c1d40101000b0b07411844140f04080058441e040c0740c0c4007039400f41e6811603c0380e802d8810000c50030309401540e20546c0103120100d00303a8442035540d1640703031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 277421879 1250 277420629 277420631
    0x40312090503160f120c200f0901081606020703050c240409050601080601030504030e10021f0203061f020c040b0409060203151906050301050915090c0c010516050d 72
    0x304141007442c036600500480302e40c0c0703400c6000700030304000c1c1c0f841c9002c1509125007101c101036101500c0c15640d40f000754a0182040380200c030061483e1510aa1031351a4100042c0001119810a80480c100000980044100354818080c240301421511b410400a00c29480200300355407d5560b107548900ba6a000c80c2e005075800200c0310103200e06d050303140241c8040b0b03001c02030b15507a5503403e00300038110560740d89010414107c00310b01254464000d0501c6aa0580c4901c03403e0031140060110b8102d90000004c1140111414081c580607211103c4182d03841407200541c030ba04141c02003042c00503200d641051110840c08280c10340e10740201d0030990383c483c2154001003c1075598040380141186d82c0d40103185e10310000401c60421612183c0c00c038003010648801c0e00038903e051040a100e44103018160101c1d5050004001500c1c5c010340c006d40c01421040a2400b800007403006c904d00d040107481003c0f00e41070100307841a401c4401d00c50581c2c4a1800d0714032641003000420090100d1043c0403462002c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 277423129 1250 277421879 277421891
    0x3090d11040204030819030f020f19020102130e010f080f070e061f05131a0403060e0309090405030403050d02031323090109090209010503010c05270a090501030308060108040312 78
    0x5a515581610002c0d81c116000c2a9210042282041034010a2491b6008286450140803001c0001e00c00e0750400031400c1c0302c462500d80c0190f0b00c541605000f0b05032004564080103094001ea2600211100409035904140015418130300164401070058000503407580c8007259a103160400040c0a10445100b551801d0050300e03200081010100c49190001d17480032400d281380003e6500000900304001c030240d40d001c105440e081003004401c580404000c00d010107000501c0801e10a42c4000c5042400204036440c0c04008404940c1c1d0f12401c982c251000c1d0802306040003402414401c828a080c624406035103407100001c00501c55540500603c1101403c11066510107401e03c05004022000144850341941e9140100006004064000c0780204008000000d150505019045004059440e41810405a2400748291600e4440044840b495540a41280f07071105084400500b0420402060315070440c280a8115640a06400d04001c0a0020840465442082440101400c50b03002c561 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 277424379 1250 277423129 277423163
    0x2091f02070509151c05030904021c150837030201021e0c0c0618010503041707060c0306140d140304091b0201050c0a09090b0112020a170903090d 64
    0x7a054964006a800919041c18441d41c8640c07141e41c15082c08003141c0200d91000640084484040740c1600203002c0da006120200c41441e01c1e802509010381110300340c40440300710700f548405960b41c00c400c02124442c6c0340030a01c003405080c031110031a81103080e54101c1d240d44c07a0050020340291310210500b81001114101c007094402c0d01190080e441414124035120700c04c01c072445039607101d420704030813a102e07104d002e191a04009095901c1400784010b18081c0c2148500103440300d078402803045903400d0104144d20030140f0f0b08005094018024507001544003500030f800703011203072a60030090341c0d0251640340321010703624180d40320b40450703200015410342050010402c1c80c50049802140f045801e0143c111203800841c2010341c0180d090b6030003805661039060241d03030981701e2100c0c44000601ca90740103019050007600314203800c402c185009101c00750b55580e0b510807a0442c0010b003000800d02c417003040d100002d40c0380141d002110a0060f525114052001601100c04800d0007091104100300e6114 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 277425629 1250 277424379 277424383
    0xa030812041110031506030c17060a030215071703010e040f060b221109030714030330161b060e1504050d050403080a030f330902091f02 60
    0x300c82d0400ba19240201221803000b5001d4003400f0881402e2000d14040014260311038092a0511100c0780c03a6400416201625852001401000181c00140c3c2c607800100685078034150400035001d030f042060302ca403647d00c0e0002c0e000c0c2c1d4901d18103103814014001408100700100d119a0032079808401030045481521f00230b00500941c40d070240e03200104020700040a1a90315000c3c0403c04080b404200040b0100c9104410b4051402650f0f01903028003424803003c40c410141e820025402811642400380d5007c8019480000c40c80d9610929018803103641c4495540390802d030030542c00010201c080074030840c0149851801d82c2c99010301d5824102d4401444855806089051442810b4401141501120070381000c010f6400b21080c0c401e054401810074401c1d810384d0242c0e9401040710b4902130300b254085001d0590b250308241484d641e0780b0902030360007074030140c100c000002c4020301800c2d0300304000d108100e248562200c2c48481c01000084208d40e28400b0300f007030524185003840170058022748124 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 277426879 1250 277425629 277425653
    0x4091802030102030c07050f0a0c15050408060c0705160509070c0f05031602030f011404060f0f0f0608070b031e0405030d020d02030402100512010e130203030f04080c0a03081204 78
    0x40c1d0194400001d0014100401c3c0c010f00c44a40034508940040c0384218070644d84e41c0c0c0c0f18501900c1e804081d40d0030310200c201e00400c0c0e02e00f0541c2e403410504003500c030f4884030b081140070b07186010208000111041048424804031403440b00103079840d03c08038135100100b480008000d042c807080023083d5101c071040069251001003d603400108a03511400b02c0f41988622652060b410782c420306c1000801c0c480c04005012385902800c90582d051590380300c036610342c8003500c088501100403c0d11040c010350002000c3c8500c2e60403109236440411220310b00083e05003024800d80040554010400400505285003160290b0200390340703880e0300700ba03503035800c2007811409003110407a80c0350300014081c182ea02817900514002c41c000c455240c1942403902d42070314944106d92841c86841101e1300100181d0320141445035115008500807048503a0940c0000d055620080443e2605000800c041c042d4650804c03403021666410b66101c1c04a07411a142d2682ca0f01800c2584510022140001410060181000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 277428129 1250 277426879 277426883
    0xf0306030b0c030601090b0301140607030c050a05060601080703020405010207031e0f03120615270506070b0406050c040803190e040906091103010b01091a0702060307021e01060506040918 82
    0x10a54104600042425031041d5000790000341c06e82d2000c41d81c0c4050804a038100c1d65603c8002c0e000c0c5c9420418404640c01440c810350078031602c6100c110200d0800c0c020026410700c51400f820161a040002514015000e0500c8003010301c1404184401e980008851042c0c81d0485607200ea0074280c1d0001800c0d59460356001486c0f5000740f914103080640013410041000b041910500131f56403070380042d084070010050201300040c1d00f1180c000281462000110503280802034003051303c0d40314008582c0613888800201c032608241c03010030091040705d106880d001142c00c5065841c19140c40360329030b81c0e400340c490844030f50340c100ca08404040f40140000b4a40c18070161050200386440c0c14030b0320051460042c15950703840c03414030782d000902d010300c6000381490058595840c10f40c104140d0004890703050b401c00c04041030070001310015946030809144611825401848200e441c0c500c06841c800c42070740d4036413003070b0f041030820b114a070f07960015034055400110000404035040707101140038210030000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 277429379 1250 277428129 277428143
    0x40c080105241e070312110708070501271103010509120a020c0a260a03140d0603023c090406050604090609050606100914040903020a050d080f06100f0f030603 70
    0x884440c0f0b010b007101800100d07004ea1241e141d00c03407540041e101901d42144401088650820050000440700000303098424001c0000042c3d250640d6200d001c02056100120124041920240e00300146005401d00b050000d600078003581c1000f910030b6941d1520308544150711a03000c5480341d81ca074400c10031058400300003062485255512036000e8140d840002a0840820320001c1d01b1140c458005603458515078140e80d4286202e290010061240c2c1104400c004ca09880300c0000026948508180412624002c0e511440c400680b00701814502020504a6460441c00c00c6000540e2040e110f61760040d00844003180c9641d80390f00050040c00d0010009000d98034209800d0240000061070500c910707010b450410004000c00c4c010303500303965640f00324101654a401107003003504198005600c620b201740100d4a143c1641e950741803d1001072a01e90000030030b440c0401090200b0402d1494201000387c2c1c0490301e110000500410000700c00407010140110346c01c940841a1083c0e1080c0010354114103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 277430629 1250 277429379 277429417
    0x12411b190f0305010b190e0a0b0d0b0a0807030b0403030216080d060812090a14030114090c0901050618040e07080a030e120319030c171302040c08010524 67
    0x2001a1150798060003040010b483c3c4000807502c8440d400444000385640e02c580d1034035503d85901120441034000d040c83d004410102d00107101041c0c0da0103406d11405084000c00c0c1d01020206028070044141d10042c0c0303e0784003120130808111840c81a640141d00b502d0b0250340c400b0014100d510a042c40080180b10b0f48002a5112402d10b00d0340c01401955002e1058846442400c080c10001e40207a04072154005580030f8100076586512a8031a0101809800881c0030190244040c00ba40000c5401c1c0095030050b400032401c0d0700d403040407540508012a46d260038201d2686100c1d81044a16010902903540c6440081800c1d41c03c11844c0700a02214080791560882850020300080040d1805402101d500070240401e44001c070903030f00744910301043c01c0e02c1611404000c070090184800707220184124003070044284041003001500c18503a403428805100750390f1050108541c0d61601442c10050007000501166807000304201c0c00180180313044000801d005030200c42c0c0d206480030414000f101032 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 277431879 1250 277430629 277430677
    0xa020306040b100e10030b030c01031a0303030106050d050c130e060a03170a02150403052b140603100506030d0c110405070807110f030906030712411b 66
    0x202c80c4400c0040c05451151700c03c031212000790142c42200b0007055258000ea01c4000c044d52095203c1591f1100f08100d0020030104400440e0665000780c201c1000950009242c203001410360060315000020220780a10700040e4030a1401140041d00902d8440c403101004281d840d514240303500c001d59080039500c66841c50900c6003410a50004207a5000741c004c03e62110382200e000c01080d03204235059141c00d450803100d001e00c9000701101d11a04458051009039450740168075200d403c2c02020545007420703590918404062500c420f0069440c0c0690400c02000717466200410000e81040c103070308015910312050300e444108440c500c0000c9401c03510740b0301000541640b01413403a0003114503860f051803010400608688540300e0048d05e88550703008000c1440d65040c003400850740180a450450400901c1d4001c5405640c41c89603e0300b0721720345d102001215075200b628183c586402c00c0c10798840c084881c02a9442010006080c104080141409070002d03a10a004070b4401c07291401d141c01c1c90180303903 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 277433129 1250 277431879 277431887
    0xf02040e070f081218240409360b06010909020d0510170307031407051005090111040608040602032502010903020c01091d0a060807060c120206040305030a020306040b10 74
    0x50700c29610030303116100d1040510b01c1000103d4140e66048400a0445144030080c010b22086c2030010b8001d100390031000f41e0100d019540504081c01030404003003101c03022002e20a120340040c0383c000510302450400141d1202d004804003031141d600000d000d03501e580d84030060ba4400c4495200c0c03c0000e000240e041140c0026511142c81514040c1c0c1860702581c440400710704284400b407550b030041e801003141c4000b20b801081002844c6042c641d942e07141410a5031541c0c100b10003103807036150042d218014001070401c00c2c0210203060070040c401e00e0806161100091030b42c4805480545601d900001060302c45245078003810300520100b069060840800030000c0c000c003015102030700140902d000c580c1096104104000c2100c5c0000250700417244108040e14611401502c1022010b40c0c507040041c0082042c0424401004a900c514205c03400b00e0924801c1348410002480c01c54208408020000b5040800e503134200d81911401a16a96076001040060001152582c0c0c8440d6400608017a1940 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 277434379 1250 277433129 277433159
    0x608011509140414120a230306130506060904091505100f0504020a03140703060e2a0a05040e01180f050903030a0c020114011d09070f030f02040e07 65
    0x22411103180d2039541c030003400c401c0700c01c661085000c1c0d54180011901007041c02a0b075441000d43c500960b0540da0704c2402c04a035692060719410007142d0076021445690f40264040d002c50001c01c1d1381541b0710302d4140c5c005100c1250482c00400ca455860011031015202d0710309840070390601070b00811900b07a10341081da100344031300c2c500940303a1810f29000032a0120003100d0b01c002c0701d00f400301c64803015060404103c081c1d001000c03a8070030950380b001080c903c1d000b001c5010b40100155100040c110b81030404911400340001c0030034511003168030303078a00d001c0100344149031043c0440301856200d101c060022156842294080d0009030b18201c0086050300e2019002407071215044801c00940c2000c40824058130012200d2100c0c6410a000261403803075941c00858408440f44000603100340c804d00c0002c9440c0342178200070303140c0111210501e40c1c1000400e640307420401241c020100e0030b10f454074400f07005400c3e0000600300c40801e0480404c545980d0407095444414000341e409054540d01407aa00c100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 277435629 1250 277434379 277434401
    0x703030e1b01051b030715020d2003041202070e070302190c02010c0206160501061403160806060609060403050312040210030e070509040f050604030e0307060816110c04060801 77
    0x140a00e50071100e002010440180349060b1211401d001303080603c581212890a2500b909000811120002445041412203254404000140c440d21040242012540080311010211020488009400b640b07601941e90080d8801d402001404100c4400c038141403c5138000149003940409010840e90140c01a000004d060300c401e03e032645601c042225090a10b20b0080d0205501141c000c0c050b09015008008560903280e015203140030b03540c1c40030708650341a8021080c80f0a0304040036181d2405201d0001c0c0005905c0d07140c02402d08001185449800c047d1415201d488001802c40c0c59031604030503540150740201c2030302d445010307442e07100c108401e04907030403807081c0d054484c080042d5010740719030341403c03130b4003001884118280800e1110140700540306980004a50084400141c010004244614825611001031040c0304050514101c1a03801047c240118030301044a40c24440c41c909840031000c2c980081c0c481d10030305149040159103107a40c1e030420700b08130010512010540014031441 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 277436879 1250 277435629 277435633
    0x1416081803010b06040605180102012408070e0f0f070e06070b100b03010f050d06060b0705071a0f03040807150614010815060318070b18040e0d1e02120703030e 70
    0xd0711004c20446100c1e9000c1d11001c0b80c3c09003c0140c1e600464560034540441c1800001440803d04028480c0c0204170403040c1c89241410f0000c0c07100b180c0a0140c1d034024004800d12001c1e40c202254078a08645005260301a40e01c0030600003103c00344652441c40c1600c802070043c2d555840036092040050f0000c0395140282c00c0e50410000b0b003c100300049a04880c1710f070744103008060402040100c2c400080e41c0070f5880c103803111008600c4200c08401032003514480c03001403520618065410f0500c03074005040c42c200803014040e0850782c0c0f203024101c0754841c0d44484026500c0707400d46464489003203010152101c0c1440c1c40300124000340d0040707030301c1c0340e00c0426201c46034140e8403841c1e038400650031a1740341d9400c85010310210b000d41b0745c4100d080c80301ca403c14056038042621032000039440c1d00001d0041840080911444005040a100f10f070b1035802000f0181c540080c0307030800a42008241c140302101c00084007150480240300340b2488000e010801030030703a6101c0450500401402610302028428 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 277438129 1250 277436879 277436891
    0x5101109120607050904090f1407050109080a020a0b1b070f090f06080714010908060a0f0b0103050405060c091507080702030c090112170c100f0f090201141608180301 73
    0x2440c000592038801c540d0f50b0b0320342d85405d00e80c1c02484003410f0942412070740806240b903c400042c0440e4200c01d0941c0c8110014090103142000040c40941644d00200c43c6030000b6801e440581c0301c0202c1007094440d050111507492160b0810384990712500e10001d001c1e03000e1000003041405280701201d048a89229040c0301c80002140c800044031707040d124242180e84119020041441c14950408100605050480a080e42c811102c1d090240c00c0b556031100315035850622245110030302c510ba40b964400c0ca0204060b161a99501d5602c14000d80210520341d40401c111120703070345540940c0001c1144c0c0340700c0d07500d031941450884542e410030a000c0f4800c1c02909500c200c82d041c01d9450320304a503992214024860100e03128100501d020a90460204070100702030b802a00742006003028a08040d00c00045c02c582e4900040d00b00e5680d03901c1042c2240c02c0c05660300c003503a48828400d821102001c221950b1304041c20a1440403816210018610320f00031862000104200c900081440001e07070082c000b07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 277439379 1250 277438129 277438159
    0x228020c04060b0903100c050c03040f030b01060311121f030803010302240a030e030412050f100c0e061303050106061e03110304120c05160620030a0c05101109 70
    0xa54007544c00301603050b600101c084001d8090b6030f0051943c02d601c07030a0040c41c0c04c60155055045034840d40001010700c544aa0401c100641c05000c1030040405150401c00c42d544008002d0a80c800c0b400901c80c0c0301e03204400328411100030340180315040f82c2c43e00d40c040c807540c1d24a4500309541092009a1141c03000308109420103d00c0400c000a4810011101e458842015010b80041005e2883c00701c60707100901000c101c40c0010180e200c40b15016034018143c031030194010f285001c44042114a0301d80c00c100d025511203411818200249600302c400c5070b1103481c8041e2014001500381c0c0054029070038160f0015441c3c0d0400102c83c00455001e1304a5080c00ca0a00e00380d0694003e07009840450788100005004290507030406000025140781040540c909521020310703103003d0302d10110900c081007008001c5036070010410f0740303c000b0444401101c011400b20880c0c0303e00950b101c80d001d20000f1040001040028005050000d804210410000c020204106095003040c03c02074050b05000070a885 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 277440629 1250 277439379 277439399
    0x3230a0c1e1707030605090c0903010b01020c0f0d0201210204080d0c11010302030406020c01050c03070e18040206030c13090606080105010c0c14060915030402040c140a030228020c0406 81
    0x2501501c2c0c0c86580b5080914003201030030b40c0000b40194101541c410303000c100c40e522064803e005064201d1804d4588030381108041c21a0441030041e03040d94090000307000292140d9103084002101240e642c29440f0305800140c54030000503000c190410155032220b0b0360548198094425201c0381c1046034030144614000b030340d01c54003420003c0d1068450100c1c03090705610035001598031078403986c40941008660881075007580c2c0241c03902140080f01101b0070034803d91101d8503080180003120500c400051200442421020142011f40100303000000940c001185508603460a07020313203040d0604c40c0d036401100d4000d20007801004001a00c0c08000180c0c0e6100340b10520000341c0084c4040740e4186408680011440d0101c2519001281030009541d141d0300c180c4003140ad44602503c10ba0359160600c100000c54144483c0c203001d200502030303011900c2c2585800e84003800301710b0030f0069035001e4030044010461b80f00d112040c1e49481e00c9100ca0103c43d404560389d8030890702694244407407519401000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 277441879 1250 277440629 277440677
    0xf0602070b030c03040305090d0b060f0a03020f0d0f0b01080610060806011b051609020301030b07052104020301090830090307031202040f0821091003230a0c 69
    0x407403810410b201081800b0000c0d001190440e100382413580c540301d0010302140307201034045000c3d03031b404403140e0802495040c8100c6640141604887c00102d20382940d0003c0c0311401800a518019a5018001000c0090900400002c02d810050710300442d80c0d240115a503078402203034800f6076810011400144c1134020413070039004441c141c440c01d540c039000040058404008903030035141d40c8200c5040788072a00c4501070000140c044500d01699a40c110b080050401c0401f4001104002c010801c003060484411400b8010008070207080e0455103c0380002400341c01c440501030b2401380b0000d06401208003446402800780c03a8408510b121841710120340ca00301c1002c84420f2407a410800400e00080e10951008013100d841000050a2a454a1042500e10380ca034005001c0381d8403489000e113102d03070000403aa0213170401c0601d683c80e240300c2101040814aa00310030000745902c88480d074802c4a0741c10300c0744064002194901010b0315000039840e01816021600d007010511500484201e8440c1c00c6841c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 277443129 1250 277441879 277441889
    0xd0e060609040308040c150201020d18020f0108100b0d1b020a03021908041505090312090f09070302090909010506120601050d0b061c03021606110c0f060904150f060207 74
    0x80c0001d03076a15181070b58100f1005004465040c41c2da0340c0801c5044020680c6008800d0301e134001602c1d41d00c0ea803076500844d83c2c040c0c0d80c291000e402088150042c0c1d540300c10031420305028030300380701280c854003125904115560451075901d800482d8143d01e0101e158006041c0703c224040001c607100c030b45013042e80c0b903507144103019005800014100c5850a01081041c02d5688240c0700c0c1ca1825580e0b810407080e00d030482803030310009400000c0260007484c040000c84a051815001c040c0340102d80310000e81c00d9410703500907070b029240041c001606c1c14000d506568501d480a0004034140c07911b014118000c2c801101c40508c18100f2410b01e036214000002d041741624806000040700c0d0405e42c807000c900c9600200803030342c4503100d809407021196543c40441500e61080e0010b01c8840810901100041480d4000c0340c10000c5140c81c50001003c0016001078122085d1000e002c5080e10f0f0300855018801d6003500c0f40c000d8240698240c0000100200780e0032a403003100315032512515140e00f261100b1042c031403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 277444379 1250 277443129 277443139
    0x20601060305090a02091509070503100513110307170901020405010509040b150703020d0201060e150111011503080403020901120308041e060c080601080603070b16080d0504080d0e0606 81
    0x40c403219000e5445a50040e0340c5a007111a24001940011b003202e40c22244000e1b50342c0c0780030031032140b030038034500709030b0854a94140a0b00314900b68442e404110742c40c0c4241e6101e8030794a803d505d8511000e41c044e40d600303442c202c5107991fa0f10342100c0107098061a10080f80c484030a03400001c55146040c400c1e83c2c2590016580c0034a8041c2440400c0060b02e80414150703444804485540641136900c4002c2c5000d07486600034044074583d03514040d007147e2240d44000320182c40c4000f0030031007111400d1700b0b2410402c01d00b092460510000d04142c0103022080c0000d400c6804d544c00802481046409481124402c55101041c1d80c1c99149440d01c540c03404400402043c1c0c8000072800203011140c041c2002c0d00940000072011042d80c507200300361a1018010380c04140e1920034880d030395078031003003460340701d041a802040080d240481841580c07040c022031410480c1020850710421541c1421151050380400c0c041c402c0e030500d4108a400c031303440441c0c11300f40e44d880c100301103090040c0403d07001d04c101d8004003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 277445629 1250 277444379 277444381
    0x1406060307092706020910120c0201050403120c02070506030106020c0901090624020a1505041e021f03020c160e0a0501050a15050c0a050d0905060f090d0201090e0a02090f09070206 79
    0x828a07001000356400c0b5130a64091041d5002901c0d02c9001010b140701d60ba82e91854064503015917821100d440003401f045904000c10480800c0d0001a8000059200500001c031401103d004a040803090341040da80560300000018815500040042248000b00c4400050707036a11a0913600701c412601c6464040007c18961000444da2200c040000389003900650341c04071520340d20501c5407011021007800e032039650018030080c040d07031a6071170b1809200f5168440d0740c020150000b0b02203100d5507400c1d0a14081070703490300c3c02c840c0c401c4d01502e107812207182c110340c50b012100d0030707000c0c2c50b00f0303580500056449078600040607001c090003803e040301d40140c0b280503841c2c00c0c00c1030442c03500409140350b01449000c11a030f00d030300e8504000c00540b4901a401a00007140c0c6501c00814810165000920803882405030100714841d1303030111030141608807000d02815086100517500711017554064256419250308000c41b0241c141c009000c42c0c10111862451540c0388000c0210121040c0d4032a4010b9201c80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 277446879 1250 277445629 277445681
    0x61202040e040201200105010b0711010e0312090d0b09010207030305090a0c05060f040e040f111813110a0305250303051c0209040204030312140108120313140606030709 74
    0x8100c504069501440c10b14817030901d0340c609080d15000e074008600705a000031841d05000c2040f0404020302c00910f054646a240301e000079988510004090524000009078103090f96076074540090741c541d0280416071645010800b150007500111801c0d80071a0602001809020000c52601c070b0f550360141c400100c981c245001d20036660080b2100b0601c003641044041401c50060800300d03c41d501c1681429445031309031500c80301866400100380d00400d02245100c0d00c0e40e954410306d540c00201c50a083c511003404e03040c10b80c07022900000e51b0780c01c12407011000c401d00102284202c0503200001d0b00c00c160582e80d08150031907412512001d80010301c00e00c00c00308040e40521010100382c41b03009025060184000004040b0381c8280e00c00ca01180317081048801e0702810b4014415101c40740404a80d480d1315085034180c50b5104001907800816000000898080c10070b110a07519940015980022141801006a95400a403001d40c0309104907080080c406070180600e400c0d950075002d030103a04440823 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 277448129 1250 277446879 277446887
    0x307060305040c0b0c0c01030e0102030c041e1d090105060603130803280c030605240f160b01080f06190e011b180e0609060904020f0d050601061202040e040201 70
    0x240040f54a04109000015440140d4000d03041500f0b0000c003070a00e01e001140013400b00c8045c0c1c1d4034481c140c2d0050007040342c9100303080f0695084a009403003503001d448401d00c100a0a2880380c100b0310030311101080b1064a100d80800803403092035820700030010303602d4038401c002890104a40d0500c403071007501c80e1200015100c0740550303041101200d0640580c0421400c0400c059050801c0c3c207031856031501c04c4010340750f05028040051105455542c40310400f9040021018904940c014100500146090200c04654100e038412003180140d070b000810b41c0d20b0800392122003032044005610951221445e42c80740031403458001c7c0220041611400e81c807d00343e801a12080304550425580c411382200c2c20207440090116001c0c1c540c2d1420621001c4003591126406190400c2c0b100c003c440c400c03ca803a0301d581c00c60641058007110301c088659620f01c0020701d07002030030400135084107541200404004001403800d0607201da941390800c0000144644904901441c800e4040300303043e5102080140d406 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 277449379 1250 277448129 277448131
    0x1030203031602040914030d0b04020f0403080f040b0f09040c03051005040e030708030108060f090708120306040225120c0b04120302040f06050304050706080c1c1d0604020906010c020307060305 85
    0x101900114507960b00d40c40305400d6046e0042c00c28016000060f5804808419200b045540d010440d8114104403440b010010980141d00005100c420b0018901e45414203800650340100301c0b6429041d51001103891080d166040b40d41030714020f50a00c0c0d100040d0318000d000b520710403501c2c1100c00c0c90442c5000e0800014141402e12902103000800003070001c9020000290b0107020640d00030140750400e040c3c4001c04207401000d00e00181c00c0303501c080c80084000314601c420114041e460b00d413241c464000181c003c2c401c40307410440c00104044220340ba03020a8094080b8a8040c02240c01c600c1410101a10b1102458a00414003148800014005280580c1c0c4071a100306030f140060400c0e8884071041a05103a5812a0f000f00d54040300300402c01000b0800040a050302d890550502d05080c8003440bc14040c2c2281303e0261450300074181000384141e80080601d40b45012801c601781c59410f4925260304042e00e0517405074101e42d002a119500415251045070f0f4003074000c14440c2e252220403801028 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 277450629 1250 277449379 277449383
    0x5010801090209090a1a030f061b040b030a0b010912050a02190b0901030905030d0e07290306120a1203091b0f030b0903091908101109010e060f0406080915010302030316 74
    0xc6d4a4209441d0b5440c06c1040d217501140900c0200351a08028500f81540c0d0810380301d02222036010401801205156015241c101642880124207154661700503101d2564540101c3d04096011403590705003e0b0001d25100d100340280d0700000c020090b46c0b4002d145044a01810910841c200f0644900f540b1940c81800f81a0050003524208081c600d081820348844000c190016489a001840f4503103843c4141500c48426002d03404105203026203465441c000100b403603104010200c0c4410000c00c081c0308080c0b0b0f00798015403a2581e110034510103801030425000540b03451081032189a00d100c3c407800741ca402d13111042080850b50b461030b61020710180d0001c0801585020a00003241d04c4d8403134131081444076000700300f2007450034200700c619031401070807c2d0360803552810310340690310007511901240e801c01800c2c6890100038005a01049891142c40e442000820b030000d03002680310b60002c03c503809102d2510076982103410748540129244000e000196040c3c10400070003168000954a0200c024 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 277451879 1250 277450629 277450661
    0xf020c010923120312090a05060f0702030913020c07050a050d0609021c05060414030a080c090303041d0103030306080d14030411061602010906020a050a0209041e06020405010801090209090a 83
    0x40c0c80e404034140c00711003c40d00b06250300116150340e03040600c18601d40d101810100501e48074249031646030396080090100c04200031002c01058541e03200380112690810080d007034042400c0509543e100940c044460703031020340610403000c0344078a0490444421510002c201c0d1384d00e551f03940c55030305c01490148012a880103d0b02000500d40540c01c451042c800e01801c0a0107403450141001d0340c10060f111100090382d00308100c006e207030541045001e5045004410304a480701b803104040391441c85a0b130494031011030307098010001e245440083c039040c0c902c43d60701480f4880c1d82c3c4003081c0d03980f0f0495a0a0010402d17681c4e03000a405213401c0515031050003541c20400c541c000501141c0b03194440029502c0200c14140d1075010f5580008007600104090710080c01204025100c0075120727003a0140091041ca407120100f001e0028842c0d0310391600018501c00d40d194109071038010000e5001d03100b16804a4449000054075090503c282c501540c0042c004081580e00c83c80854000c3c10140d1203a0010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 277453129 1250 277451879 277451939
    0x3010e06040e10020d180f2004020d0b030f030715090312050901020a0e0f01200c0405070203070507091a122e06120206220e070f0f020c0109 62
    0x12003081048043c41c0003100b0005903510561000b901c143c8064134000c0d00429500d806000004015404515559400440340e03181c0c135440d13030038201c7c1c40c0e00c211110982c01400070030003031038000306540b060540c1c8200f241210000c00000d1102030f01e034014128003500d4400846404154030009420080f5a1031080ca0b021260a0f46106100101c610039508121a60340c086116110603810034081c085650007100c0d440818101c2100081084501d1707030442110b18248031452032629020841c484485000400501440c603042c040291749810117442501c42c0e102e8008005207819003845910510006000880304c051803441c04c3c8900105828440242c600c10740807101500b86c0402d43c02c511505080c2c138007a0a0311060f42c2000269200d80d00702c1140411446919401a0742d0302080b070300301030114806005608e51944c2c90354020b18065001000c0a8114010400d485604c103428051100c0c0c140c0b101d49880d2450a4120383e41d0740c1866110b800300b001c015050007040c4158004c40340e444014000342d220 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 277454379 1250 277453129 277453151
    0xc0e09070e1c0c0308090102160e1308160809090c0304030c031b0c0e0615090a17070b03070302030402270103080d020c01020c03191b060203040312020313020a0f0b03010e0604 77
    0x110103ea801915078100114009981d50b03410b010318080030721000d404410340350600708103a05114028244024403050504d1030020811803605444983e082d148010300b007082c5504001c68241d00c00c01c60584680003540c001580c58a9540640740500e03019601c1c11414800f95400f0340e4054100d4032490181c00c1c11407420800110758125543c05040180e4400990313042070001c0c0b010314002024500d06000050041889685a004044040700d440400c2901000c4686105a007811110340002e03425003000010009800d03010340045014610940f152584c901c4159102e00e495403503c10f00b110b03220b04030401000844c13000b4014000e07a08034013038010301d0845590100350072613001854550042d040440c080c0401166a030062000080500740f000d00300c414000d0940403511203000082c005640813001c101414400c98640840d0500c00c40115500c0c208564051506004640700b24818a402040804d0b5504000201c004840900003c00c3c113507400c0c5405080014402011207800a5a408c06651 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 277455629 1250 277454379 277454393
    0xf06010c020409061811101b1a0c0909010b1903090305220515030609190212011d0901271b0b070b070e0a050d060b0a090c0e09070e1c 59
    0x780040d110085403042c0641d0300d4003c0c0d90000003041c1c1c6225001402c060b40c034103604840512a8003a03010f0381c1c541523030090b00c3d20b502070386500506100200341d078004003c1440000b000604261408964030740107a82c0c0d60301080b98034819008040100043d0040c0141741902070740115806030f00c00d0512600b04020802528042d4001a1400340540300b550010811801c0c0411000076015815600c00d15515080c0041640080013400d002e0381144568481181484198190b500b800796000c600318107540e6402c000c044500c908020b800c800e110840104c0c118190500c22003120003854a1010f030a014401e0301c1100c00d00c840a000c2e41c01c682000c00c0c104100c07102911204c09040c40c5490759840d440e4604010180010081403442804244070b4082e683e95038000e12401100c81c22206203042000520380840074114101c0440d4202200c2c02000c0f82c1200c1581003224840305d5542e481c40482d541108011fa05071054803030340b02203120309080019030308024000c00c0c0c410038142c04e0400400c0035603648603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 277456879 1250 277455629 277455641
    0x1030b03010e0709050f07020d081807090c17010501080711070503032b140a1e110c010c05090a0b0304030c0b0421111c02070807030b06040b01080f06010c02040906 72
    0x20140d40000c0c0f41071040e0340f90307403081c0746d04038001e52800f410500d07003400080d41e5400308000c120148006500010300e54802001e510044001c3c40302507500c070960701c1b1503900c09000340c0c400e1240800d5401d8054480c00540141345070407076205030741d82503007a212280103413148030011140400703034050800c01046c0ea84081005000040588070011301d40001524480b0000007054207400d219410f0400c6e1900c1030b003000c00100d802801602c0002003071a501e280001c4c20340c00d00381521100702d081651140d1030181030005030140200003c028409191004001c6580c2d02c02d020307146620070044c120910001013040b01440c0d01a209080034900000e141d00c5132458840704850440715000300441c0760764416249850001440014100103440d1803070524901d40b1908090640000c4580c030703507400d118541c800c00011006004480035111015100c3c14015043e150840b42140601c0c02c204c072400080d4809c100f2140f081802c003000c144103489100046540740e8805805031382c06a11001181d01040141c4500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 277458129 1250 277456879 277456901
    0x402091203070507060306530d12060e04080c0703020d0c0306060f0305030304020907091701060e06010804030f030207060b04020c030a020106091a19090207080c0c0a06091401030b0301 81
    0x80c020280f030401e00600750b0f000780d00004030450000e041e1920340e100300d44c56184050041d00c000c440c03e00c0742d180c46a420040303c045030700c0b0391004643c4c0b0414038000882d100c02740301a180d8661544844d0041d080080c1d8407140304d03040050341c900c800a070200740300341c02a209000d480b5050750026990b903000240b0400c0d07000c0098a0b208031416041007084030034400c01e002001d2204500c03040d1850364841c99100d01000340080d010700300c40000903481c02e00c5901e1980c05405d08041640340c21b0300c070301306440c004c0c05507000d044185e0381110042200c640c015050640b00303a9042c3d48440d020380004000718041d40180c1000c80c2c4481d151096a0925515800a0070003001444011611440c01050080c20349100368880c04446140c190304180c070002d00c15407072410364400d80360010058000e01d184000713007401d0361005401c40c0c80440c1c00c0c4100070400c8020011000c000e0704950b4a840722104116072014144110000301e10340180400030048405c0400d061680d05050000300782c030004011900791244238901c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 277459379 1250 277458129 277458133
    0x6041811060403061e0b0315070315050a150813020a05010c2f010315180209010c0b0a0204081209060426070305060712050f0c0f0c03040f05100f020c04020912030705 73
    0x90103500026901c542007006c44200d00034021110074802c884201c000281c0004105601e884800c080c1c0703140209840c1c000c0c00080e0640310b9190303036840314224248100d0411400244030f03002003001400504258400d490f0010316241540f0b1502d4015980554174550480340b191280001c0441d40c0318402d6200c1c04800300b07088541d030185040740010200c40540c4412880510485030a21608400c002d11184414000d600107a4684d50f800042e1018012080d0040c12908240100800c03100941c001d0003c580241c0104c1e055503806440d00c20090007030313450700c0f034001000384030070851000303154900c0040070b40c12026030514442d0315500c54140034458105641650005061007100741d4040b416070940045108108110f042007420a04528005403100380c580c580400c910789400f06075002c6941174800c0804803a55141d44819504041c511880390a06c912a0a80400d09140c0a01c242d1003520304550b02502400b0025000c120080d0410b000c0680c0103001c104556201032400c00c010301b200341c01000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 277460629 1250 277459379 277459421
    0x6041d011b08090f060c0a030b1c050d360e070207060801060320030402031204031a0601050a0503040609031103040902030907050a150311070c0e0a050604181106040306 74
    0x100142a220001e000303c01e66134040c40f00d102c8a0b440128038150800301b2084d5103030740c03504140802c8019195201d103039a0b1000748980400d20824882c2d41d1070b6136040c4a00c0c2542c04044a00314241d60800c1c082401c450b040d105440e039400c5040e41c0b05a04650306c5000c240e48a00e50b52180106003150008568840150b404110144000e0340c004a0403401001c2c5840c0510121441040d151202c0c402c4a0a00480c4600400802e04554081c0b0a5401e00b465501520791603c3d6242007480a511845c142001486c0158000c20b68952180c07040f1010074259490300e41c611b4aa82c5d82d20b5004241850341a01006441c913003c07201007205000801c01899a1200075859060460816007010000ea012510941d00e42e80c0c00c00241030000c681d084035003258200041d03040064501000c2520a4104c01020300300700d18404a40441e41c1c200c520f0040b80241001c101654410080c4012624010a02c202c08a8610514000640709090098031410003900c228100380d036030307030316501600c0c100d40c00b040f5a80d240341 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 277461879 1250 277460629 277460681
    0x170304020109050a0501050a0302030a1416081302220b0603090304050909191e02040c090315090b06060c190b0103051204060504050105030603011b03050a0f0b030606041d01 76
    0x1003516003c0d0008a4201000c0c83c82c0c0700002c0c0061141c50b04807030031306801100244010000340d0002c900708010303000000c04e170f1401c00002c0811200700d0031040003052218000c6031010200060170456281d0181c0007440d925500c8258040c00c0c00600904410b1035161104c0d01c0e15a10788001550084144000442d210760070041000290640100350300c0c406e900000388842c5110742100c00c9101550807009003003c1161062140c82034881c4098041d400c6818100740c00c0810b50301c0038812084a00404420012903584400c0006031030100401501c03031241c85001c2900361034468001d0200c00b081c40d0031907001e51140c0c800128103004503002134844089280040090000500501c00301901c08480c440ca00742c14030f80d02910a0060307008480c1005804000a40961001d61113091905148001c1390120002010010007404044a0406002d41082124003a0f00a140220700c7c052400401401700fa0b602d200600c001003000c90030000001c0c14501110460314000c4c0300725600c2c0900f84032032818800c682 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 277463129 1250 277461879 277461887
    0x703080903010b120604111c0f032c12150108100506060f0406030c120e010f0f060b070b0402060714012c150402040e030418060503030a0504031502071703040201 71
    0x41c80f0254020f22078500ca14415500204540e40c0c09607200019500d50240140071540046141f4180c501030217440ca8503600703103c441e5100304902407184e030310030342d03180d022a00000311a03098030080002c00382158100005403a1034031140c1c0c0200a00b40483e0580005140381c4c040182c000c1c1c0c0980500d400002255146020500510fa0300c64825030343c642c1b034400c160748140c00c0391265100d08002c250b500c0c400342a01c0d80c45010f0001590006100500c07601e81d900c41950700a0203c0120507007031503e0185150f41c089440e00034881100d01c41d07051182041002d88175105078000080080764804001c010f000e0000720302c0e01030f1402e1303038030ba0400011344000d10880341c40048010300c541201d14000340c5828402100001842c0070f0303030f01c1c4110302840c45884070310200300980581d8403418098040070901044a400ca281d100c1e000c451250800d10050703507500141a1280b041642090024004110038400301e0024241c0301c034210343d0301c2001403916001d600e864060b41461011032140c000008184030a544e44 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 277464379 1250 277463129 277463141
    0xa06050904062705130b0405032101080325060e031222081c021803060a0203091c1403040b040b0a0b1315080a0f17040602030a050f0903070308090301 66
    0x209500c02080784000b04900700250085080f49241504c070030004105044600d080142d003a480203041d101d80c01c00d454402e8503904400001ca40e003041e1034050880b080750380c070a06412101450081d42c50070043c0d440d5a11810b402000c0e50101c0c0c00c509100c81e00065003481081d5050700d208001e0750322400c80380080058002c0280084000213114030007100c0c21420800003a00f2258001d034050b80d02c000840c0c1c1c2d0b0240b070210003003c0112900c00301d0481d042c2042c12203070b02c44010044042d605c56544000c2010100e001c1a41c040300558050888500407204079501180e0825180c20320007110700d25040ca440e000e0744102e404503644040e00c03040c041000200600c09800030304084040c031200000c0404290180c44001007119010b0b101c00030341c58003103038a80c40b038000b0744105410b81d202c0d03880c1c0341400120607000100c211a21440d40d00e186440d0b14248050b2411340c4d01035406135181c5a912403003150720340c10441c1038252082040091081c00d80c0c0c20810345009501c5402da207501c2c1c8030000304050071158 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 277465629 1250 277464379 277464389
    0x703051c1220030921130608190504020316080c150a080c091201020c0309030c09070914060c011d19080717070507170127030c110a0605090406 63
    0x420300c0c0055280c07061201c1e100740e80c0b18205454944a07941c00390f010b0301d801c01c078601c501d845400f083c42d004030340b440c090000c0031280444030520204a580ea5800c039001c00040f00c114034152001c4004184010300340d0041030300640020102e45616245042006c821081c43e80110080c0d88507081ca000c16040c00555846440800c0d40d0050030517600050151207070500410710072403050001191a502e030341740350401c001d41012100071074980101c02d000640d03070b5000500892092194044458052030050701152040c811951005c203928604a1310908078003500000660000003807014007c0c0c0034003440740400742c011492524041c00100b91030f80341030108005040c0c000720f0f00340c80342e04c1c0403a100c0011100344682c452345086410003007807000c0501d8041d28074020000d0081c00390010b44100409d80445d4011805130080012441c801141d508801d401c83d14540e84044d446810b00c04a8042c0c0500c0d40707074500501003000484600d00000365004031981101c000b04102040a11090410f4452100904 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 277466879 1250 277465629 277465631
    0x103060b0c0d080703020f0705060a0605060415260406090311030f1b0c04020301060203210f0601030e0a060c05040914010e2d070c02090702060c0a030c020703051c12 73
    0x1003041007646844001e481080020301c0340c90004203180078030a5040b41c010a80a0904235110f10040c50007a0b01c61006807174184d111400d08602181c0d510f00081118212528466030710380c840c01740d41c0b054600c0240c06034024014030010b820700c0345080f683c2c1056881a8400e00c00000c0ca0304003490b02602c0100e90326410102d9900500100c815481d20000b15036422080400c0603060711420600e00b0314180da0f403c0d42d10340250000c40000380c01c0d070b0000060403120b9484058400b140c100c43c100320003a903a00320340d081a081c0c81c02d00440c4403940070354840d0300540508010369410204030b440d01c0081d1982458a0f4000480c000b90800c12100d00c0e1081010000c1d000030f4991055150041d801c0d51010083d00551014003014030144d40e840010104e01c0041d0040d89040318980b0384400c1c0078101e00741c0d000059002d251448009028a88003107803080c0f207901204200d50510202c1103088004101d0315402a0075482480008070218404205d0440510042c5043d00d40b111100708004240300b6503041600101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 277468129 1250 277466879 277466887
    0x310912030b030c15070c0f06080702010b01090e071143060f120507030b0f060307090311060702040e0f1903020a1b12110a050607020904120302091504050103060b 71
    0x2c0e580400c1d115400b0400f1a001200d9600001c1d800806200c0e40c280103214015034200003c09607100520001113412540700c0c4841551460001d9013a20380740d00715140000c580e11410b1001a400380d11840c4c1000d034030710300030319102c488103000c52400408032461165a880c4a0743c0a070116210078444004514610704046025504c100d00c0003910032500541d0f007403048105c0015042031145031078003842d060b0760000b8031180c10b002c4030260080c801d44c41c420f80503501c11544103a180c00c004088070f006005960315a80310900e0354a403141c4000301900741c598071200800c0302001583c3c983c029203840483d22000380803030f011003c001c907190880f030400e554412030700c45903c200402e0f0040342551455812605011020b0394000b1b11100d4152690042074540840c1001481401541146406104029102d44510680760787c2001098044e10341c00951242403d000180041d1154440f104590801e060140c01c203803400c000100d14007102c02803503a82e1040801e0802040d030381800340d000105006019a494 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 277469379 1250 277468129 277468151
    0x706090b0d090809100f02060c0f0318030904060b040e1303020d111501060806030105090f0703020f0f06040b12060603010e04060504020a05030d030f0b09090c31091203 74
    0x118020225915981d55880c40a4402c0c400150300f115103408000700000540351038400301919840b00702030820014820400007445510740c0d442203030403c0321000503031801e640d039059505880030a04101058140401d000900c00d40e1558011000942289042d46844601b00990001100c40007401c0c4605105e1416000f4080b940102d10002c2824070b52800484101410b4000d51900c8e141809030310782040d40320300008625602242807402440d04400900032030f00c41c440215030720714041085801d02c0c1c00418080005181134000e80e0790350100a000721060b1380c1790f0f40001d207180c3c2082d1300c0380c01480000070300c203003900000d07981c001e50017401220050b0865042c610b04401e04074005000408070341e13070b07180400d05660351004404014003009080b52810543c0681c01006040f0a2003842071180c2400080c01c0d40f4a86018002e2040d8002001011074007000030410032407000304c82100140c91a8030a0198560081500c00c0d595884000d0340480c021015161259041c041c041c48002010725003a07603149 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 277470629 1250 277469379 277469399
    0x512163b04150b0304030e0a270605090c0c0a080c0a0302100509100b030c03010e100e1c0f051c150503010203040b010513060e0f070e010c0f0b0a0207051e070609 71
    0x1043d5689044096126603841c6030030f55078240031003003856102c40044400a43c40368000080003d003203280c6014501d002610850300c0942d0f44a00416904c2040b00340080c510303058510141c000b4011603030444401d40e4043d1900007940d07110104801040d00700c03020301c20504d601040f641c601c090000f44100031603e070890b011900e440c0f800d862801e5440c3c490400c448aa6404c000800c09004010001c020350400004141d80d111a040301e44440c0350f0800030b1001c4e01d0300c000305180380306403804013034402c6901e84200c0c100c0e0300c0c00c10700b6000300900c5803d01004040c2c0c03981000040d0800045030340080c2d403a449680b0022007084650009209a004008100018162581d02811907005031030823000ca0315410210405444203800800c0d8102c603c0081190042052161501a001980b211400403200b9001101e20b0211a00301800c2403c07c42700850004410301069a40a0541100142041615903070349003000888140145540075078082e404c9108402d000e0000200541e0503c0c07980c40b441c0c807003e00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 277471879 1250 277470629 277470671
    0x211403010806130311010c03050718030201140c0712030c0c090605010f0f110a03030b1903050607120b100c0c0501030209100503040f06051e070512163b04 68
    0x883c804085403c2402c0501a00c010083c00003043c0090040c22403d0000400a00003101d03103400045040c1c50203040c03000c070b003902403044d01c3d0103944001868020003940d03103440d40000c4000025200349500042d441104040b01c4929038803d9480481d011181e085c20608039032103400020015141003010001070b03801c10940c1c4014041410122199213020806480c440e4040142d07070101e010f1940040101340c0d0562120405140440d50000c15006002d20314540c1e01c014040203040c1e51008020032040d40c0180d0141003000d42c402004501000c100011031000760200007080c021800c02d1030790004006100d403485000c1c02080ca0f00f14200760a81c0c0c00120200001c0e5295014040000049800d1240d800c1201015a0b00220b0038001810074443d2480c03580c50022025103c3c84030031020556151088003200e10f48800d013840c1c40495140e103501c074034100801e4101e840c180f0071540030b41e10742000c25000c408102c1c81e1011400d03811450300100700b040070041c151514880e91800d4440320520175124511 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 277473129 1250 277471879 277471891
    0x7030f1101141807270e010209150c010b03070303030b040c0305040201050d11040b21070219060209130903090501020705010206060d140f0114040606090203040c03060e0a211403010806 81
    0xa40c400d2000100704d042901540256504424a00b0002643d681c000801c41c0604c1184008000c3c1031400e441040c00c0380503480b8041c1d804a640305002001e8055107000d04a0b2000350000018a180324800080c80d040195000310081390702d55940465601c0d05205200c080c4a180c14140890300d01580024258460728030281c07045d80ea03910840481d01d0486099a028010300c2020b00da41c0d0301425405c28041350b0603802d241180c500d0100245400c2e1001c5800d00143e8910000303496902d00c03035540c40300a50080c11035285c00c1040c004143c0c0c80b9807007900402d4101070107030701d9541c0c18a060400090600c90184c10003410b55000c1410700c9140e80b6000c007817140894114405c200034903501e841e090b040480050f04024a91b0800f546e494072000f43e00b0401d40118400c200c1008a1a40c4d010000c0c2039020840e0080d142c035800f40000c002060301c64102e05240702d2404260703100000315549107503c540c40051001c1c1c1c0b11b250f82d507045000c181c1112584102d415007a0a66040d5850406880d944441c02048 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 277474379 1250 277473129 277473151
    0x8030a090e13021c0209010602031611040209090a15062120040b0a0e040b1c03090b0f0909011e09090c0509160f0905030a02010e06040b07030f110114 66
    0x55a01c42c051111280030550081001038040e210010345290120b40d0034080e44145418800003401c103000004407030800c030a1070030301541200561030b84410500000c01c030302e0300160204551521655003401d81841a0380c4e041c40083c0030481540c1100c0b078280e02e900036005001c0b0a403001240c20204124940a481940303001041e54224419514030743d100c2c10800c01c40c00c0c6004180400c0c015800c10140841130304682e1a07c58a022580800c0241d850b00b5403460740145e41c040b04180c03003064840203014041d0007801c1c2040003d82d07601032407803194007078615299007400116404106280c09030401b0700601001210418000d034040300e0b034030301c10078510850741d1a1b541c9a40c20300c20000031482040044c04002c2c24049039180ca440415200311ba10422400084c410011b0800124040c8410340280d8a02038010402a02c1030760044d00c00c00c001ca0300c2d01d070307000005100c0080c0700b0130310034010402144681d40700c0420b000c0c1d4403c046c200c00294210980c142e41800019203c00c004081859032059203000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 277475629 1250 277474379 277474381
    0x150909020312121909030507290a09020306090102030601140d061505030103060e0d05031f0308070602121003050a0204180204050108010e0c04090506010501030b010504090501080c010908030a090e 86
    0x40060300d401c100b04600e490045000c1500480c00209892191140a0b0808844514a25041d942040710000e902c02408103109000c020b02040d04200880d1301207540c00b80c3d04c840c3c40c004102c58503c1203821515421388030348900ea03d9046040900c03005d030308240c48000a505508083c1d0000c1c2c00c003101c500c3d002020800c0458015030b0000650082c9000380507400300d9280b040e0300400000d11640c4240400c0d0303206818040c4207141100c00003464040c2907107550320070342592108407040203d640b64207c9116104403018000c0b0108140c90010401d003880349500681e43c9400d50400d03d50701030014140303508220712000c104080391000c6801101e490f4111400281a028000c03512688843c070380703004c2d400c249000c0c00812000015130061259030183c60480700440d40480030001070741c100c45c1005241d50089001009554020b0f002540c41440c1414100d05081e121020041121026482540302e81c0c0b203428900d01c107580292010002e00382d080c018501d42040c0503c064202555481855900a9040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 277476879 1250 277475629 277475633
    0x4090c021002030703060314060417130b13080c100207030303050403031d0a11030313090b0f06030703020901030c0302070305070f0206040807081b010504051807140a02010c1101150909 81
    0x100c4000c01c0350352969400c41d1a81410a0010010400303800216411030140d018140c02140020b849440755602c0301120310110b00205100036182c009080381d4202c00c003002d0001c51903200c008064450315982401208200c0d141c04005032614080d02003903405183c003954040d040703c1c1d01040b00710030390350181030203d0f083d146c526044006110f540c054810411400303489038404a0040343c8181501d020300c41400d000c6104408250b120710450031001203404235060200300000441c4c200c040c80c0c1000800141071b16504034045074880c1d200721401c00010ba0300041941c082e682500c40c842e154506840e045060034625540900f0905c00e102000e002000382c082030300e017103507911001c54000c2c2078540f05440c02d0741c1c2c0d07031a552603076144041c2c1c0c0d042c0d0641c0c1d802500c02555218800341c50032580014200155003260101d0142d503100b014103600308100c040c1c40d2000e00030b5558001040421410740c0001100031440d10000c081401507000c94045905009001050510311200b2205985e107100c00025405a14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 277478129 1250 277476879 277476883
    0x221280e03040b0a050d0608070518090a060c0f0807020705180a0b0604090c020c090402030d0c0302010e030406090e06102c09010305010504140d080118021b06092104090c02 76
    0x5030302c03c000300c180015100d008654804041c0c00804404a030600c50103484003140754070b50980d03014030b9801150f42e03c846c4420418100c905608291308909840c0410644e840d84403d5030541011b4a01042d01c20b00c40b280031691201540d81e01c00558406440304c103040030000398904c00c1464100440382091008250603030510b510056407114010080c42c0d6032652801c02c50f01422603d03400d440503000300d809400326405c111140d24425640140500313042a2004800e60f0780ad031480f130050b4110741d1786584c03c243d0031100300024409888030fa2958900c051400006026030040141203600a0905a210f2524140c2140030074103c81c1d04546240d4007074540301305581c2c1c0342c0243d54145a001140310b00000a015065124900480c007580c62410032561413803180f5600c0071584034100c0090020001082086100702580c000c01d01c1c4580c0161400c22401c1004002529440880140d5040030091200040b000c00101110090104220030f4802d101c240f100380710700891042507002e50301d842000f20a00d2003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 277479379 1250 277478129 277478137
    0x1020f0d0207080106080105010302150a021002120103060c050721050d050a0204050405070903030206241f030e0a0201020c060c0106151d0f0f040e030d0221280e03 72
    0x201004551a028180400940c0c5488074811000e00d54607002020440e95018000c00d0705880c0c01400c9201a1034000443c608144d01004504003140079145050503003407024002000d030404c4c4100d41490075411420b006086480c100d6200040c46401c0200030001140d11900841d00341400341c10b00d500c42d5000c6c0c41030f80d00d4840c004100f40854030307000400581044543c00307002038a60541c1c04200d241d43c1c3c100103442c0546180005405640440700054034401700600d036110844103484500d1903224181d02140c680200321000e081443e514400c1d400c3d0840d40342c4211250f480c0071100400c0e04544c1030700040d484401008010b401180b00098001c40c2c0a800d41040d0018260b04842080316019201c000300500c08145100d0b0f0700305601810a01549482c20403040d00400040a00300703c00141010040100201c0302562000e000034083c48584004a102074640100c031000c90018080310720010100780e40c0300822610b0801510700000b07d680c03208018000051000c4000016500c000c1078015183d409 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 277480629 1250 277479379 277479403
    0xe10050d0e0109050106060809070e070e060d0c0f0305060604090203090c330307090e180f1011030f04081305031b010206090105150105090402040510051314030a030c020102 76
    0x2007800320008500005512881d901d0b03004400800042c0e448640407030702d10a056603045620f034071840c1d00388030409600010641042c00c40c06c00c400400d002070701107541604030108442000e03030b50306120f840c0150002d0030041d40c1d001a00d0308008078a09500080d006000b0760151500d07166004c40054100c403020800c2e200008001000b08207803405407200c0b00c94100c44c03504074200c1c1040d000c8000c54000052015240124081d80b6900f0446040060b0741901f03000062a44600103110740c814148803c090000183c3c0c0d4507001c0c042c080e8010002c060005544600501e40250042001004070032001e85d00c41b590000d52114081d982c0c0c51443c00000049216508043d40c140102200016a07125401c418100c421007a000d440f0a81d4841e8000c0e422100c00b255200074180030b0b440b03540c01543c810303001001c00c80303801000182065100d10109402e4035004040f500031138030001c1c045921641a010b010020000707401c1c4c01d42110041e00200e52580c6032940c0c01800d000c00e4600c1007086a0081c050346523107a03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 277481879 1250 277480629 277480631
    0x602070804091b030c050307080408070b04050313120c1e0801050c071202010920040f0e030403050c0909030901180504020a0806091005030307020603090708030705100c08070e10050d 80
    0x81e40b2094400018880701c0600120101c02840540255000e4052003c0e5003803540c94a50440d035860740250354042d00180210746202080108400040340e403081780b80500e000c2c1c00210b4403003002180c640c4040917a034100c1d9249800307030f4105000069081c03044c003046d175880001500d250a1030560080e8601d15a400440055007400704010080010101800c401e50044904200180c02c03414140d00b03d81e0803260140030412420311740101602c40580040515601600004e80402e2600d00f00088506a108036900d0343c10010b02041845420040c0c2c00d07100303008682000803424603c0909640303105688040c1d05005004196880302420200e03034000401c0041d00070f555440107050001c0108030f0441301e4034072844400300442c0c10125100010019903d001d0001d524100131502004502d400050030840310344640c05010503420301c14806480761501c648010714160f9801e89102098421581d644020804c020342081612035128855100c4010282c892961541e404281145c56210f20280f081c041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 277483129 1250 277481879 277481887
    0x80f031c23040218160f050f0703080414011e1503020d050a06050109020a051b100e0d11012c0a08041e140303030601050d06030c0609080d0306050a1206020708 70
    0xc070010220241c400d43c82126011001c10700400c000f0805142030318a03901480c0c00744a5410010b016615a10111145040541c1410300200d42c2c8441a480306104070002000c0c1c505010070440c0c1071082d030a0030810f0100230b1007441a20741d811301d0040b00007060703010381d00d071035180e0b821000191010f0440555000b030074000d0071000b5410425038524020808907500e0b40340c20000110846036100391188148986d95861508000056040d1050000c0350303c07200500030001409002e802500c581d505821000f07014040c0c49070000e0024202c4503e00a8951310b6905205500c40300200042c8601082d04604080c03030340030005150350300e151101d41403009240d0300001402150044034040ba1107100240409200c0241d9114050298020800640607030150b105002180b0990f00a0019001400300d80380c00044040d50703500c9507103044220f58801030120b540340b20705028085007800300c214121102e007014010981f0304030100708440c45500c1000800c07088030680104011b980d40450f94220f0b0032404290b05d07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 277484379 1250 277483129 277483181
    0x100909110a0e01020f06011401091508071403071b140f100f0b030a08070f061b0305061c0308070203270108070212220503150106030501080f031c 64
    0x1190744078020305800b152108540e040c0940c400543c881c00920042e000e45141d91030810b1b11a00151101c1c006418080766180100b0b90004056406542503820398404404d400d2000000e000d11092406800c81d40304204100a602074010800c200748090135905100001c440d810403201c910103403070207000c960040740707901080010005105805101c40c0070040107866480b0000c102110990190540c05800001c2c104010504410142640600070884411271035102c3e581c0c00304a600341004001200148030700b0101d06a4140700356544400245c030040b41c6071054009210300301a52500003010000000d0006107160310034415101820003082440a070004000090380c0603e550780b0215000a107514001500300d440000c110034000303405284540713440c42c0d04404081d00ca41c0316130000500303419a080020341d900d0411030b10101c0380c8401c2d040c03041541822001001d0340c006038421f10b00c90744201266500b07070f10b01000f00c0e085080c450b501ea400b82d044880c2c88201404040155462014816000c0342c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 277485629 1250 277484379 277484411
    0x901081b0309061609030b01090f0b091023030613020105090a080303061305100303110c060304030c050c010306050105120a0e0601080d110a030512090705041508070503030a0c02100909 81
    0x4091050135404a500303000101c421111081c0f00c0c8030161801c1080740c0101305803509030b0b10000e06640301c9180440d06c0d03000c1c0004900001d10a0b10080d100c00351100007000707441003003036070780c14a05403020b88951a942490000780d42c54a01a0038400ba81c862801100c045a000342d084844051000d0450b8448655403180c0d5522904102c035114010010030006110b03003103440c422140f02d0402c0800743c1c0308a40c19a2000c840510b4909000025449a8812100c0554520000e1442544683e540008101682c030f01181004040b60030181807504089041c401d603a0002d0568041c4242950070340c400380c1c1c44036039400c058a6a01d40014560080c51300200d841e40010650b00c01990840c0c680e4400b41038001c500640d034004181015002603002d000c3d1008200c924445250408813001c210b42d07840351103030f0002d41294203d4045443e0103c00070300421941809200440087c04110013840c01c0800881c0c002e408044154002441518031503658501c00e40520031420181c60010400c111668100302081 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 277486879 1250 277485629 277485631
    0x10c0c02150c120304030207090501170f0a0309060302070f0609141504110103020f09101110051509100305010e0703170c0703030e0310020c03131a0901081b030906 72
    0x290003092056041c0c40d06400000854049109400043c030400c400303105032100e82c0d08050011400c50184410020b1139500a0103000e02038625032450401c000c100380011792500c980498140000c0e0081d04507500441e4100311104121482c80c200941c1e503030890b240910f0101c50b80c02e002803a1131325040010041c04489011810030907205822a103001c40c0b051403900c891031085400a003181b000c4007030b240955100e900503040c504401c20045081c00f56010010340d0241e81500b1200c0001c3c3c0704080d4002d0039800b00715800000340c0c0003208020a00b40428108411480050720500400d0094041007000d07120302900001183c008000b007110241e000306440c4c07548820300c41960540c0000d005d401c018114041240c0329036045800a046952550360195402c0c9070003002e165250251060315075014410740010034420403107a02841c0d5407403841e4003450181d000c07074001e03032420030303914a40d9142c0460080c2198152102402e00d4551542d5100c034100b01023184d800d12923140036000c0140050010009011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 277488129 1250 277486879 277486883
    0x5070c021207050a0e010b03160c050616090b040b0904200427180303050a0b030d17071404030816060f0213090b0319020f03060403121a060a030b01030e010c0c 70
    0x14541c5179101140c02002101f80030343d2010600800c04141c0b000200c610752404059103041c46c0c0303e0b404050f02c40d641080d03400c540c03400b201c040d80b54007075820b40d6200540002402c040e40700141840d003404480d895038001c030340c50240640c0c2c1c0c50520f0824491240541d009003640029556919a1911203481c1140944400842c00c954031303d202103058107083c05009a00300d40380b00b840c00800f081c2d86040f406044040c2c900f6000e41d0351481213500c1d0361010f2206607007220a03074a440c56100c1a1070200c4640382c00003055441040024014180c000c0031040403501220380101c04982c0b2241d006564071400000500014010303031910342d6a406804440d0083c282d6a115101159106036803140c002007a00e020140c1e0540c0b64110704980040302d05031514500c1c0341800074106c11089607011000c01d14100c0b054070240d01107044808810814026030281ca40b1070701d4550034142100c00c004010a1841c09190344144c01d054a4183c00710b01d60f4425440501c0c4108280000e111041f0354640142c040c1c0b501b4070301 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 277489379 1250 277488129 277488139
    0x60b0c0a05010605010c03080a02280f080a0c0206070c0503040806190b0109030c05130b10020f0607050a0f0e0118031b050a050906060a0c14011a091905070c02120705 73
    0xc001040c5d8007a525080c0c1c3d09425848000060359805800402544442001051609121240c00d01141e8220250303c480700c42c0d4480780b1040708080c4016001c0c407001002d03000c825080901800d5100c2d03001c80c83d140c1202d83d034207200542e4405803410f941035000f0f41c0c01040c0070707114040401425450005680c40104100f6800b08079800903440110303404010b502014040c0300600c03401300914103120224191040c81d045000a0f00500c080020324683ca00c080c0c0540181c1c040b01c549154404207200b05a0004202d0034058684000d040016043c003030301c00c9c458002c0c0700401c1c15003190b0b6401904c50151841316518040d81c0c46442c0d1030002403122814548002100e525070000c210390800c0b074442010366034010030600305a034540040152035400f120303d402c100120120301400142c889003010700044030040c0040b44051175403d005240700e440c0b5890303a214110550511900b507041040811030001c0d42e51021403240d0f56204142d941c0d645d0400001d41180d060380124141d080041602016100c040310 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 277490629 1250 277489379 277489391
    0x7030b0f1929010e1806040501080601060c020d061b17221104090c080d0210020325021204030c050406090e06161704060f0506010206090a1104060b0c0a0501 69
    0x12201c04540c4003a403469296a41100c0c0d02480000c00b00848098103414948102507140c0c440100320849948150032104007841d6051100c2440c1602495016042010041c40c10358980700c0010903140d80030f640680034041050f082003d002c0c298215140070306482d554100e411081e40e00c000c0c400052440c0c208a111070305800326410385208200030291803201c10021001c1d030780540700e44102052001482e640103a55001c07000000d025280c40400400d403903c0a004080e000c00c2000e810030080d10700741c454081c0b042040142500780741d0f803001101040e5099111411004000030303440e00a211004071036514010400008128034244200d00f074401c01d45007405a16501c003098811785081c2c2c5600680368000308002100d80b105003840f10791600051030710305101504007500915200084d0380c1030705d0a03911207840746000c1d04140181e40d00148280f00814403450110760036030715440d8030308004108211207407000c078480d616a08200b02400c8200000fa69480d60000c0030750356005091700c1152b1650900e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 277491879 1250 277490629 277490671
    0x40605010905061209010e0d120e060f1f05060d0917030103020a060522090203010806060904050607030914030a080603070614040e040201110703110a08070810050907030b0f 76
    0x101d00c50049030809000581041c000d10303011101110010001c400d290351764841e802d800d000402403500c17003d0841d01d5004941c00e44403510020b9641100f02d1014942c84501070280d1500d111080950081c2c01d0300440740003208041c0d01c80884041c50f030280c5d030f00c4a00421202d0103010950301505055214003990513515255504102c11400b092001070741c0310207811020440c45000e04024121b06100250790b03044d848090314035041008154001c2d07680320f51b000c4010b20110300c00300990354000a00f1900b0801c03e00e001c2c0e407043d030b40c0c00300200200105912900e4040820510642c400c40d12051f10b8244c030b445a01846c1b00800700042103540341d200c0e100d1442c00140080c050000c03403000392210301c43c40d45840c0c00e20171203160340b0a01070422810444401d40e0441080000c1c4690f00182d4415106400f251001c0030401c00d07407a000b5040f40710a604080340400031510009540910751038001d1020600d80d590101e0369003012010352014018240038400c2100c0010242015480384084141c2c0a02c6a2001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 277493129 1250 277491879 277491887
    0xb0306030c09131407030c0f15030207200a0b1206010807110a020405041406041b3002060c060901020307030f06050306280f090c17120304020402120c030604060501 72
    0x10f40d02500d207440d19070b28610203c1d8200710709802d111341d140c0849001c595070b5a16111070200c00ea01103280392115000c18000c040140c1071408401406150550801d6650f4aa0b18419460f05000c0e110489210494814544505083e4001466580c00300e50b12494403174000d00714800c0440700540084c001e1400600306034020001c407205805e0000c020729000301d866090000515015000703448802c26040d51004103001040f0352441144100c65001061401c3d104a50a101858000104010402550342003c00000d1851449400304141d001c03040100740c0003080d000c1c4034840300000c00c0e020f90310800c9414481500114054100c40c0d0302048052840f02e40c450480e4864000c2c642d0541092000c00d800780b49075030101840041d801c1610305061030000a0408441100c40d4040d806d507180e5043d00d080c051300c9060362000300100040030f94040c0d180078a0039140d045004050b94507040c0407000c10f0554031564151440c1400c0030503d00c06a09161521440c2d903081103982611031800c008003c2890b502c2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 277494379 1250 277493129 277493131
    0x10206070507080304110607050a0506010b0c0a061806020f120109022a10050a0c08010b120c030901140406050f060312190e03010c050702180c0f0c0a0c0b0306030c09 73
    0x189035a01c81c2801038958884900e54030151090341c0c040c000d8605800b40c2c1c1e4a04001f065071601c104002c003200d210034644103007000030580c480300101c001442000340c009000320700c00700441e034009000070340d902da0710300410f448840c42c02003d0400ca2001c82d54008855102c40207019010041e03a16440503a40c62108009a00c14450f50030703451029180c828070030514964105940f4440c2805980da015000100340d41240d004681c000c3c031103038a50024140e01c035000000240034211055100380307400690f04c503110306960042d00300f89041c0c3d000000242c1c510b4003984050791060411002045505060a26202074101941e501c0c800d886c651010070100d2030000b03035a5041040d5000c42c2410040807034070460340034600800031001d20491014820003940d0a108103d00300600381c484d41d80340e003a1740c018450050520303c68a8080900182813242c42072a100644002e038089071141c60703503404070404803402c1011054005003501d00740a030100d04802407001451040605404841d0b9070b404000401101c4c0380 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 277495629 1250 277494379 277494391
    0xa0308120709140d2013020405130207020307170316051501090902010806010e01090f032612011512021606150f090b04090b0c031006030608030901120e010903030f0506010206 77
    0x282602202e00103a44000c203401703240004810f6440e40c1e500703107021400c22082d19550242c116030020b014040d926000781f007a10500000c000031420b04002da40400d40d80d0f1030070b0050400d0034a90301e0380c00d5454441081100c5846000c010401000e4a803468040d071f80f42d01007800528208400000864810010b02c114421190141d5880c03075140c90301801075903d81c0c00041c1d07041c1006013082d004075400b800d003030241000b1880341010138181c101031205205c05440c00490a03103620307010001070035507101d00da24841c1034030221b030b034900d40390030030080700380c600030090400406154004580c2400386450008844102c0b40259001e104018040f548900744290303501403204c1d0610411000c1c0801500350340203981404000d0310002c0e515003c4c0d16800c2007400d04450711003007031000008204226a007403902e43d00501550405010305410002c1c2c045d240e00402842c0c80c10031480c0f007203205540380c03950040042e00e074055008024040710b604005000c1d0120b0059525035500748004510a5480021850f102d82c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 277496879 1250 277495629 277495639
    0xe070b0c0a03080601050405030123131208060319061505060f040b090a0e0c0a120c050a030209041415030615031c0201150608060405070c080f07020a030812070914 72
    0x4440382e0301034841c5000607112604008003400089170700d440900c03078140000d06c901058140c50390800400700f52140d0040c980e882011a5030105c00000340120b00182c40007500b4105100160358540109140807401842e015192044110748000d00c6401d9200b50800d00044c1c01c25039004e51580103002a40c41420b801c1c12100348100000c010400205000d455100c0000300070503401503480302034a5140c4030507079000d50940000070380c5032071041c0c100b010065443c00c07411062005d8082d040c07000d0b1550040a01c01010725800140802003641c5680c055120210700b007800c0b112600f005c0c1005c050304091405550300070300c1381f0004a01085441400c0602956008004000301040f030345132324444400074a00c07030301559200c407425520324140d01c0d9060003921440e5512400343c50f10b5010403080e510054031403414850b99120120210301014101c4d07e00c041440131180c0e9400c81807001c101076000580c0090000100450801e544400140c0d1030b81c050040c40d96002d9100b500d03000f440700d185107244100c80c1c2c05 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 277498129 1250 277496879 277496893
    0xc030a0b01140303040302100314100509040b1e101a03090d0f02070807060e01092306031e01140415080607080406140405010903091a0304140c03030d0e070b0c 70
    0x45021035a0300b594180d000340980c0c0c207207075403903020801c42908559600c000c43c1d200c0b20a045000d0030001e040da0710102011106910f0303454080450b0440c2e00103040545a8039203140011540015590f880140200c41000ca192a103000240e180e09100342d8001d84084032100003181c60805881c900b507a00038010340f07001d4840e43c00601004e07100e21140c0100d010960140e00306c00030b003042007480640000e02446d00d0300780c50002d0900005100c204a46c000941014001010154003450110580a401c800351001603a030786500420000751a0559000440480901c00203d80d0280c4c0001ca00f0075a03d00f5101401b001c100c3d0007000c040c118042c01045001c1c3d214100007010749110f0315809030400d026241c0060350300500400d0611048040780c040c0c0b1242e45030800300040561100008004085628051920310009400c502c1507100c00781c8003820b80c448800089000301000d0081085038900182103e41d02e00b00e91201d0005041103a0080206000e005000075075112210212407031890a80060091 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 277499379 1250 277498129 277498139
    0x1a09190b01140d0807060504030216140d03030b0604181d03030c1c1b140f0d110c0304030c0e09120a030f06030c060507050c0a1415071a04050c030a0b01 67
    0x8408001042c1580400c030036036030038003255640000700700c00b600800700400c09140c83c1c01c0184c6000c070005c04414102c20050402c000f864400546458900000c03038112021444608049015040000c076040c2c2c089000500059400310b56207501d422580001d20501c0303484805110110010b42e2060103042039002000000d01c2c1c64081c40050240c440c2c82c403002440707008041d581d00b00300c404000c000e8120312a040401c820f119041411b403066a4140c1c04e50343e180098042d00003005008030114160f03d9070b20b541c14901d0055078213003990203940c464000c03242c42c0c07035076401e01d8811401c5ea8401d01640d5014000400c030380283c0410880b02620316500003038036200100c2c0c0201c000784500030201f1003480d40c90308044002900150524010001981e81540ba07034a1814a58203103224814014458000d44504200c060b02c0c45120090f1000d00312544043d860020090f0310840c0b1999400800c3d40e140c5401a8240c800000d94050040f4000c01c1110001c0c0040014103984020003403001d400c00c4030210041107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 277500629 1250 277499379 277499399
    0x1d06060702100f090803070303021216140c03190c031101020c0a150f0c08071209020901050909030f07120f0309030e0f0102010605030a0501020315180a181a09190b01 73
    0x1410302d902d4507101a6070750317482061a086400000c0c0403000290001400301d283d6805203211908690341c8012100045070247c0c0182c0305e00040f41d000d00d00980007080e400300c142010703c182d80101c0d100c0e5000c107181d1034a404c0700628221202e50214049980c040c0388810000051081e200540c404000600040e1102d8440501d10140140c600807075030780b641c940b81c40f86101800780d0b0010440e551912031050a0040c40600b10500702c2c0044004246000e56080c0543d0b58124058110380060701c0e0440c0503100c03000943e0031441000745112303114500080c11070030400d4070200c100c00e20400390b54400e03201e04620f00441c1075aa07030301c10240004c1c000500301c180520f420994007e02c160140000142c00d5580e10103e42007409120040c0c0310769501000b00400001842c8000211901c2150200e00e10f084600008041040152401e0740c01c0d5601c1c25803e0300c2c0b5002d030003207085003900010844140000d903101c881d031041d01111040300364040d0941178508980c0f00404e040003140d0010440021747e0806071411 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 277501879 1250 277500629 277500647
    0x220f030305091e06071101030b03010e060402040e030c060403110d030203010506180613090509060112080703050706061a03160504061b15110304050105010b07020a0302010f0e09011d0606070210 85
    0x75001406500d03d0b101c0d5240c074000c001c1c0c0f80c0700300540e01c8210040d00001d0200c5821415550180c0d0616090401d003440c04900396900c0346c1c0c112000030300c441c1c05403c072615500810208081c68480c580034002455041044a01d203080a402160b00c3c0300e407042c0d4200c043c2d010038426190440018851814000e90450400850000141c03c00e4241003010b050040150307925806082401d90b11414402c083c40e061001c1801f42283d00e0611310b00d620b42d6980e61100784500400501002004100702042040c16042903004000d0010407035140300c0024400800c540c070039240440c44065021803802c016000307005840450391240ca441e0414205100203210b034a800240032070765400c900180840140061103820030f258021400c1035224913045c030f029400c540b010b821401d440351091149038016605d01000000b81e950a103040c1c60494007003081594040d092050031340d03000054000100d00311044042c5588445896260b00c90741da1603a00501000e4418101301035002007108152403246030040102c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 277503129 1250 277501879 277501909
    0x23010c03120f020a0509030714180a09050604121106100b0f040816031202010603080301120312052422110d060e060f0603091f020d02220f03030509 65
    0x20541558400c0b1076070403a4020b0510340c01199010a004a01d81070400030800034000d41014403802c0030f20000090340c0b0100d00c22420064800323500010700d100384a0703000038105550003800c8800c0c5045c18580981428000143c3c0e0340001c83c4071000c0301c40da20b400124180203c4120368030000d424144070250b000380c2c0c007181f1041028402003100141c00749040122305100518030003805c85043c00e601c2d000001c1500c40854a00310b80c10a4810310208034000116030441c1c4810460218840251400340c842d000070780c0b5036030022807810080200280380004225400d041da101e4003c000755401041000d80c905821654000c014000700c41c07801010185e10411840348000358a40c01d0140d25140d03a4181c8400707402c01c8100141040a1011504000a8914002e482103420509503c0c2800c02c180d03a500c001c49814411140006940c801251964101c801105500d00c055580341308c0f5031640700d175804500c090b514508003600c100041c000340c800e030700c9401e80394503658241c81c1043d00c008002d44041e00c0000cae = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 277504379 1250 277503129 277503131
    0x15030c0a0e060d0203070806010807241b050a031110020a0c141c0507031d01170408091e0307050f3a031d0307080a03031112010f23010c0312 62
    0x1100003685e07082004000901d40440105540d60406c1e000a040c01c01940c010351800d01680c0740501e00180c0080291108401d500d00001c402160151412480d05140d1000e4010700072007080005041d848850b1460079141e03002103628081c426414030040388647e00d1020000351885003010001a12102444a1408408116400d0f2800c81002151541c101007a000101e80d0024031401016004200c000400c81388000320001d9034608400030313240c0c140044510ba840086600000e0400c9000c9040d030b00040c00180c040e40c40344803080d00307200f003031510208142d00c244100480001e403413030b04413540c1c1803c80001e880428054205200d04516804c03101408a05040c0408002d0140c56000060030599001e0341e50a480c140705400001143d41d00b08000078081c0d005110203001c103000015080040076890f107000100721010001c900000d01a9014006048a002c80001028108103107400c00382e800340e0200844410a0b22854142d00041001c1240403440e003034000c4001c2030289410410706c81204c14 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 277505629 1250 277504379 277504399
    0x4140615011b0507080604030801050118060807030e010203090a050c030a17030a061215050603070b03070f0e13051e040c0e060103020705010510080d030603050c061c05010801020315030c0a0e06 85
    0x43e64a0030000d950f0000e1855610404c00c01090560041c50203005000a0a10700b90001d07a40501d81001d030130501405051200752004200720030300c2079000d0425049600021926401c00d00b214544802d540c0340141c070315200f2a10000060b1401140a41c00704d0781c404c0e01e489134140050461070042e0801850409550303550f0f440007510078809081c4001403446501d0449030b400400c030701c0b001140e102808540c065404460140880d4280200300c1c0d03003040c050b060464042940312421a100c02c6020402900305c0c11450b03050302e195880f500014080c2843d0700c03036000000b818070800d030700c1c80307074112000b03031003032006580030080049414442ca400000614002d40f4291403929401e00b50741c030607146590214003110081101c0442400381c0614030115180c1440320b83c0c5503880e0380340c1d1a18485e0465200702c00c001103482e18622402005030900c80320000030700196a580c10024000e400403110400320108003801c240c02c0f40340102d08800c04030002480d80f0307041400c048043c03001da04010050b5412240942c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 277506879 1250 277505629 277505633
    0x91e0302100908010507081603091502030603010b030312091218090415090f050c03010b01050d050606210601020d0903030f0c08040902070f02030f010c0c0b06030313090504140615011b 81
    0x3000d058490111b50f20744031814245080440b0500c900f204032402054a0000c0000c006203408c101100d5210b180c10001d078076900c452002a004000242d4200c1d4144800504001500030403600240b081d03c016056136090890180b86a03c02e10a00b01c08240c450700301140511320b4608034110301e803c24015401040325a802c004070b24111030032440d0a55080f40c01e05a42d40130010700b04800b00020000f50000e0002c03164020000c0c00368000e01d81903a19443d2074500081c40740d1210303030a03550b04007450001d514104030f035034500d41a4110152030550040c0129a00c140300107002c0e114000840754140c0d6a02c540c003a400d44115518208140100e500c1c40042100040b9200b0300d002400300c0071302403203201c0b00d010701c10720401d45495200307800480c2c0f1340d05150010203080e40143d01d084049400600e03001c0c50f5920344000070304520070410020f01c0c074101d8103000b1482c21040e03880701d84550721410182d41743d6403e0029082d6200d40441f00d8800c070b0400820826403551140e003c0000110b031206031030540360000c2d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 277508129 1250 277506879 277506881
    0x1020c010f1d0d030522060c0b130b04030903063206040b03031309051f05090408091306032a140319030e01080c07050a0210230406091e030210090801 66
    0x70303100941c0020b101003440341c0b1b50701003003101c844a212480d165090031440c10201908407100c040010708030300144400201000c0145809400d510b603c2080c02845241505c1c3c0a0501722a80c0001c1c1d4a207803619040301400003a000c0440e4a8000039000e40c0032403c0d103040d29540501004008540160721015140040d0301d0420142060340301d2100c03605896414070302a08112280181000041009440e4030700c010010781d03545506a0b0b0098034000e01d1592141007003542442403040c180e400020b400102d4030701d113006e50720050690340b058805090b8040e160042045041c04080f120b00442e0341948208600182c40e140380c44040750150554120011030b8502c2c201c0030700074000503030207c2d0001054074003035a40003851641c850103400f4180d050607059101c5968030300250000074010080d4044002c902030003003c0d081c104459030340c44007104206c0000b45001640041c030800b004540401c0002c0341d961002c000a002111250900c41000ea00d15001c0001c6400441d064505100704054003280300442 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 277509379 1250 277508129 277508149
    0xa170a0c021203040617060f01050a0203120c0d05070c0b01150908160509060a03120302090d0206030403090312032702150a03050108070e0603100f0e0304121101020c010f1d 76
    0x40200699212494444041e2000f94005c2c0300b00d010346c019004003c0035903904a00024100c8080ca00562500000700060786144104000d8003006903025080003410200039000307201014212109010030b880f0103500b511800d5140e000248014041b01c010b0140d881030000c5405902e8003072415001c030b01e91b6083d809003402d844201c07420079441030020a000b80c3c1080301c00250414000e440c502d03c035600c0e507240c1700f09460903a4040d000b01034000501d01c00d03651700c1c2c50181810680007401581d9074200b40c40c02900b034201720f100c00c480246a000d04141e200c0c0c024440c00c1084c000941400510351200d90b24000e03607129a4401301d03071201d4900d22404064860750050000c41401e514002400c1d41054201c51030030306282e100c000f0420070b1a040124a481c0400d80030380b12500741402084070240c89a2940203040281c0510000f4807010800180d8000406000040c1c50b010f8050a0030307101440c3c004a8680b0840d10030a40070401e140d0040f00064840c801034011544e00308840c0d29071421440c0000da0b4095 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 277510629 1250 277509379 277509409
    0x121b0f02030706020a02150a09030c080f01060f050d08070f060e06070215011512060905130303060b03010e0402090a02070c060c0201110c1c1a010b040f06020a170a0c02 74
    0x40804060440c01e00b00015005003080c0c2c00100740840d0345900007810048030705501410380e13001140e50205940541e5214000d5075020754402c1c0c0751511a0000d60781c0d03021000d0040855800c2140c0080d0f03802c0d490390708100351a4040c5c080543c185070342e01c83c00000da00003402142e10005040320700340460b0f8144140100d0581d81c0000c1d00c030500308804005c0c5010301d11032074004104603101c010000345c2c402900e0007810104604080203402511603e160052040d07a02055006050004001800c47e8182c03081030711903c261810403030030b5120000c2c1c42031404240904055500c24101017409403404038805640042e95433000741c41c9c140165108540340d405a03000001080c5400030600466030007030a0035050800b203d0003800a00e0900300007401c0d11190b0300c0f0401852040808120910590341c10900a40008090341c41c281d5035290782e200301d107510621503406500403052000c500c040c80070951305942604280010f20048031402d0f40342c0700703030300105070701c0180300c0c1456002d401611030040d402030402c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 277511879 1250 277510629 277510643
    0xd05070b160302060c210c130803030a0e0703020d0206070f060603030806090f0f0403080702100e10060b071214040e090c0907230f09062b0902010c121b 67
    0x2600514003e07140900c0030302184145072052080403a0345258407000455056100001603454554640140281c400d1406c0c4014140d8035040101d10110000000c5000e01c06000b020850b450141100036281c0c101404025031044841c030b940409450300502811000d0b0044d20069204030f40c0c2d83d20380c0111596540201c0c013298000f01000a107180c00300c01142d01c07020540f0034400b9860295220480170701d004000406209141e40410840b51081016650881900900f042403460060710181c2e00e08542000340802410b01202040300e03142241954961544034003089100c0104901c06c0e0750800c0380281500c040241030000090212904281c90301548000018000345084c0009100c201c0f07500514806c18007220715414100102c0c2e0003540c1c42c00068a0441c1074444583d008102101d1048030a9103070b1141e40801c0c2e192603000f1080d0390301000301c0803c11001c40605400941380a44058103400ba0100759121505030214021a001107401185813038182940060707200140b5104055041c140d5242c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 277513129 1250 277511879 277511917
    0x10204051002070e0c030108030a0f1809091b06120f02070606060f0e0303030903070219090e16060212031302040603020603010620010b1f0201090221060a09020604050d05070b 77
    0x801d1135419aa0003050300b0340c9552856040c040704540d82c3c400d91954004100c01048010724407889400203008100c4062013200d031140c0c0c4c0b10300e401c02401d41a5029180d0307400081740740f00c2c069901079200d41220203948440307000c3d40e800305088000b0305c0040d0020301956020041040015114842c40000d040944c0352581d28030324122000b0301102031680d00c140250f001f00103015003a6800000d43e00d40d00d80c1120180150002c03800725224415040d404090750504060311a190b4030f401103102c8803200b04103011104800d54410040703030303200f80308500c106c5110340800200f104038203144484054240050008a40b56580390301003000b0350300c264400000031703000104d024880204000b80e155100182402800740003520800030310b20340700002c074182208907540d2604150724000e402c45010580c000702001100703596420007150002c00c0003c21b204600448002642e4001148114018070750064600c0c1d05040c01c00081c01a0861141c40940d014420f4920000d1940000ca0080500c0911000f10380c640c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 277514379 1250 277513129 277513139
    0xb0c01051e130c091d16030c0b0901050c01020703021509010612020d052505040b040213060806030f010f0f060e091c0905090114011403040b04060207020a0503010c08160f02150901020405100207 85
    0xa04001010b00b1b510110804010804281440600801da480d201103203503440440e400182c89510030640b001d25a9400420194140f60700410f0281414602400c0c0c2e056036a51520310300d00300e6a00e030103101440d006800c1c003500541014004040e8507803180040b15859001e03903004400b00d05c1c0c0b000700717220040c0700810180a641018042c860480b03109540c01d50504590380154a00d824090160204000400300010300540d030800900184070010340080020721a41a0408050002c415070150705071700340b100c0021626078644246200300c0c40d44029201c500280c0389204005e002d5007c000007008040000851a41e0310b80013051f0007002c0744624202c400d00041d0024202c1d1030800d1071040c001006000300408608160a04c0340d00c00d03170000d401603075280103100241e9204102d421068040d8604644030140319003710300c05000c1d440d0209100101819400211221301010b000540140c002e07880040c20500103803149a045400c65001505003500c800120300100c4000ba44000140c0c011142044 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 277515629 1250 277514379 277514383
    0x10807050f19030b1807020c03010e060c0c031c0c090e0405100e2e060b1303030f02030f03040605040b0105030d0c020418050a080a1403040309050d0317010b0c01051e130c091d 77
    0x102d000d080c1c0c000c0c00801120f40b107460f13351038014242d000700900050b1840f0846418401c440c4410107040c00004520400c408990060a943d0580008540304000c08105542c10601c0d051207236500100610a96903100640706c050b080300000380b82c0902c10321110b0307200c03902d0703004150283c01c6d5002e031000c00040440d209003041e910342c0d620029855804200c44400590303d510841d040d640c05040c802081480710008a24512840e010f0741d051030008030a000c20403a1035080030b40140e004094010540c0d0301c40c820152210f0b4100e6040010500e070208441c0181003503003140d00800c00340803c0c84149969620788a00304000b0074000c5541120000d54249103540015603e11039984c81914141980307441d940190124540b40200e500ca078902c20040010544a000c1c0820241290064613510703503034501c1e86110079000651148001e50800b800200c103100c0181c507000000307070050f28109060311f421000d5481c1c1110103c050320320701c0c0c650502103020310b00d43c050702054000102c0c481e0880c22100c0c480b24 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 277516879 1250 277515629 277515643
    0x16050106121a070f080907031e060f1a01030f0b03031207090f0b0304031d03100c140f030402100c0614041e0209070302030a0603050a050c010807050f19030b180702 72
    0x380c84481c42d4184403815a10038410407200c40941881e42154031600d024526140c0c55920040940c0c2e42c08001503007136461926001200352240e001402010b22000d407900988605400c081045e500301401d03000e496100f03811001c82801070a100040084021010a0a6134001c19075481c3c401d20381e05c2401a02607000d0803c0e002802000d10500310142804040f0b0107510015001508000d00307160009162030480019141c0350314000c1c1181c00d810a40c0941030080c04818112001045000d02840c40820441080381c2154400c0d1444a140d513031107a0030092a050918108820441d40d06100c4c0001615403152144524220403805c04510b8145048528410b42c422001f80340340300011804010303110010313910340124541c1805a00c035525808020020000742d40058014071892102d48140400032480050b00388080c2c1c2d42e60956a1350680665840c441d4111004c0340b440700704a85a0310308510341c000d81017600f035440e012070f224171218000b070068107502414030039a49010041c0180e03150100008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 277517985 1106 277516879 277516913
    0x81009090c170d0207090c030905070b0414100203070b04030201180812010501050c03040311031501180e120a1803140312060102030f0f1605010612 65
    0x5003014040c80b421400c02d07820211600c0245000c1040d039401c10481d001481d0a91030600000c0003020001840000c0650354140500000c80a0151030018005200d071b0944440c1010225420064a00081482040004540780304d05d60080140c0700c05030b401c0000c4d00940e07515424264007400c59118080312828028070040d0401c45e074030b405455040c440340e00480d071310787c1c0300c0e001512a8480c0f1280c17500b4070b500900c000c01c0040c20103480c0c4082108050207981c03180124101c9074400d40340a030070450f81c804100b01440e69042c0c0324440c103c207984044000b0641d407510403074a01d246101c1e9080c0a010802c0310340d0410080580f980c108001107501020a035101c100003c0c0d0a03489810203400021298004008104035610010a0f101c4904c1e10780c0240780740234440d204008490740180300703141568800403508404a0030070f100e0400100001c841100e003184483c60031440001c681450 = true := by decide +kernel

theorem cover : BRFrame.Cov 277338129 277517985 := by
  have h0 := BRFrame.cov_init 277338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 277338129 ≤ n) (h2 : n < 277517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
