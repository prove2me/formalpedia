-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1116
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:18:38.500981+00:00
-- url     : https://prove2.me/submissions/28e181c2-f7d1-4914-b753-c11b1d4e8b70

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 200539568 ≤ n < 200719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 200540818 1250 200539568 200539583
    0x1006051c0f060b130e06090c070807061a130e060c0f04080d05030106120504020315180f030301091103010b0403081e030c071e0b150406050904050f070f0b04120807 72
    0x110722401c9840c021306011515001c1211540c0c2e880402d40c9283c0002e0f5195544521408041071131160140060306200b80500304042c0342200b2640c5030b408440c0a8a544c00004054840c42021480c0006081c219401c0b044c10034042a80c0c02c008443c4c984200600003140140003041d034440c03070101d010940d005000c000046070a210800e4030003811541007445010001085c00e40010b82205c041d00500e07010b41d602500500e100d41c1a075410000d8040c0080000f118043c8a103148200800100a5240d91200742c4014650301c1d4100b0242c0c1e400e07034114003096003034900104010000880c00204881c1201d80200344d90303803034901005109001681005200f00001d2000c01480b02086115000300212403103070381403c00141000300c44080c014112030010304041200310005a041c106051135010706407000300b00103605501c8800003a0f07d14010340303040d1040c0c0d010851468481404001107000360280812248540e864484176a80a00c202e00401210301d2203182da14040082d031030196042603901854 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 200542068 1250 200540818 200540831
    0x2a03051512070509011707121109070305010503061f1e031a0a0b04060305030d0b06040801020a1119120302130b040803090f011b02090411030f151006051c0f 69
    0x40c103a50b5078100c0c1c09551311134150300c00001510402030b0494060f03650311101401c2d1146c0b81c02d000800c0010b51032002d03500d182e1a111050b20b640c1d80c07104040c0c030031450383d00c0c000342550520b020300d45480c0b802004510b408600c550303903201301d114505200084805032140089100600800105404c030b20384d200038052990812900485294200e02c18454001d02c003040150300344560801040d2030141c4000703402908208091800101030750050b980c080009030105140a940340d404600f241d00c4102a8000034210485012040d40d003488015210341918261001c0d068a50b100e10b48020702d00c09100c010300d03900080c40905451581c0040c001081000311507078a80e59a06407417a00c0b50300440015200d0300200c0c0701e80220b58010070084843e2510b81124640b0341e07140c2c0d0b0031b0016000020b402510f240507800c2641c3c01a42c1c08002400e10081c6210142c004070301e051004ca60046c0028040c0700f02c0e8116000107101c09540300301035880507600b200d000c0d04c4e1440104901c0c8000c2c4084103194982904044 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 200543318 1250 200542068 200542099
    0x50612011b080c0414040f090c060f090b0307050412050a0c1203031b0e010c0f050712120804122703031d0102032d12090703062a030515 60
    0x39480d100341020b8545000640d95440aa200340c800d40c0a030001145d20708500c41c0140c185a07010081090a501c4000f8041c40240c858039107003071141c1d0100d40040c0d14688000080c07541701d038600f40100320410038a030450902d410b002e00180118068124940c544070415018400200940c0ba4240c0e084681c1403615900d0b0316090760703000803000307040d03001c2414000340d0441c0c040301202d1281c1800490b6207500c440700d44d90004680b641c0d1808000d68220100001c1c0d6404503c09214900080189640340304108c45245014020740c1003094080040c03211482c100070101e003460f408820411064504006020070082111070111410007a00d03507210503598001c0101900404030750641c1c0f01340508403500300905001260f0f244107100101004680c01103803035200c55645129844d01e038901003080b900706020084c554808510480340c52038541e100f89000c0040c04054414a0301c00f84860403000151400900780410f004900d18401c0105950f41c03000500d8441d000c04080003003803005202042d21030164 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 200544568 1250 200543318 200543351
    0x91c03020309120d090506030910020d090203010e0a0c030807020d0f050d02070f2105010209100c1205030c070b0402010311070b0a1a090109020c010b0411070b010906050a0905061201 80
    0x1050010b004101c3c8080ca000201d00000d85500c15814981d1141c07941070408081c0f0000c2d42002c0c001810301d20514445940000a5001510040e0514840080d0b02c820034010542901c480f0001c0026a4100003c03580210307941070245010380c0d800c44042ca0b91b030380d481d10114000e0030031000c4c06850071750403031010001c100b00810092140300c9503130f084940312070b15a150702c02c0d060b803a80300d1118018607002d0181242c40d0a03014444605018100050800c90501c010468019a00200d000065031100742c280030041d254803031900e46c0c501450f100e401c40c80c0c4901840224414510060700310b41540000504580c404e801c040c88c40301951014540b01c0f032981c40c04c0310102c0c0f410380d03590701914240003091205510034488030150b07000090190b1881c5e464001c01c1c400942c04004460700750b548034819602d85032201d01996401070000c605c1c89540f1049400e1081c2440700c180c100419050600800704030030764544d08079000f5590101d10001719500e0b5900000d14416881145090550030000c0710307505040c0a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 200545818 1250 200544568 200544577
    0x2a040903080414010203010f052827020a05030601030902030c03010c2307020105310b0301060e01020c060a03020d09060908040e011401080f190e060610050408030f091c030203 77
    0x344910070101200781c1c0c03d4500740e000900030b400d100c00890204201a2422038284131710840504625803002c0341543c040101044181c2060301031240c14410039058400b2009400c109080c10b2a00314100712099100420310311000e04000d0425444d821b285096580074402100d4485c0020001c21a6506014014100c4119045c00411a4800ea9144000d41d03484008540003698169501440c02c1d0391405200044640c0600300d1030102129282c0310028100a07035140701900743d01c008640c42e58074041001b000003001702821411074100d881c01401940350042968408030642c1409a181c410f6a24480d001301102c0e000984000d0408190300c0c24400d500c4010310a8441041d541c800c543e032a000d029030100c07120050070380041d1900e070025800060000b155500140a5080c440c01c10440003140001c0d5040410030900c25007000060103218509205000000c2040d8141641081d10700303526a42c5034000c401034100c0d0150300207143d420715542c0c805018041818407401560300240d60038025941d802 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 200547068 1250 200545818 200545823
    0xc1606021605040b09010509090304080a03030b0f040b100807050f0310030209011a031605040b0c0c03010b030f100e0703080a030603120801030807030e19060206060f01050703022a0409030804 84
    0x8900004034150405015013684240040d0403a50241d103040188660b00100078401985030100340000b0450032000d100d60780c02c0314040e0703401041e502249010014111f00b0061120300c65413078907486084545031400c21349106945400d02942c90b030b54814003a036583c80340a06a8842410010400200001d00344408050701c0c020307a01101e05a072240c4d0307480c1d085100103070081c0c030340c01060001541d090303605c2c03400c3c0c03101001030724109040540e1502d03450786a4202d8041c4041e40d4009000d5034105003800d00c2900c402c0d034000c0300240402d0340e440c0c03000e40e1030b4000008075030081c0b5196864410204130411148000f503920249850743e40d24800001402170500e40011200d40c0024017038103000c94801e00b04103050301d405c140300d5490a81d07107590907207800c00307082d09694001b140c0004200700c448400104030000d1002e80c018046030724004082045101071000300b281405024440140800ea0014044442d4003204142024220f804000464202022024154007900704810720080540c4000b580d800b075071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 200548318 1250 200547068 200547103
    0x40204150b030f01060908030d09031b0305030f0906060d08130803030c0c010b010503071d0a09060b0702180906010501140403020d150b011707050d020c010504121101200c160602 78
    0x5d8881204441901c030603c14400a07038030900c070511022200381d1120f128a80309050183d041c11412400c0d0020f204591b006802051010003000300454072100362507408600800681603501d0a40001081a8030b0076001614040000c110313074060b014140d400c240a4100c0c03408a0741c0320b1500f0b8a20055a0384003c03280302e042d5082003128030603940568181c90168a550300c0b41079020840a5031008c00d840401c8088c0c0c1d00110308400007030743c00860311a60024000e01c80c0215980c0a5a00501c916409024150183d000c0c0703103c1003096080e800308600c1c0c10340d402480e005200749512001c00e10700c0d014a8002070341c040c41e8001038100304140000e02c1c84e40102903140c00e00800010b000155001c00141c0c0392940c1c100000b0000480a52182005000311000010014100400340c0c1d2280e084510446040f0740280c0c406d000c0c95000ca0700006d0400340d800d1400c00070b101c8440b071904a0100b00c0c4440090b030540c000d021801d01e030038580038048120b000042800075041c1550390f81000b90b5980002c82c02d1501d80c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 200549568 1250 200548318 200548321
    0x4090203091c08040c06030903170a02040614070b010e090a050d05072108040305091314070e060414010309061107030e010807030c080612010617010b130b090f040204150b030f 77
    0x383c01203c56621407500700191300072080c43d200090b0050110007401304c003008680c0220302a42e071103000c502806a80c3c040e40068903241025005402c0c0451000c4054030762006000394000034542c03001c0b850640302410180708c02500d8610019182c01607080c802040b86c000d0680002401d94008050301115006081c01c1080c0102c0341d0001440400d21020310000407a500005000300740180001d181309100508010283c601c154905811103c41c4900c07054401070000501c000c046e40300e0000381045208680319850240740403401e88000c003032801c906050680f81c80701c01d014030840f03502029005d00410f0034a0b60313402d0365240092007500c03900c0a0343d001c104000041800300b4480d205c1c2d54529107c40c1c507101e0321500e074101040708140460352071030740542d00c0b42c0c404a0010460301041e03c801c810080041085520141040078280e03605005072209481e10703903110780a41e11001d62582028183c908000d0319212070002c02c0140c030070400c10800365107426200042c0c0802d984004d45c440c484810080809 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 200550818 1250 200549568 200549623
    0x3071502181507140c06121009020426070b0d0c0314060f090c070204110a020f1f05070c0b07020a031b0b0705460e011409060409020309 60
    0x302d212041812822140c244020320006513030211200f002c801110449441141c0d920002e900c9070b00a0044070700e0b4a80c1c0c4428040341010507500c0070094080c48000790308050400000011314400c69801500c80c00c010903d5014140e000d00114026201882407203a84100d01d19000c00070705002c0484500080c60001428034605001411902585000304075050548410007001301504000e81281c50141003000b81c000103030f94a1060044452000c060103469801e8103801900300454500003840315004100b004a1000f202c0c060250b4030a194800000c090300c400070704684030304007107200801560303c24040c040199000142110450b200c0d668040714544841401154840c00100c000c1c55068004081100d01c0d00502c09001041c0b044050001c402040c00004440d1011141e410030010710300901d548010300d10f06035204c10139102d609100c41a240c20000081c44981004ea01002d02400800c0c5443c2c6666150308940c01413000080540d181c0c201640002c1d2038000000c2000c4001540501c403115 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 200552068 1250 200550818 200550829
    0xa031d06010e011e050d060e06010e09070303030f0e01060803030916050a0b07030c0804150807021b0913060515040b0306040b0105040207080705150f0a0209210307150218 75
    0x10b03240e00c1020074050340d03c0c1a80005040c40b044e22a400c0600f44000082040d4640000841000f40038600201e80c1d421820701c09803d245042e040940480e80b10010800e04001c00030303007142200c0d8035107000145149000080c100038420800001429400c12100040c040c00010140d800b0710103100543d0b0030403e40883c4c04900c0d82c003030701c54140c02008000d020417802c85d2001c080c210441c02400e184800c042d050b5614005036000b500700644410f0003400340c60b00daa600c0400b69910940c01d000402c1208a02d0b00100d00902d04845114800d00702040003c08440441d26494241c6d039200d402481a420b1034141c05001b084102c2c1d14900492924506041610300056524000c5130000080d060381d900300030034040a5806175800382c84c581c1d020017041d00080c500304940b03160040c1d1602141120b0601211b59080b6a6020745090307406401800301c00400d039075140300c1000000b02c031840c0220940e07901120728190f0203081c41c0a0300c3c0078040c588130000c802440e0005c3c1300c421907200d0121041200e8108024 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 200553318 1250 200552068 200552071
    0xd0f050f03040602100b0427050d050306010815011101091a0c1c090618051c0302030714091207080303070212130306020903010f0204060e12010908030f070909020a031d06 75
    0x80050b800b0f540401c2c240b2069510071821803501402c00300da5480894464101001282c82380c01d11034202800c940b051000902c0381c01003015141c9000d925505100c000207000500103485111101d41050f90401d40780e0003003140d80c00703d11505009103c0c0b181181004c03c0142100e4150a00d141d42c89800100072040c0c8a00300c5940d9142090944088520040d4100042918080881d1003641e2011600c00c002c0e10040d0313080115114400501e19510650550460a104d1700c0004060600600a001c11190017403c0384690301c0340440900d44441c80c0b01d0011300350311944005171913180941c040c08602d80c0341c0840103500c2035549400320b03004c5401d42c40c00d0210500c00c041d08c101c24401008001d000141d600e80060090b400002c001240003000c0718002c80483c0d10640c4400003040240003204041e0401c0381a01a112017980001c00550042e920340304a54400240718032a69241940007804041c02001e040300907003005142151581c0e90b481025000f00010010200d9680550b02e884001c07250004246 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 200554568 1250 200553318 200553329
    0x5040e0a03020604170c1c0e04090c060509061b011b022a03031b031309020403050a08161410060e060a0b090402093303090307120309020d0f050f0304 66
    0xd0100360b0751500c0381072005c035410211440010b8104800c1c03200020070042203e01c000000d003003000700038503550043e001011070350a85001d00d003010510008105e03185209001ca41ca141003965503a03c544000a04500c14800b520f26851036031070280f01104015801500140200d1085a85c9094050b0060360f0360080344d5000c014028011540500c20000c1c54400709991a026044a042c0102100741200c1c010044a21941ca035102240300440c002c40c609801c0c0051205030320840c500340c01c5403500d9440e51042c030000341c8403120005d0281d8071206002d01602e1090742008410082400d89040c4949505844014149140c01c140c400302da240400050f4034050f1400900c4411400e03d400800750180c1c000f10142035200703500703110355202d42e190301c411242d0f4a01c20101002002c640080c00f43c1c0c240482036070700f100c010000d00c1000412032002086a410035044a00292a4203903844100c2c0a4400894003d41100207912440100451103982c600158030036000e4030714020600d2502607482c06a403054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 200555818 1250 200554568 200554573
    0x4050606010807181406070503030906072703120c08030a020301180b030606120f0d03022706070b040f08040303020102030f090d05040902030a0b04020705070303090807030206030604050a1407020705040e0a0302 92
    0x200560000401c0611795064041c0c0064289080b603110700e82950400c4a01da80c564010504010036240d0058a0508080d0303410a22140c0100c5682024180010303808010640c00455018006890149050f0161268000c91141d5a131802003000700182d0802c1c42000c0601341c410005e00f0010086010300990910050001c0c407083e6160700412080703810200640f20729010744040754248283c10320860707025184a841c050398602d41000400240018090ba61100c0405441c19000a60707422003241c0403139402284011054070b860404020a034400a001080307441c00040c004100340d01034014610440a0b00c1ca00740302983c40c0a1916250401da485441c0001c030700b08011310011480b036010355000211f21074001480071001000c10100d921070041070307949500c0420104201580500b10700c000e09221030107090401d1940d80800c08600024080c0d91244d51217100051441c043ca5000030101501e000404405091541c0041d40300e40c101e002d600d008504121b281c2c032800400240d807000031a0306600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 200557068 1250 200555818 200555867
    0x30201140c1204020f040f1406060301030503160804080318010e030a020a0504020a1b03200102191b06110c160305120309160905010e0609040c03081c0504050606010807 74
    0xb007040c14030001070080f40e0203095040c5002d103a4a80784241e2040d14000c0400042c20000207031015401100107102d944960000c000502c000b40021098441c11000c4c8800201d0000b02d40c44c003510300c2d01507a00815200d02c030200340030400400600c042603596400380c85800c031825188007411b45032801428080e40100300d04030104882d007402d9006200315240740c5003680f501a07131000c00103920b40300c022090300010020440d6001030140b00320100e40d6603c0d880000c610b4290550042903950303810030601400d004c501005402601c2c0050500d0000b140e0000080142a10980003035006400003030320b0030b00510440d9848140c4d14601c88104066a81260050403000555140508240c0c0010f041504a000b12000b80308009030400740c20000d0004c90310042182d604248105a42003c01802284030f003400394103000209407800225015030390406d0b440e503501e402404260711b8000964a807810b5940c40c107000c000500c0808180c03a801000c090f41c0e00221612820000c407000c000500200c8041c603070b0700c17a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 200558318 1250 200557068 200557087
    0x12060b01110307330e030405100801080a0305090103060b031f050114040512120f0c010506010806010c0b0903090d05100e0601051503070c0204050702010c03060b0a120b040207020d03020a030201140c 87
    0x210f1468108000b100c0f05588102c0c0707941301080d070301d1190185036154008030b4148030a103000300318119941011f14100c2010b40c5481c14640c4d0b6030920450140c00d000e00011104030341d034407a40121015000f2000001d0ba43d041c001c008160b1000c400c2d50054440c0c1c5980303000300d895849180003403035003004d505000f81003a04180410080040c4104000142d03c1114041c4a500b43c07441c02800c098446205c3c8243c95040304c031160360170350700001c03c0141003140e5507007044526a040b4214a071140d820004088a507560f4005444c070390322400c01042d50001704000a0000c010000031a1046601c080109118441400c0640c9540300001e0007141c0e40640c10344604074880c50844040c44d403001251900800e003001c42e0300071400b140c2007611610f00513512820b2081c0c1c41c5425005000c014030400311007501d0700d01c201d00c2c024441046004040c0c12551103e046041543c0c2d40d4050b00c54060b00100345600744c030205e2030080d40d6044901c2e0110003550070a000c0f648203c4098258a01c0f030310300c10031001c0c034210180 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 200559568 1250 200558318 200558363
    0xb0c0f09040f06030222061d0a0e100e0a02031c05070f0501020d05010303030501030b0709030210030b0a080601080120091e13110d1a0a0510050412060b01110307 71
    0x2240840d51050f000016a0305c00200404481c01390060b20084040d005558040d910b00c2e070803600a0414080796018848020b92801d41c2c01282c071207001500a01aa001c0b5003404a680c5501401c00d040030b508c1c0e6070494000c204418a60b200314110341c0401e15002503030303403d41420a201004181c05000e000c002c0f07240d000c80c081d06644140b00062603d100043c4070000c68400703070015070000b95a07100600802c2115070003550000c501741480b13400d1514590000715100d901d1413080f0704040e12a8880803031034503103ca01c18050440802580c05641c3c4803c803150080036261060b0702c40d000280c200305506100e1208580d003004e000b410f141040e200d84140d202c4800451104240c020058100c204203149003442980d00c1080d0130b0713110980d1481d0740c00040003542d00f80400349946000c1002041d040c0d40e150180041200d6099070255007a4102400a4400740155400f0805815056010b0010881c0d10b81c400d0f6032018003601d9030b2100d41c4008500d00d41d2401091002001009000c0e914072500c0440b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 200560818 1250 200559568 200559581
    0x90f0d1202010b1f0c03110f0a060617060c0c01020d0f0c08011e0b0711031c0305010b13090903020c060304080c0601151d06090604030b010306051b0f0703050d060608040b0c0f0904 79
    0xc0c0c00c01f40c0c18581e0b484040391401c0607810104080c1c0d0801011074003040801c1c01984010460900314141c42000c0b40d19484d1a000080c01402c40d41b40000390b01000e0440039010b4401c640c3e100c00341006144001d1000c440601a0b03405a00d00080c10400007042510013a40c040d08404402c01810001c1402c0586031107003540525402d40f55402d1b01c80e18080070380c0d000c015840210041009040108880e030501500351481a000019440c20501c034800303601000d0024041110410600440e41428a050913418400c070704100c9500720b41d0000c104024090100002c000c1c0020010850740345a03a160951035803000300b02e61b40e01c00225040400300081e1070820140c813a5003001081c080c90260000e00107145503216500c00c0354002c9024004100f807043c54440e055010003186010b503e5001751209021840c45400c151100402c000302c0d140061620640c25907842c2240101c0070001a905c3da10050400303d02141c00700c034011030300000500481c030900213484041d40c0305103129042c00c2c003800030040903010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 200562068 1250 200560818 200560823
    0x30210020906070b090a020301060f080c2106042001020105010b0a0302030907051f080901020301050d021203040e130b330f0904080a181a090f0d1202010b1f0c 70
    0x9050000c3e10203d0840c0152900840110004003021129481410b09664180d8444504040d00d0001009001008174035140350740011155140c5e400303a1007042c80e940d5004046030b40d0b0144203c908100420031000c040d0911030070702c0080700210780d0300700004900b80c9109000d000c005807001d20065000b603010341c01454000c145001503031903c68030f41011403903800800e45400c401c00303e1500c1100009801c1021103801a200c58001d601e036604000c08581e042d03054460081c01105070514a6072038130b030140155005004040714041c11030401c480081c50500300410240c1c3c0c080c40f21800328465030310101c0e29210074040c00078550b00400210300305000b0032840269280e08542034110801301e40d580c1003199482240700d0001c1c02d03100c01748054014001e6070a136a003256400e60300301c011b00400901103250400480f620139002ea6488490021036602500c610b032030368001c6040720090b0b04100318079040000b40395107507008004081d0304074200401070b400c080006030701d8001200c5034070045100d041150034060 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 200563318 1250 200562068 200562079
    0xa170609460b04030e012304030b091609060611030702130b03191415090a06050c0910020a0b060105070209010e040305120403030c090608010321090807080307110d0302100209 77
    0x741580c80300c14038504225030440c0020801003000d4515030708070480c10701403840c00003d01d40030815090f80701c0007071107280000f0740300c050110009030314200304002c074031441e50390030b61a000704070380d2500380070040d00c0540074804c041250400d54000103000002a05e0104c0d8000b41301c40d540810031480200144014007805d40c050040703130704488407041886542c0d00c00620843c240044942d000c0381480c2080c802031212a9143c0b1001c0c140080301c00e00082c281500d90f00030100103030341c2e1507021700100c881c45400d18080c1c1065101624451168000c00d0314405a40105039002c0d981d5500c0004603580d00c184040294440c80c00c0c030040c0700c040c462100190703209109081451406d8002000c00b1401941110b04800003501c5948428549600051f094000c05080c1012130155045680d18002d40c001a00b9a2101c00281541c1c003010504c0fa00310f60008094500c20350784100c1d02c8900702c64070f030b0344030140a5510a81d60420b8044900301031518070b4159405074040c1840d9900030300600041c1d8000320850340e028 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 200564568 1250 200563318 200563453
    0x3150f190b0a0b0d0c02030405101d210c010e010203070308060a030218011403061009090302070e0106030b0a050315040b13050706050a031404020913020a170609 71
    0x42d1144840d28014000040c5815160078540740007105460011000c0c03800c42d0801c1c001000241c03900300b601020100a81441203007140d20a991041004895030303c20b5010728104594242d19981b01811a454940031040e2412a00842d00540300743c009901c803180141e2080002c500407a00c01d210a50300310200401614010b270341c0350001050780c600340c03010151060b5a000101b1080709a0500050036610940180400740340007a0303000d11801f2644030703001003291242894000c041c42444458040c0995121004140d40c41e08002402070010301d210030b000d1002294045020701d00000c10201d180310104040c0a6503a4958400503002c502510000300c00110304d4074100014420321001018003032607a501c0d81c03903903000b03d0f0040a80d03241301c0c00700043e0f11001081c480940c4880d058507038490810b480c600714104c96880420960211640005002c04001c18409004075022540900442016048400300600c04000d20b0481842c0354412181c20103c50518010000704122900051564226030340c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 200565818 1250 200564568 200564591
    0x50c1210060915170a1407020111040509060609030105190c02061911071a040308010b07051506030c03060103060506010f050f0d0902011101020c010c03060b12041401061d01030203150f19 82
    0x100700305498030ba1140f910b031980740e086d5225034070b0310b03e5205000f0310007800714041d0102d40c030000e440780e802032602944e0104002112611500e040309ca02e4403000c0d008000710b20f0440070440e80f80c0c02c8402806074503820070303001d0f0703826920018425005031840c501082e00d1185502c064001410514180c40440784244000c0e4041184103610804034407441d80ca04c41c0600e40b616004207007150582104000700c409101200104400080300020094030b801040003d40741c54000031b01c0c003c8407180b1958113102d900300102c20402d664110a0184200f070722401c9000103420800e032540c1c081e9480300d46100340180407041c58207419401103c503d60060400881103110a40c9a0b42a80e0100c0d1803940b980c0c2d105c03480c900c07406504d885400024580d0805030742c20041100b030320314030211010300041c0c008020004144c0710320000303601100080108051001060001c03042d005040802440268864007c018800200540c20f4105602c6601d11004bc00d800d0341e0f400f01900c81c034000003004144140d540b041107050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 200567068 1250 200565818 200565857
    0x303040303020a030206240d050723090a05040302060a110d02030a020a080114300a24180f060908040b0903070f030302060f0c0d050c1210060915 64
    0x5035000364007800c44450719003406445d1610280c0140f00d6800c04001c500040c41c8200c41d0b110141804480c8800d4a080c681451881e00d202c1d604041e84420020104484481d6030460f40c2d0861801616900801d030b4450101d04120360040310050050b801c403900140b0042483d9001d03000842c00074071060300309041d811000341242c00403100313020942d5000a4180f166900034240700d0040403a10340c3c0324100c0018802151400446484c4a450b03a40c6420f1048242c210740001000146484d2085030048001810500d09401940c03044882c1d12076800c4000b0b125603035501480c488420517070102d0010160590362200d068801100a41c0e03126640d810070b100054524000300000c1034001c01042e00c070f040100c20982007040c0f41e440901c40d0241e9280400000781c012643c194480c9500d0141425503503101007083c0c4900c241070801400502d44003c11001840c0716000c1d001e01c038a2040340040b03a99480b081040800124040c9502041600c0301c2000000c0c607444018000c0000307858580d07410301d0315010065 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 200568318 1250 200567068 200567077
    0xd090602090111060c0d0e070302040e010b1504050303180609090709050a050301020c060105040b13090c03140303040302120c0f0a0803010303020f03040f330c0204050a1e09110303 79
    0x554040e00018145000d40c1c0c85441d03181d961000d000030744101d09160000c4070742845a040da40c12815107505900214840c02e0000c100119000b90062101c49081c00d07900d402070086000b0b031071140c00254031040807200d8810a0700d041d940c0140045190800401004110240040e1403507485a810440c8040c0c0b1346803850118068070081c0c607a00012030810081045c1348200350030442c0660b01c1071001800000d4006501c5044900559001030146051008100c030340c8610302c01000703414100145001001681c03018202128001e01000c1c580840ea01a0701e602d07440305507401f400591040c24a22180b440300d0300200b500a503c2401c0300c2120180d01211410302f181a903042e1a41c0c1c4001c4010002cbc5274061210b05482601c01020310310b0f1904003e28a0801c00c2d50340640000b172162510402240315a2000c004042d5015031a604500051050014501982640101e0080d4201070100d0444155401071840103100210f1010615407680e000308020702000301e068410540c034458446403510180000d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 200569568 1250 200568318 200568323
    0x10302180415051c0804050d030905030d270810050703020408070801020306040e0106060212030a090b16031109010507081e0c0a060606020601060c0f0c0b1c060905040f020909030d09 80
    0x10300e800707440c020411071036013030800d8a10035251500954800198103002120142d920440d6001c802c41541c4c1800c40c0c0115403a04400d80500c241e080c9012482c0e0444a051500314070f0314155842e600d0700100103503d58015204411301d552100851101d00c0d4815003269502007185c2c980142415620020240703018003940c01142d02d0b0350b00006100c0340b0b05207801805415261080244151403412600a40e030700040329401d10012008800f0412509140d0003098a19400c5000035940741020365031070300c0701c0520762648404a45400500414189018140c44d44800141c55650030004a500e801100da03100c008441d40e00350301d900350724081e4038841d005000c0fa600c040005002200041c51f0407011078a040e00084155400180100072180c0d200f18034107003240d4802140c000d05016072a1034928641c0e1600709403405d42020034010705206038032301c90984400d8907410501003d0b0740d44105204585c410b803000703442c44980070391140140c2005900d0700e0300070b443e15040324a0b250b80101d0303500440e41144000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 200570818 1250 200569568 200569601
    0xa061d0616050c1c1509020d03090e060108040b0105100903020d08040501081003080a051810020616110c060c1c08041101111c03142a0c0c0103021804 66
    0x7810920000b0405002040801d44682c810790a85504144400d099050001c1c008004010206151401070f0041c0440c564050003808190007140380c060a00d52180c0556800b004218001665562107210040c0c020f0340c00a000385001d07402d110500440554041c080030521540360000401600c4c1c042c0c441c1c0410f4020440540c0356800d0000040400401801e5490910300d50700050000c160140111000c1c91041d0404580c1c41060011915010790240343e01d5500403544400c002c481d0742c011903114400c81c4003c0c0d84a281c4105070f501940c6030b14460400590750303401000540064184100180041c1d5190b2040358251400c1d0110240800c5c886013050000458440c144020018402c4607400282ca0908180d000d141c1200003d981d209101c41060061182c400040c48240b80242d002d489101040c01d4800c0c02c52074101080c088941204027000c1c801d550030b2406070000707800c0d4407e40d141a0761684c083e010038502400110043d4024041c00101c440b0410460307803071550ba5104003140300207032441 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 200572068 1250 200570818 200570857
    0xb0105070819180b03071d04090c0812120f1008030c01060609150c0b0c0c101413080d050901151d06092e0503060c0c06150a061d06 58
    0x300140708074038219050002031000c15050044c00120f90590758400c46c549032414030400600c41040c51140305140258106103068028410701048940c50410380e5000700440b0301d4802100403500491003061000040c40380a00d0110701010000760041e50421a01c0c0c0500180301c0c1c9074001c89082d03522524001e03242c2d031341d260010450a80c1007003860300240b02118520f4948001c022000c4c29105000707030014464141400007911103600b010a54003088003013003c581c0d6410140c02d89000402070444c804c40c500c5600030008018244e21007050919903072140e034032400c1c809100f90100103000041c1081d0215525614107003c3e5040c2c1c1c04200c2c00400c44043c29189100d10404071480c0c80e20042c0c00c43c2d0081c0100010030000910855543d0300d000900b0280c0c1ca040c1004401c804c040340540e400980d41805504d080c410b2880101c0058022001c008080e02c180d0b84509120b03c04e600c00e1030100740e41000c90444d0030040c081c083c28105100303040c1e54041d010f4130400d00000034110b512146030313201c21030f81141 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 200573318 1250 200572068 200572117
    0x40609080d090b0a050c01140a0b0a090c0504050d0501060e070e010f03061a0d110403030c02030f0a0302190318060207060201060608090a1407120b010302011e09090b01050708 77
    0x41225004541d50030840c0e842d50400030701c0800c600c00e0100b5503091040004101e03900c0361007584030101c1c1c6604510345034924100903031003001038400c800e10b0700e2041c400d48502041c3c0b15040c3c4175a41203010f4030707222540380602d00424448004103c14094505d550303209000101c08041d850142e128600c02e0340c40448540c011000500548480260304040600d014000c1c40441000501c03886007003103004003103858000409a80002e0f011214480c444804e001c507000042680105410030782501c2281510080c1090404441da11190f0380405401680f209003d600c0e00c0c40128491148103000c0d180c9448411030450112080014940c815001607000a50030010554280720b000090026482c140380d80381080b403052903a4500118015000001420040b030441c0380400420004100aa1011031000d880d4188514840d40921060340420305104000d840d2100410300c11400c610141c486c10840c0f81042000d00041508030800c5041c03150802440005c5150030018141444515182040210020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 200574568 1250 200573318 200573323
    0x120608010902120a050c12011e2708030705070f0203010e0c0109080708030904020a05090d030521010e04110f060d06050a050102071a030a090804081c0801050609090402130204060908 80
    0x886000c50f000104440000340b00498400c6c1d8a200468114014000d0520303058010302d804581900790000c0441e0700c002100b2a60444100d005480c00801d04554111142d401000e480000081402c0c100300002465240a00040c1c000319002c0c844a080748052036000c00d08503100141224050750013240c154000d980e10602c94805000058060038446240100f09552409210500c910864022a0594206204030180c0d0350306040140700040d05825400c015081e0351008803960151180d0511007401140b002000e41e048803500d12040195a6458441e003500001c40c000c072a500c24070038843e24105549040203418010150940011a01e28103010080d04010b923034052070654002010800541031110034070007540600d80c5840f581c0f40c0d109940c01c0000d04624000804c9944c0c0418041800c420024001c0551207a01d00300a042426020b4140d81090092041a43c080030070098040103040c00c28242d9001803025141c04038402d1070444101c1681c0164010f0400500c40c3e5a041100c0c0380304 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 200575818 1250 200574568 200574589
    0x150917040305100f020c070501271203170f13020d060f0b0f0a0b0f130312030f14060604060309030e120d02100c08181f0605010e01090f060c0201120608010902 70
    0x1149405c62400fa80340010704e40f101c0c85886003e051054501e1003041e14140960074140d0340305814420403016407a40480c00c4000b0b00e640003a00010030309516100008003160501d80038100c070701e88079069962015070349400300e041d8035000c0360040900b02c001e6000030b413140180220741c41d01c081c000ca4861400b10500015100c2202403030b00c201144d01c020007101000b001101d524208100e085699180d140300c00100700e0070325034002481078007508506020507a0551202010781c0070750380c052004522950030032040003000e65080e40d100b10100f104201c09402603204400c1c107842400c2031f82074015420000349018140146070411034200041c0754013583c2d8107003c00882044006401c100d40402c07440010428080144020b460a00c08100510000010480062040d43c1c0d6900451404850230001028000740c2c41342c98081441c1260054a541c098182041034540f000c140c0082203140c100101c2c2c0716880750030300740d060015403041c1c501b41c01d503240034542c0a80001d42c0041180d00440c418880c0d2000c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 200577068 1250 200575818 200575841
    0x10506010215130206030612060403021c0f0207060305100b041412061506030417190807050c0a081b03070803060a06090b0307030c1e21050415091704030510 69
    0x103803a41003120340c03d40e401616800e150140c821545075a0b03200c1c086018225070402c0c1c2866845008100810160b0004002c0c61558148404400f6a44007903400d44030b030980c0004000250b001003030203100c4548aa405540d21000300d050141c90982e903000b0002c081da0098210441248590f4a070b4400e60506d0180948480c5040d4010714441c0392955110040d0011030301054400d2000002240921403415103001d0702030200302d070302c0c0da4511803243c03400d0104041094143c041801c0c540002c2c03038a4020307000c0c2d40c0ca14010030084c0010220f650b0300c843c19948029242d041c6114400c010341e03904401007011304000c41c40f45d89850740da81011b00030811905656070090003080f0121100380140501c0009403070304582c09060104600e43c000600380d030801c0240701400d0404504802c9204c0c043d5108000c20b03a01a0300065500c0411102411b002c1941c2003140c0152245100505501c03905240380e120215046c06050701802c2e00d5110b003625661075026501c10303074442d0b104545035628440184946551f141 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 200578318 1250 200577068 200577103
    0xc03060518120705030f040b12071d0402070204090812070324050f010c02120a0b060409050a02090c07020301050403171501021f0204030803040812090304060905060903011401080105060102 83
    0x10107200559a542c540826a00000d403004251181009820004c5d03c03214055001c100340c45039244c44514003180c010750144038291121034045081b072800303903840c2d0110020910304484072035801801e00001e580542e5003240c110342d03200c50f9000400d0b010005046900d03040c41c000100c0382084c1c18000c00ba074003142400402c0c0503003c400d1b041c200314080108412604261002100500920016501406060030194002701c50300040460b10703602158040c0190b2081d140403e02d0340f0348134140002c692110100801c00d034000b05c0d1440141c42c1070090b03c1d0303100317807800c44c0c007841c2c61460341c0030a080d12419141203021508051404d10742e201d0000751150310031a500200403421912900003540c44080b00d291092000351041c0034184806150101c401540d0040c0e8400c0e5242000e10b0403c02660115440d842c189280c10046180201e0200c02c0303c0444110307656038040d040c00c1800300b18440e403240707100c19403643d030720340e404a80285022a403900800303002000040c40d145c400000f90900150030348114241 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 200579568 1250 200578318 200578351
    0x9010b090f0a15030804060f020705060d0b06040305010c03020d0c0e010804060c030603021c020901050604080307021e10030903022e1d0703050c010306091109040c02010b0d0c030605 80
    0x80d11500c500aa0007112600140c2542d1500038818008001c50300740d4116106542c0c030040103100d441030003081110301941d601500c161000004a855200c1070007616400351080161149444650704152280c2034001c11562500da03030790792100e084505005003600400c1d000f06200c4441d1840d81b161a80d0b03640b0b207090541c1c20303c403584002000008000c000030f00c00c51380c07420f201040610a92000001c2c540c06040c8038484403008054540301c400707084c1304900c01c8021000200d403900709072040c1d0703007101c8201c401141803035000e60030000c102c0485601518030420020a02c00c050f07403200e00040051101d500e00045144403424003d0034440d15800c00792a02402c082111180c0309a5580204003072000c4c0d00014154083d20310a0100e0740b040440e4074007901c9a40404024408041825052072200740c0301080080d03610b4011400782e58404603400c99000d000c0c80000c15504041d081b03087d120085100020302040e1020024070007400200040e0f0302044007210a00c204440c61080723603041416a451900c03503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 200580818 1250 200579568 200579591
    0x60510030908073503010314011107060917070605091002130e18060106050309070801060e0408160209130201121a10050f0a08150904020a09110403050601080c03060901 74
    0x201c3c8100070004107000711100e498210b03125028801a0400642218036600c0043c0c509802104d400038007054584401240c0709004044051069403240c00052001908002032622040002d003040003007900d1544000c2024165100302d10000d0003003900c07440b400038403801c0c0000c0061410410343e41e10130400e481000b5007640ca841040c084011079101801504641e504c4d08001d55400800e4001102c0c644540c40c00420002d0700400514800d108250485858a980714201800e961903846012145c0303d100300490003042d1100010a101200c0c01811704101c85c040d4041070600404541340c15000c0d242d4400304c0c04640c0d1086841021803906001400210350f54500c40d5007245200c10094802c030240301ca04000344c0d00903000e40d50311181d4040c403123854413070600000d400300d6011540c00b0803034010b8210845851a0507915180210340249c00c4c29034260038040400c0041c2810345841012003c03c7c88000300003101044511b010b000d10a01a200010444050510b080c0f0003400305401c99040c400704290 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 200582068 1250 200580818 200580833
    0xd0c03030e0d051b010207061107021903031706120a030201020d060f14040b01110f0604020f100f0503090f01090614060a080604020402030402010c0516081209060301050607060b060703030605100309 87
    0xc01c088010210103021500f06082c021f214404c4014040c03414607450044000e404806016040c2c020391703c03048581000030200304603c001d030200601003500d802d040e40080413403400940e4050f00c0a00700340302c0503841c02180f1746803000d19841200183c1d00040d220074892983d004010041c054206424000d80c244085166991440d14180d40119580c002494640e03110f4907d529a513070000701603070300340d400c0340101903240c1100302d4040c0d0085031448241801c03400c1074210806908410340da0510301d0030f030111048509030b0001d00080101d00c29a04c0300e006140003842541205031043c03030000354040d940340740150300ea0f4000b41040e00c118142d040c00c000c105004070754a94015130440f00140da0760784e0781c030060300c1c1c06c48121390140c4203214180424244c5d030348101d140807d0b40c6411003210301300301032889103200500c190b81c1181d410005c1400100500d041a1006d8201c00c0d1043c4e00100312591034001103281c5810041083d00000d40ba42010007030f87c01e00d03280600c0b1a0030585018048000c0a0310f4881c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 200583318 1250 200582068 200582077
    0x203100e07081209090a02130806040303050f040308060103050402012001050f01090b030d0309060204150314090d2a051f060803040b040b07050c03030f120a050f040312020c0d0c03030e0d05 83
    0x14001c1d03403c140000c1040036254103c480f040d41041050b0780c801c3e220404c1c150341fa40f0031101100842d01cec010220344d40030400142da61080d98543e0300c0020f41d07640d07200110090480603104078140181100d81c20044a22800b00c40d07103a0b03040e81d00010b070b546010300703100510403c180c1c04403580724607006203080191000b20311000d1521140c140800c8510203460910300230b200d2680310509a5842585148481e60b142d00140752035207044201743d58580380e000c00a17490715256000d040c0822001005116203000185040e41d0040b41c0307500441d5400d0290b00d0307046c1441e590300c044115a500b040b40d00301d0640d0140c070134000a032000da8021810641415800c501c144101c1c0a00c11828038041a0801004420131070025030043c081c09884e103c074803c414910301c07500b041802c5a04e10000c2400030b075151510f44074162091051401e5031100c1c1d115510140c403a400302c80041d91402d40c08201034008003808000c14070109000303644611000c849410018100d40300c841250301c00f1740020305400102035201042e01c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 200584568 1250 200583318 200583337
    0x210a050f0c03090604090509010507030e100b01020a1e0203190510020f0c01090501020414040b03030a03020c030c01060b09040c0201050609040813050a0b0c060108070602060f0402010c0203100e070812 88
    0x1160303580304078407100740340d070060b00f0015500440004020805541340d0b04201c0c02003554600038481a181c0305000e070151080f0030200c091561180526680440d800d400c41e440c280c0060040ea022a00542c40d19003201440d50013104400c0c03280d8180c903046003010858140000c441900c000301242840d954280c4034416004041201c6402151280034424010201c842481c5003e000300300b81996450715a010303410a11540b0380307a001104828040c2d04007809045a6110300a001c1d601d00800c008095009403c035501e41c059610051051040c1c0c01402d115800180c1a050f04d40d0f915030302c0340820041038544002c001411a4184010b200e0644c41d800501c680060703000c0c00254030780f1100d2415401c0410564409a441064007500041068003600181000022507094034090b80e2a54000d640e0f8000500c2040d0040e031007a00010620f0400f2000d20381c009105241440140320240c0000c2d02c1c0104011212690603034903801042e104208105800040c261000500140303502c140142581d4000c03101705 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 200585818 1250 200584568 200584597
    0x306091204120201110f010605030105090c06070b0a0b03030313060510050f01080c0d020a030515011b030c060212090d030b03061003020415170a050d0c1502070302100e210a05 77
    0x40200f16800343d0210002c110b244c83c1140d08005240e110107001e003105120701e501a510f004041041071801103084151850040d0449150400942d10905000002403649589650355a410300c1c079650103000850180340310251821852415082240440308045c1454131a21000c400070049911840c04500c0c0410003403e10200c10794484070b44102c5031050044142c0c03c14800246020059095030143c1d018101d103003c0c09616030980c60041d02c100f1f0000c0c21100f28040d40c202d45800007403140c01031001c00c83c4616405400c01182181d080505281604c5007240c0d60050b05c01c0340c0e48c1c1c61345446213110341c200071001040182801d03c0d079a00c00505034080070380a036490360540e269802040e0040d1000b40200c1142d04100020351040607100e56000d101140d003030140c070b9040080d1511518090b2000d9400c1422048107861403d1410000d52200720114103500411000141c288024030840302000341c484098003031300214840301030707906000852201140f0000c0c003850f45496403000c15540d02500103160f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 200587068 1250 200585818 200585849
    0x2010b04090c03151b02010e120307090e0907050d030c0b091513050c09010e06011d0a170f0717071a07020904140d0306030b0105030f0c04150e040f020306091204 71
    0x86403003c0e01ea022481c070480d400c6584041702241d030550261204402c05e1007035400400755541010007510080c0c0301703200050741d80c800601185034800d41803038100d0b088004503442c0690707400c080f62003400311410540c042107050f0444014400304030b0300c0a0381f251058000e00035081d45151100c400c0400a414003e200141030360b20340c10032034100002e0041410062003101c580d80e581e200c061aa46046800c223001801c0e80307000c5603800d02a81c3e044022504018484a0120300309240794a80b1184241810214803800e074407003c40010900040010348820b003041c40d0706040240a0070700d001c07143d41c881040c5407500420300c50707840801c41c2654110f640c104d4020b515a111810207019109661203520030501a0b003010700416038056102c001140c0c0300e4018a600d0380e99850402d5110750319007200b44900c3c0c101003034500d201d250540c40711081802c01d604544405884180300049020100c40071a844112200942e043d480d00b00001540420402c00500b006143c600817861540214810005c0c0c3c07410004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 200588318 1250 200587068 200587103
    0xf062c0a0801050f0702190506070c02130f0902010e0d0f1403040f17060105041b18080a051015050a030b070c15050f090321060307031a0702010b04090c03 68
    0x503091004000210081c401c0381000c2c1005181001c05942c850058402c0184500248030181c4400003625045009803603e0303540d0450079107850350100d0007280d0001490800c2d1800d1502c500c10290701c41f4201344009041c41c44c0d840050501907025180714807400840210600003003026500c280e40c50f03480501c24241515801500345180207d40082910b0102c0900100b11019241001182c1f03c01117011507080d0790741e0b10281300484045000d800c44032007032000e039094024000da51480f01000003e117119036850f03a80e5400c50502041c0301c0c04441301e40110000587d4554540240b944000704014004032591074800080d0300080c0c94800100710b8002c110029040f03c1c0540c50103011141c11010203003624100141001c002c0004850041501f9895408034080440010540340038024240d0b00da910702c4601e10404500000044c4903980c544100c40c0084001440e41c030341588060b41c12141c2503060b05100b040a0301350f654581c0002c0c007461403c9400008500b616001c8070490360020440c0d00480000d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 200589568 1250 200588318 200588329
    0x50612030c0723060a020d270905040f0219030c080d0504051504050307120218060310150b0c01051605070c0302060a030f05010803090406050904020604031112010608070f062c 77
    0x42c20f40b140d01001c08115010915004540c1d0074031000181c1d11008807440d10081d090760028086c0c0c00c41c001d08030800c1c0c00c0c080e410311a4407554126006802440c04498607500090420702c00800140c1d0520382690100204900c0c0c100f080702401d0210060301110400400042c001c6c06248038051090402622544200500c00c0466020b401d014066810b1680c0759440b0209840c00d24100700d005150304140400405008400c1030b0203048010040c03e0340e465500c1d0400d000d00034507500203440d070790b15040004985448030020040d501380d81001140700e1a05031565400c00c0c104109503414003d04200f00d03000151103d0300d0800740d036411140c05403240ca0750a0100c0042290118040003585048008030311682c0000c041d04008204640501c0707695114414000c4415007a503009400020a100c20b000007042ca0301122042038014102000501081e08400c0c00d6410590200203547c00400c2d0900844003c04085805000c8505001c2200f440c030400030314050f00e00c02c441c40800e1090410000d040d5445 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 200590818 1250 200589568 200589629
    0x20301031a19060b0702011101050f04022202030118060501020a1104020a0329090c040b090904060e0316030306050a0303020d0e0102070504020d0618060326120901050612030c07 78
    0x300d9104001ea03513140d4903260a180d0013914260f001c5850300c0c50210b500541401f8141c428070306044400190348032542403181c24a440c00c034000b032285807a0f100035000c1c0316901c0514028000c20220450343d4540c0c079003e40031900180c000391b0454000c040c0c5507003ca0205025540c002d00c081e00c005030b0359003c0c0d52044005106445120b10181d1144030070000019400800c0054400100c6440d079207030b00c0702090b005051149101c4c0982118091200032078520f000300d41c03d40e0103400b038034000c516083c1c40841207085901411140c0050359106100f01e06041d45440ba840140c0f105907200983e0300d0850720080d566070008000341c0c08010300703804034030707001e9100744500c4008100140c015900c42c00a04243c201800c15409481e80a6074850703580c10b0108441c0c001c40f422660401c15503407002190f00d085248a9410104400d40c000040180962144007001400d114540e000300000c1c082c14041d08000c1c0d03805251019500300e5005000c1581a46d6003c507942c402c8544408030014420740c03100402c00702c801c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 200592068 1250 200590818 200590861
    0x8070c050d11090115020703110324040b0c0901050d0923030c100b0105040b030702010603080414010f1d10020a021509130908070809041404060605030d03020301031a 73
    0xa0811400b0040c60729100300003600304807200c050b2681c981c805a4003a5240124a4006a001c610101b01082e200449040422406404d84641b800203a0715800c5803044040c50a04452a5808201c03e004140a0b03140c1c10110748103907240b4111810300020070074024003441c220700a6440c5105002c01071031000422468465004806014504a044a88a4100103c1c01c80b103409982c030340000148c0a0300c07a0320b2024070161035042c00c090030010702c00c001d504001c0c03044003959031750207010011444d000040e00c001c10195817040009800c01c000184901d0500e0007150600c4841d0083c0104403900c003000201001042c0d07200317040c405140700104e2030810000e4001c0c0d0048c0d480540445100200c9008010104040d1010704c0307011968500281211074501c0060b128160601540d030000e00804018441090000c0003c00e41c090003a10200e5480340a60b811103203143e941c041000141401e101d045d26011007410118115855900da075840b030390308220891841a000c40000c3d54550a201c140d400000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 200593318 1250 200592068 200592079
    0x408060601210e03030703060e010305120c070902070507060f170f090c120c0f220f0905030a0f02010b0f0f060f160b09073006110a0e150306010c08070c05 68
    0x44680500c3d600c0340d00540301030000908040020458440541e0703018102c030b6020004110341c064940307a41140e5040300512006038005d001c000250344040d030018000d41405003002c1c1107034903d460301c050003007041400f2000910406144c440c81c0c4c1c40324064003a030710080ba0394401d140395403011200c0e070400c80700303160007036019034803040c4407580c01c00009082e4444c2000384d50040c0c5003190341c0c0800c1444541103a0340303522501c50440c50f0741c06001c5a04001200707200b924002c9640d20060342e030b003819034001c40d92110004003100325601003c0d509000710401d49a0a9440204c402070307038004a0458000c80d0450790007a03400140030210813449408440d04a4030040c0325541a004501c0c1c20f01c64001c040d9178001e903d01c148040403030002e5201c1c0300b5010507480d03030401c100c400144000c48100003070102c1058821699581504001c0ea4145004044001c1a5610006518010410422680d140d00c503e000b4001c014010048541d07041400c5100640d0442151a2111a14075200d04c84010540040e900712 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 200594568 1250 200593318 200593331
    0x80a0906021309021e030108060718050604150305010515070204090809092706190c0c0c060906110304082e020f0714060402011e02033903040806060121 67
    0xd040c4c0c05006140600c081c005052054210310b070485002c2030007048e45035040314012900c0c0ca03002d0710609080c04081240300300c5480d0394200040301900198081ca00d00364800014240550785031044a0161108031001c1d00c0f0041c401c001c4206a00681800a001c2c0d03541d04405014041c0710b80960b2080c610050000e40249841203c0c5006c0b03903a07200800c14071009407003d0886400c0003154079031003050507070340320140c010190042e1006403018219003014000c0e020b0303095007c03c00509459018245039140e405009142c0701000306903041079520024030340c0081c0018080c071030300030501c1d054050342403400c80350101001e103001c11200450745001551610008100c40d800381d0007001392010314002d00d0003c40300d00105035515120341c4201c034024002031945c010740b1500c82c401c8500064110040c03048904100000380035074218a00328040c200042c00300760000c103d800d11040320781005200d001c040c500302403030000da165540d0406004a4184201e009116012840030715840b48520b100e14000d0101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 200595818 1250 200594568 200594579
    0x140409060f0213240c06050720030309070f030c092d0f0c0507120815120f0601050d0b0705030601031116020a0f0e0a0e0708070305030d1407080a09060213 68
    0x1e803042c4a191002c098036420078883c0542c4142003620400030b40c49030729020105c1c1c0d892034000e1070010040c0d07092040e052206407000c05041c00300c0c1450800c400041d40c2d01d00701424042d14024150740309511200c140c000520001e03000c0d041d14000c81c0c520000c0424081c240700401c01c5a21084a8010459108840b041000303a806e500a032090880c184000c20448405913400c444a01c0b401c440a81411151000303604114440d03d9542c1e07201c1d030200c5030400048011400503c01021040106880386c0c008100040040414440d8500503e0211601d8560858070781c3e83c40c440e080020442d8060110100000722203902030703007107025142e2100500aa4442500d90b4444070800c0c80030042e805480300d44c0700450b4640c0c0c1010402c09071150404101c1080c2c0e207159078a030207840361118460441c0038141c40010350b42810807039a0090361041c00519203c0660b001503038111034820456112034a0303040c06000009400240b225081441c2c040e0208a50b00c46080a001074803810701c06045110001400064 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 200597068 1250 200595818 200595847
    0x3010b030f030301231f0201112106040510060e060708030c1201060201021e03040609020a1d1501091503060b0d020d0f0608120c10050c07030e0307140409060f02 71
    0x45e14805040e92030701d81415000c00c9040c0c3c40e5900303d15041504404880d03d1030203004517501c5103011510001c2440c5880313003a08125078018220b03005180c81d04400515502e003443e846254000410343d81004545007002e4042e5224525100d510103100b0040d0711050356489200480f001d80d50082d045039964108191001804da00c00850382406040301000412503501c18021113424414040010310030740d00c07400c80c03500e941d0301c054001c4507060340c4d400d40724005032507022050700100654074403180c40c42e0705401d04001c200c500801e010380c0c0089002c014402a81c201d807902d802c0e034482e59028400307588001c100350000d21a0390001c01d00824046103418002d02607070000c1412640009080c0500600c800a010684d80075004051541c0c000c402c1a0381403080300400780903d1403402c42112142081d004164080720400d4440d5002600f0014000b0145500321a0700052240c05800403c2450702d4001d134140011402004940300c0d07a01c0d04074100500c43d05400c12444d596460804641d201ca002c50f0104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 200598318 1250 200597068 200597071
    0x8030a08160c12110a0606090b0102061005090408390d0206010f050609060f0a0c02120c0f04020c0309180412171f080a0f0b090d020c040b03010b030f0303 68
    0x380815101c015545480b80304800d6050350b0140412450540140b030590b80b105500d041104584a01c07010710000c1141e901076080140940c2000040300a20900020308012004044007040c51100c4001c00c11922520b100079440343c5c10600d000d8840c8a80e05100005c041860710340f44100340f020603440e03550030b156501d004a141440041315030901300320344103903102c2a092140442849005000700f00340d0070140010140d10000400d01440e00100800d002d03201d40025154000041c00c4200900850401c24003030b603042d40301c92004080384d00700100064240011110307907a02458011400812103e41001642ca503100004e085851402c1e1000c4c00c1321528404540641d142041c80c140001000d02481d0142e600318030690140d131850f52400099009500d5440031100c01500d4401700046042c8241b00a1130543d1144030f0701d80f021b4829007042015003001170409011a0040001c06a02c80d07000520001e591009540200c3c24081150000380144650b0207007039014020031105854100003c8004c5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 200599568 1250 200598318 200598331
    0xd0f14090c0901150801030b1b03040b0a150e0601030f061203030b100c0308041118070507051203060a09090606031202030d0c02070b030601080a0e120714120304140708030a08 77
    0x15442e503a40d483e8800c0c440c072201070095011a0390340c401440802c0d81800ba1307a41c8240c119101d0941e14210043c082150342c4116429582102c00b0400e002c43d111043c064920b00b00488183c0c180c071319007410301101c05013031301401007410b06680790480b884442868010300003c00c2885254554030a40d8100a0040d26484001c3da04c5048a03403500340a5a008400c0388013401d4140d40c1e0001c1c40ea031565554000910706100083d8082c83c1c00c08185130600b00f032002c1c0b030710990040d81d41a032034018a103030092604450122041c03000c0c00500c01c1222a44551101030119144000d02080c4480d103428150000d041503040601046501c078040221039030000010484004001400c110b584a8140d040782c40301c41c103000d540700390803081000c141d040d0301c1141d136a500009800d200240c0ca6942001007840c224000650283c494400305400052007202c5940d14452050a809030103a0003401d800070b0814400244000c01c140c0b0190140e512094041008d01c0103064540d048030340d50a107500c00500780e61411a0003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 200600818 1250 200599568 200599579
    0x40501080606041a0705162318060f010309060f060501140702100c03031b0905041a0607230a0c090e030901020a0809041e0c080f0c0d0f14090c 63
    0x460703454200034040b41d088600100c224661400c00552002240d0b00c80c0c2c20a0f115841020141d070200181a8a54001080c1404201140c280c14984d440200b441c800e54103445000c807030b258180c408402c01e04503617010300304613203c00345040500300580c020040240007800d11458014070300f110345941d911900954000341ca0b0900d00003110345030341c0c000b8030130000001d4004203c079101980c80c1d801004c102d203400d4402c0c20003003140c0b81c5c8483d03000d0340f15a851050500040281030208140d0402d071040042008807101140304801034032002c9520342c813594500501c0018401c1d03811402c510070003551100c5021500c00d1326403034030345030501c403401400d14054641d81a160600240f01c0740d400204580750040306070043c1c6110760554440c54800e401c810f00890b002600c40e40b082c1c4107400c000c04041d0600c1e0520000080d01500341c0002840c03884001c0014085184010500000c80e8072281a101c1c0d001c042403000c60b180c080745171218040c000e02c042c010000c0d140e02c07082c4420010082901c0340000426944c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 200602068 1250 200600818 200600821
    0x306061d060d03050d05040c0506030a1a040e07050d050a15060807060306060f110f0703060e060a06030c15050f030406021b071a1303020d0b010305010b0a050927030f04050108 77
    0x4100700310000e800c00a0216004005e95a01c0c0080c9030065a4800e0040304800d00159803140070074017a5100300c0d40d507640c4907501c0c0001400c80700d01d8088042d0044090f1420403841c0c01c1d04198550703520366405214815011402c54104021040200840d0036500c410191102c5c0e9084640401070200d900443d00c0c4c6005001000c40c4070b0340700b031003682d04888003079440f0b4036a20810300c402c0c0d490b04e51060881070070f40a64403100c643c5020402060008501c11100010304441c214102820800041c068652540c1442003c02c04210a004640f0956031450030241680c40b080074242c585116001020700b1440f008010001130210717640c0074040f61841c483c490501e84c6600c204054403500c1c1409044041e100c503d00500b0010340c03580241c002200301207142110252039400003602070241c85000c80d00e07a039008006004202081c014040711100c00d0703034484203041c1880006800184002c1ca281108145102540f45801c078641083c18890048002d99944001c000086042580240240e1740403840100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 200603318 1250 200602068 200602081
    0xb06120903070503132405220f0803120903030609061018062c1309080403060908040315050403020622020a080607170c0a03021615090b06032a0a0306061d 68
    0x81c22140c0c9810716545280c92300d54035581084803007103034030b44501e41040706550208400c419201d0003009411500c000b1515001603500d4411008070040c9105003e4006000f80185a2a4203100c0c0e274000d001242c0e145004a284801103c481d20a860168246088003100041c1e840e01b0a4030072207032202001914641c0103580e80003074066108a001c0795000307400102e81e1460f485450784004c0140f0300c1103040b0f0346001e540ba10b50400307941d00c1d8401560200b1001408100f0084031003804081c20400c81e000b409945800d450103501e40000928009090091008804403a1100e0f401d4040a95000344511381c0180c8410140e603030341000300c0b0880d0103e85c5c1032101001e0b001005840c14803551058401c00d10b03001500200b24069003140030b1130301401c402110a0030018441102c0c20141d1500b600d00050705804c80d0620429105001d0f010074000d802203202028442d0300070300d090014242000c00b01e2205071210003c00c40410950f440a0302161401002007107210188404130301106002151096030b442c1c0c0d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 200604568 1250 200603318 200603369
    0x60503061002152a0f03010501030606020d1d0f040f09110102070b0403061d0a03030e100203130f02011116080d02030306130b010c020a08011b030b0612090307050313 73
    0x140396142c00f085070600003605440c41140103001000c41c00044110040c54100b000f14030340101c401844100004001400196490b1144d40d0040100340b006180031302000c540500748011501c0c001252550580118103180c5511607114829140540200422011350014400810034000101c4040d51200400c80d000e600c002a401c0541d800c42501d03d14140ca159540d1005110250b1006401150300b00e100a140708148a60300b5424040c0d280070134000d043e038141600b840c9104641e202140e05c1030042c86001d201c000c0a110708075600c407659200f14040c2c0d000584004071901d0429100c1e205a0300384401c0000441844070488401504595071000008000e0fa1640022076800703800124103050b45880b545c6035004008021010304214030580722079008540000d155030407002c0181c1d1160310160702d10782c41c64111480c0038031a10b41000f40c652444002038481c40b54000714005a2461000b044080c50180111040c03207501500b201c0d84d40c0700f5205010311080b01803080c4018406101c8410240d69000f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 200605818 1250 200604568 200604583
    0x50d08010807060207180f061e150917100f06090b061e031f0e2203021b18040b0402012601030b07120c0e03010f091104110c0106060503061002 63
    0xd41c0203040041e043c0088001842c00c0f603a490180c6c152210035258801c0d8142c8110300142002da06070941c0c10050600020348100d50364000a8080784c07000003080c40607448491070b41500c04081d250041c2464032081946024040442d00301503a190981129254400d9803100d01240d11903c0140800d9601104001490040018005a842c0d030003441404425201d4010340e03000e030202000f45e46400171000710b43e4407528075402140d040114081072100c0312440c003004408021030403106014403190780d5402916041c1c04140d00c2042405d030140c080095444084c001c20b020910404031440707247c039050100c9001350a0794140c0c0407503c0500e480d0044841149941186801740d51441a243d207150b40c0c10828800080034074082100310061303081d03070808900071140140d84581c0c0e0b00d048072100c042007600310f44445c12007603c4c0d18070f0442c0040025110350210f03440c911080b01c00140062200081c3c0d089803103400301c0a00503510303005001c10420781010203140103000940708001d25540c0180103981d00c0c0b42 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 200607068 1250 200605818 200605829
    0x70e060a0302010503090715050306010905100e01030e0718150503030a1b11091314031309050901111603030f02040b07020d05100f09050d0801151d0d050d08010807 72
    0x800c0401407016501410080d03801244030002c4640c1f9903503402e4001c0e0024640584c0100107100003041c0f003c291781c0322000b01d0281004440803103c001d4084070240642003a10007403414581c03503029400018005005000042c246903000c103040d20140c1c1c2c10312000380720703641681c100c000d90700a02017158100003080d503001d00741988441e501a202c10348200640c0b100ca20040312203a01d100f00c1c140c659100c082084c0d006180d1800348108207807081c1780045a0101315110311005a10504c61030a9924000f015a0300f200d110b02c000080341c0e1140314917517004d407042c02202d9101c3c034000108101070070003850029005502a950030403241c40403140358404c0e44207601c030740052214240801d401502d0081813650109200d001201d10554680502000342d600c0200614001aa111521420b0140134880d2405000461401007001e6040041e404d80c1180c80207507480801c480d0708034191441407c0b00b080362201400030142d1480c02c00c0c0303162065890b41c3d811031200010350070b04000950503030000f50190513a0b1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 200608318 1250 200607068 200607079
    0x6090e03030907080d21110a0507140316060504050708030c070e010b070c05040e070e0c1b0a0201051e09061201080d0309020619090504020415180518070c150e070e06 73
    0x131021b052600c1d0450683c242602000d64030b5403500e600c40c201200a00d01c0520b0380c2c0300c040c2c40b07580c41e0402070503e010540403421160403c202c0e1041c191402c8544404080c0c0c04000014643c95605004c2c0c50f102c0103410200c07191000041e00c0c00c035104001802c0045580c0b03c4a400302582e01c411541c1040d0107800b000600414100c0802e000a16141c0c014088041400d01110710441c0d03a02c041800c518019950407100a5000504003489400c101c00e1030038003401980107100c010f45a50000b030040c400d08903000000c3c2e400600680c1544001d5003100c860341c500400c85511281070001c0c822804a00f840f800c4614880c101002000780d0180c040c034071070540c0041516062400044035079009480c640e01400c00c026500e8000316140d81c032480940084c0c000300d600c140e2034144007100600306044c41d41072400aa492008100056501d0615103100c20940c8906580292a80202522040c0701024020300581c01c0011160b40d00003258003010300d070301d0f582c41146c42603030b620007520103501d00c1600c0301234104 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 200609568 1250 200608318 200608337
    0x30f032a020d0314221a130e10090203040c0f050f01080a150f09050406110f030103021e0904030f02070f0e01140102150c0d050610020316020406090e03030907080d 72
    0x38014800c00c240e003900964024a804561104200300d80c03205c0e0024910541408000d1100c040c0c18071003108000556500359160070428500c00b030f0408164410840c0c1e40c00710000190141e00f08001c644010721280c4419500d900b810b2410754490102c2d4003d05a249440070400220342c0303031030718010401d00c406841e10f04450310740040b0782010780045542d2009c2200000f1001811001c41c2c0a560007c2c4a00030b00043d21b800c082c9098030640c2e0b00b809004909040a22030b51400303181403001c480c1142d43c1224540a03407000c09445584805210080300d07071002492302008145074004007003013608003450b801c1da0703000b680701c852030394020001c0e0040000d00450a40140403002030300f101c5000309641401140e107100e00982c8480d01070746040b14152110b59002c94140003c2a613400303140d40141c0b044641c04084540002c00941c0c070f0144c0c189204170090080410801d644031940030700e000d0b02c29210180040d0040303010282d500e034015540a401881602c60008200e0703008140210703041038558944604 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 200610818 1250 200609568 200609573
    0xe06160506070807051b120a02100608120d0506030a060504060518010e03070609052d190209040b06010315060e0f0f0f01050c0102040f0e04020f011805011107030f032a020d 76
    0xa24420345000544c0303103c0c40e02a8000001c07c0006451000956030060202d00852607252040d40c0c6240c1c041d00a55000501102013030080750f05842d0007203440000051140e0b03e450000e1316103000342da8040c1c98240b620050006002c00c0c3d81156110f2203805080c403401044141041d400c03240a0003115034950801d209210004d03003d83c1044107a00d0154044451034008007002680300e6015040340356115000c1d0034a451380e55000d015800014001d0400190321a01d55004200ea1030b070010402001000090300040c440d030300a41c008140450048402d08120f5114000a00304100e00d40400344107007100314050725030b45040d4130b04200c01d01c3c0140809603c200d20348010740743c5400c04014001c5a5409000200304003d90280c580001d100c0c1c410920441d050034018403801c0700c040480701341005080e515088910a0714290401218020b103028003044660b46055410204250001042c0d40d640140354802d041c0d11201c030486400e0720100c00c001ca541c00c0c0d029008250f0250400035013007007254000b10003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 200612068 1250 200610818 200610847
    0x40f090210020a15090f0602180a0b030106050a030e011503030504050a091b0509060c060f010f09020315130204050405010801090b130309060e010e090f091605060706020a0e0616050607080705 84
    0x80407841011035100c51307034887d9149000e030b030044141007071824502003400c0b2080c0f4201d00741e0310040031030842c45461541484d80090552045500b03080034903444e0110582050802d601c40000c0a00c202a102c1e030850322443c000341a039209104a500ca02419400400ca80c04e182c07090282241c825411415016941e400640b501d4106a41c007907808041480001880c1e8000d01080b482100d215040c285290705284241d0f10081c81a001604600d2040c403c21588080307001070081c803000200d030308241440d824a0804040d01c00d5800c62500a402c1000001d22200c05400c05c41e00944600c5029500384d8501d41e440380b252110010140c0020843c100410402d40590b0a0024422041c03406601c80404000801c201900070b40320144403803003440030444401cbc01800040c140801c240c40c9116001d18040014481e0f01680d00003520301680001c00a1a4a0003200c0003030100030007924494075502c40181e01d009203900f010040d03a05004450001d440c0d42e00c900c0c06580700d0410741d16200d0510200c45a00309 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 200613318 1250 200612068 200612081
    0x20a02070e090c0d08040e130b040f150903020304140102030c070315060902030c0304120f0f11030c060702060103050c04090f0b060d061b020114010303020606010507050c040f090210020a15 83
    0x14035a000b403007560301c0036813183c4000c0003101d8040c0700c2044c1e03a180f400310103958001006004200751560684100e001030b001c000740d00e8105800500c0600385200b5810891840b00d42d084128026514011140c01019008005441151840c80c880d559280c0321400590f200d104008400090360400c640500024403c501e03025480194031740000f0b5866101c5200000700da10540e0501c071200d03400b00c108820000305d8061301b0501111441c05142d80d21500401900f60300c1c0603501310080c0f00307482010300e0b0f070004100281d910a0000100321500d42c144000c029440340000e010586450140442451282c01e060041240700d60307100f802d0100340060341c0c48001c00c000c40a03004541c4407441b5210360340822a0350044a1000d41c4600c1d2203034044003a2a0b0190864000158000004107080d00400200717401040d1140e001400b0300705103949a0340b52400078100900708801a600500d411450040700d40d04d60b2110860620135034120303612540c83d100503a511000fa01005000341960303a0350801d100310716013006 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 200614568 1250 200613318 200613331
    0x17160b04051f03020f0f1c15170a0b0103111002010516030b0118060e0103140108031602060d050f0105011418062b0f1103150628020708060a020a02070e 67
    0x1802e20b01d42c400340ba10180e06c41d07802c04440c0b03003001c5a40910500b1203c5000324210f0320090030806071444010b103a01514851040103010184413001041d11282400090240355200e002c20320503603102c0c6428513035003200004040c0505908812020082c1c01441682e00450007104411822600c400c011400703018020b201e2030411807010302d500081c0041804210103404a611070b1302120582000042c00c0322254015a09070003540001003041400100c1150713051049100c030040030a4007070012850b140319109040506074940740802c04040d1074900f0f054142e8030260303101941c0302210014010703140981c1c22500350503286145100c05901e071490040c140385170210381154004102c501c90614814664002082c081d4451507626803c800902c5201c030680c3d441141c031429804e006010342900e8484603038480c01540d00107104c4070a0031000c040614000c404404801004070700c504002e445e1900313480341c601c1507c00c05000c1031b2010a18021307105031941c1607000b08bc2003498564507540d17412014120 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 200615818 1250 200614568 200614571
    0xf0f0c0d0c0b0a03050603010b01020c0f151303080301031208090d08090f0316020307050604030b07050c0a02090901020901110c0607030c1103010606110f0102030103021804050717160b04051f03 85
    0xc0c202c548400540300d5541c00761000203103850030074241400c2d40d070310101850464001500a000e035079030303c0e1803105424034180c0f4441d43c1c039444000c10084a00c50360421510910f20034000204220b40c5e20000c6042c1da103e0800103451520000382600c1c000d1302a200c5070065006202101c401610900e115988464140101d078180006900c100741541e104000d412076412491030a40154141046400c1c010301c416559245042c2c5140ca511000a00280244040080002e09a07145c00020002d200495800409100382c03804e188403078038002e5208260301c6000c6204403d9000f03482a02180e0010f01c0d40000d801c0518000560707070105c0d541d6110040c22101c07a07910072200303112920240b251002a0040e07450741100c00b4107200303401746800340041d43c1c0c05040e030041006200584910202c10207040344031510340c08580381c40c41d22509110080c0c102507100b400082910a0521002414040c000340410220007001c0d2140d2144800d88918018907030004414401e10304800c20010300c281010006250 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 200617068 1250 200615818 200615843
    0x31a130e01090615031106040f0501181a03041b03050c010c020303070b0f07091502030d021b15150103090b0f040f05070b04030c210602030601050d0f0e0f0f0c0d 71
    0x19920110703101e4903035521043c413050b2418420015090740240300000110390b081d040c2403903d4900d022607420740c00f95504100620301d0070349900000c020f070500a002d18103203480c81c0c03040380f028607205900304540a403044030100e1310301c1c4091585a518101079030f8000d0302425802c00c2c0d40c001910510f9101c10203d80500c810001c000204260710711550290025901c80c02c01820420002480416590001e41d94003403070a605803030b030039000001c403081600341c060701588404120554540e00c200d0301c1c2ca40d1140e40180f001000e61010024060b522642080650b10000b10901d4011421580d083d400103125840c0f51004c200c0d8a180080469803241c41901c1d0340e1400301c000d0790780c14280310030781e40885500c0f8000704040c0100101c081c8140f0141c010700180c10042c400500010340007001e01c01018110781d41c00004905540d10540880c0d61100785060b0038000c68040460540041500311003915040c002c0e0070000010312408034140110011030303c000e00303100e0321600c104401c8240d40c403007c44000d003034a81c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 200618318 1250 200617068 200617073
    0x30215070b0a0f1116020d0606090507020c010908010c1d0d021305060102010605100c0312020c0111090f01020c06070b09030421021008060d0b061915031a130e0109 72
    0x95003512a030030042010940c50780ca803618009548089980381d031181000c0c0501c81c9500d0242030040e05480d011182200807e4032401e002c0000c2c103984d0070082070a8282000c000c0215000030318003405810a988420015654541884c22508a41c1510300043c28114800c52160141a44040521001490000d40c080c00f43c1c0091207018080000c0c102c0b0540b203400704540b540c0c080c4200d03002042c081e6a99a9940c8000c440244402c0c91305c14024217201c0501d031640070012050781615400e04a0000810150312091240c10590300586240c41c49070640501960b019480820008e2107204080c0900707052240c0c558440c1e0400c100144450b0380340c88240000182030340c4002040c0303808041c880f011588410380d40140840030002800303440030b03c0000014004a5100c0d8403d0002c0385412010112550b125500023801a229180c4c0c1d0252180e0300a8010480404184011900741075649082280d01001d4007954041400000c50300d40c4044811245138600303409400119184001100009424035582d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 200619568 1250 200618318 200618333
    0x140f04090912080a1404080304030921020a17030322060609020309161401050703030b03060c03010e01060c1703130212030910020102120105010c050307060e01021e0c060103021507 79
    0x103501c1690350307085050401c0b0020750010b80054102c00381500510090103010044c03209803102620003460f042d0000700090625102d00803640180140c8446108601d10600c040d09642814101c280e110300d92600c0300050460030008943c1030443c030300300a581183d4424081e80d01410280c502c031160800a05400c038005a080c0c8070380f4019082000005071203080046940340b5061518004e50030554114a00340440300d02c00b03407070b490051000d2814030fa68007021302e002c43c098000c0070303196905841440c0c00e02c07100030100f101650607541302480c0d1211503aa581c0d4107c4051070024005401030010818400c0907014000c0110740c01700c00d419004445840d10390100300d48014480c03a4000e50303000480c508010b8940302000345140d620b14030003582030008081741c4242e10350042c8140390500c0300c500714800800905006559286070069800c1150420711801a4040c2d4001806c2c500703100e840301c8102000c49064030940340004000c200510351f9a00755828040560650100d4500c460802d11030140040d00030f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 200620818 1250 200619568 200619581
    0x70c020d080f04060e0d02150f0c01110703020d0c0f17090d03110f0706080c250303050103020901051c0303051015052d1918090b1807140f0409 63
    0xb696022540c8600d4240b0003824084000301326032190050740459005640c41091000c40700b90714854680e0780d1781189810000c10301c01c100031000716500f413401c4030000480a41c050719505000707400b5125401c2d480c80c0c1c00c88458407420801050100b4620003500805c640d071071150074400400202600c0c1005440015200d0780031000c044001a00c29111030403041d1050040f0741001e1071100040c402c42d4100080a41503107801400c0076001c0c2404528411452407810440700443d0b2008591300b80705601d4100100500424002640142a2040000f88034282884030300c0b000c0d59111609280c1401c1035404901a090181c10826011801e107804110307840f80d0105c440c0d0450352504c816030740c0d204881a0507101440c04d04c205d650304004040c051148204241101e103d110101200b0350001881e103010f4400190915000c03410801588012965075490360000c800301c501120003c940d0f1a0303111080e01001400c903040800282c030300c00344461a0304041d000d020905607560410f401c0907125003001084400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 200622068 1250 200620818 200620837
    0x20306090a0209042c0d0306080a030309060f150e010e0f0711010b101d0603090d121103010e04060f0507090504090804050301050c120112030219020415030302011d0c09070c020d08 79
    0x883c205d0b03180d030301402013240c1100d0300f01e50700b028040249041c00d080d84940007000d0250516440303092410800c0801c0d40300c0201c201c90743c0020010164400c441510411240c000c40303c245691800100e1201005440d00717218200c0c14040c24080d0b40c940d101200c14191802d0548029900d40044203035594034900142010b001d00e030707100354030348104200d200c00e141c90304217405002e40d9042081c003550b084041007268010310603080480d050342c602d402204c002c0005203910650781d2004000480c0440840301001e001c1e50007401c040c080c0d2029280d015007141e00560f8408081000a10304124604040d040148254000c1c1840c50a00d5071b15408130307003520411504200100d100044140c004800b40007404d01404010300c514420482c584d4001c2c0d501e002c04e40015440f000c204004408641c1d9075003240210350351000c44814169540d14000e40070b01211184c0309941d40100052181c21080000ea45140c0a0010150001911520001c1e202501c03d400181d800c940310700710707845c0407500180050a039800c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 200623318 1250 200622068 200622131
    0x4080906090d050c03210901110709090602120a0b012a050f0607140c060408031038070b010905070c0206032e0b1e04080f0a0b0901020306090a020904 66
    0x21500e04140c00c0c0740c84a00560000914082028490051b1101341d0f881a0b80c2800e00d652410051203010303117448555402402d40b5420040002c0421841f90041c1a038003000b401d003030038181c40310741c810410313500300c0340301e560014200c020015045445409020b00c9045041402047c80340f06490342410312030700401c44100b86e80800184010150b02c0807802226441c40101203052100d040382203031719840050401780800002101154820540c15000070003004440f04065120f80128011440346464506403d1152003014064842e501420101c0d4802540134801e54600e0307003045030300d000400d006041e130b401b0440504001c0c00184c03584c0001318040e42c0c00c1040d94842124202000c1034000b00300059040408510a04200f44889042900c030b4040b155100745401c07031001c082c0810311340240c0c2d010751080d108c1e0f0b81c405059603d0103c2c403004404c1c00740d01406810355452400170b00385c4c4019281d00b0340040c0c010b400100114072907400740c00c81440c0100041000400103050a0420b249000011481d0303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 200624568 1250 200623318 200623333
    0x20d0204060e0f01050901020a11041b021015060e01030207061808030a0e0307030f03051302040606030e010e0a05060105060d0204050d030302030601120e060610050c060108070602070906030b04080906090d05 91
    0x900e8910101d0000c2c3c42c003441c0003407400704d4100000307440743d42440c4001c00c00320340b0308545000f550b5240c210803c89006882a0b500703070809114029035541c00c095549180a02d01046680b8000f804602103094660644940034a0410100114000e50103c40141c03026035540400904031100c1a5015403907501480c04d007512401c140f84810104c0f9a1220f8141e41030780100848000640c001d1010041443c0074100007400d592100344c050b0070714100c1c01009522030304d022008650150540d101d1200b100d4174900070001504590710080d61060301e1340d405041031344014010130540c0390071001040340042e51000035080c9130766107001c036540c00e024460480100340c0100400c0000d59010400134290307001ba010520504041c41181600c0e10005040c40c1e000b134010001d0b1803545c070b0082c004c95081010340f20896103e1f43c1d44841c000d446424a010b9200113000b40800001d10994038042c01043e030750401d4035441e440c2c8503952410181d43c042e6242d9034200f40c00340b20640f120381d03951080d000044d001d900a0300c0340 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 200625818 1250 200624568 200624597
    0x130c0f0f0e0f2202030f0609070906050a050d12020a080a03060302100c0b072003030901090b18060f1e071805030d02030301030602070525030b010e2503020d020406 72
    0x1410802481011a0110282001940030900030300080300e51825010015071829400481d091180481d4a06c80900c10f28003401061400012441c0469842070010030115480d1800c000c02c0b2102e41c410143d001c01094004c03c00704404540c1d10558801500440e0012141030740c41c03800e140c1002d158800482ea50302001c1055041013420351004030110700d00f00c80e05491503580c1c092442c4001d0a42e20400602030281c0d10404403221010030524140b03411241c80c0d03c4d20b030b0840d0b801782681c44411158003400e1004905210b4043d64050f95124038900900301998030101001d0792100010a105d150740c0c92003000000300c2030804441030155034a651560510140c508840984800940c400c40c0240c0c0050740b1803240580c048181c6c2d043d80c1d801340016983d0460350906501d0400c000d85d59499411140008010b005005038429040742c1c8a60010700450381d84000303504400904441c2404149000c2040f040071494510030785004c6240c9040c014200307a010b1541600b20780260b0001000300e80c0b01d0450005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 200627068 1250 200625818 200625839
    0x10e1c0905101d150c030304050706080906070804050a0606080f0124051309170304030e10170406110c0c0406050910061101020c031809150108130c0f0f 67
    0xe898161582c440c24050514010640c0e02ca402d0b8040c04000740b0b0b9119441603480302c1c0d40140640034040c84039103c10301c140704691280e005403402c0b102d5104214001420f00e0060f080036104069a4020300741c0c03941c851400342e0340c0c8203000303000301c5450094180c40000500603208a101400c6540000e22840603514040d40c21500f0b003180140915001c2e0800c44100c041c0080c0c0f40058850030fa60b00100e0035003003040ca0018185020004011502d4021000c5203030080ca0003451103680030355580020402c44c0d209018580c0c1404040e40300042e070f004003c50801b00c0c0404002c2d00644150000229040d4104178051540c20455280d020b82e0000c11380700440b40740c54003c080192004444000315418010741040740b464003803149034140b00b00d400e1085903900082d415900d0072201e060659030385801403296000b040244000942c0701d0306414010034550803004503074514803141a114050591500d80309080e21111301c120407204445d030100d003c100000b501d078068000700720b80c080e205c8030242400500b00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 200628318 1250 200627068 200627087
    0x5010905090f070b09040605040c0e03150603070e130c090e070e010e0610050c030406090608130b04110d020d14060c130b070c030209040b04060b01030b1f02010e1c 72
    0x70125803050b040c000b40e07074802090714411034090054490b0307224140b8010038080d21a5a0050b98003c2c500b01d4903041c40354000e020740d850316070b007207059400c000f00f9000b6641d401307001070700c9040d09a442104148144000610740d80c0d005201482d03407406201d499070300d01c007120790349810050384991221138000000e1400c200240c0905401c8150054a40c14001e40bc00781c000c1c003c085c60310036a441100d10040340d0082003164410804003040e0795485449400c047c0c00540680302c0c00d00003aa40b000085d1241821002c582d0215610608108994441ba115540c01280880c3c03499031040116805c0741c01170740e903480040340d00381c03091300c501c103420420145490030080001e000c0007400382c0820019010000aa0f0240c05071a901d50a064407200c460a0a8000f0001a0002504404803074184010711000515080c4200d10034841442071900890044081c0d0300c41071407080e0404a415400b1f0b8461980c1400e1fa04442014400043c98903059155546030143c0e241d2a9980c95000c4009010055840414003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 200629568 1250 200628318 200628331
    0x72f03060c0703051909050a0905010509061c0f0c0b0a0306150216030b07050403080c010f0e07081005130506040f030e01030624020f07060f0e150304020d030201020d020d05010905 79
    0x22400d02c41661000707030051003207040600a8140030440040001d0040728030700054240a0002c0101d02d45444480c001010700b8021548540544030004400d842c022807104140d01012012240b010040e40c0c1e0005c0c4a10804002c9603600d16111021542001450140410380d090380d42c04a48140f50401060402d2140302042d411500200100b01003041012104811280d20540c51852680e0b60581103541e4010340e003005240450000f464403884005400508803800d16040400c041044060096501e22240c400d40205403c01409003200214990100340d0012041440b42030404a60342d0f19400e02004803011900071b610031510009044d07000d03085c1130070350741c01303080411941c0d040281604c0005080314040c003441d100310b151000e040340f0a20042c000740f22104200e401458440502801d48412000100001340720011940c80501e0041007080094040c061603900d1511540c09200c0009c0035800107a0542d9000c100300c0004200d54401025020002d180000f059410032881c40d003130310b4000c0c041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 200630818 1250 200629568 200629591
    0x10b192603070201052b0b1804030801180209090c03040b010f0b04030627112707110708030a03050f06010c03080a0506010e060c030d1409070605072f0306 68
    0x140c86040001080340c0700590242002a154031400d04030488001c001c0c20403d0f00400301c4804e219a82495800034210500101c90400203440d0040c0808000c4008035400f60000f0a03d0004000723844400381c860700b4481440d071015240c41d0000f0003140020506031014000050000100014070609141c541d000d0001030350411400f6203811200110750003a40400f808169980c90041d0351000f68014080e48030070b0703c2c4038101c404011820300b401c51403403c8090a000d00600c45102c1200000854600e604042801560b112915482d0701101c1c00314104884205a02c45c00300301081220041014201203010381c0d50106e400d25249411075041d8401514060621038100308180020b03400502e801d600180c5600300250568500740103e9405a0000708203030460000aa0145030000101c02031214200c0d80700281700e0542230540300281c041c412900100f00b070708035503428070003544644000c10619000d00e03c0400310f003041010143d100a9044120b030710f8015503100c0340c69641000c2c826650310000700d990 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 200632068 1250 200630818 200630879
    0xb07021c08161b060905010e01090201021f110f1306110607120216050303040218040213020d0618020706050606040f0509040c1a0c060919030809010b19 67
    0x1805884420003604004003200c0e00792264501c1c40c0329412a40701c51200500401c00701c001404c100300240b40352542541c1650907c030b4428031440303050060b000d82690681c0241409515401d104e10301400c001c406040e8130f030f03d42c1d19480d5103a00d0f50000d4000600a0b59000e940d40f00d051b2a06c410301c1d2016032180c001d1240c603200c0364510580100345d107507000c50241800c0859290b1881210002d01c01d681110400508840604081c400c0c00030117584514401c0d80d0000002c001a07440550010b002c4034005e50040e0380010303045c40c61203a80c01900c0c2c0f00e060f280c00880c401d0740741d51100b9031015403032070000c200c0d981c00704120003485102d0250542100c810740751640b90a040c000c42c12080b0246005a40c010032880c17011408201888031004020220000140c500c0c034042c1954000960180c84024520300c51000825503103107020484540b018541100e02c0424155a9001e0305d2301c900040c20144195070f1030000c041e1a0b155003410260780000e407041d403003100342040c0840d030603803100500c5414110200350 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 200633318 1250 200632068 200632123
    0x315060316170f070f02010e01050705070606120b04021002010212040807290a0902010c0203030d02042301020a030f2d0908011e0e070f030507060905010215071115040b0702 76
    0xc24540c4c020318189806555544403480c02d0380035000841003c500c562a2204111282e5405030217010b0f014840c85c428000c095540004402055942e80090140001100843d0051074180c6100001c4540c500001d401e2101c0e40c030401c3e002441c11141a81d4052001507008104103e001ca0070481d2810301f40a100e02100303d078031031000750b940241244803195070f031904c14055a0203250946401a401000c80740d403110fa0b6a40e000c00381d08540b0808100c0c0004940b01d0051071070401d00c43c1d00012041c1d0003420300c1c2d5100d84049070151a000004da050140c0000640540480034800e22000010318060280340e182c40b840084c158980c07039005500340d07454580c1820f0b840081e5400c490090401542c085800103442038001d003071650710390020040004c0c41a001041010200fa02000ca4031103807126480a079a03076006a03114500320a000c17040c2144000010586c074015054070401c0301c0c07240d003101c4402900000001702103009940544407440540100b081c01e81e41003140c0a03000340303108404254111143c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 200634568 1250 200633318 200633341
    0xa02180409050604020f18090c0111120706051b03090604050c0406082a0303030a06051009420201050f070906080c0d09061103100b1806031506031617 66
    0x10b48004e126052039815006e090342e6501e00800c2c0c5040008641846080403044075980e20102c581d254007040010005640e450001700b000728070181030b21081854a0029501c003001080003c081003002c00c1441c0c00810340c0088840610312038054540186040d06242c24080d150220400d0003a2051703080640901140c0c0c40403c403c0032100f11448404030640007946240644214440c01580500c4040100404441541c10401c06c071600cd403070071480207002c0441110200d03c1070080fa183c1007600d4010400c9456000441d4081089402003031079480980e00710107444900030728031240141c0d198400c0c04180d0469a11080d0030800604004540074075043d005031400c40300900401c280c21001c03d00c652552281d03082648440e9000d04100107101041c040c00d061504143c50404c0c0c5446400c07000700b5134044220442d20300141d4401c80103d520030313a40030005298070051032451600f960382034019194031050055030140324501c2c1030b0f210301c833410040188030100c11041b07280a0440c2074203000700c000e0303034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 200635818 1250 200634568 200634571
    0x10b03100b0604080a03080103061a0a14190603020c060c160b090f03030a0609050601020c0f0d08070209010b030919020a06030504020627010f09030b01090b0d0b0a021804090506 78
    0x2450360101c1d25191450015030709000e10381c4100c3c01070041c3d2241c941095030095032181a2445020300700301c103554150021800c45c0c500107100d60440d01100382804011410b1401405c03440005210510050340c1b91141904c003c801d50003100421340100f001e202c0c014082c010650f01580e22403402c0e00f040f0907030f49005407002d840c86003d8580c8100c1008030380ca901d001e020309440200d16204803a500c0c20005007020080135a440780c2d0315a82c2c580b9011510070b42c4013260a040100000780800d03101c001c0081004649072090004660741e0340104100710040c3c9900207814002c120440c00b20f83c9900c0c0c007004403070519401710710124102d5260b040003070040c4e40c5d150801c81039072108e1500150b030b1399851002c03410a10480311400199171810000c1d0490688016204a0310407082e81c80c2c0c200e8490080c0c0544000c65a408010324041940c001440031035610341c0200d229240c002c0c07552401c0300c13640c0c43c4c140031210152010303c0b89035000100e448802031181e21503940000240c0c0d0810211003103450b0180c44040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 200637068 1250 200635818 200635843
    0x3090a060b0a0b030f101401090b180904050318061213021c0b010312050405010c110105090a1811090d1202010e1605090703020c06010b030408120c130503010b03 71
    0x241c40e80300c2a0161103180c1c2c420041c24114000d1030340c038100950310910b404401c4030707041d020780b502100104105401d840c120402d2130040c0c4426002ca403c14403180302d5600300c005800143e8000c2036a81045654440c03000d80103c2c001d0010303564603640c01000786401c82549a045004200030000c00c1103d040c00300d0740075482880228035803407401c0c4d5071000411504600720803c1040504500107001d100c9100d103514102c9201e86c5c0c2c010800e240c1c028094550307000c0d501c00d407070102d404840c104001c03ea842d41c40c4049494140f400a20b0540c0c41000101c400c0616002000c000300300840d11090000644034205900d8000d61105007032070303099000150b08401081e030090201400c80d00c0140814002d4000c90421952102654012030509039200c0444a8621034580f19200d10300105124034003d20848182c0551200a00b1150b030030300c001540d8079440a00300316100780040041c407954110807140c00d406082030628459075040088030601054442d0f411043c4242d1510140c049181d0b000504c0642105 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 200638318 1250 200637068 200637071
    0x140418030e0103151421031605070f090b090609160c050a140312131205090301060b0c030c06061009030b040c1203121d030406120605040207060501170c0a260708010f0b030303090a06 80
    0x18409c0c0303031080c07d01485910225400d5001c030800700315840030f80c020740a4131505a03420300c2e03103035119401c205d2600740c00d0b5004184408410213a140180c810450600710902a5080354001c0445507520740c801c2e0040380701c41800d500041640f500c0304043e0207525400c5024040e01010551950300d609290a0035805030320240000010240d445440030b40081c2c0c01403a0500314161218451074213652244d015012068083c014000080c50a00c0e100d050f50a0200e0347d6a030b44844103045548d102110706001e4404e07903102050b04030015215018440001c0001c0c031aa40e900400c80010326001c003a039000c04911400440c0c012100040308000106841c211009483c0450704070242c7c0f48088000c001d26040240c0040c00000c0400a00c00035803c0a81201c0151091702460f542c1e0a0460b0f0312485407000e5140d200f0800c4408100e0003e10040781c0300c580182201c104c1d00303201c4800702240340c611154032004c0c1c540d4440b0340421a5070398511a4500400054000d1450b51805c00e2145444200340e1000030940c9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 200639568 1250 200638318 200638357
    0x3030e1b0f091e040602190201140103121103160209070c12050d0b041802011704080d020d02160b01030302060907080c040f0e0a030504140418030e010315142103 71
    0xc006a03010008200f500c82c8a01c445042504009010750b011404088510600020310704966105214010701c84600d896840003507400d6613070350131802c45400c03030070300401031400c1d1801c084034000e02c000c1615401c0c0030b0700300d1101300035407041c4220100020202c0b81800101540200456541c1c12848002002c3d071410503980e4a4104017440204001c000403a0041d01e00b642422130341c140f032210110341d24002d80350141f0a800140401c94408400c50b002080c5003402d000025420b1441d4016202601d807540015041404080707096002c0140440140c540618a0b4010030a054040c440a500009210050b04401d410420030030741e103404420140c1c0c0980d54500ca141598400355106d00c10601c2900251030f007401d10b600b4014100c0e04140a902c00c0440b01d0300014030b0a240900c00c40725020501ea40c45121198140c41c262180c4d01c40070100c0d8103140d1a500c1401c0c5a40f00550000054500402000d194154038014050814010031070102051410350701c8024010000055800c841c003100d240030b014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 200640818 1250 200639568 200639581
    0xf03070e01210905011503080f0a0504090509030a030b032d030d0204030803071e0e060a0c0b010929010c171c02071511090f12030703030e1b0f09 64
    0x30a00c1c0e1052a0310844000c4102c1e0841e404642002c00c2150089000b8084124800091009081184401015120108130311160803007076102611465542d0300b08a81841d68a520842c29600c080f24940000d400010b01440d0b480d8041c401d101016500b50024500101a040002c00e00480241114200a000c0c40c403a107001d18208100d54030268003180a6496a590f441d21943c55081a900140400d0295030528140b178805070002e00079042c2940e0b0180052040b60600c074480d030007010128104071089428401180c1104121b40c024400500001810244184041e103407480c040c40c2001a07041090341d2407150b0f030340000319840070768000c0c941c0b00000340030350a819401d10440c1d00104c0081c018102c1c1c520342c1c0003a94003404d0214001c80f02e5040c502d510214020450350340007000c01000c9801d200ca81d495041c001c81240440001070501d02e0300d6160f80011500d19004100101c00080e02c401500400340405e00c80c1c42142c2201420310a45040070030000740c0400c07103540d0510302900300d00c0002042e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 200642068 1250 200640818 200640827
    0x610061710090f09050d030207031b0302030a051804060e0a15030c0e0c1207090e0705071a0916030b060118060c08070804030b0f04120906051801031103011404060b0f03070e01 77
    0x80e450388041205e0109180c1711b0007401035080030340c050740425001c018600c0c500314541107140c8170340e5065001c0e51801d00b90900641d55034001c141a00e00c80d07407a4028101142d291840b40c1d2016101c5c60001c0c031039038a044003000c8159080b15843d044802d4031010204001303060b102c90380c000e403500c3c4041650300b541c810114075040c1c00f0311000d940300305840c0410f001c1181e03040740201099901e051861030466442c10030a503580e1003032130002440170740d484652448149030751040681050440068420341003110036030024104e04c5420680723464044000307210312580c12055464074461040260b03084a0719000c3c02030061001d00750040c1a10700d002900e43c1c10004ca4001b141e028551140c86100d031030404000b06401c0f035800f103030129400c0280300b80c4451290f006104603004c4501a40d0350514041140c007040329071804100009041c035885034500410300c800507002c2c60280c0480c61000002c1b880e00310400050b15000e03486034410364000c20207084070400d14012261f00078605d08140950141603030040300c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 200643318 1250 200642068 200642081
    0xb10030c09050405030f07080414041109041e0c030b030c030c011e030902060403110306060402090d080903030706060b0a0e01080601052a0f0a020a0e0f010608180610061710090f 78
    0x2003002c1c40052011f08200c040300180c41030b0f51403c99202e00342c200c80c40500088a40c5800408410a8107003e0343c0c0c094034068011000503182c000c0450740d15000b00d008003003600d0140b546003005c240c03030314485459400c00b00925141403008400401c00b10009900182a040c440750300348411854a203200314125020790020862180e016001e507540c0c1d5500e0070f115031490103082c150f6109020301d030003003800b0349498000d036514039200034000d4100203042d60350340000703600920b809a05800b0070320245003c0303140341c03080c00f0091412450450341d0b0702c10288001c00000c01c40e54002e040c40895400e01480e80d038000c041c0e40c040110045080c41d85a443c100035808100c0f000c0d09030680d80305034215400310307040c00b00741605020300c00d5581c4403066072108076804640d42c0468891010514001c010415a4801c041d42a0460300c88900511a0764044100c3c50a11404580494014500c41810081a64809800100031101d801001002e003000010b2850400c518070645003010344a40c510f0307403401310303039840354 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 200644568 1250 200643318 200643337
    0x71715010c08031807060e13050103020906120a0f240c0e10051303110103060b0319050c1306210b1f050c16050a120f021324030b10030c0905040503 65
    0x40301703016658680100301c014850300700c900400c400c1d01040c400500d00e00805050f29401480e2400d07954442051001d5500d0404a40f40244151841c2e500840d0b0103002417002c0d180030380402c05030f00c65103100380c0348210300c00612843c0c0c0901c1c0c81c514a0720107074400c040352001c810865030039082d801c3da000201c51900806990303080406c0122000030401c0b559100405440c40c0c00c1c1c03002c0c8000c3d03554030114111404112454101d5041071440400012002d03482640e02c0401c809901d0b081c21400d24000001c00710a40019020804070b10860081491580070313031b29805000c20007840740b4842032010403803510340c1080741c500d052121181c0680c0b40f80100141c40e184808182211689807070308041c4190325105204590242903403e42c0890179190b071001c01614580c005181c207010074440d07401e00c5070b1001ca0800c1d490341c2a60320782140c06543c00748110103840f44d00001440203014218200507440b120003030101c80315140c550808100103a040701031003003101c01580002a2a544904000342103120f0302101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 200645818 1250 200644568 200644573
    0x1080309090609072c0909010506130c05090d020a120602030609250f02100f1a180f06040906060308030403020c0f010e01051b031306020d020c0603040b0601020c0603071715010c080318 81
    0x300f20106a0541c0818803801042f80d04100d0200c80303041c508210381c0d40c0c0e418100050810010312105040c0b04460b0b0080350301c040c2160400c03e64421005007c03c42101c400c68046400105212481c41c061000b250072801040c2c4c41c2031100b800d44160b44040c00343c03079040818001c0c2041028031507402400080b070200181c8a0a03c1844a0403c80500a007400c04090b01c02c80c0000c8090b201904012801b03207050ba200003442c0b902500d80c0c101d0044c81810082600ea03105445800c1d2500084482c02680003c511035503c05449050624000c0e04161484011500414411003031b8a030580e400002044943c4080c00d040b55114489a005004407ca202c11020217210001d003000c50b02000c9500e03c022681c041d1f080e111060490743c000ca8403844100000c035400030080c0b000ca0045400048810703040306050040700c0f211a555004100203170000c4076a4008281c00612000416500300e2001c0d510011507d60080988002130000c0c00d42d200031200034212103004000580c5000b101984602d64901017400c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 200647068 1250 200645818 200645821
    0x100b0406030b0409050712050601080105040b0f1801020f0318010e03041a071e050d0207080a0311030c1501050f0102031c150803030f0103230a08030c0405060301080309090609072c09 80
    0x10038003a440803080c01b159588512704c0002220391040c41064080e59214291038020707140e02d0310007031f005580a049900710200d0326440b06081e040034030080031001c0409006688904c2c090003591141c843d241c800748007d906100b1011055003003c02250159008800c08000180d00042403507000d00800341d000301848041d8009000c1400380c85800341070f05107d40102ea103002c1055101303c1e22910241308950700c580c050410040000e004541140d206211503080f00c0c102105a400e00c2e203491381110601c8105a0020018066400e141c00300400c813101c28001549484107070148020398000700b0440c02c410942e00c416420034a04464040030003002e0503000c403501c074200744808024220007031200301d4101e280c1c4a02c6081c0f840032000700482032104140500b00028450f2103441c81d03548014070303404210108200100746592900081c0d4041e00e00e4900454807412440c00303101880d20090f111921034003074901042081c0d40d000c0081850441e102d81030710b080307420741c10150000101d103c0001c2d0703004a0120 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 200648318 1250 200647068 200647079
    0xa231005041e0506060a2a0b1f08010204030c0b16081809010f030203030304021e190302030c01031e0f0204030605040305030601031b140913020f070b100b0406030b04090507 76
    0x303040da4201525502c041049840e100c0800105200740300040d8007140c0c0d5601088008544503040304440d000b81c549400e07101c201a5250700010b101155000c81240c281c04220030070b000010090000303403c854000f10b1909055840b0022100e482d845400d402c00c4001440c16400c2c400d607142c100040b544a0100c3d510344100b005e040b00014114035409004101400000541a02d052168001c480d00a00074600e99200c035001e1168880340e180001011b41c411946a401544440f118110b5071031884811300740b000e00b944109410080111b070a07a0400d824109141000c1203030408214030f510307200c4c000052201d491100030010b03006550003d40f046261004000034550042d00461044000f6601004681001001c001d4847c511030705032400030343c200d0482d00c0d10209150007806805c01c01041080603c40d03558201d010b907030044081c034065103004103a110821107050f802a800c865100110104242001e030a050130380514800e40c802c1607125464014103032a9944000204d40e04101541c000c0b40c0c460 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 200649568 1250 200648318 200648351
    0x70e04030221091f02010e0d0c021f050a0c03090510030f0b010801080316050a0b091c0e0d02131e020406020c040b090f0709090603030f080a23100504 66
    0x60440c007449002ca980802c0100d89202260b020010040802050010461948890803007003440802590b59480c0c4480a00344200480700240c035066075424006034461040c003c0007884514001e1340c150f200c1c20a105d00c11740290070b86500b03084a1030030716442541800c045942503501d40c4020b4004104040018100d41c0c140c001014602810b0010301c03240d02c0744c000458840c0c1c805d1080850a410510000c48000303440034040d60392500407404c5072002d141c0354503244008241518000425070061203455481c44050100d024082000e003001d14140c1c0b03114021400ca40c60fa41c0d0028843c2050241c0b402c410021640001001c00040b80e00c0e100c400480c9030000001d501034001c100152003103041240031887c0078050b01354015400790000d000b40c0c940307000c068024100070b8058400c0c0300c145040420303064894450301004500a80d01e01e548485030190181070141d000d0001060141403880c0048140c1103c2c5c0d140b07280022800d080340680e075810402c010001c6558101076030060603c00b10724201ca460 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 200650818 1250 200649568 200649583
    0x10b030105120c10030b0d050601170d0f02030703030906020d1a0108060a050f09151504090507050306031b0a1d010f1706310f0b0903040f17070e040302 67
    0x2628598682c440c034084241e40c618407541d203564000c40782c01c1320a0b80d031486038000603030303028015006040140c10b50791078a0903c8400d07005000c00c5814149904052802008030b030640001e07074100700000030314a041c02501d9107d1314a01034107040e290300e1300800308800ba0741129101c00104a0422104d030b8208100c041002c022000240082d0403400450890702c2c2030340c00d8508950b0010011052950114180001c03924014070b0485041c0f40c03012400c2d03440c1c27100108a0010b08c409010300790b5070303030600c0022021a40302070500400c105040c0104032258800040389200d2517501c1c84645594803040c1e00213114038074281c001d4201c44252020442051600345081e5040c1c4040607000c0b02d0494a402c0d8181004503084001c2e00140d0201c00442d460814034121f0418100350b1140380702c0b5503107100c0d41c44410044019030499940310082d013007206002613400e06a03000490040034500e82031810108404401050041407160040104000091401004010000c10340e00302c031014203103803a08029403103004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 200652068 1250 200650818 200650829
    0x70b040f03090603060b0a0e15070c0f090603110f21100614010f050a0c0804030f0204050a050f0105100908070f050a0b19050a1205010b0a020f0102030610050306030a0605010b0301 79
    0x1814480410354134000d006100a492a413128a42003c207440b004440324003444d101d4a810900203a44582c008026034001c00b18540900f510703180c1c2c54078142c490203801142e0390044110500c1c1040600000e178444070302d030646180450b0b906840508c148001005000c6d0b0302d002050305c1d5074440d040d41c88680c0c0416400540c400c0d08008000342a42c071408940d81c1c0c0e540c10300b030768005404a070b42520901d004070b004e01721040140c0f80c1440700c03001680d10000c541c0c0c041d800a85140526419540841c906405841d900c01d0500034140010304145000906208041c065540f045c00400325000c0c203240306614080080480508a50100f5900d0006415880c014000ca2307015040681012400403080011180c10b22101d603c03d460140f07010704100c49030f40000200a0800445042d0101d620045008540c080c0001a140d1641c0b18480b600281c580f90442a0410081e40140108a00740e81c0b0b001544150002d203081142e43c0b0303981c800000c0c0c1000201e03140100800d103014000300303995422801031410384a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 200653318 1250 200652068 200652077
    0x105010f0905160e03032802100b030c0607080d0608030d1802010c02060c030f0f040503010608070e0a15080307060e0124030b060d1209060e120c0d05011d01050604060f05010f14070b040f03 83
    0x4803102e042402b900c849088290709030f0710807040d11826040c604000d021040c059503206040924005e08103055a20035803003c055036202181b00c1b400741550b0300c1051450f14044122012600322070340040c12805d0f41c910082d101d11130100d00382110000c01d004585001c41d80007580c0307070385510341d05038440a07400500815000f503180c0a00403a1a200008043c402c0e00c07400781030040c0a9440b83c011401030148080e8011061810800001c0c40c12020005000d41c01c1c4101c101140300340b04600500c2c08c5a4003101c441c009200380c90041c0c039003019240501004c3e40c0d000040007919a8609000c0f86005510314001801d01900011841050b64050540e0041d01c401d50f0319841c40d82c207040d00f0450000c5c1c0400c000009600040014502490b212400c990791500c0703040040703500314075800d1402c1c5203400c4c0e16054405945445c02c100140c44e0621412000c2c00340e8203ea41c250780c1c00d0600080240c0320b10702030001800040441d18801c906c945e4291100d4907030000c03d443c542e1502d443c0a14510900a40c12000308 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 200654568 1250 200653318 200653333
    0x60f0c150408030a0f15180506030c060409090501020912060703060602030f03010501030903020c0603090c0102010f090f0b07030603080a0f02010506030127031e020105010f0905160e03032802 84
    0x115412400e140555000402103081d80c503010350582c000d00030055000e40107507641610101004946884034010183c1001c1551440f1481000ea4150f590090000b4841e030014003e0985642c0c650082c3c4050f45c4001100158020891502d140240326034507443e075210605529860f21100001800d500c0740c00309580c203100c0315589040990340ca00843c045884414810320052080d54403990044c2c1545010348106c59101c003400d00418420ba00c03d9680320300c550000782c1005041e58090040c00b28040911204003c0710500d0b456004c03003a40f0a0000820111005002ca002c0c01d201e40c20034405140c10a1603d07940c0d00015401a00c0002c1c06102c11000d5402d0200040044c41d040c1b2402c10002c0e01001814248600000003802407055004201e00380820703c80840021000c00401046003101c40e000001c965040401004030120558410540c1074104000c1000245450200d1010015641400003901d5041d10000f421405408032040800c6a444214114149500004940c000c80c0d6001d8034001c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 200655818 1250 200654568 200654593
    0x140c0c120c01020f0a030e041e0f02090f010206090a0816050102040b041d090d0302030703023001080d0e01080402041805011401051507080708090d03020601050a09050702101a060f0c 80
    0x4605d42e07200050045402400380e00810b044c16080082e1110307003840c40300c5120542882c2541101d80455120007120341c0421110503c0c280b2a403100300050003400113000760b2030b00100c402c4e1344415805000f042c2540202d0194100d64003011028001e9900c41e000307549442d2214020021508648203c0064280410380340508081018846002c4d004060140042510034242503000c6e60024110208050f42040350320300141c0340900060781d50412548902d43e4106a02c41c1408048040e00107000c190403102c010018150407502d100340100c03013804e111301c007070340d440c00010b0081008001146c0184a1580384004014040d0301c00903220411000555444e62207000f440070b1038211185040046104004107030208100f03902030b051981c85182d1031843c0c248120081080320b00031b91400c13030150b4004001402589000d5200b40040d08000d47c2c00c0003613140c0000e00030341e00d94000ca80703e11111b03941c808c0d1680c0004003084c14201c90308090001c6540d80c0302001c1140c00341d8041401c0031050301410100242 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 200657068 1250 200655818 200655823
    0x417010c0e0105070204050c040f14030f01020a02030d091505070807030507090617180106030f150902010801030f0311030408030405040f0e060f100e0f07030c02010903140c0c120c01020f 82
    0x759140c1030756120708007401542840010400034000181e107035810304c000506038040303000800142c4480f0b90340c840040c0142c3c0c01e262074591403201e100708c02d034018401c1524031540003041d52802c0080c00b6000c10420400e0900100c041c2c0d40c4c0c3c0e40341040c541400104884180c2104009005605598007080542d4540b44112200e01c82c0380224400108141506100f940060104a420413154a06160640c09144240f03084815691045604c840e4440000d8140145500c604a038450060402e00c85400950b000034550031050000501106201028030309044c07280000f4008141140100c1e81d441e80c407100080d139203801902c10244994201482c07031072040c265000b10441c8500ca00002d001584034103046d0500e602d8004d0882040d101e95010006e0403180c0084018082e07080c0c00d001c0c807910305008500030152030100000c0303015a03040c81c58117400644e1192180c0591501070081d152a040d80050581c201030401030100d900c00691240c42ca846e160104449903060400d8084404683d10400401e4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 200658318 1250 200657068 200657087
    0x507110703080331050c0a09020403020d031101091515050102010905060a0b0102120a050711090709231e0901061d19082a0a0515090a08030417010c 65
    0x140000028801315021590664081c4242d24041c91580d5040c05080840c0f5558002407000f84c9041d404100c68511904106002401030b040c0d1800641c41d103030a40d00800c24000d184c10b0010100f1404414001c808103003903100380081c9a109096203940c0da420f403001320140c0702c1111070014002105800140c01d600521541c80c0150f406006400e01da90341481000050070600602c5045d40282c0244071204070750361009004081942d01e402d030f00e8581c1e50508007030301c03a00724124500410150003030148007504003040c41c085031520b08001c10703140c2c400110000a8031050101ca0f03000710001e549400c804105044890750100305441d81c0d0142d80e6192411140c0070510f400039401c840c560b500c0320b10b807401d2101b4224401552600c81114407131381c801956103010f2800d0904400c2a00f002c000030540007040552130610102101c10607422400c4c000042c2d01100180d4065031040070001c4d02407402e440300710a042c0241426402c0d261181c0d43e4504242407100c1d2108651915441c0412844900c5d01800005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 200659568 1250 200658318 200658323
    0xa0f2c030f0307020f270a0509010606030b030c040c12020d02030108060901090c060e1924140d02070c08030a110706030c0c23010c0201020904050903030402010507120e10030507110703 81
    0xd0324884801041c1b090503116413140010720f00c0452084401040c1c0320f003809000f804a000000f40303078504040c8650031900c8070b80101d4100750600c4c0c1c1050150340e00150410001004850000da240410f40c000d4401b0142d10a0700c0502500200d00c0805a00042d0301660480b01c03501e041e0341c090796500d40b025007200c24904c401410b0800482c0c09101c3e07180300b20b00c001c1d00c100c0003501389081d08005005000d101420b40e4800701e032082c01508241154500d2144642c0f0610190030405490500c800242c1094043d08045044088c0d0100b182c00500114a82c0100100851005d8994803182a0401040e20b074140400390510301c140c40c4001889442440303089e11400305540c4610f005c80540d5a006055035240e003800c162070069030840c0389811000e11032105409255000140e66104007030600080d510000c1c0000c000703420900c20800542d810800300c1d034159a1040b1060010803120005642c0d0303420b00408190414000c0b81c01034407081e010351000b0700540e01e5480300200b450b50700d9162682c408460000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 200660818 1250 200659568 200659579
    0x4060320120406180b25021c03090803070f1b0c030b06040209031b01020f06060a1202011101020d0f141b0a0c0807060504031808030a0f2c030f030702 66
    0x50301d600401500002c0e08103205a4022840c3c5003d281181c0c0c21141465040c2c6184035441c0610150401140e180703040c816400d50192150414508003940701c460000854821016140d2020300c20b900c658000d405941c1e1002c1e91680301d0410701d0006100e41010b40380500440c130201c41c104221a15011f2103070000c3c0e840840700007182d0031603441d48540d4074041c2800d030b001502480f98140a54090100c0c840d108442c40c1d241c50203c0760200020700c0e0004c0315108071205c4e080300091048540300e440c40e88082d14201d490800300d02d1024801242e9421018079075171015440891851050b41c1300d90084100303a03140c000706002650203c088014060001d9905424100513045843c0409681a01074800380c0028148800c0e50f4500d52030b46420b41c5d103e183d0444855035960104070400d0b4000308441ca18501d001428507010b410400300700d540344030700c1441d80140a40113807203010951144100e5115481c51000402580071100024042c246801500501c00c1c0941511619052341c00403e503064203800924 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 200662068 1250 200660818 200660827
    0x315061205101d030d0902010f0c050c10090b12070306050111190c050406080c09070201110f0c011b122418090602031602070803030c181f0504060320 66
    0x1004802088020380d24018641051101143d0070000e0001d40301400c0c828002140501d610f20004100542d14520709050110700e0540601180c0e0004161040480603682e1140c1001e4014040d00d401c445540310030703940040054400d0b40300ba0b2000486001d844561800d21140f6115001594900000300b02e200c3d0b198007040447c500001a103940ea8007540c0a0001141000d445034007040c113603007650300000c0441d44082c0101f081c030b0401c042a641d100c2801c4c8020845030440da034241003c0e20a8440034030180300c1c085900380180d54207601c2422503c13408403008061404c4190301030080052052200005807804d50003000c1440aa030703c802c5100449008003003482d0412032844841524080c6c81041b650b80c03089180700064040c4011400b44410203841403503502d0582c002480c041c0590804d2005420910501c131240c2c5001c415290650440401d0f6000100c1300320102c0ea50503000d94403280c050000b240c01c041e8440e0410010026a0f0840c0d030309000c001200c1500040c4a1044d14903c03000590410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 200663318 1250 200662068 200662093
    0x90203070e062b1a060703090512030d090b0601030507030c230d0203010605070c0603140609061c06060f0506030402180c0d060f05040e060601090611070503070315061205 75
    0x600520020140c0c4a0080d90b85440360341a00702092043c000c0032143d03030b80341110160b10199034003606501c5000c0390440e107400c0c0f40703075402000d201e403500c03800c1e0241c650900718002094080c416101d101001c8201000b0007074090034400342d100f40a4403518082840c0c10040b506071072080c0203521000700181c40300311891900b4452010409094840180e840c0818051349200442c1d81c00114001c02250780c40039218801c508100d01c0f071003a01e034002c100f8140340c880032602d00e10b091012a54010740441d95280182e40d540c01144801c000c03400300300084801d0703040000800a10307620040548100c10425107003180c889051190520058901940c44400001c0420590401d0700c0c5040c4c1c4002c1d0511040d0911140040203015212203811450f02032031400d600f4800c6c1d04291099201c800d841078000c1c401d03820314a00107454007160f80a444200803a10a501480c4803041088200824014007221685982c03420242d1502c103007030714481901e07402c007000015a02c0c035101403846d8031a0040007070802401540d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 200664568 1250 200663318 200663329
    0xc050603060a030501050117070f06021b04181a06040e07030f0615030309030203060604020301180e030c031314060310140f12150a1e050a0e0a0f0b01090203070e 71
    0x18515648010102d070084001482800f1b858001c04001e05248060301011a809041c0442600309501090254600b0000e2550009452040d016141d20043c2100c0408010901400b035004100c5400c1e40b00005c0e040030004503842d001c42001524800414580f03d600411083d60200e296a41c12a070029230b051010071490030514809500c034041c00262019002c0756110901031503801a0003190405a0400650605211569101034110380440c0740d903060025528041c040300404c0500c081e0b03a07000240c0003000030811180802c0d04241141d8940700300c0d04903807031000c03018041c407000c1c001000b49039003c078203199040d240039070200030b0080030007820a451485203801c1001d101e42d0250310300450b442c498490400c03071040350100744041c2481c14031803c80b0082d083c00141a440000e45031158400305034032500805400308180703002c0401c190b12001c0707065000e06809607440c4c1003405140071250410981001d0000694400c1172a00520382c0e03200c1d2007070700301e00080392080007107203c0800449107860030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 200665818 1250 200664568 200664571
    0xb03030a1206030204060b0a02160e2802040b090a05030c0f1009050901060f0305070e060a0e1516210c0f021f020607090801020c0d20060f0a0b0405040c050603 70
    0x1000700107001c503a6500000c00f03460a030340c440701080c1e0001030001821a414071103505031489945181c8503440c5032002c01d62174000000c2c20500250300d5000542d8280300c001a10b1f00b20001c010006549464964640c141e10b5801034008900c076a00c0741034005250305001c181c02e00d0346000100109041401031041c004540c48a0700c0740e43c01c0040040d00460241e95502c4654041c210559408012840c00080501180c0000e0100024840c0b01422811150749a000300d9044402c08d280040300c00c014500401c510b095003021012803550049501560002c05079103d6600b0b03400740d41130700103030401401d44c440303a11a5180c85a002400180c4a0002b2800c0c0b4a4484841480a0f2951001c410180940c050310205010445c006030820414080c0c2c955001e00c1d51000740086000071844c200f00f000303101356280190903203402401104111750384c3c07081010400041020001c0151174a03450120014011810101e81191910340382c040c50810600346481028441c0da44480e09801c1981404108801d9400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 200667068 1250 200665818 200665847
    0xf0c101404080f0a0204050604150306020a0509040501140f0d2006090d03020c031c120c20071d04080a0309051e06150103230907090c02150a0b03030a 66
    0x80000064804040043c90300681c6800098841c561151041001361400984001c2c851400c0121203020030303ca08204000310790380039500690b181d104040c181c940340100314100c1c0c0d1185c43d00c0c000040101081c603224003c0f440444500510306400001c01c5002c400851001d44800014030719280c0e10440044915540c600c0185014100750348032001482d10020f428040307005820038843c6115038182001a00c0132846180e03c000c80701801b203400244a5150030a185000b96201c40f4172501d418042c03a003114482ca0806000d2908020540101d0380c0d510703c904c01c02d02c1140f003074280d42200c8004004c1090160798082040c61508505200c204c01800310b400c400c0e01c0601031058140b4503d00115941c1e41b0742c9030001e025141d24545810781c8054001c12000150606d4201403070b9102c00714200800481901c01814004c0c03041d10b500d07402a140403165000501d24524080040824940001d9060f0054064801d04881540c0e8a903101d0b0540d00404040c1e50103074001d0040c190300d0350152041502c0d080303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 200668318 1250 200667068 200667107
    0x1a031008161406190302090f0609100305040c03020d030903030e0a0b04030807020118080d17090601152304092d021c05100503160305150c07230f0c10 66
    0x300c0b583c10107030904e9062007815011070780c0003800d140315040c140d41c120780e9248101d1b0030604080d07208003c03c101c2407101e080001010317954030024003049000480c41c170142d5005088043c1104007440c0290000c10140030903008510b961840c5415032402481d2401695030205146050620f50761b81d442c020f03004071800701c1c140082c40c1c1491082e14102c07094180280621001800122401140038050361001c44088249002400c02c02c0842d00000035014111120746030a045803507a070b42c0b8211020000024144020090804e850010a0080001d0815500900c0d000c200342044d5401000f003030aa8102c8004c5042c1d42d4489171040040d041d40035010102410040300c01c5250308200f4142110307812640c1240800c0312250503c05800c0c20000340764040c0200044400e4030f800c6455070741d0ba540c080c0c1e04403c0c101800708002600380303000000380d0b070a550340002005681803040214020050200820508500c1145a2a00090b00003d0525040c9501601807204804c100034226805001c8000070402d44 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 200669568 1250 200668318 200668327
    0x10609170309030604052104260a0506040506040b0c0306010903080d0608010e01061e030506060d151d0c030d1205131514060a05010e0103151a031008161406 69
    0x19201400344c0ca110391300c114054800300e0030000220b003003466000001803032000300384400c4c13101c030912080030641c154101d17606004021001d14480d1911150380c138014881d0059005100030008000b412034000c2d8401c085040003070351100c1e4400c015010850304a40000e4008804002080c2108024031084100700702c0401c00741d0b06c4a00781801d42d190303600812580ea64401c000c202e989000c0c0c18038040729595861100155186071102c5075039501c05401e8901c10b910500c450030420800106004200300b03640d4061005980303e07090035110040c2c0c890540400d01030b4005001562501107011003501000e500d615800d081c00c0d11210009000c0200000075244244174a400410b003151f42e0244440b40c032250106001c0c1d101849078149601c05020309001c1d5070090000e101a0f07810034000f0030303181e00a2070300280d00c80d0111251101d4000310382c03040802c01c050071540e248940c0705000031403080101c0030800140e150381d182440c2d5180c40900c0c2d1440500715003003041c00101408403201030000d07801000c0c41c0c00c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 200670818 1250 200669568 200669587
    0x40b010518060d170c0f1b13050a06050a090b0109170304030b040516030b15030106050907230c071703040509061005041505040311090c0904180602030705090a0e0106091703 76
    0x101e41c02020b031150a1b50000c080d40101e02d0301003141034503464985c0000e10038068000e0101e98003000703c00b6070707030300c01a20f0320700152102d00540c1c498030007484000c1c010b0008a99410748a070080108031500c9001130b40d5404007041d030480f594410025500110000d6180074515155402c100101401c11201e6001d85008413440d52a10509800518000d10403100c0718105051000d5905041d100554000c2c1d060600420543c3d0300c0f039410640c8003001e801d064a10a80d428600700d41000306007200c2214880c00b141240d4800b100040c4e0009550105443c01510001d051629540f030107644551340c0c5c030140c034400140a9083c44070009240302100e003402400d1a454a80c40c0d902d503032150f000d413030005201203410000c0c0700c1c1c814260030207800241e440e1001424038120713401e06071180e0038503a070141c2e8454000180500240c4003007520190002400c40d1241080e4100400300d90000b1156440b410603c00e012032216048400103040361041e4980700041484c21051078000e40d80000001614002408113002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 200672068 1250 200670818 200670863
    0xd05011e0203070207081f0c0e040905030408190f060b0102030c010504120f0338030303091e0d0203030f100504090b07020d050a021b1207030605040b010518060d 71
    0xa00080ca280240c2c030383c500808002e150141c15440303035a01d07500001481400181e01d018200c00b0b04081107012880d0020640d003a14034004c01c0410342c2e0450700d0310700c2040c18050007002810130340d418102507c0c0c0a400110040c140388801710300240002c40c0341c00e0f0b0400041d0140e8419403400106005070703418190729083e200d00311a41110113036207200c000042206980c0e071092a00c0c00c2c1c00f03100c1c00d0801c0540ea0820450480340341060f0100180b030012903914104074040c001001000c0001800c5954a14000540b01d80720180305428014034402c0d1095255402030120789c407440e5543e01d9000f1070460b0b036654031151809002400c000300a090016022810b500e981c05070600c1a4045c481324032441c106140000c1c900440719500c5400c10500f80070380d10343d19074003058450b00040e4a00b02c150210b80c00b100042c62441005021003c0352081d10400401c02a841e00420b100b5030103501d0b042000e81e615400c0c480200c0400c0c4a0071591950340000504030314001d01c5c0060444c0c0510961520100c051403000b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 200673318 1250 200672068 200672111
    0x918140112020301050c160611090312190507080f07030c0f0303020c0f0609070e180d020f150103020603070c150e0a0c09060501020c0d05010f09120305060307050109050d0501 77
    0x101c000344285441030543c02d09000b499040f1403110131192401056500801c503e4090b01d070000c0500d510360721024100ca00810988044400c002d09a03441415480300342000e41c0e12250864a403030b6a0911003182e02405a410b4a000c1a00468a41c3c54186501c1d074403500c55104c82ca089080c0b100208200c0c01103020000001b11061103a180103a071107025802483c5000c60245a01015a010400f08031011101261071011210b000341085070540347c40561884051902e4800c08691140c1d00e0b080d12820340c000cc1c580011080380c001d440914070083c3c1e030210305244c00d0102070740051041012401c440c2c402c075009840c1c00d0143d41d1101581d006a014042039602d042c1006020b0b5221160b08010b11101040250003401d01c100108040c516110000c3e44030340303181130740e20b12851554003034505204003908044140707518075108101c68025403030705200650400d0359110000b45050300160031400d0006603034080ea90140c688a111600c0c00c400c00072801e0450100721015505c2c2d03039600c44a02c14142402 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 200674568 1250 200673318 200673329
    0xc14030d0f0b01020613020a1502100f0903080c0a05030c0703030209130213080307050a020108060a0e07050324090c0f070b040c05030d0207030803040308070c05030c06101509181401 80
    0x200d026140c0750b000a01c1c200c4c0241c69042400300002c03043d001699144e508504840d85240800c06400000006034100f01e64a8051102ea60078400c08901821403980040b42c400c0c442e441d070100c00e03240d00714540c0e034600906c0098400b2840410224421000300d0000c2c04586210340b0740940b501403003501080d00c00c982070700c100f1140c03034001c1040f80f010081100c1040190007071000650608000d92203160741d0310b03108030002c0d0502503841c01003a21174a903010038101134109a0240c44181c00c00120081690341300703c800100840100138400e640b034070728001d9501990740c004c005640b00d4554503440410381e0702c030900e51503684004103c070200141c4220841032203036000c1d18440618500e001300345401d00514a40c00b03801c540024200307000146a0ba0141c0380c0041d09494481010380e25140107441c5125800405040740c4008110403c420400090791b42c866810036440b14180c5175588003106003c0b900414420101c0e491210500c4812840040c40c501210300d0000481c0b5902c507181c1ca00340c0c146080e000b1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 200675818 1250 200674568 200674571
    0x513050613140307150e0f250e1305010b04020c1b040617010615090b0304080d0212190c03061a03040501021315020114100512010623011805010c14030d0f 68
    0x850017203446103840300485040903040281d100c0d0b000316280ca0804910000c443d0801d00e81191711207201d09002e0240083c10100820b03410440008048038213801011615903003811142056400d1a0003910f1010382081c1c0141207101d0020a201c01c044004c0d800c0603000342d959800050002e450001080340d0150003000014003d00b41902e000d0032220188003c01070052032201088400100b04c1200d034480d800040441e218401c0028940c06441160000d507007490411080c000c3c0d60100c8022a1060000503904101800d100a015820380c0d0881c882c3c1e41e0b60902d440804500400003078001c545c050300c82c000061805039100f5010919101c2c0360092010724540d00240d817011a0248150303803044022105140751840c3c080d071001510025401a43d00905041410480f840c2c000d40082000e42441c015042c0d0403404150320503100314104100d180081d810502049100340342c03542e40e409803041a503425600324002e445d03000d00d4030101111f481c02c900c001c01c01301c6040c203018442c3c88080d0480b50300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 200677068 1250 200675818 200675843
    0x90518010f1508070f05010c0f0606030b1905010605040501320301050102061008070302012a0b1501031a06090d08040b031b0c1e0a08040f05040513050613140307 71
    0x742c00420003125080b031001540312610500c5101c80c04207040e42101e20910305070300d40c14414a4100a04e1106031802030a03181003400110402c007845100511400945404003c98000c24980100740e600a20604020400c20001484194821400311141c008840c0c01e00b103040304044118494401c203498400c0c91403078080010300c59507905107c00307508403801200c072700ca62604100e4400e8441c80c05100c02414001d0301e003100048200b01e030b140000b00d01c0c65110036103400e0b051410072100701c84048403080c51b030303400302075403005190301a2107000160000c00302404d0100000005120b0140c0c000060650301180f50321103030000403080760080024129942185449040c0309004802c4200e08141d24808400c0a200180324a01d000464403290f0a0714032811301200403000101e410030081001c0502104070001780400e4410030408910105e0704142c0f820800741d0354640385640301101e030103c020312640160010035000b421104400c8185401840c084c0c2c140400345008500e581e0107690308481141c0d00c00b4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 200678318 1250 200677068 200677091
    0x12100b0103050c03010303020c010f031d06010906120b010b0706020f0a0512011208370e1f08010e090c0d05100c0503060607061e06030f11060f04090518010f 69
    0x2d003034004100280c11404c2d5410341e54069110f480c403d241d00d0402c0f5811043c03582c005d101c2d40100200c08517100c10304072403d460301d40843d150304003400707264a481c0c10f180c1d00044000520111078489904013204580076403d22010011645c00500140c0d1030580078030007058103003d40401000e4840300d0391180e070350b10307034680d0400d96088005a2111182e801055a5000440c0042c004c590010f034040d04240c0781c881d4154607e4004404003003410b00c048061081005109400a03c2c00c0c448540403034201213040b000500c8e69400707102407100d880002e4031b03050040003002802e03481150001141010f9a00b040c0c0701c031010412161081a056420354840304001084803c24801d03850345090614015145190980109075a403003803000040c105951a01012120030b02c5101c442e8061000c244240000ca540f81420440f1142c5d40750191040c038143d001c4490076207842401c983e08240c5070202c540c1014907040c0f00c01c00601e4000c20b192500d00e0114294180000c0030310904500c281c0100780002d1118680b0b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 200679568 1250 200678318 200678321
    0x9031106030f0402101701080703031d01020c01120603021302040315090803070f090512010c02060a0510061202090405100807050f03060a200c011a0316030b0612100b0103 75
    0x9156050144108005002d81c1200d00700e002039000d501a1800d5501e0314202c0e0045885224040700c003c03040c0341141c000308212034045500e8046901950f1102d503402040b10900041000d02c008081c00760b4448081222194011141d81c1c1a44420b1070b0000f81c003640d284c01180705001c01d100c0f55020b05a0000d8180308010501c60200f881e10254002084000ca099451216901c03004d408901841500c2c0c8480c0051881001c0c0500980f00103000f1609070520340b40054003030508810000c001d4080c03040064003000061007142d10540100c2c410260340c501d04070007920140101116029010b400708146002900c5078040e030f501400001810002c4075240515107424581e241c0c0002c0d101c0d4402c07202c08145503500144441e04881442000581c03801c0c02c0c0e0100c1c80c81e0707000c040e002c3e002080106885460f0207041d800081403000d0411a01d00316401d401c1050384600040480c0e01d00d00c152500b0a0002c00c240200306640040c002e0284081c1e404840c142a117440884241c0079501c0791140081400ca5905 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 200680818 1250 200679568 200679593
    0xd15080d081317190216050f0a03050312040506070c05030409020304030909090312050105010509060906030c0403020d060203060118050d14010f18050c15030f04030c1a1b0a090b07210903 82
    0xf40c40501b5020b6652042c00000f050300f441058451000313001059801c3d41c0b0104036500841d84081141e5469412a000380d90601048505413900c0c004e10f00041c0d81280952542e0280a038060003a514190a1100c00f41c0290009003095040000c9000040b0b030701602032252445a50103511002401c0c000e8040074070507a00142c0056042000900000c40141c0b0f90805651284d0000c8411307980700d81d208a0744413000d0103154006580945500c5d034000a001c0103030700842c050f081c223a80e42d101c43d201404584406404900c01c1d9500701116101000110b00c540c0070710345080312014004200d404200d2402400cae15440341901540401a0000c001005010049111180b030b0665019070b000540030b2052105c0d0000400405560440000040405105003100d501042c0d00540c0300030002d2038001c21480b401c10481e82e2020007083e00f00e1712003908800c50243e492800680d03403a16070341070800c0d101031450717001280d00b1a407258000c1c58a08000c90480307100f0b40850010b035030300354a00b13141d402c01c078045518 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 200682068 1250 200680818 200680867
    0x20a03050a0512090a0302010c0503090a0617090109031b030201110f0424171308040b07060e010506130c020c030f011e060305190f14030d15080d081317 67
    0x40260003001c2c5c903542500421a902420518900d003500d0400341d00750311400682c66840300d04403c010469a0b0018600307090301c401c1c030060107070540d20030b00ca55089980c1c4030303000390104003000001040c0d00485003950481c2803080c400402c200c0c0c4400156042c940281c4024a00c0d208041401d109520704400700311b02206003e001d500c4443c81c854400b8203144600d481c0401451300c2c2c400002c0a40c68448016041c03591310050655032076964904800454201003000c807042400c214480e003c000b014000c3e540180401007001c3c030343d84510380344000101040100d54055000d036109100e581d03030741803204079000d6040e4000401e40740d0410600c107440001c200e5030612014074054092011660005840c480740e8462610341240d06c48030b0a1101112010314401040308140c1c04030385081550110203440d50408840b01401105980088069100e400303000d0101c0c0c0c0c1d03206c0245480703220b204000c110b401c800c0c41c2c0c0f0f00700c0625085884240e01c814040044100981001070644140701541c3e240c0d508804 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 200683318 1250 200682068 200682103
    0xa0e0d030504080d09081e0417030901080f10091b0e0105030415020a0e030313061d09040204050a020702030a050a0b0a05190b03010b03030d090c0f0509070f020703020a03050a05 78
    0x905940d0350740080c01030f04c084400c2c4680d00d400f50700420000d8802c6079891101900b007039405020650185e0200c0d805405164000001d130201070444480c000103403411900143c40c0c01c1d10300e5842c030714030b441c0b5040d00911403001c16048420010344017502e48605403c0501c007292442c82202404400390800024a0015041200c10000c0101041c464080741e204041c0c01d9502590366050759400701e0f503142c203001585a2500001502c0320756100d500308a542200c078517844244410600f00a000c011a1600580c650007030311000000300140303011b03800707281d0000c0b40500050074242c0b9134010a260045242007110240c1c03128507141c0038403800d5403405922140b11074090110b882d11244164140100043c04480ca54035500710039144d6600390041d4155801c0507044070345030040303818000080c1023203910070b4910805100006c161a0501d50001c0c0c02d4a0024000b511552114030003100d00cfc04401c001c0d1821030246e1078000c00180e413042c8083c001180203e0040003000c2c031a04010f401c04d50b24544503407030078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 200684568 1250 200683318 200683321
    0x3060316080303040311070b030f090d0f0203040302060f04090603050d0206060904020f1909330b190504030c061106090c0f0609041506030905100c08010e1305060a0e0d0305 76
    0x70040001140d0780a0380c10319200c40340218040704507103080202c6d00140d00e802404800c0251066121000d9841030011804072142003040e04015903502544100e0703000160000c100501c00750820400501c02443d0b140c0174585016a03503459001151030315001190150001d80c4000380c0c5580c10442550040c0e0116918803180c00c00b40e0000c0c004c07400e2807100a00518481c1c004690072411000c482d4001d20050000f0f0107081d0084030b4401c0069051000d03d581d80996041038510901c2c2c20601005460002c0d2402d49841c0c42d018054080500703400b800001c01030b0400c404000117205100580c01468103072034042d103415164968038240f0b54000e24400c20750307125081034152a80c9894040d59102c1041d100c030b030303940d043c004081000317000e2000d20003085410282c0001200e82e0706502a1402a0160040da0140381c00b015404051302c00c00c0c051100040c9400340180300c0d58842400c041d8209d8071055812075040007541d590340c180071342290300c0c604082e964110200302e2a8144040c0039000c3c41c929082100e03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 200685818 1250 200684568 200684579
    0x30908030a05070c150c120519030506100203071a130f0f020f0916080604291503010317090402070b09010c080c1606020307020f0f03030109060609060804030e0a180203060316 77
    0x15aa00e080024187c5010302c50354400680c018400c8440321070b074100418280100030100034000e4041503410703a002d03040d984404054140701109440708664030081d069040e191003c0c0e10300e40d2500240502c0940002758681000140024080041c01441607642d80c24880e070318010000e050000d041702a01a1200c0303004c1202040c46002e0b030702000c1c61903040c071403c581c03180c10114008102d01c0e10354020590440d414400c809030f0b41141400004412036143c03521b040d841031030f020b190200303200050144036225054001440c034280a0b04402501820050902040392505120040e0a540b2302209075940c0c090001903e0707101141c90303808030f035404230340b49000e60000848035109460075010700095400b00c08100b50503c00d0001d0382040101d00c00321000354448074155030f105d500a1043d601c15600d061400206103024002000031207280e5120614542e45545095070a42d130712084480d40188072031404100040d02040b0107d882c0e910650060720b03803410070705151401200c02c1c01d0001c09006800100207 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 200687068 1250 200685818 200685827
    0x406050a05060a1d070504050a0b0c070b0702010504060f17150108090d0509011413180b04060303080402010c14030f0403060e0a12120e0307060e160f12030908030a05070c15 76
    0x4c2c15a007042c81800503960804111224040c0741c00c030136446074040358001000002c0001a0402c6804031054440f0182d91303103019100d030b01c1032980090220b4814001000b0913030049a180b60000a281080b610080e042c503c9012a074104031120145056104002c00716135030b01c1507091340e001003100000d08039a04110400741540c02099002410821070000d00c1d480030348400e050b2041c1c40c51120704000302503166208842411400414010780034a4918540e01d20b2400380291000c42c4e1b0107840e04d6100b030721035800454003c001445c01703030b4505042c01c0c020031402d0390400c02004200f01d100405500c86007580b501c6030070348806450040440e8031290301980810303880c5403001c0420aa50800112007910841410040c0c00c401c4010603042c0000301d003102c01c1c80034a0300b003001e1280b458425640031007212485500900d0043c018005203404001050060194100c000008540241001d030a125610960580313154840e81d10baa00040300880c0c0042017154200300d0601a1810382c07000260600d0183c1b0042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 200688318 1250 200687068 200687099
    0x170d050409020913060b041d0f131a010e1605070b07031805032101150f0e0609090c0705010606050a020604080a030902040507090503060c0f03060f0a0e0406050a05060a 74
    0x14540d0b940014045101c2da0b030000301c480300c410502c40601203a43d4558010500360410311a07148500a221200980c044440c0300d01446040512030300303400385e01d4190b515001d1190660f42150351141680100401c184c03030141c4c940c002e009040c3c2001952901c9100e0000140f40d00d001041441818007100000440e030039511640211245000070f000c0352103180b10581d10000d40405002130100280d551000c48600703400c0281c0b07401d0861220780c9a6a50002c08012204e110000d4000914082d91941240e01c100282d0107014802020070b42481c1b02c0d200015445e40c0140c481c80104c04000400004000080c082c80e4020442401c180b42041c12030030000c1c0d00c64100810040c905080041c44644803400303907000040d0190090f000700301c2071501e810041e0500b8054010786100e4480c081c00a018200090308842d06010758001072810740d01d841052010800c003201e00c481e8000d0014402280d21001c0844080c41540a40001300b035606108203503404590010b07140c2030041c050f4800500c211800380d182c21 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 200689568 1250 200688318 200688329
    0x105040f020f1e040f06030209030d0905011706060f0d060e1806040b060a0b040603020304050f0303010b07020d1103010207080a030c0e090f040311030a0c1a01060c1719050301170d0504 81
    0x19082041c02c00e1483c0241e204540280305e03d280f10400c007090320355141c1e0141a04401c1a0704458a8440881064070381d0300c401e2040e940060103124201102c01540100310740c0142015001e2814070441c4008018540c02c8101c0aa5405a98543c1000b000c13081d03a540c030383c00c510b02c1d0683d0400315290346401034950340c0007017024003110050004102030381c82e090704000041c41052001a00c8070744038a4010044c0d4025202652030340304000c10070320080f80c04000c0324100c0701010301c901d00d4000386d40d0a010a0fa00c0150050f00c0010700954000c2090301c0030b00040c001c0c0c912945600f45d45004401c0702408a5104030079401c10410440c0844003603848910400350441003500c2d5806840da5545030494048a131810401103501000c0389068945420803541107400c1d12a078082400c481c4034841510416100740308400005460506640c0840c54084061000c4042c01e5a042d10740b04810070030000107039a1030182c01c0050000401004120050310000ca8810951009080c14030000b503001440d41c0150b0050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 200690818 1250 200689568 200689597
    0x1140a0203130206180409060902030c04060608060d1505040c0303140f0427060b0418140604021b03041e05040b0906010e030a2f0a180504020103110c060105040f020f 73
    0x300d1240b11844036917284290010300034400c107881072510001600d6043d034128040d110380c130710207900d514150141205445403503455204030740d04c00301081071800b95507030b040d0740300f070795036400484c3e00400c501595110310700070210074102da03103113146c02400ca1100501d5051107420501c00c01108800280440f800c58402e850504851007032070500c100302d40221881038800500d0110001070030b0075010098030488080380011a034100a022015095458690410000085480015501c0e2406601518105000241e00200b040c9464003042c6103038025000110099495111340c403140e92101d4070382014020649003840600b42380c0c000325103014009071190b814001903c2c18100700d03031020460b10981f20303007000b1005405000005240e00c411000007103c11942c0b40540719001e1070909203020021648082c49100c100c0307090f4074200004000280017281015160f5040e0950a40164043c103050462030028200e01d524280400c41259040d82c0c0d4800030724014040e1100d00c140e4202034810a05d0076804 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 200692068 1250 200690818 200690827
    0x1513052b080a2606040c0201060e0f101a04180605030604030e0301021c02090307080d02030304060510090606030b011e0c150902031509011a061c0f0c0201140a0203130206 75
    0xc266100c0903003440c4420602c100843d8451074542000381c190044c03100784e5040004034907101d812401d1720114010022407215002c0030a50001d519659a503000410280c2841c1142d100c0ba48004400c00e01a00c60303e59010104090018010704142c04810030403502d07080051624020209444442c0140090240410000d0703c0c40c0c3c5480a40494003125244543c034a01c203400244094000d400600d5058060b2040342d1020856450002d1903030366000c019001141155200e654241c040d02000300b88511501407204009403541281c003440c0c0c0580300c81c0d1804105008010001400e90441560a0040785520882801ea16030440c104500e11500000d03525102a041c0700203401400c00f0450094051284546010944c0580f902c920b02031007601000780082803030a02207202204004070220b9101c24108640301c420441e4211082604000b00404070340f100c2d07140558400c071803a011141000d84d45800c41c140681255801041d40480c91120850079800d051910f030041140081009018440008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 200693318 1250 200692068 200692087
    0x1050f0405120a0e10020f060702070e13081b0a0b040317090705010503010618031b051302030603030a03050a0b09040b070e0118090b0310091104050f0601120b1513052b08 75
    0x1f4082e14800c4800c2110206d0a003a84001d54480c540c0c4130b04002c1035820408902001d43c03000c070b412842900b0219a50a00032007000d03102c1c4406500c0d4120881d4410281d0960008080c0c0c21054800d0340a80c8a400486030340c0c000350840084000e000101039042502c00303000d10383c0c00000380ea06454403032400c5010220b211031448a52600c0f500f0241160904c0100d4003040020180b092050f00c0c40ad8660110552507031401000ba80000e56421b685a00b0503c101180c4520079030006920001c04c50003c20701c3c2c09031802050103200241c60a455580e43c0d402002030341a003044100c07403d00c40030300c1d000e50341d614440810b60030080540683d411442d1914040041c6503002c01504000b0206c05000300710f40200761810790800f039814001a03000c1c5040100080021619100a81c451601078499100c6d00d01c01034051002004130007103075a4001c900441c0d034000d40024178044c0a5540140d035007900c141e0f00b044100500c0c8030181c02c0010450302c9044e20b0a05407000b00c45100042035000188070341b01c10114 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 200694568 1250 200693318 200693323
    0xd050310090501180608030414010e0d0212100605011b06020a05040806070201020a120b090a090501060801111305090103120807030207020607060203040c06050c070614090301050f0405120a0e1002 86
    0xa41c0004803003402c000c00440c00008811441c103010b10380300d00400030150784100541d100d014a104098106900c2c480720b8025500683c1d031102c00d0740c2e0003840700c3c1c800c0c4200d50000b4066080d584010340710b98043c54481008400303070b108003405170100b401c0011041003282c54104c0bd540b40c08000a0201c0d070003040c2441040c2c003420640303000e003122a00791100c85c03600c007400900030341002652000040041003104041d0306a440b030000030a801034402d050341d41e514420354024004800c0100c41c0c0d507680325800a008002842811300c42d04503915455910540300c0034501013641150401485500820300410000b0030071407074900c00003100d0403c00007076940c40400360000d0103512400307500700400103003090400c42d80b68019440703903100d58000c020b01615060211500d00039031640400d0307a408204140410381c09805d100c82e40790000d04111f890843e10101007400d44000f030780c200759044003240901042110600c100e00a0000c65002d4502303040d21508010001080b180c1d443d8041e075000d200700c11282c0d03c00e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 200695818 1250 200694568 200694601
    0x50309040905030d05010b1903020c250e0f09031207090e01030804030b25030209030102070c0f0303080a11120601021c02030a0f0c021e0105210f0601110d0503 70
    0x40003000740304200e08080e0707200e60020705851034862030640040780f8403500000b6544901e40002007001110800a000e40081d4000501c1101c41c0c030030132070340d030034903004140d071801c41c022200404035051450084002c00082c40035041321102c440400400c41801c03000410b48408271101850100303d030b01e81c40c00c03d841d9403150380c0181c03c2c0c0d80030003000842880340d1600100116442105c4ca44055a00e58044a41801c460384500000e224180320640301c19101ea0007422184a00800041c0303410f541e50b03100304d0f000c1841d0b80059840f10800c64104240364014542c03681c80ba5109005104200c00722074032403424420320b00c116031a03620305008140390342d10801060460a01e40b26281982c40307040c201c040d550340c01c112502c0000072504801e8545451040c90500f40321507010700b6402d002490301740c200841380403a04d005810428244240702070a0a0a68029448040d1560503103641c20100022100c00c00300034580d07814480c50181c8191014000100c150b81c00b8a185000d42e2a500c88603460414010b9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 200697068 1250 200695818 200695837
    0xa0506310801020a260103060c050c0615040b06031308070c08010519051006211514181504050403050c01020406180806010609060e04020f0409020a0305101802070503 73
    0x200000204148070150b0050510580031703202c0c00c25032484801c55502d07407110304103240f0101c140380e0010000904680c12070002036000d401c00c9414040100748042c030f484002c403141807106000348454910390901d03119001d03501c0c0003580e0480c503601c1c00e8401c4800e00d0100c00e80c0140000c5002914409100c00600400e0240c010107009000d039091829441c244010640040780c0c1c03051900e03000c070f000021260102c004844141e1075010783c4101020342c250b03e5258070760300100c05680340c0e4546e244410b503441502019243c0c840340d9071601803103e0240f10384507411691920102d0000c00900c00c1148000d1003c04800e00101c6001c074041d41d4529003100d4902845200c000303658008180030030a42d400089442a40d050b1842000b0341d1969003552603a202d41c02c0c0304034400f080c0c10b10014041684260b60140c03050780090405131404801a13004040c562080d40030545655020600c021440d501d40112500721905a0b0103204003424040945904003554540c40320140c0e00180040400500f40151200314a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 200698318 1250 200697068 200697157
    0x7150201230615030106021005040c030c0803040e0f0c040302091003020616050f010b09130f02090a1d0109030503191506020a051002030106020a0312020706060f140a0506 75
    0x820040344141c11000030b8408920492408100d0b20000103044243e90488903140c0c01000c00a9100c2034440060002900940d0550341c1c4890100200e81140303030020080540304011541c89217051000108800c4c0644524008601d1205100481c05030809407000daa40488180266445950b105000b03c0f10301c1d0710080d0060300c080348090010076911124030219010364241c41006008480e1142200c030003a201d41c0e8044100700100d0380e03501d00d20b242c00807440e101e0050100396a0b1150000343e441a01103481034040c540b16a52141c080c0c0642044002480120000f8070604404e6580130f815404000c00a401c0504540415040ca03590350304001c081c1401290420700312600c0e030400a450750315002c8152010f100304941400c00c400b030ba20131607040319550703806002544d07410f54040740d440803400c0080c521690240004408200c45d441243d005005c000c51600480d40350021010301030910b80c001c0b42c403550700d0100c10811078840004a501261031481c944441ca98810b5484031280701c40700320701000d0dd = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 200699568 1250 200698318 200698361
    0x120a050903010c12180f11060f0f0a173904030f030221030703111209060403180308030f09150103080301060e0f01020a030e030f0f0703021201050907150201 69
    0xa03a081004d15682000e01d0005010508010064201390303081030034010186283c200008022503914007032042034400003030070300346000e4840b903450b522608180243c0d2512440001c0c03100c0816080603c1c03514803100941c00d112076240858842031981b00b5185010302c00441c507001c0782100f51101004c61004001000f030951150b449090229189441500403800351281b802d103130709511110001a80311816100b5071b10300c0d503a036116003140904040200a444070405111529241c42842c880d580709404490007080a40703854180204003d86072180c0c02d45034400303445c1c1400461040c1007142c0d484140f035045003d0030344a0100561816440c444d80710010300f4160000703c20000c8600013141200c11070f5649042c01c111400c20441e0403c0303a1303507a850242e8404005100003d0041e0b07501d1728135500040a59806103990702131a410456a01c1c61282c41340c001c001c040c000c528084556a07170354880440200300754900310301a50f5441d40240107858422007a2403e11540a10035003004d4890302c026408400780 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 200700818 1250 200699568 200699591
    0x7030f0b0d08070606090608100207020409060f15170304121a0403020304060206090c131515030606020f0f070605030c07120806100f080703090c09060308070b0f0603120a05090301 79
    0x54118403401c580c00380c00e2040028040e2040c2c016401a1410340000d4920f400380ba27003034480250b200640c00c0703801580742c001c50f80202c0c4261003441300c501c2d40324501051254403d61041c0018407142c0044403100036003100c070085000000207440681f21124a81003403d40203091102814910560203000350240317004002c10154044090001c540381d1b5000c40f1201c1c0c03140701c82141c5038100d100303d03180c20450320852040550380e00d4124110342050060003d040340c0d00d5a1000181110281d040300101e030301d80340304010295040100449820060005e042c203101d00b94013098980c03400703200c1c40042040200120b41a01d4240c0c08960800d54405102900d65012042c0036005a0b421100503103c3d07e04881c40c007d84e140140c40742403034600b165550700c160342c0da40c6030103900406940e841900c142d0550480807900104c02e1180038040c502030b0745041d44910552400f20b0314108000d050b181310000090600482d0f0300c2c00a0140c0b0f41c52554a001501c2d07002c4108215401d010b0091015419800e100c5840038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 200702068 1250 200700818 200700833
    0x303050301421d060304150b03010f051009090209040204091b090c0f020a0c0506031306020c06060f0a18110d1406030d230703020102070206070c0f06080f07030f0b0d 73
    0x100c0c00c4040d11040c0c0030000003480c068140c1c2d0f82c03410090300400100000790000d0050b4260b8100103645480c0083c0b4505c0e0b1a0100e4216072a480314056440c3d501e1041c00000341e1505c10000046c06030700810300118142e03a0105600c0d000c0500002c0c0925200c4200300100311201c0034a5410340e504d51208058242e03070313204600203410a24a031101042d180b00240c52824030114804248942004801075410318160500445600040900c04412100c502d10000520351740020300c9008011001089142410f1041214440801e0308007403190b90001c0b82041080381030b04520035a00c1c901000002c8090010441d80150722610154030140c42c54241c80305900c12010750b41c1801444142c0c101e428103243c001094a0300d141181004070415064000a040340c043d0800524042e4482d20000d420580140d0100e030480e00070400032215901c920b0014021410680300e19401825286000042818504030440d800c01000d40030303408154942c90385400f041e80359008000c86c11400380030010202d055060211 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 200703318 1250 200702068 200702189
    0xd1b0e0a0621080703080601020304050d0b010509011d0f0c0d0504050a0516050f090c19080411060f090f030c0907030e060604060503031b1501060507021002070303050301 75
    0x2488801d24104a20b490203a6040180c9560780608034078a418120784080c0c401d00001000c0710f04601c420000400c0c251199090810781c284607480214880d410a8200031518405800000010700c80707900850b0301c0749801000b0303034028005c4e1640d0790060f10307412002441c5100c2c030b20f8604040d0382880c0510080000000350820380301d00501c240c844c620411428500140704510030b4543c40354003070b5200c0565203044904944c0080d6aa00b02518295080380b034019421070900204020440d444200030600c0070368072031280040001c8035614504038441c09684070a000c0c1090b4240502d011401d0b40380d041d1020060007000b0400205040c070b507031400f20401406030802c1101440385000e0300303010880c1400e180c05420300f0751b10000c000e5400e00c01c5401c0c00f4010a02c584000b1110762140d10049042c0440450206010b00060354480380c0d9240d85005101e01036500c80e416000b1540442e004201180d8842d06990541d8440000305100103150140c140080e212092030b11000d81004021120304d90303001c50fa04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 200704568 1250 200703318 200703329
    0x1060914091e1b12010501030c0e0702060c040b16060f0510051f11032502091e01090e1204090204030c050604080307030c061803080405010501090b0d1b0e0a06 70
    0x31a80c40c100c0040381000c0d1070071060b081030907601180c0d209040b144199144054507602401c4202d201800d40d44007402d60380c0a030b10955003007460810a0248541104580d584102580002d060700d044c0344802030001c3c400c0e0311425061900201d0501550700d2800311788202213410100c140b00c10071741c000f4800010700081d2408502d51f0010310002a150606030341e500c0300c142056030024203000783c00e4000e41c0c070060045091801800108480301040d1504040c144415221110f88010941a0702c1408640e08003d400f040d2000d855084040c06241c540600d03130f055401000000c81d0f0400e804000c07503d4581c51810200c3c00c60030109000c02d200070254007a000300d80c02825524103090b942e1050001612550050381c18642040116801090150207041d0680303219800001e0380170f10900f602c280080f44a01c045001444907001c0c441070010900465016000c9541c0412403030b4022000105200d04d200001000c6110070b80841c40e0342883c002048000b0640351128000526000300040700500f1140140d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 200705818 1250 200704568 200704573
    0x1050708061215130b090a030e1e1504090f0207021e06071106070602040303020f0d02010501050f12010612150507051e0315130b040b1002070e090106091409 69
    0x18886241c01e0b90000e04100c1084090001c140c03075003a6002c0c1c0660024005583c80c00090340410003e0000301210b84281c0c080005819001c00070700c2c005107102070a41c0424403403000c000c0c840c80406412024040315407003c0764120356064940c10310400d2402181d11088515141281500140c140781c1c0041985134401c0b5020004042801c0c500588104003140840d0042410b01003140021981090306c071903108005d0103c1c0c24072040395100001c0e079005400440068020342d1404c010703c201000401c0103560680024401d80d07040c01e000c034000e406500f05c06881210b2000c80d6010442081d801013000d001101280000d001c51030a0202d4110840500208068909000240024800d101355440b07401c001d210180c000d680040c070700059070005820b10301d4440d0741f084100780d15038501202d0013000c3c4c0b80c40c401103030310310646041000301d451001c1e0060141081e41813243c5500c0c0e02180c02c1098511309140c1c120591a600c000b140182480d42003101c4092900f0305005095000342d5400740300e102000308 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 200707068 1250 200705818 200705821
    0x120d060e0115020303070503040606150c0318060e010309020f15030f070203131403031303060609061a03060d03110703060504060c020a0c030803090a0b0c07020411070f170d0c0201050708 82
    0x100c000d0072000002c0300d8401a08240f01059031680b04100a43c3c0140c05071001140ba5500e500d05091103800c62415800401d2444d40d44008054000b4052a0300a207190801c0a03014075103074018002507e6403041038101661080c0107811551051100140f1030b4015010401d80710b40b0881d4140242d0080d0b50019010540d0400216560310000482d1a401c026030000404a072404420000480c0c00b06d088643c140800d1248803040104584d000c00154003400000c10910311b480b070580b0032203080350042c0301d01e203255101c550308001080080340e0304000251107151a01c90982012642125601001e08250090601c000140318680d001310303020302d0141408002c4a9548002603a0390580348070b004040544805041000c81d260f0405142c0c010203940603542d404ca99030382c2e0516001c0b41110600c07041000450000c0541c1818800c104540c44441c0000d0318020300c07a20b40380e51039546d8400080c0000407040002074010031443c1512001c070500c038010700c0241c0c07901001034040c040032209240040e62450 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 200708318 1250 200707068 200707079
    0x100303030e0f1c11030a0e0411070b060d060603020303070b0f0604052514040b04080f01090308040f0303020d020304060b03010506011b0809190f0305060c031e0603120d060e01 77
    0x55081010b5201d5001001c021805400c2121004002da0081c0c052002405030702440100038030040ca40307401c80b681e80113041b90018081004658104403800c8854000b400410001201002c8568102c0b10850b11034281402d40d141c444094241600001d40500000c01d006080040a00d61349000d008a6850303800140e0b10790081c0002c9610841d541c16072401441214113101d031021850030010881c3c7e180241c01c401442c0c5201c04160703c030341c1c0840c40307003071000070100710030801071200c00e0200f01800024080c107201910020480900540007803d103075020b601100425000c1c0d4111001000000780541d140d10303142c20701d0030080984144503030007942414001041c0c0d611401c1c40032440781494020314840c05464840d0030b440e03000b080304140c00c10640700f07010003c0dc0440b00c1a07001026600c4003540b015055140403030034040b0160201c005200c09005002d40c20034010721101812074450060200750391a000060f20744450781c8100e0f000c0c10400561000c90b048680c00c84819540c4944c442401a640d60 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 200709568 1250 200708318 200708323
    0x9040606020a170a0e0906130c05040302040f020a270305060420030c09070c03030e030c01020309070b04050d0b0603010b19051806060a0f090905070201020d0c03020c1c0512100303030e 81
    0x5106060001d06000c0174603031135140051200c0c0d00314801604045e131000010351307580211411800c406c40420400f00d81041185068010118605510710701941842002c10018100480c0000b01481c14451800724000c40562a54400000c40d0401e00701c99090506041c0f00f15110070521454104811000b03070f103c19820001180100e4140c0600b4182d503a6031002011a031000341020220201070300e03101c0228400700100080c2181191600006030b4909010755281d142841c070780e00240c2c200b0014001080345a440c8520200041d800a0180c1d5080d0764000c0020700400d080804a9401070040f02500815030001c2403103826207a0903215005004201c039044680b0401c221204d0350700800c00c106654407584101c51100b07590096080082c0e4154940001409903001100c0940041c2e43c041568084621b40b401030014594503410114901280c020300701d510707081d08802c4507181035050710140410510600450342700c9412a15030071520706000c044000d402c20075100950000f41480b48160310050007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 200710818 1250 200709568 200709577
    0x2b030908031e090a0503251205030304291003060606020703082a030a02030d0c080403081623030402030111030105060301031403071e0b1b090108060609040606020a17 73
    0x1010454109070b0011841d42c42c0d40d01124001e5042a421040018541c44c10031901e03038403a22860407100311040d480c0041b615507000c1d5103c0e680c1c880481e00e00002088001c412241c00c117800c43d40c03804da9400c4980d110f50300d200400840c45a8a140352040050840c1e1040e00e01c0e069030700c50b240c14001640c0e01d42d0100d940e90340b60302018142c0a02000350b00341d428000c1d0b4000060498291b00f440b018021a081142035400008424015030030004444542c6841803150862008690402c1c40720b0741001c1d200240590001403c3c091100b18400b214140140900048a00ea5a100141400e001e45184105c515a001528100d01a6007070a0100c2c0350000298103890503543c0141c80182140c0c83c607225000c2c600034029a45105006c00c00c80c62010a4100003503040d20036031245140480e9409261461608100801000055242880041b542c859140031a02405024a040c80c02c544035500098002d2040da980316520504c4c0c00030000b052600868441c404902074a202410000060400b10b200d104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 200712068 1250 200710818 200710837
    0x601140a050f0d0602071514010303140c1606020a060e010903020a020112060905160809062401050d140907080114010302130f050a2007050606060304022b03090803 72
    0x4140c100703011038148102c020b4801007004101e0030320001191511801c9a11a450613240c0c240c0054441170120507601892200c02c640387e140000640c07642c0c40040078064000c06000b5110382c0000c940350f417680d040010410100c000d404541555a60b140080c2d51404100740c111134144c2800303400c034030342c140c10300c01c110f50141c050300074200d8020603030300440c1d14100e001703d807441441e903503a0049900b54252141921500300342000417078440c170310a80030b410040010082c3c0e01301c0c2e02c40c10400c6030500218107104c110715144102030525012000040e140c074004e00100c00c203c145400390b9100d0090540c07a80e54081c004040070b07a40800d03143c421043c00e031643c4a64140c180c0c00d10f8001040141011110314a1501d121800050010700d140854802e460094558012140e22401110243c00045124000850824081e5882d21410780c3d03e05459a2004002c01e00c6880702000080075515000c1d80c56100a141140d400708511701109040141000400141c0000e004440c0200c0c8001c8008200c0b1808003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 200713318 1250 200712068 200712079
    0x30915010305150c0c060a0903031404020a17031c05072706051315090501020c121c030b0907020105040c0b03090c150c120913051e060a03020d080309060114 69
    0xc903010061200082c05441c4c0c0d00103020401c600d650803d01070210a021f080c032507401103120f0140741001000d071a103d142400f082240b00d0141700040c1e440340c1c411822641804050206803620541c400d00f9800303500c400022103d075a08801c40d060b0b116900a51090045482d440b07914407a010b20003200c410045201c1002c18140785040c00100d0040c006000125036080380341c06038540b582c00c2010742c0c4603445214404a50544410701044d0380502201080100546081c0956001340042c641d40347c0181031070707001c07070b000c003041502d60b00e4429003007184004c0001c0c0281c10503050144000740200b104450079074030502100d8001c030f00c1e020004212030241082800416003090043c0401c840a1403200c0ca0a080a008000c03070340a0355070500207091100c00380c03485141c80f1018070701400f00020011010a180500d00002c006040c881c10610164a09202e1805d110030b82d600c0c004200100a9a00080d5005034800700700d07000c0140c2c1c000254880d10380384060341d00b1a641d500010082e400d50300c0f2a01d5104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 200714568 1250 200713318 200713333
    0x1b0d0e03031b0c150a1d0a030f05011508060f01050301021c0c0926070f0503070e04110a12050f06010302031b010c0c0806010329071202130b030915010305 68
    0x4900455012040b65880000d4512007145480021480b043e80282d0000c1e641e00403d07103050003a00017000e1900100301042c80320003001a01e0003d5032400042c00b0091211003000e28020a01600b5400089282d41101c40c070301d1170030303151203d003503803940119200c074a45882e241c008120380c14103009560900307003034122002995900d005e000d40038221040800c020000558400240860304040d02b100404241c103400e180840c2d0604182c0c186801c54100000300c6c01d0390342080260f910005911780840303e180e07a580f429170312549001448041540b400c81d5101c1141c610100d0301000030700220060500c01c00032a4486001204210707101c140901c40a549034210170700f40d600d01004642c0c0110240d00c14584a02041499649c41c480c820050300100343d00d501c10b40041c020444840f8419010308a42a1048402c0d140400854490305000f00b00000308921840c0e06002c040c81d64040d5021410606c0c040048280ca8022514441d001290040c4040c0b10ba4501c2500b12005900c41505076500640a060036 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 200715818 1250 200714568 200714587
    0x30207020a1424031b030138070b151207091a0409050601050312121603060302030307110112020703120908070c08060f0a1103060d11061b0d0e0303 65
    0x180b142000d826040301c000c0320900140300403441410a4803010b80a440d03164248081c52040190515503903070045c4130200014001e00e95598880d040d0321403580c102e0001d02d00000e1003100c40401e501203c0c01090700100e00c032020419044c14a5200d000c1c0c0420324020b0404072f204120a100c607480702c40c22140c0281c00b09001529540c0c100d030104500d040b6440a82210b0600460101d44105400f86c0e00303a048400140480c0c80c0a115007a44000c41d44201401c01c00281c2d01d90707881c5400606840e4051a02c10100c0900030b004c0d4000c1c1d001540c0050640b515014582845030280d015400a40d0020340382c03003010564421703280300f610546901940c5264140b40c1c000c415000915168000b41d4032108180459000250660180c00c090003804000d41083d06058142818442c000380643c1640390901682000710112034080c0c0341e0080044036049295039090414240e01c440c01c06000750007c0c000500303c484144152a0030900c01c00900407079150750f03004001241d510801d81c40480d49a0402c015a80c0c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 200717068 1250 200715818 200715839
    0x1009080702010f030204050a0308030a0605060c0601270905010e010b10090501180b0a05070302160509040b13080f04050a0515040315111b100603050c0607060f0525030207020a 77
    0x3040f9415003001842d113601c403000074900c982e8652045480610000070800204404e00076132004040c00d80300b0701d00f4940c1d800d451949441050141c0c080c200114521013410615115440700c0b402014a81000346102c1c905101d03028201070319010480d03600303118221280d410864110110300419690301b207211424032004569022400c511441c4041d00c4240115042c0b810100510007045c25468107075481d0201d19001e803c01032281c071460800d000c462010401c58403410340c520f42c42940000d00312281c3d1344d03445025098104001015201c03090109400d010041c0d201d004100781d402c1140d4a1220316915400c000c4040303804800041d5032401480104000b84004c0000340451004000124512101604a402d15000079003c25220081c241d200c5413114070902c1070a4591209032001e200341811603d4541d51107040b4680c85000e1440002c55105108050340515040c500c1c0001c20b0100f810709900b03440c0d462804401064550b05108000c00b8064041d20031a8402a4080d000354401480c00c180c188 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 200718318 1250 200717068 200717087
    0x302090117030c030a080106120209090403050a02031204060e0c0a0f09020309120d060e060d030f0e010302040306150f06050301120f02011101020304060603050607020a020d02040b0d020910030302100908070201 92
    0x481d02c01808100345a00c818000341501d220385644420040d850200024490449540003c0c0b520788100400d1a03c0d40b1507804151303000741c05080c0a651110b00300c0d000c9295101c0c0c6881403000d01d046070f0500c000c100711500112410301c852001c40f102891004e00700250354505110303001c044400801c080140c1c1e1220b401a5600521076000e0b1516103140755083d1240740c2c00401011381c119903807042840340d20480b803000b9030400003d695a2415080c01e582c0604440d0001c101c810a11072604c0d1404031503072190b01250065907101c0001e01c40e0346962100d104800000e4028005014645800071800038810000e613412250207c101e0f1961407420b1702c821041b101c1c0b80d103080e070411161400141c04444240011030041d0b1140c2c00004109146003002401d0850140c0070b201190440c810342005aa01c104410391203640444002844240c00300004030317444000700d00290010144010000798010618003003044074025003c0d40e00490039480484100d8008040052050380144120340c00f551048640300e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 200719424 1106 200718318 200718359
    0x42a0e030d030b2b0f0c0815040209070216150302211501021605060f0c010c0c03030e070e0a0207030e032a040c0801051203070b0a090b06030703020901 67
    0x400b91040807020700495040b454117014010300c0c4a07040c00910010381162020608116416140d9008885c280e00c2091590002861301d4004189030584600081100c03050030f080002e50804144440d0104003016403c0c050365030010900006c44a0701d061801d8a0541c5103003400701c8005a1003400e021604540000e44440004207030701c12928182c44c8105c8180317486004007004800c0500554403510030300d600b0b1140c1080b06039000818001054040d6070306210211001c91103503600c89891080340b8000440c903000030302d02c0c01c60354081c0455500c80c0c9000030080c004040013903c0d0400108a80c41d003074482c042e030212006a14803441102880035182444207020840f40031780910b20511556008001003840103140c01030602c101c4040701c3d40244024a58100b030306981000f0403402d8800c480380104d200100d141890000b45110890f41e00808007507542c0c2c2044446d021164680009 = true := by decide +kernel

theorem cover : BRFrame.Cov 200539568 200719424 := by
  have h0 := BRFrame.cov_init 200539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 200539568 ≤ n) (h2 : n < 200719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
