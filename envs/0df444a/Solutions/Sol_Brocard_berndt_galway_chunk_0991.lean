-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0991
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:41:36.178193+00:00
-- url     : https://prove2.me/submissions/ef168568-a805-4ac0-ad53-a6e8f9d17ee4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 178057553 ≤ n < 178237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 178058803 1250 178057553 178057577
    0x80303010b07020906061e0f22030605091b0d0314030a0e2802010f030e0709151205070b0306180906071106070219050a080a110c0607020901090b0d0b0106 68
    0x41e1051503111000306c07071987c50000507080d200070700390305040e06c0709440304046581d24400c401c041c140c82400f0301c3c20020010020a18101c441030b104a48800e0300c0b50361602010400c0318101142d52040719240d60020080c01b50700720140220321001500550401c40400d807a441c20303c4207440118054032611101281280070071008074102040d0449828503190341a108403c80e00720b02c80b81510185e02400c00c040100303002e00040e4050440440c40c0703141402001b101084240c0a640b220092809000c0c280401d980c031040c104118a0620001400641c4100c108011200e0b421000303640c4400003421414014500412070010020b043d603083c291504103034104440c13a50f004900c1c07024658280014640e60505440103900c41c03060300c106001941c003d500c0e200602804001068250350701140c866940c005620001304100f40c10524020f840c0220321288440386010b0081e100310940040104040740d19004081d001410f42c6100c05800c030294110344c10103c0c01d14100c40c7d00030a10b60300c5520039404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 178060053 1250 178058803 178058809
    0x6090606090f0902070209060d05070e01090c080a110306061b1c0f02010b010801140411190801080309030d1d03100e01060608090307030309030203070f11010e0409031e0504080303010b0702 83
    0x2c0c00e403c09192a84180007a0000d6647d4200182d001981511a8a21091907040c0fa60030319010350481020300340ca141c000541d4001c503510080003c0700640c1c841034551940c40165040c1c802e0900c0c9552005405d00c08a0b00c1483c140004008041c10840440740d02a00703a500d8a0501400092298210030070749042055641c11000b85c0d01c46054030b1000308200079443d40060320300403042c0104500d50241c2d104280c415141d90303203d441240314114a0a840700111485160064460f03400300d00018540e4000003404040081a5015070030014023030a181c0c0f0b0314020440c1c1c88144000c030000c04000040c014012a01d0074003288074006590752001c2880307068580880d00b9034071642e0000c420410072008000c0001804005c0e140060b82c1031030046502c1605083c00c0f8654000c1c01d0011b0400303480007004e181023090020714448500403e0700c482400b0f4450b04100012212101c00140106101034411300c6900003904144200701e0b501d052503820240c4542c03040e40f446d0001d03000000030b000c0025400702545 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 178061303 1250 178060053 178060079
    0x150e0c03061f1202160c0b04030c0821090f10020708070f21060207020618130b01021921030b030c0a030c1404020d0905100c03020a0e0607060609060609 67
    0xd0b00c4200b1400c5101505034002c2008115040c0d69240c2a0b020034219401c05030010400f404c281c000443c19200c0d5100c0c48003803815442031104541c0400000c00006000b100031401d00f054803009052182c42090b00804401c0c183e01c5501800e51220b0005400100c554039003400c0e09141d050340d030040045a0500780340314504110358002c2c01100048200c01c2140d2010400120511103803010090b004464500c3c03c88082d0003050f5000b9032202021410300c2c81d105041000803290001180c00c1e0b9003a030080404481207415810b807050041e00030310b110380001140880340030380b8544160948100d04041009101000c100000140002500e469120400346010000401000c5040b5080b00c070031455a502c4c3c070074500d4280319141004182e03404514481d41c542c3e0580b840b142d8501028000e642941c640280c640070501414507603a850060841543d0b0b01c28800e82e4540e004a440f0a024000202d08200040e00203c00c102c5441d500c03000080355501c44e42c0034400c0104202d49507420350b5420200a00c01003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 178062553 1250 178061303 178061329
    0x81e3016050601080606060a03150b1902060c031005060304020a0503030d02070209090609070e0c0c030d060503010f05040215071b09050f13050d030903050c0d02100b09100603150e0c0306 82
    0x5640300c5c0e02400080d5881c4401c40f041e207120307401e001030301007142654155113803a50390001480c0040410828aa0f80c2c010001c6602405c0f80c0c1c1c2a120f0b203036500b15880300740c4d0009840c02d4000103400c5900307205ca070034400021a04240000e0080041c141d880002034039551140140710501900400c02404604160403103a400803950070107805146030004c0700d40d1741d8080500c03c601941c0c01420220b04003540040c121034002165034183c80c0e45911020421024240500c5481d02039032800080000c06030040c0b060700d020300c0c0d0013003001d00b4581c04480c070b444542e0031403c0305880c45001d00d03054805004c0250401002807810035030105444c906014813510b0600700810460076811541c004100054010640d00502612390030006090340e414141250380340210020400507100e0383c1900300701c0035000240c60a68404400c1c0a2100d003001c04240900c0c150141c40c004c44054442c1403c0c0001c0b0701a4120404209499416144469660000c0e90300460181c4420950400000034001c05007410510000e030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 178063803 1250 178062553 178062569
    0x11070605151c150c0c0f0503070b06010f0c02010e03030904020310031e0f0f0c0308030a1a01020102040e01151106070f081503150421020106081e3016050601 69
    0x4280c0903100c9200490200303203d041c0c0141e84601031441e803809840328940260700040358064000e11481c03c030b65aa4412102911000010000101d02d50f10418580d40380701802e42e19103110018542c019035440ea140d002e0954180418803049166031035920207503100b50102a000352035145136091034945199a584420075500c80f8482030301c04109100c080902d40c59220051105605003810000c0101500303030070003040108000103114103082580c20045408941c40d900380c03c010085030059080744501d1145244071a0900010441540d0304544008a1401410242c1b45a803141d0001342c100a400c5600101244050801e03011907940300e101c1d1070340008401100b071000c1030001c0000b991212280c24103000010810001004c00c83c04141e00c503050210341d41d00f0640542c10601c0a0f0180007176004e038548500c41d0b4a080c1204000558140b50507040e1880500310400b20540542c1c25400140c541d600b200080102006210301105c0081807804a4415800c1007851245409401c215043c5d11101c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 178065053 1250 178063803 178063849
    0x30903020f10050f070606120b16020309030a110402070c0e041b051804021906020c0310050403050316090803030a230403020303060112060302030d020312010602120d1107060515 78
    0xb84035000421107102d11800c007400350701d8801c2c1d4a4548058081e80d0030441c00701411010200c208802c40c5011030140d198042224094004c814040303980b4050044542e074194020315660f8041001101c07070101440c80944003510b428030503158024040c0083d840580b2082d440f10410080c00700c000c144c2c1e401d42240004107014103180c440014030302c00d8005003000c00e040c1f20030041411980d680c00c0e00c2c407000005a09604002e9603900001c0e455400e05141e0324040e02455400c0c4201d5603451152074422941502c52504688a10801c800c501d2090350136a82800050040807503032103820409148160440c260214110741d010750301801d0341d40705200004420b41d600c2c0500002903008020340380c2c40030702840c1a5681c2506e058025010b410310303034000f94060040c3c0c038030305124580c007000a240d0356041f11034005050341c0e91002240c0e554103084e24810202c9040c030504508500325081241f088014041241c1000890746600e0300301c3e1000e9480c0c4007100c2544004070250304006524044030311942201e08 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 178066303 1250 178065053 178065079
    0x130905010605090916171c020c1e040f020306030312060a0f090c0e031b0103020307031410150504030308041203021b0105060f1c0b04050111070b0703051308072d030903020f 76
    0x1070b520304400390100411f14101040e0a00b1074400c001004545500400c1103003e050703050301400341340a003000d05502650030442c001d1101c2240307008481c02400003600a6107042c00303682d03941d07100e004090412540300e6980f103800600c1641d8411103001070156110700040d1550f0702c0f5805048500e4a40350301d400380c3c1108644078044070400e06902c0c02032200f800e0159036a51042d0086008040c0032205140104200040c01ba880125110b07110564449682440c1e80e1034000106035001c0c040c81c40014001519000002c000408056543c85442d060741005800e0180b0f2000f804102e403224034101c89039a43d1141001042e00c3c00c082803030100c070340a46400c461100c880d1220000448581c1c0050300060109001c10200a800d41c4a110300b00502c40011752181602d19100504407019500f00300000e00b81404034025a0301c24410101c40c5d50302000e81d03858010190b42c0c1100e03407214050450144001d8445246032801a00e860b2110641f0958443ea81c0e14110b104000740d0a41401c07041d070090144076401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 178067553 1250 178066303 178066349
    0x5060109030f17040902180312030f0112060b040606020d0e010f0203120612240901060b0418090b10090f0e03070f080d020d1a0103050402130905010605090916 70
    0x102e000ba04240c0d4140d0351645031001c9541e03403003180d101d001a248000f540b42d14080300c8000247d25010201e040d102a070b81c1ea0300020303101b4007045c1e44c0f00d4510075820004000d0503d50340403100201d80f00d5400480e0344070811002400b110310030340c48000541c0054071292040e81d40004884501102420710444030441c000c4020744e02d0180b4280c0c00102280c043c0407a00716030f218556001d50b1b451180c11118105207800d01207501240d060602041401c000c000715107184410f011352810760700c0c0807a1550401d4070f00b000c5000070001400e9003003002c0d0350710101740001c20b50f6440c041d4070408070080e02480395482c0802d403400711100545440d5020380350083c24144d45101000316051941c0101c2140c1d801c1e1940d085c1505944107410f55014074500c000b440140c042002d030807080c2e4822030002e1303034902d00600c4030040d0141c0b0b070700f1640258410301c4500c4c92015418142d1092018a02a2000141a40d00da6001c03c0d003106042d01d00003010391080403036108002e0042d04040c080c1841e11410000d1503119985 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 178068803 1250 178067553 178067573
    0x50601090e071a041703043b0405060105010216030b07050a090914070e0f030a080f16050307020a1d0708071b06060905091b06090301090f03050903010506010903 71
    0x62403010394aa401000c041901044140c0c00f07070941035032542c00e40302401c0103068298071500c01d012120b96030542240940328048140c8045518640390f0b8080c0002500c04002c14190804598071448040c00c0c0c00d00c503a180000306c1324401da12803c02011154144000a8901500c50305008054140080c09000154403400e0b0280c200b01c035810102e860b1031510000f0b0320030a109400c00100b4500c0c01000070054034018100a00039803075034540404c0b0401d440280241230007102c0784541c15500030400300340010909402001140403d454550074010750142c41c4207200c00a101c1503520713500c0403d010096207042c0c2d82c1c070740007441e0441c90041c86100f003252402c00082c0090942007480046400903442c1c0340150006040309100039450005d518032440c180006280754052040050300d4800007480e414000510410060200e151480b580b00d013140402c001544860341d496059500d5600030000903a407007041c4451130b4805c0e110a615000c0380014142194801801c030360401c001560200040f0b400000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 178070053 1250 178068803 178068809
    0x609210409020a0318032102032403190f140c0108010603020a020304030b0c03040c090b011b060b09040c03050d0903030e0913120507060f0207020f0d06110d0204050102011404050601 80
    0x1015031602d103c00300030f80051400c0703904050421071501d0345004266100e0b401c040c031245e00d0403007034105290b020401c2d400c9000858041085041c100d0000c0d0b0100c46408400d008140300404880721881034100b82c0c4000710340501c0c200c81d11260314400004005c145e908111480c1c1c4960007d00d04075444000003059000e040c41190180766000400c0412170748248103c4d800345030810700071815400c3c40b480c1402c0380d52046500742c0381c08150003000f08a6804900a440740b03514144d44e80300302e550601d0202c05a0a410600885040380e407006c0709041e0703881d0785103520702c1907005910a42151b451f6051113070074840c01071031a0301080140c56040c00080e0300401c10b40140300d42034940c00c00958900303161b920080e401c0d0310046d010281c0b90702c01e000080c1d4880e0041c6100c1d0300c038550501044042c800c451003a800790702002036000f461082c030556582405846c900c8140d010311008942c002006280604076400040e5210f0a00d400150500155030240a17000850010610030400d51802d03496058499030180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 178071303 1250 178070053 178070069
    0x1c020f0a02090c1e070809040c111b06130b0306011103030c0f030405030702031209041401031101030504150e03090a080c130b0307030b190506030307031d06041706092104 75
    0x4180f500710400a44580300d0130b48845043d160350740340b01c6d00f0061004d03081050760f18400c60070000d11101c2d40d0311490201ca18212017030000e0800c0084c1d410442e800160340345000f03811500c00d11038200b950608600d07440c01819030242d403942d03d0924000040000720340407031300142c56104100b0311101c003000c041101c1314200302c200710b1078403a162450a030303084d4814544013139850700c60100c14030216000381e801840c086070100c40411800c0000c101c000f00151302440040c0844201e4140250194001d07006142d2203481100184003540e1000e4070a0100c0780d0050443c40140d00100341300d1060b0070049141d1002d000780100404250b03d80c200043c1055801d0f038002c0145a80782e00820050b40c800b0891607001d9544615280868500520401c90519845030781020b61400d00340815440d00700801112880e80e01991001c0381800c80041001d800301d24520b1007a0400c4040000040d40d60f621420b0045400490029101e42d00340008010328101c14240c0d131204d8010307000d00c07842c0d0000000045a003243c07202 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 178072553 1250 178071303 178071307
    0x3070302130305010911010905100e15120f07120e031608040f170106061b060203090718020a090603110a080c0d06180c14030f13051c020f0a02090c 65
    0xc030003070942112941c4000c00f1036090184802c208a07030703501e014035204070a0340d584001940d201c0400103500e40221001010540c0210044801d0600c14040ca80440004a00c1464003a11950041400c401210110306c2d890300e91003070016240c0c0c0485680c0d500d01c0f94960a10060030340c7d016150b1203106854100d5494584120248c0030044080140c17001051184041c100142d500c981000c03804902c1034010940c2e5203040808904540110060038000e14040083c44e401e10b0613130381d080000e600285c8490130030310034410001400720f482850341d816101035080240c1c44200c032040207007040507280c016205041c10301c3d040820311103954068038808030715841d00c5102c545491a11a0062041c00616600517060140100d404520f042d00c88001c2130440104101101007140226116040d42c8a028a602010404075021000e4030124542014040b103000300c0d81c08031680c509107020302c1400c000038550b5520310b08503d2141c0500058440011071405031514540640c00600c0c05940100015284000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 178073803 1250 178072553 178072567
    0x70e010e010c050106090c0c0c0503190206031f1202030c090702030a050d1d070503060a0c05041406120411040b030f030409050c1b01360303020904020705011d060f01060503070302 79
    0xf00b500000000c00c2106001c105280e105440140044002d00054a54001c510700003d41030500103103041c20807403c90000c40c400da0580d800c004555002034005401d04c112003c101744581c4c90240e6001c000d0504106025022589205260600181d041e80382c0c415102d41c002c2158441c0c0110807200d41491902c0c103076039105541c0403450000c20320141d4002e00803070541e0354140240400a110790549000b10201c8200340d69a842010030303140c04a26050005409010402006c075030b00070310b00c1c8078140080c419420030241101c540d2015000321401d1710f50a9217036000d204103040a10903200840780c10340280022401d1144225668070032403044c0c00010b40d8410006000290000603140c0c0140c41c0c01c200700440700318402d42c6010b0540d000c1a0800040d68a2414600b0500b42d9100020804101c041850304007058509500a4100c105501e400a400704056000103400f03219a400c07060b81c4407040e0300b088402500a03464914003c0032182c0036400a0010b102886c1c0280030749601a11510b0003681d1004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 178075053 1250 178073803 178073813
    0xf1804030e03010f1e050c0f041206091505041205160213060314030403060c08151306090204030503030405010e060c1207050f040b09090c040f060302090a030c061205070e010e010c 79
    0x40b41d010080036072440d01712030420450b84501600d6005110840c2404107844926448030345101d00c290084050381c041104011040041da6001c007218011000025111a0b68442e850504001d40c08200a955100300f0042048902aa400c0d00c1100d03500c1c0040c2019590041c148000104180103881032040c500c4501a41802d60419005594005084104050904000d40c0d403900503001c1203c55904009003460703803138400c40c14580300f21190b01c1604010071050003409403a80c01c2e1400c118500b902c440012410350185c1c00244010341c890170045a40b85414103049003101c803641040c600c150015001d100e07156080b5010340d0310703400242c4030250240d21400e6090754280b08142c50349904400205000500854440113440c098030705884007501a03494007458503840c403580c09003c840702c840c16024040303203210758050242000080c0541207102c1c2c81c1c0e1036032060014a9801680090413a50300e94800314514019a40c03c20043c3c1000c4240d102100d0001e05404249045281040302d4041103005000b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 178076303 1250 178075053 178075061
    0xc0602070203011b17160e0105070c05030106080709050c0a0504052b0b01150e0108190f110712031505010509031014100501020a050c061c1107020f1804030e0301 71
    0x5200a41e008211403a00c130006001c5401c26028030a6101603140001c2d011400010404d142c0c2803d0394901c3ca40d041d0440041d03c080c0c10140041d03c0b003085407500400e481d14241b0450000c3e001e480001c045040c1b804140c0710a4a100400c15594070005000381c171100d64204c420b640542d0000c4442061105120051003100724801640c01803401c009424607062003034040a80e416194103144540451200c0030083e03400340c8014011a0004d20814001410300d00c01402000c000106180c0c00305034055121001000c0c2c40d034082000c4903080000400d002080304680e2580d85442c0349040a01082e41480004110843e4611a060500c900091100c10f03a59040c0441244e8422007001000640c050303c1c0094030f402402c407542160940401c101182a40c0000742d204415984500140210f440d21400d00031140c01a1001d00918066034148407801c90307603401825400800748064540b1192903004005410030802c1056024585840825105007030034020a984203401d4200501422480750101c0c1c018 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 178077553 1250 178076303 178076321
    0x30c010e1206010905041109060f0f0a05032407141204030c080c0c03010b030c03061302030708150910022503090b0706020702040509060907060f02120a030903030e0606010c060207020301 82
    0x40e00910b40041642d8405a200c0d074001c5009000100110807120240241c6060683e559035100090144000142c5030003480006402d4000c0e101714042036807540400e1801a101c003042400800c18a000c00030381140c10440d65011405140040c07141210100d800454840e03c0200206004980000340c08c0c0350207808040a843d500c4010345550303180c2c0c85101904e80301c1040781c00f0320035424403c2c0c803481c5140c0090000c2207103800602130000c640302c00c0f5071540d2208900300102d0b010b0164400004681c04d0512200081d03070280d000070740c414509198403e041660042c2da0000720362044c040090f000c10300074080440d5150303100fa0b031404c41941d41010b031226812030348150403d10000070140c0401a45030040d0807214401d881c00d00c02c80e203030300754450380750107044a103085103908c00401000b0107403007940e1840400215005980c0c54441303088500140e5880f8616110100b42c13554410340c10540e142c450310f01c4010101028100c03508003480000c0020704099401303444c440d00410b8407020742d50290b007c500c1d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 178078803 1250 178077553 178077589
    0x5070509010305162c06030715050c010e2b0e040c02010e190b061c02061201080d03050405031e0c060106080f240405090114190c0e030c010e 62
    0x515079680c80c03c0b907510349a0344a01400480b48500002c0da8407012508480c160280740014240419a44007182090b13400030005a40351190f240c1c0003c080c1d510650f08000a0625a201036a50510403510750035a1400150040c55902c00740054010f80c8204034580303a8100700280703110305101c440d28211910358076054001c1c4d01500d07040594102a805503c511020303115002510108a4900c00c00e0507013803403500c0003410500801000441500e810a100342104004440b80011000150046065a041350b45003509544e0000b0040c421054104000240c0e001949024803a41c40c0965865450b40103140b08020070080c0c0b041200b0110b030030f0406407040120050300f11800b641c0d5501000302442c00075194200141900000b1031505c001030070311510708505102c50540c05810341c100b80001014010707c620225562082e020320700040410307229000303da9654003080103a41903c0008102c4190502140030f1000000c0c2568035610040741106000c8400d0a110200c002150080745616a0000380701070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 178080053 1250 178078803 178078819
    0x61110020307210e15010f051018091d03070c05210f010b01030c0c03080c0f09030f0703020907020f0703111909020403060b0a03020d02091b0d021809060d0f050705 72
    0xd00d203c1daa03000c0c5403000b2842044074441c80142111081c803500a000c0d0103426808100f003440182400c210888121009143c55070784d403401d800300c420100c00d640c1c02100f001902d52502100714202450300610624003038024510788040d99590215603801c521801d40181000c602c008505800c1403180010880c20304181c480588240d55407038028074400701d56501203450810b4141086104408203032071142e15854400d0103440751018140b2540002511489900e1304008080c0e054505004c40c480070358006009004075425071040004042005203500c04650005a000450490003d1020300f12504003403160140c844290110394417441044179040304a00c2c0c101c00092000d1198028070803a802801c2c03c1040306004403c110811071248000395002600354014005450b0207918183c0124500c0f00d5075903041c20040c0741f00b01541245004500070b513400301c1ea20302500200503120307468150850303082042e072901c4000200d80060707605001c0d20350303d260100441082030810445010b0302e070007444c00d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 178081303 1250 178080053 178080107
    0x12050102040306180314090301020d0c020d03060b09031005040206160c06020706080115030203070c061a0406080304120b07050c060f180d0207060309020301020d020a031401061110020307 82
    0x50103075001e84011200c4601d001d1100e4401030440910010640d4107640350900b68241c15050f03006031b0800f0200b907901d13560800100340307420f00074030070400d41c81c01940250030400780410001d400c45442e5449200c800108002844981d40c000c54109401d200c80e1400080640701e5001003041401040300742d4040d19044d9118605012628040d003044441d10303400c07500c081c0d490340c908840c0c0110a00c20550440307084442c86c4a500d0082e0040c0d5884180b9150074400941d0726281c0030140c440250a8813030104030301e5800c41d11403e0600881000d800c406005515061421000135160342d01c1c44400780c40900000040b4080502c0303101110441d02d00311040390303960304010b00a500d290b5001c1e0303114414076114140c81d00450070040b90800c0e000d01e1580103004001d14000054000d440360440482e45375608000b03000d06d611180c400303000d02d000c0035980003c1ca0a40941e02c821101d0b4180c0080d001d02a615008046070600003402445551a0a1026890741c407010700c1510850032844945000b29618203000d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 178082553 1250 178081303 178081313
    0x20120a0504030803090705091b070609021315051c08030114010903060504210201090201090303260924090a060b04060905190b0a0b09040207110d030203191b140712 72
    0x5001601d10403581e504154072910440c5089c02151a2103100c4000203115020101d0f03580d511184404e800509203500c112040c001e0781086508514640030282034219080c07000341060001541c5000c484400e04c400a09a501d40402c1808144180110035a03041ea8225090340306420000003107506c414144824280740c544620404a200e00c851302c0782c286140e036801085c0c414024070303202c5070701a11100d6207182561001c41d2480440b80c00a0411091074614100880404105920a040600103040c031031030980c000341800114210350758855040b802c02c2c0100260b000c50b000c805154401c500041a00c008000f18000c4d00d0144d002c0c0011600d030104104440301d09072003000e40140626020010906d440d020403008441e180600b448012050254420742e0409a00034011540a2060000702204000010b458140265000c80040c1c0010500c10b9540031282c62503d0b0106080c10122078074030700c120107a1001241001c0c0900807100c686800c90503807070300b444180040e0480d201c0c9003074800c040e8208 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 178083803 1250 178082553 178082563
    0x18100903030c031a0f0103020c0f1b010c0c090c0c06060308030f0115050f030c0d0c020304080607080f24030d0e0f030a1112011401090c20120a050403080309 69
    0x1054000c07034200b48558460510030b101e0500560031a80307101000303a04c4202413144a000c5a480b040c1403607401c00c40e102108200300001da40304003118000b03014080d9001e21000c0703d20084000241031001450451000031140c2c40110140e501403c000900907420640488014188240140503031340383c958040148000c0800452103003013a81d01e0300066036030310081d034002503c00101e030f100016020300c40d004818140600960708004040402410105030001e1001120a22203410740542e00016040242003c01d002d03107030b402030307450405400701c1c5401700039803c403601c00405c80e044580c9142000000d08904400010280c10054200ca0000c0000d1101a0403081054580c0d4425001c1e4581035083d0f103800103100d9074060307020401d03000d20034410040c04034520007491031960954890039605100006510102e00904c0801340103c4c003410000d00c06860200c01491002c9031481d5156180340c1807400003000c2c0320501482c0d880c5540d072030f071024040714140116000102441d5000003801f00100340061 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 178085053 1250 178083803 178083821
    0x20d1b0f030809060907030201120209040b03030c01200405010903020d150f060f05030a080d0908040801020309150a1404080a14030a020c0c19031205070f030801080d050703090e1810 80
    0x104489158585d904020386d5a241440024000791500801c500c200000d07402030300403030a0292000c200c0304000b81c000390664118080c1c44469a43d203102140301c0d4038110541c0c454201d51203039007a103014100b0000030141c1d01e4500002e0301444013021071004101341002e000716051450b5004210b010280740c00030b0081c01c014401c41811402c81c0d8404a002c0c500840c85025107039109040900d40b00c401010032000e07140360303036064402400a0000003400f01080c001188a510114040d102510740c1c0300000404880c0038102c01d0b03400e031038024440c0c201540ca07102c80d41c0080d000341680d1f17281d9010141c2103d040707038006404000f141d808020b0110b0f070f0066801400c4284944010350b24401400c50600c00081300158404000c090349081c1000400c03915102c001c444955803400078036102c49074603554207400d0100d034101e00254041c401080005004d003d48003440c255858500d282c2078154070f0082010203d402101100c814080c0880c0c11003e641d03260250b44a80541039804600313048910030010281c1c15 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 178086303 1250 178085053 178085071
    0x130b010807020708250e070503011d06010203220801061206051f120c0504141803090d03050c010e06010803180103020307050f03040c0e0c0901140307020d1b0f0308 72
    0x203400300346014004640318007581c041c10300604444818980480e40f01d288031440400c40c030780c3c10f0004101030700703143c50b96485042240c45903540ca514019114500e02c111074503610f1035964800500c2003030b0380d000c0122107020a50a0035218100ba681545001840d4264400359056280c024005085405003164001441c0221405c22060f541d0505038245100d00403911400250001c1d418482c20602c3c90040099600a003000051245c444000c035040b41c07401010760102c007548401700f082203110704e0418023510350310310040d504004400b40421800001242c0c000c0074070101203149038100320258003810204a5440172104a56910300c031b00d54072544841d01c541007400c0d6804a07043d155020f4021a80500c682d40d40d01d52400740c1c00c51621809070000341c401c079501c4601c0b0000058425160603240d005404000e081940d8180501c000b429070340c0c240c0f010100d03c080c14010010344035000300341d43e009400c1d18188154240c21141c10303840310b10081140100681010381c212410701d0ba000b0030840c0f1070380c011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 178087553 1250 178086303 178086317
    0x80f010f050c030402010915020709020d020c0c121b060d0c050702030d090e01050405041109090309120106050a0314030714011d1f021c06080105070f0c08030c090609130b01 76
    0x2958528090780f00c1128041d011600700c8a0030020701c000c00c1090800b000652040c0c03640c0782e8489180d41c050303070f005415420328a40c012543d450304c840d042c011880951000c41d01d8048030510900160380380d00071131804940c0050a4812901d00b41c0340e060823a05101c112280c10401c2402c0312a0160103500008d005a009104203c000c240740c0340a4071016040d0b407180701c500c4a1030b81c078002c1040054500100201e0b41148100300303003404c03503c0d104030681c082c09451000e140c59140030000e00a40f03018404035504941c1c180b00d000c00c010f8840d10149004e0325001030320400b0170128511028518820014000c00c0948031707180e03040031100190700450404034546030f0001c0c40100d400c01c080c0c2c0c9090183c603040c2a100300d62070071540400ca5074002c01d50300700e00e04484038031203041d0700c402c40844245500075280d07039440b201005142a07103c218801ca4254608101c0300040d480c0d259110701e800300402400320311400086010403641d440003a10800c0e04e008007206580340d4038509100140c43c8800030f2602040079 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 178088803 1250 178087553 178087561
    0x60c0e10020601050603070c0f0b0a0507090b0d09020622030b01140616060b030304060c0606050108040507090b0f0619030609020c0a1b0b031014040c120b0a080f010f05 74
    0x1000c400c28034010304507402008564207100c100410740e4800303844903050111011001c1c0004501d508000303141c1e070086c4030b8044545800c0484400392800141104100210301b00140301d004490015200d010305407003000112024240701154040c8601110104c0841550400b00448400c1d240d0780401c1d24131561103e05240d0780c0f01c070700041c00491040d10310ba120720305111011850b000c15000000c201e020380004695a00d280c8d001c2411a03000e608551700003009501750005006050207540021710007031034440c0540c41d041d112039032104200e01a111801c0e81340c050000155803031a00300082039200503d400d59480c4212060208040e411180402003410300b103001858000600c01c2da007024910102030642121196220072801e141c0580ca104680940c010100b10714924a020703601c074108001211003071031306185103c0c0034038141031010382c410b50a2103002e04403244c0c0004a80101c10030b0f40008503c030300d00b003c0002e44484440d049010325103d03403c4110709105054100c45d1440c800b4001c1009070780c032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 178090053 1250 178088803 178088809
    0x5010b060702060a11070e01080a02030105060a060503010302060a05040801020a110d09050a091d010507091d0c0708091c11100302030f0411030a080307080712050702250f03060c0e 79
    0x14035000a0f40c01001400101031050084101d01c0070714000c1016182890744030b805a88510f10f007038201c5540350b802040f0440450900748580c54000078111642400d40f460100010028481400024092003010420f821694004e0060350060500900203645940864078010a040c0c0140c10055070b40c8a20b18801040368003d19224060701c1016211050050420003503401800a01e8404d495843c020790143d00091420302c515802030f034695583d005450315060400758107400d210a86d8281c15840303824801c0503c41507003160001c82d444040c0035152000040016280d000401c0700003400307150014520100030080100b8003022508031200f044038030180388102e0403800201c0d41c40c0c109426510104004c10120300d154a04814000c0890380801078aa450401541094030054007003080b031001e000600d81c001d005010526030391a0100903610340064000c1d0381d0302030050340039a1940d40404800300c0249641001001d840210114140d0550301e2030071000808504500900184042c040d2000c20300e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 178091303 1250 178090053 178090057
    0x50c190509010c1b05030304090f0e030c0d080406140a050106030f061206150513020d060e06030c0d020102030904060f051207121205130305010506010305060109080d20011805010b06 80
    0x318040c1d45a81000250b5078078200d84c6501e01412103d207a40f031180000e040e170340400050000c1c104d19a03000c070380100003c58140603207885d06942040c41c0c000b40111159400006204407492200786400c0d181e540b2a13003404070003880000051700d491400b520400c101040c40380c00c118101d902660b000c12520740c645590300c044031103d00400034165001d45490000c1640c0c0c0c0c1001143c03400c0c0550b0f030120aa951000075039440d4000c4c02c0c400b401c3d40c0104410b403c0052520662004180303c21802086142420010752110240c015003882103400c0301203031040d64800c0090701d0711b00030060010400d10f078a0b018121003445440c03103401e210700310030905505043e50200b40001181c00e21510a1082c01c4ca540d1803281813006101003404110051014542c5011902400782c000c0d0301076400060503040410004055820081c2040d0501900e07001c100720205000807902ca00130740c10f251190104c0c90b400b0644190800c14003082c0300f1503084c418550340680651855248440c8610000c20200d01048144a000c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 178092553 1250 178091303 178091317
    0x80c01020a0803150a060c050708010c050415140c0705120a051c0507020d150f0e0607030f020906030a0c08070c030504060804050a02030d0509130614060913050c1905 73
    0x40c1c014405040c00260510040c54000380404048102c6803030200c0420070700141e984c000800100120301c3c2d4003c1c0030041c00004090314451000780310741405070b90060300a10551144544070b21241d554401201d10072b801303880300c42c07600b201c000e59034030140c01e07015948403020b004203440340d16001c54001d0903a200150721000c003a4004050142e510940740351000080c1d428207402c040c011b01304511401039646400070307580c184c4034109240d500c020001c0c0394030407184031001d58100d40b886e00251009441c3c000500651101070360ad00410f009080034440d00c00390007414081608180d01105100e030100a039000030704458010741e502c40f1180c0d19024116400028030b00085c0100b60200024044288a0441154818001d004603040108a80e0202e0718080034035144000107040481e00c11108c3c41d2401d402040310266038418070a0a00701a035103a58048074900442c49548000380440450b00c0d411500030301802c0c06001000719103005041103050394030080d40307a0603000e80001861401e50141054030f01c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 178093803 1250 178092553 178092557
    0xe0f04021e030601170403020a140a02010e13110c060610020d171e07030b09150f04050604091b030b130b180102040f080705040f0b030a0b06040f05070f09080c01 71
    0x8070229807a5015588058043c604010042d03844001741c0d076041250b24081c52280c1c0c000c1c201000c89042010ba0180e45c40740380143d5400150103940940c1c3e1004140c01c2d0400200c40080c2c0d00e03014030405200504c0002c03c0d410b40d0702d03008036940003a4080440c646100d400182c0b001d0156201280c405c07030307c82c10b541000c203000c601e003074440e25080b940855003607a0140d1410441c07085281c03081045c00001c24100c400c180042e4480c000c044690400b402500d8004d14040c006410898810002512841040359040d0041c0d0380c2e10001000380e9150382184500d941c000f80d04515298803000c141e90314400b0b9000669800c804a0082170009060408040b61280c00400b1070010340c0390004a602096282598451290340900022903014240d886a134010803011000b090054580000e10042c0d030417540020900d5407500c0c4044259450100d40024004d500403043c80e89950340c10b001a00030070840240103080d62801081140107a00040304140700c041c503803140400a942c65441d41c2d0b80f01404404640 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 178095053 1250 178093803 178093837
    0x1104050c1c0b06030a091209050109090203151207060906081005040b030111041d010504060b120703200703110d1e020109021c1a06100e010309120e0f0402 68
    0xa1a690100078032110080009008141408960001500380e0401d07a4a100d10590b609403910410102c080414051074690818241c500c1c60f080001c1d0403501a8414107100f10b40000000d142c02c21180e0b6001c054602c01440c001ca03d00203641882e0742d0300c03000c1c096900460f5007241d0128000303009043e058440c0c9405150140090300300001c2c880078040c5c200d1130582564071045d5401364003040300054005820182021082c100300c08c121044920010b0340124001ca15142041c40340d82c81540444280e010703140c01c4500f0036115184224001c014041c10091090211b000002d58221444000c1540307a010381ea81c00c400c9400381c0050f94580c400d100030080494400201c8281c20700e011441c078600c002250000062046140e0049190440c90003030340440ca82481410004105c1c2c0841c9014003d220410100d01d41d1907c0d01c0884c24688584a400c42400103041d0f00c0503c0d40e11030b8001061403a03001d149400c402c0102da40103060342e481d10003000e208400386030010036142000d01c01d49011446032103002c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 178096303 1250 178095053 178095067
    0x114180a0617010e04020d02012a05100f0e0604061515020102030610021c030c03110c03030402090903040602120702121b120102090d0204021e04060203070b010f06020a03030509011d0a1104050c 85
    0xd035039800100c031718050031030030168ae079241c404040c1d103030040c0c01d40078078058880c000c4614505400c6500c2805894801860f043e54100b074000700050503644a0340c824000580f011074500303181060403881e44110b80b03000b210034800c1c20041d41074014501907082558021a41032909406a03180c00c1601641e9400c1c41c2ca40c40340800c250710982281101e80d4440c10300090a00039003405640c2079000085c88900d55100205220850070001d5100340c2c4400e00390044d40c00c2905040e0000c0d164000710300d0380340c0c0050001c252300040d503413a1283c0c5059405000d084400207400201064011100251114070541400c11215400201170003161800000104210481d04650742000000d402c601403c0700844034000294004007020402080608401e40003941c48401520700100385680c141c0120042000300e04080003c3d07600000d40b007030700c980e00d41030109890f950101e981c0d0042076407886150440040c0b00700402804004202149118054509204160810002d00013910401e540c40c02201800700280 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 178097553 1250 178096303 178096307
    0x403051c020d0603030503041203020c060a0218090403110c1014030a020d06030318050d020108060f031c050901120606080c0a0201060b1206040513020114180a0617010e04020d0201 79
    0x31614412412500504001224048404546541c2c0040b401b280c400810300060228140b0303281a01402e601c0c3c25480c0680007038605031034000c054015403940d42c0204110046164035520040e10390805002c640d014078003030500502201a0503460001c0c0d004941d070000a50420070b000900040042c2c0381c8441150b6040543d54895000804400c580d95090001001e0203005000c0c6100650003569456152404080e081c03844400f41d40c0928850b080c80450840140d800102c213641c000c40803525000d01001d007801190401400404502842e0040761310007044507040800b5000c803907001c1e0780f43c0211800c0f20000804650003401194041149180041d4071418070100a00058040341b0001c10b22135502e50101e55950400c511400003024980c042000b107007420320a03203030b10480104d0050040c21070790700080c08400c8121051000000e000815401620b40d1700d10901104001920322008165641001003130120450030740101150800000980d182e110480d5a01031900100032484001c015401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 178098803 1250 178097553 178097587
    0x30f09021c080405031509061e04030f0c05120d0f060e043e010f020303040b04030e040204031a04021906020d08070e0405070e01080603030a09030204090305091f0e09040305 76
    0x4200c0721902c0401021455460034000c40a15001e500d1100100c0d040038001340c0e04140000f0061419070004400c0c4081500d8601052500560581059038508421520881d0980d0405602812910032280d46440d0040d03000300401c0400c01551041000001030945070703042da138840c402c0034402000304d404180401c0280b4440c81c41000c0c3c107600315518640d1045920f20450441d21040340702a0503010500c95540c11201e4006082e45c0c0d413002d14070f1850555a100100780c00508081c0c10841c400500c102030341c4039a8120740140d0b8200a90301c102c2e0f8a50682c1c1e07000c0c07180c110383c1240914810300499291303106080c0b100b420b8910603006400303010b8041e10202d400640c018042c60401c1201726410781240c5072440b50310b0144c0d0b410b503038003a10310000740d00141105102400310360181c1c0c410007040002580c000c02100540354101d40c003181c04076050404a44601440e442c203070b0300070384500c000700003180740700c01c43d561107a140c0d1514030f01e44000500300b00c00b0240844018000c12030801914200d040d004034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 178100053 1250 178098803 178098859
    0x60a0507020a060e090f0405030a08041403040801050a0b0a0303120c1e050705070e0610050c070806010b04030c0b03010506030f040609050f01020406090902091c050307081306030f0902 81
    0x180190810500e900010a107594590000b400718036500d0000702981846240395500280341140d0038003034181652410b03039070f10440c01c00b401088518400314007089000c68107040d08070702681c102c9441c0c9441d403801034000e100c10358600350424907010484405003007660141c0222501a12010440401c000451010b01040d0b07102e481001503040d007205101c2403541c2c0c3c0018400003542c485442e00394500e0414940317000c0760011034443c500c2c00704104080e6100140d00252545c02e01d0041e846030907024080349001d2030741c3c000104500511001055801c00341c8040c1007101e000e000380f1811540e9400404c140d5200a000d0503402110400c00100038002c44001903400c10303c18080000c1d410700a0b00d42c14140140394001414594000070100304659000c1d1491025204139030003149801c0380c1c10001075550030125150b00c2514000352844042c48000e00c280c40c1e015810840a036a03d84c40030700080c8143c42c0301e02910000c40c0c500207441c1103020180c42034510480d80076069a01315580680340f4184090228 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 178101303 1250 178100053 178100057
    0xf080c01050d0b150903061f05010c080f040803091305040f080306030313081c09050a060c05031201090902040507230906250203060105030a0c1511011401030b010909050705060a 78
    0x4803119800c2d02d07a03904124408a0060b240c13a117500b550403c06090034009882c4410715001d02142c04100c29983c032540003203813401d082c0300f88234010743d02d0203071003038056242c0035a410710001c0760020354000040000d00d10040c00f110b0030313070144100d400d20710b00b05e407000d03a00078100c0180b010040c00080d031040000c0d508401d0080c2201d0501c07501c400c0c80d80309410b4640042c900394101c0071004030070102e00940d8201200541c2000e094190804001c03401e659494402c0a0800103400c2414061280500840315011000542c030784180d038448441070042d040701e48007203000da49080300285440c0d00c54500511000005000b0f08941840351a5241441d003110560720342c0301d241001549a0b00d01802101da541c840c00c0c0d10b420440e0302d5580101818a001680092b009810040c4240c1c00940a883c440054852004045000b800005d004541490740320b24084010b40c41c0602c1c1c681d2520316030003284e04a80c49a0300000e0079a0300e851440e0103481482800809170381c4404000c0c4650318000c009090341c21070074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 178102553 1250 178101303 178101311
    0xc06040b070914010c150f060906050f06090d21020a0510180318080706170604060602030a030c0e090a05040506150a05010e030c15181005070609031101020f0405010201060f080c01050d 81
    0x70098550468060250310001303d50394050802180c9d116000700001000200da400000c42d480070f01142c81885504041445040b10310007150401408103041c0102d61007650b4440d403c0b200040c0e02958920200905031903d210b20184111585114003070381e0054080341c4803450305915240e9044c0e604074842c1c0700c1a081103140c40000b0840340c1c81004050003c01041c0e444600b40395941c54005164a0007611150189043c140280109a000011181c06407030310f180c009410482d042c800c0300c0749056001c099501007521428010b1403049500301501542c014010349005485200852560413002104c164110014090812003076019500b12802040007400f41c13900d01b0341c100c4c00288819003e2030f065829800c04904214003030031034103009001206c2541e40000024055901400c0c1c0d0040e12001010b607926000c103101014401c0036100580c4205c64005d6485005008804049400502500c1c0c015842c0510025046c1009a1340000700d0301103101414501c5903c10046032960301100304110031a0312 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 178103803 1250 178102553 178102583
    0x2030a0512070606050f0108061c05060a050703140f07051b06070c051510030602070f02031f11030f0a051b19030b0d11060309120c06040b070914010c 66
    0x240180101e899400c0758040d6036584614008044491039005180608414044800310780d070011f043d0b540105040306d030070641d8400c2d0403842c02c0c4a00102401405401000d0a1140a49035500028000c07250b503207040c03001c1c2031241d2581c108040c0803100440400040700108440501441c002c2094005218414a004211482d910302d0000143c0310f48d00000c0c030172100c3d502802070500002040d03287c0800012041d04007000d00c100307441940c0c00050b050540c002020303400c00c00128581c0c5503030b80c1d01905603000e032400e04d603074400d41c11082a8110300351400e02c080c00241000350f40490384100300c50419a0410746403034842d040145001001703074050461521075800c613100284060400a13034031f091914410690004000c080d5211045c02c94000c20f030030b041c0800040c64100002040d4070050b1141a1659a580b94081c40d01c45102064007845200051220341d40380041111440781d030181c890281180c482880446026803d441001c514514895080c0c000c0d6114462402916010328406840594 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 178105053 1250 178103803 178103813
    0x1215090509030d06060207180c0509030a0c0e0610120b010c0f0c03120807020a110f1305040203120a020303150a05060c010f0c05190311040b03090601080609010b0f060702030a 77
    0x402a41c0c0510690b0000c1900034010303400b0f0040b400941154405000c0207881c001990000300600c1c020141d0b001e80b103030050304c0c0b110b00c0b510540b120b00c0001012622905824202800a11580c2c0541d2041c1007a15000421b2814181d0201d503c45030340307036079500702c480c441b4101c08003c0440d814040d040084036011640400c07007010100c02410b0096848120080c034624012001c2c00010a200003405925001c110b006074001c00c41071500340e0454072040d03c6600180010307600ba0143c0242c00e9124400c070300e6001c13900f003181c1c0c41188280c0c402d50455400074001034100b80c0c3c90041041d0f40c40160f004200040441c60040c80c183e803881e0f0081c04e41c10703015844100256098018980303012544c4e40d5000c0d0600805c6260041d1000c0403a00d01303100740b900500c1d9003203038140400d0b05488001e054840801d050a0454441102d0040901010240e10303420030394049600c0700020310807091203128260125a0100062040c02c0c404100103020380d40003d031400610140b0380007a0016685801842041c1010074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 178106303 1250 178105053 178105061
    0x903090d081e0a09050904030c12030b030106061d0402030c04051002010e2b0c08040902090a030501020c012309030d230103050706090602060c03010905220f02180601121509 76
    0xc1c500d04843d0300c2d206008001030900707450341c2c003081c4288001c00600002c2078100c10411903194020200600030407c000c0c1c29805044a02c400a030158a04400015415030201c182c4e1408481c000c06c8120640380c140401c0288c1c0003d8609280c0c020040100b00101d01d000842179908000a000202d10100d1444400d81407052030b00d00c0c181608110304d00e4064030b4000d81d1100c030800549051843c10031810340c540000da40140d003e4200060760016a00300a80c0d2400c010700c000756480002036595002500115000c5e006550350750b0400100011000c42080c1c0580c4c01c01d01c030305800d400550030185020481d00c064002000380044500d11940082034241d8801040c90107540527a00410071b06182c281c0062600d0f03c01e900c0841103400075414840c1c28031ba608202c2e411159028004225074840c503440c0b09500f85400c414004000700c0c1200303141004812481c040055008540b0303501c20085240d0a074002c004111120b90001e0018110041d102141c0ea0203050405001c1200550840c3c442c10340100b12 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 178107553 1250 178106303 178106347
    0x303220507031b09050f0705090a0b03010320060a0f030203100302281203020604330c0e0103020c0309040f1104060503010312030603050d05030a02210402010e03060903090d08 77
    0x90391584100c02e5070301c0407122066000301401c2c04c08020340e00c0c0154154540c01400780800c0704115000071007600382d5590300d2181001d084484c00e407903500e50b5285451841604003d010990808100c2c262011a2410905884420360b40d80c9969031481d0035100210003d42c402041c6200c0750010150120240e15424900c2410b2403207072010203115000380c00a48003125443d44224078400d048500140040d0b408148503801c01c0c1d010a103441d6504503180c2c3c9a000d10040c0280c02640d0001d0351148840042c43c0c0c224494400007511000f425a910500441c2a4800d8580d540382035403041041d603215080c6503105400c1115140c1c000124040000c46660b440e0303129511a4000600200050040c8a54628138940480482c1420880350f407440c0e41ea19207611030030408200b0311001000090310440540c040720102c0d81b07040340901c0304401e20003a6502480d010b807400e070f000a225101c891081d09000031502d0007a10b21200560404098008000c1d103682c0701ca1044615460511800008504000e411004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 178108803 1250 178107553 178107563
    0x12031207021903180902090d170f120a0b030c0901063006060206150d0807140d1d1509040b0d0213020a110a020108070302031e0c0406140c030322050703 67
    0x140314110b0f84c0c44050400d95400a1500c54030410522a1559030301845001d440d52106410550142d4402000407034080d800c107070250340000150f402d09410b040b00b0440c1c881d14050004000801880c0c0900d56580146012241c1040b109070043c030a240c0207807405501044d52448003658540100c11942109203010541e441c116101e0000f03100306a0103002c80c9a000729070300116107401d01e200000813910fa0715a0b10141105800080306414440f075000301c091490344210481e13451500381800202080d01504d030990035400241165480707443d07c0d025820801c1c9140c41e83c1d0781400701140400006125080040d80d109001207409401621081041c40c81044031400058a80042040c0600150034050401c0955040100020010b030b8102a20780c0c0c210f00303586030060312076991032608a1014000400d1078105900340e000c1080a00c44000200300b0394070030b80c0d02e401855889183c0c40f0043e0140c42442c0d00c0741d40040c00060486040d0948084904100d5000b0204004079a141c0d02d040c07601c03541007a12 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 178110053 1250 178108803 178108817
    0xd020d081801091202030c07050d080702040203070507080301030f1a060306161709060108070506040305060103030c0201090b0c010902192303120a02032701120908041508090c12031207021903 84
    0x280701d000c00e003c110010070701514116921070ac550f031255441d20030390b04020321465001c00400c054600c40c0c8207881c83c1e1a405840fa5139207584a041008502080c4a0111201848440454019203649101030300418010303008000b02e44815208075101301000071100204000e00c1c4204600d100c400306428052581100a0481035041180b0142002416003080303025100401041000510000e2124112601450a10030b101e1062004072803400d19a801030340140000310f0721000e4241e065010a80d1940b00702c07020360b8500c1c034440391140e00c80c02600c21800c1700089001d00040d0384c080c03c1021082038030020b00f9034400211900b108150364010342c900000680c400b09414010140e0041c180000035503e03003032600c0c120314500000388841e140480036030f0f0058032884424200f0100000b614050b000c000300b0341100c80e0170090001c0c1462000c0b01c190085106d1a83d401545080101042e804d124021000d54500500c134081c400840300c01a107000c085204903c01005680710b41c142d8031108a00c80e9491007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 178111303 1250 178110053 178110067
    0x10112704111b0c0d0605091603061506030b0d060e010b030105040308100f0e06060d090c1d010e0606041707150807030510050f040b06130609080d020d08180109120203 73
    0xc10509040a040c02c220391003142921155070701e00760798808450b8440e030302003640d65418180034105214650030a15820144c0404400c006240c1c115000b440324003090076020a694a80c100c041e144020520f5412185444401c4041245078111002c000a00000450300880c401c01082c00c543c0c08540c1580050820b5060120700f100c00701d46000144400308002e0740700c03401d20030360400384e0601600d15845002e00150000d40d0f51440e4102c8100b00c0c3d04880441d0b00103944842600104030302c191403060103035209002152108000c4c2509024010151050b400e007414040f29040105400071030400740d200b001c4000944030700440c10003d0780d00e166562240a8140b0440143c241e03031000d0880d0500d2607081605102c2034941e4986100e10040071200031800000c041c000c200f06100d0514441c0000200b0040422004e800c5603252048590501c216606c00d40065406c98841c0c0d15a407100e0001051034010541c40329103c4115240d103001070000140001984d0b541050081c00400c400d000350b00042150 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 178112553 1250 178111303 178111327
    0x4030908030910030b03100504030302090319110609060c12071a0601020c090a0f0e01050718150315051c03031d0606090403090503060405010e1011270411 68
    0x40401081500d0085040103440c0001800c0c0c0c0c041c10202100709541e800d450021a5400c2081200825400d602000705050606004000e94001d01c0c01c3d80c0240701c4d51a800c6139030110584d00c0140d0075080345a41c8108034441d020480c4944c421000c480d0f00a01c1030095220b158004d00600c4848024054610790303a9503585001102c811500641c401e0100c091020441140d0300820b00c0a1092400c640184965507042d080000074103003000c0407240780e8501800c000240700d0551281d0301807122030b160066681c114002038a0144880d020700c18149241d49040500c40e8003940005641e0118501d442e50003e4490700490065080d181840d94160a20100c0e01300f8150140300f10503155a2a135450040007079502c1c1c015540301800b41034640188007200014060611410112000d002d00030151403007802d0905065001e000702c82c1080280d40030301603044401d00241c0c82a00211031500000905141c030703044a0b0000a00c0100b8419503030322810140344529515031140b220304e01040c51440e41c4541d124081 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 178113803 1250 178112553 178112567
    0x90e1005130902031005010503100914070609031403030c18041e020d0b0604060c020111150c0408010606030501050f0409140303070c14010225060608031911070f061b0f0b0403 77
    0x10885d040c946401031015440108622610a9000f04082810412443c3c00c890801072815203055038020000701040c1c8503880401b0f5411203008280e20f860010064072701039140c1c40103031142d2500c480100007140c50341659000c5103400701c42c000c0001504001e0118040c40b0b110301c01e81c0c203001d45940040c080700391002c5482140c080340301c261395040c2002e0828078080c05015800d50042e050025075032002d0140ba40400100c1a43d03d032098100341d40c0d04180700504959080750144103d0780d401c04c0b001242c100e1003845210304a84001700900c203241d400000f400020000c004e0305485100010000018045081000b1030140040342e071250103072000d0b07041101d00400c801d00c00c05181c1e401000034000042410b0344940c800b8800b640200803104161401c2d50060407140c3c8805194040800c03524242c1266400d110401c545035242c2280b50312100d41c06e207455074000c0c02401d43e0304001c80030601002e0310603100e1031100c06080c107900c0120050b80e221107080082007070084402c01d000c0320402080641c0000d0f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 178115053 1250 178113803 178113823
    0x507091806060e01030902060910020601030b0c130608071e08070207061803031b2901050d0b0718050402040311010201060f030803010e0a060918060c0906090e100513090203 76
    0x21081001e6070401800030292888069900d040585803650070043d0341d1040115260440000c00c03c8000212a802c06500c8103800d01c0207803002d9103050006200709028108444015504048103850b19052620a0791078141c080c007c4000c0000107403100c607000740824010410310f080c80d01c4580b000c1ca440d040013032801c4c0440e08032108001c4480a480d03004010310018a081c1c0b42c0c181048a100891b464034101c081420f1800585003140c0300c04e080844404145070404917021a042380e16031a0b8a560034000111941300c001804020010001100b4038401d41c80b980e0782100800c0c0c084409035a0310002426a0850342041e640c420040460b41d407a0f60302440f0f188000d00303424000d0010a45152201a138602052158601d001110300020b05040340d80d42c402c002410790040304000305006c1d0403c1850007440d40c002110001e00c3d1600c1082340c45c1c09440543c045647d26943c000c1b40034101100070b0920784001e042c01c5044040d0060108480d5a6210f0043c205054000001800d042034010980340802c148 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 178116303 1250 178115053 178115099
    0x3010204061b140d030b0a0b0c060f040303180c09150b070305070302030d1a120c03120918041b09050402150a090308040902120903030c090909030c01050709 69
    0x40204503004010301d900011020780326203000b0740c542090400c070f6100380c0500c1c005008103400d040c0490b0b0950701c00b25048000383ea000d8070098441c004420f0901c1540d055a200d43c0c002c1d8000741e840140302e032580b6407191113464081210000d480400441d10b0b05400111b4005403019400d000c980101d00c41d0405082e9050344000c81c2a10300068940e69200750000030703040005c002007650505000704121a45d010450f0000c0051203444241c81c0c0d1862880c00b0040e204003c0000c1070850600c00041113080d18000902601100c006203201c2405540b000c0300458002c29000301041340815130301d02c5103115502421346000608414006604904c401c0e400809480b40b5010034040980ca9002c0c000c4000012001d5041d958040ea4030203403000340a5510040034031800041c04074003840150043c05640b0f040c0005103440780c0301d80602c20f0b101d000844401e513506905001c80000382c6000115035400c520f607041580d01d002c0503a40058290307a030845041c07011944a0400b0003140d402003641d011454840 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 178117553 1250 178116303 178116307
    0x515010303080f0c04030b0a0207030e0102010b131a090f070807140a0c0318080d0e0303031306024005010e09040b0603010e1b0406120c0e040305070807060b0a05030102 74
    0x26641c060842000603285200c500e100c2800500b0020740d480c121405107401c605040382d03d15001150501a52000300128000703043e0344142d210550050240003110040140b40301000c4510302c40040c02070580840314001e0540c20340310340c812502d034020110300031010300d580c80d01e4a1a0150001c0d0580350b024203110200580c820700401e80c200e008081c6c4484200520780040c010f9000d0904132004400e0a03000d16641e480101c0000f0344071000142d014001805132607841405ca414401c2603200c0c003084a410b030340c441500d6510710000310540d0007070200d035000c02401d82200400307410600340350307854041e460005104c841c1044a103c0c00c031001d6a006010920f00018100b05e5403000c80c040c1103000d0001020324090038082280daa41c20f420031760380c543c5c40030102c6030514003582d00302c0f461551580b42c0c0d6015034035029003c2102c00e81c0d0324080d0300041e00039104204442c90701c004202d246400600980400034140540000120800018014070380159800300e04811120100904000c86500441c8640c3c41 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 178118803 1250 178117553 178117559
    0x507110d020c0910030b09060103030f1b080903070b03010603050901050a1b0e242208030406050306010e0a180615121a06070b010801050703020a140304020a0e090a051501 75
    0x4005140010b08034103030303030462007034403580a99804003000b0303003004241c035052031308114100307200080d0307207049078041d0760350703020b81c02c0d00540588602c0c1c0881a00300b0745844000350030002c40e613a64005d04110101a0440d40c0842c2d9480c1c0301d038210b40081e0000c20000c1d441e88103004080c1402d004242d005004401c04024040e20000781507000d00b01c4818070703010311103052522562544c800000f50b00c00195403410400003a0320901707514040d440703560031001e0b11a1904443d1110940103c056007522855001985058200710042d920340c2c10007040355041140941d060b07400c50312034003404c3c1c4c02014043c1c042d002050140c40640180d030603a400503000602454102584150f000e00d0b21202c14001c488001200d50103156540102d80d01c0d50021500010300080c020708010401450328102e0301c6420003044551503100c002c4050781304d003130351400020310010a002605c0124400440d005803008200c070405540e070b03105e6100c6105084811100a400452013902840070520581c074010013004071380f210543c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 178120053 1250 178118803 178118807
    0x1e0d0503280e0f06030112021210020702041508061803130f0509090111160606030605160206070e060d2f0c15040f0b0405120c070303090b0a0806041814010507110d 72
    0x144100c0d8a01681a02020123648441ca01680040115001e40d01e00c1011000307100c0183d032200204074092440c0c0340507035602c040c0b0b60002d201550b860901900c8075480f0b0716498001d90300c484a4108442c081002040211110210740c040149040610700400d0744c81c1400300f154043c8000c0c280c4c105a41024004010f0b0742c420402c81d96840d14040007500c0c0300d181401d04a006004541004140b249000203000b8145000c01c0c1040c0442d600d88c0c00c0301da6070b54515000b103c0480103083d8094103d5001c0c02240e580d802c15800c14030000e501c0800a500014100001c1214081c01c5055858034000006106420000501500521181c90784800034a410306956841a0080203100504000c200101107020807000740080c40408480c07010258460020600080e190030252104402040e1401c40001d0303503424000503240440c1881d120f1041e80da5032101884041c0c20400c440035680030394540b4100025249260030710800b00f42a000003460718001c0d1000e042101003140895041c1e00002c2d010304626 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 178121303 1250 178120053 178120057
    0x308160206090d110c0402120901110f0f16081207020c06040302030309090901020423040b120a02010c050705040f020d05010609051e0a03020402030a0212061e0d0503280e0f06 77
    0x280f2145802c2c0d45031110b000303401c1d0900c455211065481400081c0640041481e02c48450181045600800c07000250b0705200300103109111440d01d0400c81841000c040089800c0a00b000100e00038105946600c2a69100032582c850030322080c101506009000900341e0410001e1060142940c0c564541400e44d0000307592801501d200d14498031503400000c16071142901502d0080c0356401400f4440711a00600070f1b082c0740740c00c0700d250080c0e00d01440f4006601d804184800020000b4001e00290790503a00110756180b5130020a85140c4516400001e858449208182c818103189800685401000301c0702c0080e42c406034040343c00c001c02400103001e181d460750031039a1085410303d00300350340c2402d54001c01c18045446e48043d50051000c8104640e03820381d50014108803c4400e90124141c1e075050400229542d010100d01044000b080c0c3c029081c20b00c4d000f6012901d019004407410700700c441c0b40c1210401a180c1800b401d2203420074040c4c0f8a60741240c0041e1000d03c0c102c502003034200e4180f000c5100b074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 178122553 1250 178121303 178121323
    0x30806190b1305060c0703061422030903021f1815110a0c03081801090b09100c0b01060309030f02150609150a03030305100f050a0306020a0912030816020609 69
    0x14040007540c0d1640c110b14800510003420090912600c0710441c030800394644450788001c0c0c2d1968148451210006440881103114040e00c101280c5002d10118241140141c840e908400384124948080301682e40d8a000c0524070540c001182072602c076182000304030f60b4004846002d204452001880360300070003e80000303490610f2401c3e1150002c84a5100d11701504003401506e00c10039449c02100303000d0308500509100810a01404103140400e00465004e00580310b001044082403051980ca0715003481c0e98004088180740044500300302d0345508034070040a81c86000030035514001041015000a4030040c411003a0015001c1004107a940601c0031400038001c62241c4200700015980d0003031000440c3c180d0001501c0b000300d1588a1070058020300060b074042c00d0319028084005600204074000c04240e031006042841000d146a03280d0f070203034000c64004030a002c1c8041c0003103441c240003c00d0212031402503649000508210f44603e4159007804906021134100008014043d100040d0040309 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 178123803 1250 178122553 178122569
    0xf0204050f0f0a030f0b07030501081b12010204030b1303080f0c030403180b1902070b09030304140f030a12030c030204031e061b080a060602150c0c12040b030403080619 74
    0x910401d0b50000f0b142d03c081a08002c0a1100c05505541402200c084241c480d014135101003103580d8a48504079a100c03201051100966900c1c01961801c0c1000d00d155031141c04144009410310b030316aa24840710900490300c1c0d000c3c0c02030102000e01811b40c0141c4141e040006189200450f0400c0001c106607880000d04c042e080c400c480a0b5071460f0010062501300414108129984442c0c80049051841c0300032000380005200300c0c0703000316030300e940d01044481c0c0010003802149098a051003490051445140c03c030750081001c1c44041513614180006500030b4462041188950900343c40601111107440c07140081610601c8140006255020183d0301d03000d40585a00101001c1d00d040c00c080c007400d031480d06480c41010712014642e50007407001c0f0f0154070400d42c10f11071961550400c070ba888151550701203071148108003003401084800001c00059140c1000c6c1c6000c10782c83c0601598540c0b2940c09482c1c5480000200000d142c0d0002c4c06031303000a002c461481c005600c200c4117100c1aa82c500503407030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 178125053 1250 178123803 178123819
    0x1080112051e0c150f1c0b12030d050c1303060209120d03200a02060c03040309031b050405060a05090c0a1808070e01150207030321110d0f0204050f 65
    0x41403103402c210401d04401d04000c52450345240c408295259080300b00303c2e90042e103e0700040001c9a041c0c4054458498030b150110f41442101b0042500c02d02d03840c1c02d50345405a480d9604d804c940c40d20b82a403100b050525000b1a600c4801070040c0703089070001000101070b49170078419030200744500d40d081c00c00c89400180158495518400180b0345d104c054603000c1643c8100e841207014117400d80c0000341c8410000c508082035003003058402e160352040016040068100c1d100107812400c2190146400074001e1a010a4403038407a51195000c0403401d2650f84080300340f0307600b04442c3c50140111035101d0000d50700c600e20645400c01003100014040e0001c91240c8011849425480c132400107858501044140c0c1171070555a40019520b4110f28050021021501340011030f00b080110b503a08008040e070381c002d0594925544080350300340f406c1c003a40d01200c08242e0128428500c103010303103080b0701048442d540d6a41c280c4514801280e09007802c002550740184410801980e82906118808109644ae00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 178126303 1250 178125053 178125089
    0xe0d020d0f0e031623090f0105090709080109150c020a110f0105070b0a0b01020c0a120209060d060507030e0c010c0206070b0604020c1c12050f1f0b0d0f05010501090302010801 77
    0xc0c100404c4030303008100081481c1d0700003040000424141704014501c00b40725004440c440c140501e620003101d1010078425460010003180c2420541654040101c0c5843c0010980311001716013501c54094043d12860542015070142416074440d0b45c0e0b2001d0305000034400720210359184400c44550042e0540f01312911005071210380d010b20211181d056209441d00c00d14540384031a10024651107100c00d00510880205034024100002c4403001d88000b98042070301903556500300103180c1c0c402040690480c0d4079101c2d0400180e421301649014141c0b64074003240c080c80801c002c82c40c08450803030580c1044405040d15000d62160740440b200d440d0400c00d581c01d599102d40208000c2e104150800d0194425030302c5411021240300544404824140e8404c01d10780114164641581e80569080c20303203109840103c0c0024044150105a01c0080081c1a546941d035201c01c05642d0804000a2501505d4180030702c2d0180b118030030140502401d0a00d40303042400c40e000204013800c140a440d40880100c0084 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 178127553 1250 178126303 178126309
    0x305060d0302061b19050310050a05060715110307020105070e1e0103050a06030b070906030b040606080112210c03090801050903190e0907030f0e0c03030d0b0a0503030d0e0d020d0f0e 80
    0x192041c1e000c400c0b84017036241900d0002403142d8011161800f400f80c448034007040d94603051650804440005141c07074100010758aa021340b4600003554405401c0e1f64101e810300004415000e144035620f20b800004242c03500c0d4502906000c00003803d94813608204149507060314030200d508811400a1030b0000301c4e5914001b80d2030041c4450b4101038441d2200b00100035041d0b0380070700184d05841503594144805028103040c03005849440c020000404e4483c00140800303c0705d40c403810b0313545004600202c40500701401032a0141c5503d81c20a000441d0b1124820903d6000200c2c44020b1a9103c02041146041c141460302c0380252010300485401c41c2c88200c1405106860034084990002c1c0a041907041c00380300a80241001c41e03802c12124141814042c0c00b12002c600f0070002c0b00042c01440ca0080d001c0c101100804c1500302a607801040e0a00c04101c40c0c4080010b4510f21050354000140d0443e07070300340f0a03e00300840c0f0b44030f01154400450760070204d62107580341c3e544003118100300d4548441c503000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 178128803 1250 178127553 178127557
    0x1401090504020f040f171507050706110c0d0813030c0213021c0605040b0f15270f1e0103050408040504051524070809040e0307050303070305060d0302061b 68
    0x40e9009002045240110401c40020b104488066441c2a5070070740d1881c040401b640d01c0204078169400003840c1070840c501c0000794a510a80c0b514200386000b409680d80b100711069209200040d100c04242102c0040081058000c101d0181c00c02d1080ca141074181d1003418001c0c04001401c000132801c0712000c646038103484c503000620040301035440704405440f80d640c06002219007000f0b94100342c1d000546040900c201c0b000d901c3c0141840d45028644014032190365155980000d2060040007405015081800300c2c9480419104101061890140801603405250070115102d850741201c0703c0360040c0034604039041a4030038200800d0541d40e03400d0141c007602990f400690420304040401c48c200c226048041c0d41044202d070300d0303500d64091030b41004420750081c3e8142d01c800c804120040209041501130400050000c1020900b222141007072800c5da000030200b16581d50002c402d120300c0a4060140380e9000c4019609100c1220464030000d683e01c02c080d140b60b203900c50b81c2c91103101900c00201 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 178130053 1250 178128803 178128809
    0x9060c0102090a03051518100506060c03040603090b0c03190c0513080307120f0912020303131205150717151002071406040302010f0f02030d091113090b01140109 71
    0x180783d41199603003403540d101c0044556000d1444c0b4821700003000c062560722442c0045282c0c1e401030030f5024038501c084000f0000a00780c20b80c49402800152500b0300700300000c0c00503204541e004103042003c0d15100743c0000d006010365800503c18400c2080f140c40c00030100c0200a000400811031400743c81c4d05540b2441404030719203c1c0c01040c0750100340c0110000060000320b114118004029010705001c8500e002044030f4a0f001810450040052142c43c1c501d03d02d4850000b03007030b6403400d00310401c841e080304069071095021412203011142072000910080d080d02030713071001d800740600e0300e40c100506c0603e40d04541a4104281d8001c2034030380002c050685a0500068902d0510555214019507200c0903072244844c20030014070780b00642c0c100f10081c0d9040b41d40c1a180c0046a0b01c020320266598103c1ca801102148002e01c601c0b19040181c1c000c2841080c000c46002030103004010038444c0310071603e4029540f05041018500014aa0070401c5045840c40b00c1d200c030b24906420012240114154 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 178131303 1250 178130053 178130059
    0xa08150c0f04050a030b070e0d320d09080708010b0f0405090a02090c1305030a08030403051b0a0609060b03160e0a06050915010305061503040803060f040f06080c01031109060c010209 80
    0x101001c42000941e86c55a400343d06140c0350703c1d075401034290400030101071241c0014508002d50f4804000c0107106e01620903402c1c071040409a40c0c4161207030f501d1070482c12805003030016214100400c4160014000c00c409441179400a11942001c1c90210f40840507804090b8000c2c0d03941d000043c03180400b032091421181e8000c004040c1420550001171054000b40200082c0f001040c400007401e2400044c0b4151003a809014141143e54585081d2403907044440d0101c10121082c900d02403884040c850b02103c1071003410300090707155030360803c0001c884a1460f80f900035406610040c081c0040d0a9046040301c2c003500500810356a05034422018102a90209412400341028001d29003404c049090858100307036010803040d9104007c2046d01180003000111600040021030081a035080085912001c00f411041302c0c1081040820704640502c10500304555640c4824004442c05000700021180709203000e001c0300143d164203402c948074030300343d5038803c4030000f401140700d980a40590300f5000d001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 178132553 1250 178131303 178131319
    0x50f0d060912081303020a110d1403030a0501090612060b0f060f030108061518060a0b0708070501050702030f0904022a1e010207030e010305070903200a08150c0f0405 73
    0x10745803044100c0c115842642c08541000002540381e04c40d000c280f9185078042d4020030000985840304a8440d03040700e0b8958000e07540d500c5e0300300442c08403210007075603c4690f001140d483c07411900500032200d040c0c01c092100c9042800c01c000708100f82076002c60b29074000c40d0010342c240d617400009017208410030407076400c920007040c400907450841c0091030482e074144080d15030780d0380c910401218104040c402c0e194410201c05080d40c0f41d8000f4003142d944103002400004070951100c070354110340d40000108070340c0170200003100d6080110030301440d41c2103003060001794100000007e100542c1d0140128a5001c0d507400701c2c10b0074800641218400004803130305a2514002c410130300344ca40318004a5280c1071144844c0502140c22078052080341c0c00107806aa0301040c501186e80114003a04c4007400b4101006415440400030800c282d00c0440d00d0306010005000a200c40c00034001241074540c030841e10754101d500c080e400c02c0412100744d92700c0001e060701e082d5070b04c5c280c2d5143c03030642c012504466004504 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 178133803 1250 178132553 178132571
    0xf02100909181406010f03080304050f370c17210a020f030a121a040c020d020712080712090909080414060306030a15020f0d060509070c0309050f0d06 66
    0x5080709000d000c41c010345001c03e12408044815946200070300c00c542c841c494400041010501e8000134640043c0300f6810b60b201380a00d02c45d52442c05004400d0313a4450400001c01d8000038800d94540b407616016640f0800015a40e9194940210198403030351842491015003e030401c582400fa82d050305c82e00340006401e44507002c07540d9240350440764508001d8800c44100c0c0d02e6841002003901e294400b070399513010901d103c001e00040505104c490400e0a200b0340010106195230f54052400c964040b54000d01600031104002482e14045910610f00c0705060a084000b00794618203c550040c1c0280f0b0600758048039010881d00d821135940700caa1407a00e072076055005c02200000070b1040b10780101048501c0344140c01004810321041c0e50517685644184020800034048190b0303000b000300810001410080b130a400c0b03904d66480180200402a52100d090000b0300d0032101c2543c006580d450000d082030341c507a038040c1401c1c00c0350095510820311507040c03400c15a29048040d00c5241d1120090007801700d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 178135053 1250 178133803 178133831
    0x6050f0c0a050a060606052502040e0303042f0906040c020c0a0b0310090203010810090201032306030d080420030a0c0305160602010e030a0507140604031e03090f02100909 75
    0x116003541220345a007060700018606100c0c0054580e60750720091f03501c0c0f0400040308d0f45003402681c0001241c00940b10486061004010300156100b039006100025807100202411450201610b00455012011340782c5e20348580c40c1d03030705c403c0d070f101c181070703e0004500003205d40c242e00d44580380400582c070400d08a0042600100034001e94007c580c1144901c5d0a203841f0031000d0160702007405520300c40d0b0b1042d072041465810940152981c00d00604000601402a03c00d40c0740301c2030364406507030080c1e002c2014880300e03090400556240401d249416242400c1c280d590b08015642a006a50030760400c10508140b03a40078058444907690000903284880d91380d2a055403500311105a40f100031001d0003000407030710f0060186103030301c0089a020398500000728405480700d03081000c0c113841c1c4800380c030301c90b210140040114500890003510340d20700320816200005485400d4078069810542000740c5000010140e070311001c4926411101c50851660200c0c2c122401c20070b42d07002d001d1321801c1c07064440c0048 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 178136303 1250 178135053 178135063
    0x10f0b0c030403060c110f0705010507150f0e0102040612051515160b0402090f060102031c0609061409070c0b0c16020d060b01091a030a02030c040801060603020406110d080106050f0c0a05 82
    0x101c00030313190212400c803047c617240d5182e8410a400b05800304540800a5680d02041c82605000c0b14001004241058001c1c2156805170040030160740c0000c00b44445070308240d0390035503400182c0040c0164580f800c0001c01c0821501c00c05406005427000c60740300302c0d035280d05880a110004000143c9070a56042c080f805501c01e82d000e90142d402c110100c0d5944582c0030319140700d403406800641c90b006000070801100101d10102c1d4000f01d64030100030824031614020311006041100500051544100800c011508040c0551052114003142880007443c1d00a0241e4000321195026480c1d96001401070742c2c220701e00200a43c4407441154400801a2039401030799841002c0e40c840c0385058590840094070b0440000b000d001d540c0620008110703148076002964001d030b4a1080c9030800342e682c101c0b43e0a5a134141c01c43ca0109401050921a06601c1034040780c10140d410006c00d00300b004100e0143c40860180284410023500155603c1c101e944082241d403c0011482121a1101c440c20565110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 178137553 1250 178136303 178136327
    0x3070b0c03210a061d06010815031005011a1e03040623070207051206060d03020a050703051b04090308060f060f0c01020309010c08100b0702240d0f05010f0b0c030403060c 75
    0x14948800814556601480b11445c5411000519166110303c0010b440450004083d042510178102000c049030320305114404008038000b0012440f075042c4020802801c00000440045950a11810302d80390100ca1550ba0b6142503030000390303525110780c01d110000c0c11505441c1d5a41c0310490b01e80c220141e030f10720800b910400c2c032907095034203071500c640c00c02a000c59190810f503900da2096002c12001e01c0c0a030040340850f40300740103d68411405079034980c206502e40c0d1060700c040d008083c0c241c5600400d4054800c80c603100319002c00c4045000e9801070021200039000901595441d480403807507850703078821038105400d001a09902d0b4003001a0aa01070752044881300a2075007025410101c141c014550140141c000d43c8000c45000d0170003c0b0007446d031304040d2003a0b030300565002c21001603851005440952140e4811300ca6030f1003001894a4040e01c0700300c003000b9920f5113403200400c90b00303609850175400d0310240c464003980d03010040f1400d0f14601940c2c0000c0d0501e03203004001409150441081301c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 178138803 1250 178137553 178137571
    0x103110103060906270207020d0b04030f0504030b070e0111070b071a0402090c160b01090c0e0118050d0501060e0f061806030703080a02100c0e040e0c03070b0c0321 72
    0x35a844503580f4080e65244d125415508181e0498031051280e610548508455021001820721290750001661042202c4040d218a94140240014035a12031103103085c048050522920b41381c80d40d582c2c114244002001e010401040360221640340c3c3c41080d0101107802200203c400f81921110307500010341c0100701c119965a03041c0080c0d041c0c07580310610f85102d190002e0000c0106d030380360351841c05140d001d045401d01c1c800301205034034005600c4041140c081d12a0040005503c0b40414011346904e040310600b606000d0011302044520400481100541d0030598610390000c61f1490f21a0240c00a50021a02c84500b0390400482a50041e00b461003114100c50706412500d0700d481c40ea810700713811303100c0a030940c0000c070003480800c42d0b580043c448a140c80c411640c0130b4940400750400c4400203004400015100321540e06075160034000e43d0300511041002d00a4056010002560b03103000344a06108180c0201d40c06000b0704051058868141044190030806a204101d00554210444811803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 178140053 1250 178138803 178138811
    0x10c02010c0311040302010c0f0f06020702120109020306010603180b0c36060702060d0c0e041b08010302120102070c080105011a03070509240f12011406040e04060b090103110103 78
    0x1e0658428001c122003070000c12022494541550011951858000c0050300d0740e4104440d00310003e0300d901043c0e03004a0065400503150b0540d4410044032160300c405101c0d40d60f041400940c0966004505681118141c3c14002402803088034401c440007000c820141c21b0340301020404c034040341104010b01c0b1940d0207030b01c410390a4030420b00380042d410024040c010040e0f008860810070b401c00000412286000034001030502d000c5403404020f54040e0851100000c4522404440714103207405002110b03546070300106074100400b44000c2c1861014480680b1641c00c180420406100030750403162020f401001e908030042d00c9403828ae01074402803042d1440d080000c0d0190800341125410390b40501a1966482d20700030050041000c00784065484110101d02909030a200311070300c1e0000e103a0881e070f1300041c5480c0c00d505001c010700100140d211003080310103104400380f10350745d2004813000c3e180244c201c84000c0e00d5a04040c0003e281440125401c001241c0000c801c0c80f11103503c4200c509000d98080c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 178141303 1250 178140053 178140071
    0xa05061210020d060b0a0906030b041805100b0402090303090402091503040309080601291309020d061a0304050705010f120507050417120307050903210405030f030301061b14070602010c0201 83
    0x400d8500ca120f100f04001f40300c1d403005111891080d04402c0c0c4140d0300900c00b0802c0c04048115150301c030120380c0112007542c8003c0d01082c000d9100c0c00b66a459036000c9a00b18140788a0001180d2a8881c054041348660350018004110b5a204d01e2446801c41a68841c1c80d100c0c0b038540740182843c0c040f03006001c154420030780002800c0d260b20740003281401c00d04c2c1e42040c564040403191000d607007120b210070003c10001c00000c11503403020b00c0540409900300c00c0200d98140b800710401e0140300e10860154580f03204000b0000441c5c40060320408850081c03070715000340d010f801012500c00100c40c0d01412818100000d00c07280b9135001c806401070303a9541c00742c035a0940c440c0d06400d0b916800210000030450086c00003c425602541c060b04201d40b010303003a1403825200e188000c003280c0d40c07141034076031402004c5024010340c10304108056070080700c41d0083d4515410054040c2031042100580e038482e20042c40c031007003000341c4a500e8105410701001180c0701541c5419019018009172102d1800541c6011145 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 178142553 1250 178141303 178141319
    0x50a03120e031603050903250501030b062512020307030f030203040b04120504080f060a1107080d110c0607020a0b070e0105071401180609061401030b0a05061210020d06 74
    0x1008480d128100218039140d864190049140f000c188140c4c140315061001c840340d900c082c0005d03801c01140d450700560011000020960481141e0090350400d80f401001c1d00343c0341c64002c1212a4000c5a40c40c076400003013002e00030281c1c040400c1000b4921000c00480d60203182d0000040c00b0514403903204c3e0103541552000c11000c034002281d0252859003520003180c003007450145440340e102218a409840d02c0d4645000528004008080110a43c031010810403840340c0d81c460071b41c01c18801d2400628081d95a1960394903401108405926142e4844203c0c0301c00e2880f101b102e00c04483d00d0203031886890203110294541030240310035030b44042c6040c00505514881d1a01030030b00c500503101c50f030601c1440d4503182d8a492246244540707d65960103103006207824000d4801c0603038400c10000c03841d03005074a00032003611104080240c800500000500c0042c00040390b6035844044454002107a81d102d500055a1140d120410384040c016801d4040c640743d16600144800a4000000e00240d80e4560344 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 178143803 1250 178142553 178142561
    0x30f0a110d271527050705100201090b0f06040207120c0303051f18060305070f0303090e07050a21021b06011a030412020a120f0810060207150201140103050a0312 71
    0x34002183d82c0140f600d81c140c1c5503c94040c0080c14540014403130080850b0b40001c0043e042c1c20356440c3e22420b420002460803c500e050310070b0081c8003d000d403100544e1a080040f10240c000f204080540002501903216030f07060322083c40e084112a00ba0303079102070015041002c1800305800103030a110005844a8444140a001c100d11860000d900da1810103000500840b4041c003518080c0c6540002011480410048011f4104283c1d521450703072541c603000e44000800d074801c2c0440030080d810058129008405c0d143d64054a0a24180d8009190b004030140a107075400703d280340d4030100d246250040401d115001c590350400c1100c1da40d0746c80d8107040c0d03051001801c507640045010400a00020010380303440d03903d00e900380102c0744051419a80c45000041002c04000000e12140c03d081c0c07403aa20000d103542241e1070040884005e170402c403009490b610940074242d40b0028840d106a000c40c801d40c00800c4194214428807590750712403400075222034054a040d00010301e403040224a0b0021403207 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 178145053 1250 178143803 178143881
    0xf032106031104020f0d09080a021b0d0b0403181509050102010e1b0607240507081306150906090b040506060310180e011d01050c0906030f0a110d 64
    0x503a070b140c4000d5142000081c1d0f10014011562034001c0c85000b10b84031030790103004003852003402c0003910b0f80c00c402d0000b8909200010f10000c0c1d08010801c81c1075544981c400c41040581046001c65503986504040c0c51104200f04201141d0b0808140007610719010585a20b42511036600c00104958400049003628850000c81140c1d03004010091fa2410f4031800b0809080c00240c003060814490303031110401c001a8030f802402014500d240704e0085443c501c07406500c0700303003400d1680607820101c074004241c4a44003c010920b03a0f4500a1180c80742c11100564010003160314103002d01078032040701e0400303070060160032030081d4100390201e0882c0c030301741c010350384136004c0c1d44c0403c030680340f501011381007154241c00c610070002e60710343c0500103100003030240e02c900201088443c040c028898801c6130031141c00510b20581c611003031281c90200d940380d8003102d410480c2c01000c0360f0103480f01e5120350300900c0700300b04241e0000b100041c03240004070344c1d40114040c1002c00c80072181556416810451568540c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 178146303 1250 178145053 178145063
    0x80601060f0503060d030315031a0a02070519061803051e0901140f04090504030e090c0307020a02061305030307120f0203091c0c090e01060807051e0d0f0f03210603 72
    0x400050301c40e007032800c245d6244900a01c2c0c0461405400e030303083d041c400c01f290410b48000102103401150303c51000001a0040388401c401c41c58252281c58103910b90303208141d1f610a104420816070207110341d0303802c12501e070346e20485241c010030407a19000e01141d01c07001030388440c0d000300350a22a100a580c8241c032140b0710180c40c0c007080740305003201000345a4802d6800300f021250038000403c0480b40c912980344a070348280c440544070007643c0304000c40c0701d00042c09164a00030410400040030383c0480c001480a9050341d140751070b40241814000b001e200b41d008140c05d80300105450043c821064035106882d901920f6011120390a038030120303140e104800c041500b00c3c4822940313a401400e0304000030241b9004080d040714040d2904820b100f581c0c095501c0f03048581d1070f24030034042c0083c2404890000e14044454440940141800707480c1c42028240d402d00c54844481e100b4240600703000642c01f40ca40c0081c10003070092944c54040c11445040c444824154031030082d120702e44503a4810041503035082 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 178147553 1250 178146303 178146307
    0x405090105010c0c1a071b060516050c040c0f0f0201060305030306011d0904052811040c02030d020a09030b0f0403090b0c0a050f0a020f0108010e1306110a09080601060f05 75
    0x801074030705944500086842440d10103000450a945804503217490051030b180582d552641d040586411005021601c4412038042c020042e40307401c00d00311101c4142c171910f003d0300340425042c002d09046102d40d007035812034140035490404903444542c0e1007101c0c121b074860401202001d03034124200c07415400020015441040420420342c01071180e200002e10603141144030038402000300b0500f000c10340d01150554010a40358400004903560032100c1e11107130b580e000c030040054451205c3d580c020700d400f41c0195034480545c49818070901c215407081e60414003c4d07650305051035000f002c00c92184010740f2000544800716041c40d2003049598026600b55460030522400d06e10a40159032100c220604680f140c0a138150003d4000c2c4000c01c0708051400c09010000720b940103111022203070780b24448c100054100184134041002048a80000251801e80c01d000340030314011004041c4040680074928001c2055401c170383e03100030320f10b046d100042c0595142c0e0340e03180004d071048460b018400c0041141 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 178148803 1250 178147553 178147559
    0xf23030a11041d2d160e130209030102040f060c1703070c030e03070503070806010807090903020d120b1c02040b01020d050a080606040504020403080a021204050901140d05070f0302120304050901 85
    0x30b5442c9694004001240202c20382c980d000700300c0e001145802e01c140c2c144090404110304650700390281c1894500505000c6a5000080c2c0081c0041c7c0198a0800c0b8007a4081001e121645007541034a002c2d10640c070080a03119100c0b00d000c1c01c06007140705c0480e180281d8503000100c20880a040d40c0c020800340c0c68910200d0440d90f0207880394100e0004868141c4130b608800a915503040211030300900c02c0c170001d002c065041018581c280392480c0c00c019076040c1000328400c002a400035035000c07250841c3c0360400803601e800703646102800c411030495a00c00c00003d828040000d00a500d600a01c1c030890b010010043c0c00c4005a07225a9600a980c1c08250280030520506025140869100300010a058503041e00c0c0c0c0005000c0b600940c1040d100074802140c02c00c80c103a010040001c40700d0034001d031541090304d02400101000014013074500c00010100326035006403207101002180541c4042035800150310b41c41c00303418490f09884142e00c2240890003070000e600f00401110250307000075020007102d0b0700f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 178150053 1250 178148803 178148849
    0x15060a08070e040b061b10090201050f030a140103110118030206040b09010507080c030301031a010e18030d1406100504050603070c150513030e040203160f23030a1104 73
    0x142c0c0a0396940c120340c80790241805691800b00401903851010040005850f281254a25013103c444c2038251581c030300440c1d400980e0b004415621446240c0031752a0303407030381c0b0f5641040c09071091003120700210401400100030443d107014140d24100081c2e95903480c0e01321840203c02c40000611010707400c8203040105200344000344005080b014810304126281006507600c8250f25844420303c5202504040010300c1001340840c0004480721600501d02c1e03295040c004020000c001c040c114485005c2820035003c035580c414000c0d140741d200c03011401c100c0c0440044c42e8488200049031071030301c540b20110340c4010060141d0309480660300041c10407411995080c03030039141c2610106040d035131354106021515051000c1d0240b03510078003155440300c2c2808824900a458200094241351180e8014420071640d1444216007505d41e002d07602e440700c1001c01c80b4009940020681d9003503545e20b2401901070b4100c00c3c909000718010000e0030810014611100c06040e094000c5002e01c0e401404c42c0111101229 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 178151303 1250 178150053 178150067
    0x1b010f02060708060f0f0a03060501031e0803060d0606080f0d14070302070e0c070f0501141b0706050c09060a020c1005040b030403050307050d0515010f0905030a08030903040e0106020615060a0807 86
    0x5c010b0300031640708481c00b0000d24040c08551003114403903182c10040c4200f01940183d003251300219044000b0341c82a03642c528059010041100c0e00804481240c1d0050151a8112600901c03499007540c3c011164408180c1d1103810804a00d80880e02a410501e15049241c084841d250f4041c0d01400f10513007031000d99140c448020304410b000c09414802c54000c9140307811145000b0b44150000156050280c0d410411607400800c1c8001040707690b0721005448039504110b6840c6075002c48000b03866502e0800c03241050040da44500c0d0404004100341018075000a40b803901601c0844100100c000c1d1041c084072144190b004951242c5814004280060700442c05141c2150702801c149003851003034200d403012a00d04403a221050090b242d828441541c0124554894281a14203080050305003000310356500d82c1000c0c0181901d80c000f0010fa50786409200303850251400d00606051941d582d0720003907071120280d5900c1c070504000c5440100c9071400300c04580406199485e018503558a0344e10554941c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 178152553 1250 178151303 178151329
    0x51903020607050c09011203030605010c020a0909020d0b0a0e06090307080f0f0405031f1a03030301060f1107060e090108030703020c0607060902041401180605030c040510081b010f0206070806 84
    0x58413600003040071a55a10444d18080c08240d103a040c2c031148242001003d4039820350140b41071100704003080002d44c60740d14481c2c00f903641c1088082105c1c825031012a9480007100c4c409000340741400309000d030f02862600f014446070000c0d01111000c1e00d5220301c50351a4030031510001d155801c00c020075003001d00100701610040c003100d032225050660b0740c40070a04100300030142040002e03c400700000344110034880c2d10341c80d400310441074944000c0c030004683d5a21060041c2d8003070201e8040d4419000348280341600100441c0c20a84e14444d0741c460740070300400303415000381d031281410900104504c000081607030422038244d4024441c5001d41405d004095001c41410341d440c41c1c031103170a0070150300c0c0e40c040c3d070017a0b000600d40c00358250326005141c600012540f0070030038558181001081295070000303981010390402c507000101a2640c0a400d40c00c004113501400300d500039281c2d0b03203601c101e100c0751010301454280c031000418000548120b80701e603800c0300c0140205103110702182c200d08180080d8044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 178153803 1250 178152553 178152563
    0x501020105011410020a080c01050109050a0903090302011d0d05010204060215040c030b04022106060301060b04060822050d03020a032a1110020f030108070801020c060406091722051903020607 84
    0x201b012a10383c2a00e9500100307a07910300769120b200402c06910f03188565580603241650401812205543c0140381c90240d11021b41086450300b145242c1d01c68900c0320518540000340380c1d1104a02030314002d03010750418460385015000355162203241d014080000751003240d120981c109600c1c110750b20040143c402400aa8004020404910b100b00c0c900554841c00912540208610314020007094255016900288200d050034842044200c0d0006111500120854400d0060345040217050440d4010080054034a104484011803101d4242d8001c210399403071940e051260041000b1050420041c184041e03845040d9101031340116840350300c1400541245405075010741c0f085018130f07410303600400300058640390004010091180c0810442008010071030003981800c001d151b100741c0740d480c0244080c24071510b54032264100110440d05015826402d1151070f210b81440c88891260046100b182a0000396554042800d14043e0501c41e07041194100302d4400c18116403e000c1e56800400040750 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 178155053 1250 178153803 178153813
    0x60708101a1603050702030111130311060915031e010b030103032d030606020f01050405030f160203010f02040608090106081002090301020409090812010b0a050a0e1c0b10050102010501141002 84
    0xb0040000c0714150031014080e6940b29140d0300940109800c4580109624100c024100041c203a10003024450604580e04020489412130007203020614900c0b59600300750303008000781c03c210680c80914000d540180708010742c80690280a0080f1001100300703000300a540f0f0005e100400003e48540c83c08000c0c860744407011400c0d01b00c0006c460803003018107010070300425100e100900506904101003607680307020000078415030030281c40d0241c89214143c080f501c2160001a541080c0341003c1b0300c1000d00350301034002c10980070140ca04100a400c3307405420000340b42c007800f150040d90305001d180d00741d07201c0b40003803d1098541203070f440081d8001420351f81c265400f8000082c2201d07091040b0750030740f40034108090361861501c0c2e8558441d841600f102d80210002d008002c1100e0380030042d10f8034a00942401078010509400259100f2100c10010706c0300c00381c4607541410849502d012034042c8946086650159403078400581c2a078209004001d172160784401286800c1c42c0c00761618409002c10f0040e64 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 178156303 1250 178155053 178155067
    0x120402010c150f0f02090f0d0201020708060c0417010e100c03060e0c0909090601081c0c05101b030c080f0402040b0a030b06030709110a0f0207081e060708101a 70
    0x4014030504907202d416050340c601c00c86407000180c4c02000020745090b80114601915880000ea00300c00406005000741210090541164001c00120000d0001082210000c2c0b500ca1103e00312031b402400b682c00c1d0001c8401c0011036403241400381c803940c8000306000c0e03c2804003030460400100080540c5008150321000000f41c0c0013801203000b03004098980000342e8071051403046c00070403800507207040241d90140c401009550300c007054460084202c1c0f2210051303690f05440c112084844603501401c240100c84d0840c500014039800f0319070709035807440400d03401045030409808582032054070002241c40300c0c0014070801c50b50034586500600c010030000c0c0076642c490128540400c5078104981c040c1c0b102051002502d42040b8402c02003204100c00c0c0544c50b082144980d4601410281001740126072002e04132050080c800c0707102800440302250480000703107140c44140005000000c030240560404650711600c20014241303d0080007034010701551800241990080e0340544402940c0c400740020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 178157553 1250 178156303 178156313
    0x406050702070f0f0e13170a0203210910110904020c1002030903030f1506090d0311190606081203060d0303020c0a081803010506010e040c020a05030714061003020105120402010c 78
    0x150700500fa4226803d480701703080105001480d080030380700b107501040015085001880c100854007100d22140c03161900c03845400317816413450040c2c10030841c0c440c80410b86004080e50081c407482c481d5a0310700482d46040c50703c807100c03004c9444008140ca9030100402c410b403a44c0c02c0580003043c9622000081340c5000c013040c00f110007240c0098802d403006810001c144010840000085500045110f500c804049010307030024000d881548005405003001284447c14140100e02e8034095030341d4801590382c00c00c4240c00c80d614200c1010303811034880303140540208061f01c3c000386400e800404005000e1541c0c60795000c00c07000301c10300d01c4210101502000000e4805000303202560403e40304e00000da848031415100611446080344100d4000d13032500e41008a03503a482418001c4941065500107011200d01030101d0510f8014071001c1d001e444001190300c200b004212000401c00510b60650380b858540c41040e0340d07403030f4030b611000e400108107000502070a44803480c000c0d00a0710504103104a0b00780c42ea21 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 178158803 1250 178157553 178157579
    0x117070c140d090e0a06060207030201031a0d0c08010e03130303081305010606020a020f0306070c150207020411030402011e050f030c090306090c0405070c03140904060b0705060a0c0e010503040605070207 89
    0x502c002506550341084042c100c00400c40d0000c1e0418020b00c0031504240c8000e6486c4a603110281c1010307190b4100a40c1c003410600d802d80914005070a581e499441401c0c003988605030381c86942d08962a1409550344c80001100340d07040c0f80303c041201445213141d6102141c250710040c10000c5a55540b400100000b1801d1060100810040d0040d000c0c0308043d00400000d43c03000c1c41c07614000e401c0070301041001d0707074000820840d0b19406409074201001c0888800020b0013001402500985403002d0301981c020402c0c065486030b4402d0340c031007201d174080c0c0348822154290820100f010640510403090743d48514409154405910b2030031500f0f0030915800245021419a90b074807090708400c090300841c0c1864046c1540c00a000e003008002c0003e96a8000d1650b0088420204586404640c505039030340c80742c0003d001407814100d015110883c81c10201e448001c01d66009100034074043c08180314034011807142c0e5003c2d105844260555546072036801c00f5001c0209440c0450203424000b24615200381c407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 178160053 1250 178158803 178158823
    0x2061b03160b100b0f1911190c0b0412060f021e120a06080d1110090b0906060d200307080706020102040e09030c07030f06021c0e0c0117070c14 63
    0xc0300030b154200003528000041d11034112036010380e420420443c0901c060811a07442030640d83c1202001d00782103104889102d0000301d0011280540c00c107a00b600f02034025108031085c0144151120340b503032565600f0b454807591040d0704030100c4c440c1010011800f00c0e8403640242658035000b6281125144650300c405400c1c803805158144042010050f070114608016403005243d1010480d043c18040715594071008030000c10100003200340200100350040c4004880300300c850b071080c032642d402450000203060088804011034421500000d502d45081c0030210050303504074001c010b4260520540110700d9a424011b26054401e06500080341c1404100b036000800d01c81c0e000686940c2801d6507001d0742e0b440540051101d50046c4817480143d035001c6900750841c1c0e44500c0500e502da00078644030700a805641c0030806055541c040d10714440506030808106461a041502c4a00450344c006498041001200000c008529000505901d008000310011180501410400c9042d0b1284d1185000c403010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 178161303 1250 178160053 178160063
    0x2030108011b080c0c070b0d0204051905010f030902040207050a0318060305091914010e010f0e06131202070909110a1a070602030615120601140702061b0316 69
    0x401100e1801c1c8228003205810141e000b1803448070703480007412443c0c00b41c40e007050600d0002e10300148080c10040c2000030a81e040a8903103481600e144840203400610469029a0700908a206507800c0d829000c8241c0340161280038000ca1402c1c0708134010400003504a801070350800908000c1030741000009141c0380300340e9840311441a226464640c490042d40718a060504280074009104004540382603080c18424805c69030560b107040c9540382d40324408142d040780d4601507807411107420641058556821000c41030240510f5010b9180c1e9031001222116980000100c9000001c0ea004e049d01c03003005400e20403108603649505002c002c41d17001400850b0406021078072000f80d42080d030a1500200003210401c0d07803651062580c24818440d548006020a90001c0050215603c0300040340d050716541048a4807012005100c1090703500503074119001c6581050000c2000070744008460300c05901a10031130405424110001e9002c200802c40807450000344080790902e004020a0740c3e4145c050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 178162553 1250 178161303 178161307
    0x503220f030306081501090906060317030f010608130f0c05041a09060307150e03190303150503061b03060d0813090f0504031d03160b0a180e0705070812010902 70
    0x14034018007240d0b40f81e80701910325008400e555011800c01e017070083c1150000301d000f040d8040c59207441320040440703070001082e041e0b144200824180c2c10b407016510400c41d852001e081e0b0798882c00c0a81c0c2c000c50440349444400c044082c50320016458001c801c00043c801d810140009461300d0004041d036071032210074a004601c01d01003c84610340540b40d60340250702900a04009030030101160b454000c9202d4960074440c0c00001508140c5082008210065103445001c2a024082c90010060201d050400e072480e80420130110b2a0f10340804e031140500c1c080440c01401182d07070140c0d15903c0e04001d12031a0f000c03000e0580b1002213240240100180880200564601c506120905c401c032100005561403552912081000080e0410410510b000c20360003a1901008103000083ca40a89015204d809400c400400114107807040c02400c0750800790f4594000403070445900d800b00d48458800c0304004031694000c03410450140c0000c3c00e10b070b809041a103113002070f0300c5e8005031181c601f030f4001c0c0e44090380 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 178163803 1250 178162553 178162583
    0xd170a030b031603030e010804080d020301180b1509010c03030f09050a031205010509010504020d0207140303100512150606070602070809012606040f020c0a0507030b1f06050322 78
    0x20a02006404000200c0c000c1c0103103046480080c460341c03a0b011447d040c4140700010405000c044c0c0259410b2640440e4195a07035a120701d500817110401020028032542030403a45401460008888110910480c6c002400d01040000445190b44034250640034140e5511264501035a1806a174840e140540000d19180e032961400030a21915281c410880520b4034006104030340c1c1e0038546904441049802581f640b100c0d86000009100361031008112804094003a0064203012001e1481680f20284101010f540e40007800700700e46400140c171000d9080b40c00c0c000741460900c82c2450f04114050300300e07030400900c0e5840208070f9104c0b2806607203411020850518640e0300090030040c0003104a04107040c9140b031f14140242d0503001d052603120701c2c0c683d9002e0365098903e0f41a140c2441c241022605084510300782151101c1d00d5001c150750068000c0b0025068808800001500109010b45400410703d443c1e012215a00081c00c007070480d0015465160724911000c00d08180c2502402143c03c407095 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 178165053 1250 178163803 178163809
    0xe120309031507020703020f04020d02130f09020901050f22060504140d0312050a020904090c05030607030c05041505040308030106080a0e0f1921020f0d05031003020d170a030b 77
    0x1030500d10ba00704a0004001c00c204158081203060032a981a11240710382400280000e01a0052000b1031016510219034111103640c00f00034482201e508d401c3c4407041c0c1d43c451404405a2189269a42c0822001c1000a190605da1001800d03c1590411602000840c00103056a03012f0340d6441072000900115043c00000412558011345040440740d071030b007071155554080c040841010b5000300081c0d1380c1d40000c0e54421070ba0111020544010030400540e004c80c40c1039280041c142c014a80644109400600014040c1c0314208900c07440e40c072440c1c00e042c508014006580f0141c1c5010003046001d000000000e5414000b0310b001e00000d80b0340740040e14054692004807140c0c0c0030903020640c81191120074281c0d000c83c0b400000b5014140c0100307188128101440b06400903406d81a145404411080311180d000c2100100342c20081c041e074450012043d004c8901c3c2c00290f400305850405580100300600d04416950080e91003648188640080c6080c01400c5800c124103000200e603c6408500c9149 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 178166303 1250 178165053 178165063
    0xd03050708071709070e0106090e010518130302031e03090f070303050414030c03030c0c18040b06090403030902030a0302210711120a1e060608030a0e0f010e12030903 73
    0x20100d180c49501890401401400c16140c0c65100d41c6564583e40414843d100922000e00504458814070300f2a580d1900018620f4010344141c0b411030320188008100c61400640b01c2d42c1081112440c00701c41d84801034100380304241071008406511003000b045150909071031413011702000480c050f0343c0701c0c60401b07442800c01d4001d8a00000700d030044a81070000940040030340d4140c50803a50400392207000940132a00d0044072421a56041c072020880340741d00c500c0001d0703d10003402c06880841c0d4101d4a102c400415803400c0c0d50003045140c2c64000203105082001009611501030320f008503188010782c022a0400852003c180c00603005440004100200c168a0070035101c00d00c2c11040c602015500e0703501803603c4e20b8044074130501480468008550082001300e9113030750010421450054404448410385400f0001160641e040400c0094811340c00300990741c41d140961541100c4401c1c8104020340881c5844605052100c03801c50300d4100d88400380c41b50b618056200085035680b080b00200b503e04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 178167553 1250 178166303 178166311
    0x902030610170a022113050705010206070905060a12020c0d0206060f130e070506040b04060f0302120412031b020a06050a050103030207060f020723010e06210a0e0d020d0305 76
    0x11096041015101850042a140d40180081c800580b41c55401c0b070b140020012100600d4016004481800046c500c103c841e6852148114100ea01c580c2da54401a83c50740c070210341e900e010680e0340c0700410040c01c044000f040c180403c0c0c68520001442082201c003244c0000364107428036881590454501501007100c0d540000c41100d6546105c0785040004103882e00c14490a0141d03500c54154a260354020481d00000c0c06004011030b45503a04d814486207660894400d007c00145c055211000d0302e8000d00c01c0700e520258015902d00c1c40e50300e58486c409001c0003000d10307004041d1303994070750b43c6c008120008141142c8000e0b07000e40843c414605050090b00d0020f4500c02c1014a040010400240c001070b01f1001c407405030601e00f4040010207000e0741445400c2d072082c01408a00a5000c142e191030b21554101a1000d072070f4444400603a1090140742c0c01100b44403220081c0c0d03e04040c60000940614540c030103810100458840000030b06c42c0d00300040844e1060140e40003540410200d5014000d042d0701c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 178168803 1250 178167553 178167557
    0x3120207060203041211030705210c06072a1809050106090204050a0620100501060216031e050c0607030306031e020907030203150d05033001030318030c0902030610 72
    0xc02c0e0a1503803051752885803040040903a9076003c920303041c81c2ca040c060310004104c0200416240018600800f80c040d0f2031540158550042003c0301c2c0700340c0b0300f010544031104d070054204820710800301410724075244441c1e00e07c0d420404000c4006407089000c00002081c0202d2400450241301610380030f403d44085800c40c5001fa401807009210343c1d203844c030200040b640d90340f0b0201e08140304004110310170515010b8220741070103400304180318000e454000c41c0c100e40d11542115510340f281078000c040440940001000704402801300c00d03103a0f2409103a40951030181055030b4000c7c03441c2d40041c21940c0103603c2140842e454413402c1080c4400740303000501c48182841c4107200081d1950000d11440001041b0380d00345030303020001c80c90500d4000c140e021028005003401240a201d41411980ca4002e03410b002950142080e10900005290140956800c41c803001d07400c540e42541e0f000d68500040782c5104211900d050400408607403440e803038100510959034016580d05020702803001c042e0018850b40c003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 178170053 1250 178168803 178168807
    0x20a090902070f020d0f0f0507050f01030209030703060c02030906030a0f050705070b0103081c0c030603110d020a050904060e061f060e0f0111010b03030f030901230a02030a110403120207060203 85
    0x4101c0b180203900e003e960441d4518031120b079500d0b1011080d90006400740c07070301e112840d00000f00100012440184c03601101c03d052894001c0004405034403a00c1c1441ea09034001503020000151a904003c2c082d040074016241015210004039005401c100ca1144146440e01c2504407007003d244280c0340c00c484280b5201d40340c081c1a841d000c010300b0062000400c6820000340b0700780b80d41c0c135190030f00300001e81036101803080b41d00c4500010f024040c60f00090f1040b20545410342d0491030001444961942c0c0038110412403403400c401c000c10a18010419540c060b1120050526481d05010341481540b0075414625901800c09001c400c49056400110512841200c9100c0c155034205816a000c242444d1480c94882050390301409440010b03102601071201084418020051401552107044180020404038181640505010400c0c0c07800120065403240450962081d9070025903004084140c0411014003910340c0b108550300513802a11183d05017443ca8004d07036410310414004110f103100442c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 178171303 1250 178170053 178170067
    0xc02210316081e1909030e031005090705040b0d02030d0918020711240309100b0303040e04170c06040b06040c030b0f19150504081603050d03050901180303020a090902 73
    0x66010000e2111040c80310441100240055a2001413600740b000010028098502a4500a072040f4100b800c3e1905c02c2c040c0701e2061000c15103900c81c0c1882121008000d00c0c4091230013042c0001050f1059000e0341100c0d50b44204005a1030801c2503100c009581c1d0b0302d032102a441e1001941481c406c2001d074040b001c0c0100001c201140ea14148412003650455090400500f240c800412070409010140100500030080103940c1d140840c0a111050015005000e00701c24101015124803660281c290700c3c0c1a0f0902040105a042c000075584140307800f84180783c00d11600003039240c80301c1110215008080341080020034100307802502c12040d0395040503c80c4010030400030f1403605c81381e480540601100b04140810900c1c0c64075800c028100b40f1410016002c102c88002c005510500400101c0d208140078500c404400520401c1140e802c40c0261521286182c0120003602d0083c251031080c0d0740b581c0d081090b8400c260402224107100341c070010f80e640c1c043c440c040c111040662140f880140f0600401d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 178172553 1250 178171303 178171321
    0xe06100e04030e1e0d08310303030507200a0212010b01090b090303120a02030108010c05070f0320030c06040b0a0e061b0c0f0a06050c0901120c0221031608 68
    0x1626401c60b044810f25242c8130860003400011003140100c1e94818000b404020900c00740d000200400e01c00900344801d01c00f0040160526203010150320f4011000c15002080483c0c03080d8441508250315150096001f01803641c1c6c24005030320041c10340c04541124010328214602790109181052207203000b482030020850002c0c00c8107100380303e20000150000345009840c0e40c20310443d80b040050310540292420402c8004000b9002400752503d01c1d880c000d4500f1000d030003001600c81e8650b03c020a0b80b99403189680031601c08019070805a490707080d40c0c06061660700e003480038094506680008090b00e20b4a410301c0d900b8040058107089100340f415044107500440411280e900c03403010150202914885245030009100358544e80001e0b0213041559039002401080c0034000c540508424461038840f0b4031429918414140b005010410811142c1c0f024401c0d074201d820000c0d505e00644814078059000344181c01203d01012100000c0041048080f0300e0400c43c50404503507c0c50190301a2600c4554 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 178173803 1250 178172553 178172567
    0x61023091b070f05120309060106030902040603020d08070c0e1b0903070519030c15092106110705010f0e030f07050f12030103120804050714030c040e06100e0403 71
    0x10980100542000590184907000c514440d10718041c22881d5111000e007028441c2c1c50f407091045030340d40036a168003091811400c00342d90107810321201500d100d07442c02000b40c0c0140b2104400302d8006807038a00020259549480c54070101c0e026142c904d98a1450780b400c0c18041c0507036041001c0c030040200602040107007140c0181c1220302000d103083d03506c411303050029181048680c0b2440e807100b05004003c20703120384905110300716807241d203215481c4c0b611054200f01c980b03900d00c04100042c401820030452600148650350362a26941c02104040e40c0c01c0c5c59441c255041c003204082d002c60700003600020400e09200b5401070402080081003484101054140c89101d114130340d00703903540701103807800c1841428007082d101d140711401200c04400c6544502c08668009200075280380407100300f500380480c003941881d0310031a4001d0241164904203030a0b290f4403c02c00c000c0c2c80d00343c40703040c000d00000d4540307114821500b1030540043c501450510100c0494008540114041001c2c80007804002030700840 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 178175053 1250 178173803 178173869
    0x3050306010c11090403200a0b071b060f0c09090203010305121312120f03140a1505041806200706020702010507080d09120207060503041101020c0307080610 69
    0xb0344411104864200746100f03c40010f10320754030140c40030a1004058200d0010098244090358486c0010596000a5140c0ca03d0b2003002e0075283c00700f00000c0c02c1c1807003400b600151125059082c01d8101d41c03500c806044800301d00c11035903d01d40d2901005d10243c4c1100303050004010140c07007940303558115501d443e02c80c8a034140d40800140045440b40910301188540c81c003508004550340c84d408007a05111110144002554000c00c2040c807030005c400780319015503130b01e500c420329070000030b61503404844000302091184415421000e41c401b090a136150300a03084003445200b08804c0d0b9614500700a0111045202c04044120341d0184541280c0321410590304180e8002c003005171150601d0005840500c200c0c80700034510000007410b1072200030207921242c1c6031400759080542c0d603206035000b640e66403414025840460307418030009000960540d107142e20104184140c070303111070464010920b01440d1740c11104450f0482d07420410403841c8591400001c241c41c1e0381071840407040e0040960340c07012201c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 178176303 1250 178175053 178175057
    0x1814070602100c0c08030403050a030b09010302091b090d0c051005130303030234170a140304050703021206070305070c020a090c090e0c0a0e0d0804170708060a0b030c0d0305030601 79
    0x6043c103c403c034000c01100e03040326001030500f0f54900d014030300103001c0d40c01500c214011a19104c03900c01103090510300107050760745c003405056164039421002d44000f61804121014072808000001c516118a0b4140c141c1c41d11862440114504000070043c2102d120a0305c441000014003801009401101401048030340604005a031444551751202121400c90001901c000c1c03280c03901c01d065080e400c406814240100304060500208540e03890941c45001400000039107001c80540c09078100c01c0056401a108d1412240805d54a60101b40f00901d41c2c48400103540000081115954260003001c3e03100c0310a181444110186600060084040340200c800303865865122000003801661401d019000d100f80495182c42c050281502d1a80b00f6002c180004000f10070108203401c01500e0110100d0b8060300b410304250514404d0380b03041821039409242c910440702c00040540307040c0000b90080a000300003081410100d420306103800c2411070a64000d030141c02d080c0b00803d6101c819250081424 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 178177553 1250 178176303 178176311
    0xb030f0c1314010608160c0804140d02030a0303090210030e100f0b040f0b1005042103140705150601080402090114031623271801181407060210 63
    0x1503260714010040060500c486038550390002c035400c1d800102241c825a80d80a00e480302d225800400c403484141c00b0301c0100181c00c180018860743ca0700312860505400058140c400006150f0006450589145000d5021a94a865800942c105004030380f010030450308042c0b2103901c191070300359074034140405003007002035843d4501c07400c500c3e107500310201c4160014003c1c02220242481c460042117040c8589200b1030400051420343ca0054003a20f04440f030581141c000591100c11060070318002c441c04404100000ca46070300d031211481701400419000d60000c00702441005004104280040c0845062080003810440160b850a41d514155012840142c16842c130280c007180c42c00082d944956800e1361905004900b20000b40700840300f000070b2030841000c042240c3c1c144440c40e08079103004c0d01d000050740304c940410100b000c0e1160700300000d40702c810206031900c0342c0d641c212490900104100c00540318114144918000d50450044242000d41941c1d85080c102035980e40790806051400780d29 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 178178803 1250 178177553 178177579
    0x601030b0705091009090c030b01020c06160f0309050306010b03010506180102011d011e0b010c0f080403020603090f0d050a020c0d0510060b0d06060e0f0402031504060909060b030f0c 80
    0x2c40c009840314050302034254000307203825603400380c1269074900910350310742c0c5868442540c05100303018660540e28103801502c5070040b1042031204960020b030b20b0700400c00c1e200300b0210010769180710140155002c4c1c1c0d0f500c0400340c10201050304280c0306034000d2095000900040c4141e550300002ca81951011140020062041d06d00507801b4040038203101c448000d8081003240c0c0140306400050310411201391110410071031035904411101300c00340320740c00528804030150005445811a0300c885004620582c2400c2d50303540011480c0d80100d50b0b80c03009400081c3c2c202d800100c200905a10200c40f400e0030340c2445241c010007943c864010500b14801d42c0706415882c01d100301440707400da000c800303040180030302612000000c0741c960003079040710405450190700040c040d1150b50700c4c51a011005041181144481e0104006904060a41c00403074182440721001a9594442c0d503000380003611000c10038410300e04101d0100c4604002a034069042031021180c60340c07012802c3c2c0c030001400c4851401c01e040d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 178180053 1250 178178803 178178807
    0x30c0f060705150115092108071110170a0b01120207080903010906060503120a020d030e1c03050a151202090c1201030b10120302070b030604090c030f0c080a050601030b07 75
    0x70090040081e0703501c501c0000c2100d4400d141d4000450711702e5203c0d0211a550344011180320107155940b401290042e9031040c000805c140010b08600d4000d03000ca4034015090300025281d0f0240c00e480308081000100042c101e0010340460603445001d0740d2040091601103400039180841082c404583e4542c00145440ac010304881078444084000d00200703c5e03405240340c01c80060030700380110742c0320340314080013040c1c0a8032842c2241c1c01d241043d0b001c0c1c4803000c40b611096000d0a80c9a00c006428010280c001040000322981600700e500199004681030401003d40c004441481140c0100c9900c44082403140301403a201c13220301181d040c0c40380c1c3d410350b43c2c0e14256501c0b40124490140244140c1c40004144030000390701030300a0514203022045c0c3d6554400e50720041e40340110040c09a048400c0c2000300254600246510148c080d00105403c40b460b0340303004040c0708640045860000958a8405102c4810700e0314001d84180e400401d00b0f2042c07500e609903180300511005000510207400600100c4c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 178181303 1250 178180053 178180063
    0x305072916080f040e0f0406150b0a030b01030e150415020403021804020117040f050127020d03050d0228090812030703060f15030b0423100b1605010b030c0f060705 72
    0x5c000500c09111034208003400c00c0071940107a90030303100b06090803110341590440403214021210403040d15031a0000074042940905200094241450355440d80c2c103802d08014000c5400442c8900c000d00c00c546401c0c038042204107100080046907a2060200b4401a00d80511f80d04001c001c1110043c560341da2440101c0d110100411450403003c8401c09000c00c200c6126111000b0034440e500921801c1913800c0c001c3c19118a6141c0ba000c10800c00c89000d01500309201090111401ba20b092480c0540c032900a0b0166070000d00b00c031190900d40d1500009080456071007481890700e51610b462000d10f480d031290382c2e8840c0e4098400803580000301103448540603902c00703c020442002e0380c1203403e90700d0392086800c801c3c903600d660201c0d0074407070441d51030b00d0540704010b910b100d00307413444103440c00c4000c2d00390150100070802801030141c62004114015000040c0c003070701c10320002c00840c00141d45001800d445482d61454000d51100f03e159420340e4503000711182d10a000d5500603121040c030b0501500d0a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 178182553 1250 178181303 178181309
    0x5030c060f0412030504170109200406030b240904030f1419031e1401060f140d09120206070e06030604150f05040b0312030c0f040305072916080f04 65
    0x1680e42500103410150032001030700440d400d0690491044104040023826600ba0000003000d41c0301405401400c4d42e618026071407040c4020f040003800f162282c1d6401c0c40d996041da444449840c0d82c0c80c0c129031403041c01e0340c2c0c484e8042040c4e0b0618100d0820766000b81c0801e08240b51001070011408200c500181d4070401d490034811348011601035503015a0303018006008107400c00c40d144500b000c20091060031400b50194080302e10550310000e030f203441e904581c0d540160300c00c0020018414400f00d0060814030141001e00b805d1036000440420740d1408080d0703038032050360010940d0441b100300181682c00040c84000482c080d100180e0383c0d034600000400800140044103914031803503001103240d5440c1d4080700d094506c02d440810082404c0d604041c0c0c0d44004840706c850100c0100002840d444164014100d04a60700440c94100354803559802d09101c81380c5c006044c0d414803d00e241354208211007001d400ca66002035824a0003411848000208101800242050b8800203100030100100c0c0300712801 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 178183803 1250 178182553 178182569
    0xf0601110304090203010303030507020d02150702120d05010905091609051503010f0f0f0908032202030717060f0708180f010f09050f0102090d030e1f0e040501090605030c060f04 78
    0xd103c0d01c8085020082d0401e0000341c3c0003a240100040c0f401d400010b0349400e01465400903c0c1801da040d140fa00420b0000303020804500a0140041414810f2805001c0041d807906002c40d0540c10000000c0896030000c20700c081d660301120400c500611143d8088050300c5207468045103560715180e803510f00b4040c140e840c64040d1320f80119a01d405c81280c2c852901000110400d02031a58400080d009580154401418018040000c5460240c4040c50403140407810500800040000e8001038106003c43d4001c01505c0d140d8040f08540b2030303003440402d6004031040001c407890f06010000401c4210300504440c0c0d240c801c940840207480d02000f001403054020b200a0240e0041c140f24032000e8001407034119400c3c4181c03a4405c001d54018000d41e5151200500b16400d0074205ea2001c4501600012942d034201220718041c07121059400c141d078803003a5040e10380400e034000047c03e0000300e030b9059024045462401800b0f10060340c012a44040f08141101c8554036a803490522840c035215075807086032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 178185053 1250 178183803 178183807
    0x2802070e070f170115080a06090e030706050a02070b0402060a0c021002070e0f0106020606011b0203121b07051509060d06080c011e020607030f241a120f06011103 71
    0xc1c05035120000e01e507010042d40d14030910041c2c00c0e1004401c40d81c2805030b0b00c81c0030054001072540e10300c114000d60b0300000000004c0f804542d5803001d481140d01c8a0382d440d286800014590741032103a0f50103101d40010007160b0461920059480300700505001074002489000002141e819032442007404429081c0c0040c2000038072882c0c82c0010f0769400d07052003440321150030007000a0b4080c40d88020b603030480d60070790082c000f1652900011a1020865400b0307501c1d0b916003c00403805602c04010700705400c00d10701081c1d6523400300c0761090ba00b281c552103400070a0303511280c010f00841e03d84400c0c1c2c2c01302210803140c6c07640f07e040100000b0524040e4101d68046540360a4001928150015103425141800c1e2a40200700c03004103c10402d90601c86034160242c0d00c00c10201c0c0450748254403841202c01403100014503407800515051542501c0424902d801201c04000d00c02c00e096046000002c42e241c0708120700d00340c00d9152540c410040102060185c410602c0051070690140308100714968903001174a07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 178186303 1250 178185053 178185061
    0x109150b03010b0d02030604120c15051005030d02070e060a090504060506150403050c06130e101a0c12070f240b0901050d060c050405060703051e2802070e 68
    0xa0018004692603030301c02d608105602c555401d080c00c4069503150082d01a2000f40d0381c94490070006200b0740040030400c00300704495030100e18000c031149402c03c42801e02141c94103207907103000039045a94000c10b01c01d030003441c16084282d40000e81482100e59040c800c8031156201c00000b0f09074803865125201480c00c01080104003c56036011510901d012214030300342418a0500030001d005600008080b40d1110003815001e20709880580405400804400b004640b14000f5408030704013607611259408074840140403030103924481c185210b540e0310b00700b07050100c1050010703915080309460704c020107000540001442211007030511001d401829540361002c400341e8410030603d00781c08600615191464107400c078540854400e0403a42e0042001030402003a4035203100034404090f00c8414041c04000c0000c0e580c440602070040307507000e0b4488a480f4440c00c01850071003c0b0080c4200c020382e130b041204058a603510b0356550929200204061204002041d0036031500c01c41d03801503142190f40d80104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 178187553 1250 178186303 178186343
    0x50c0304030b0610230f07060606080402031c090e090f010e16050d0b040206091807091802090105160305070503041214120a05210108011b08010b0901050c0109 70
    0x16000d20025a01304c1000b07190224200e5031440303040000d0300b01605c1601448513001598001c0c0807008803803c0c0781403801c80b00e0707612070040311042c1d030098000c628141c041200750320781409402c1c0e8502d01c00000c24101d00f0020b1005150a01a00602180440c5040803c1002400f00b0000801d80c04800c001c0044c02c1426a001b540c0c1c41c181042181c8a0401402c00b18041c1469410501c4080d071041640f1855181c07030b0708201c1c581c0c111114580d0024580c00038101c0b0408100f000c9809040107868182c4000e0421800820310030a504c52286914010002c3d9080c507644402215030512028050100480d480e02e0100c4082c032801801030706034030000c140403400203107850108546030700c00d080b00c2800c4010400d04da610394410303c41d800c203040818480280c4007406040104920000150382003540c1e0034048032807020400070382158410340e540311101500060701a000514040341410328022561606200c0c03603043c0708003540c0324100500810320264040d070942102e00d40a520107072448003190024a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 178188803 1250 178187553 178187573
    0x10033b010c0203031b07082a0109030f1205010305190c08120405010905090412031e0509030a0306080601180c050408010f0c02070b12040f0f0206030c0d0c050408030712050c030403 79
    0x35241c0085c00403402c3e8600c100b0b001d42107800c559807145000f81000e20005e1540b103000c0040c04041080c0401802914076848288a1461418400c2d1681201e0a50b50f917001003c58142c1c84d50110300a03e4400103101280001403c03107090107030302c1104a8008508d1501071103820650303205500c03900c0f80020060114040388060403d4403400ea85100d40c0540c0ca10802448000036940506040740e846807003a107003842a0842c0e100401e801000c4e1811480d44501c0300d04403041103400e2140340c3c001040101065515000e8a4000c1154000804095042400034258482100c514480e071540c0c0e142d0003c0743ea8090810795005140c43c800804c2514102d2216401820800d504000117002e0f549010030f4411b1418155a007191444400c0c0300180e49540d140182150f000350240c440e146400d510f00c0050740e42c03900562140182210f4140c03144080c11034801a50190b90304403080c020300340018844506c0004c151030380d03d90410885440c0790540c0d0300030341e8a071003803600241035808001408000c0c8842c0e01e803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 178190053 1250 178188803 178188811
    0x1c050708060601030903081b090d06020409240905130b090c010f080108100f090c120b0105010906120c11060c0a11070812030424090210033b010c020303 67
    0x100792840e0b5516071004508858900307030f00801091014000c0b55a01908104005000c2c0c20101491720f00b1160307a00080c40d00c0009142182d80c6500000c00388548100e034015144941a8440100f44400c0c50041c840002405401072898883ea2200000c4060b1484402c50f403a80d83c00c08420207090030308128958490050407581404260f5483d280885c07184101c4034103041b246078401030842c2014210424001d0f04c0382c1000c805000e600d42c43c2178804034140201490042c030f03408884044131102841c094002441c140d01180c148011160200304164001c00741c40041001d208000510000c00e40d03007580c1c283c1080358480e0b258410142044031000990008021038541600c0b0752010f0040b4071005a91003186001d85100d0383c01c44645034401c101800055500031340301d511440c500c041d58200401c015030300d61505075016503e40180c4010750410300d03402502d100c1075250500c02c1c185c0118090740340482c42c4003580a45018071842c1841400030118903102d04a03503c009214524042a009541c2d800c156 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 178191303 1250 178190053 178190069
    0x5070b07030302121801051f06230a0807020d0302191101090501050a0c02010e0105010803070204090302030c060c0d0605010503060a05100c05030d0b011701121709040f0501030b100308070b061c0507 87
    0x240201c0c0b41440300023800e030f000c2d204c00c2941a01c81030404a088513243c60701016410701c080300c02c5410070716551150180099004658030b40c099450042e00081c40c0125220301070050510410408080c030020301024410450310b818401d2110954211a80c010001008050465441d100510000040c0c0d9080701200314005d6000b03103c1c1e10510140700c0e00300c3d60207101d003c4de158400c02c2030b0001403e068208c000464041c0c01a0ba080408650f48182007071801c0b29401030f038000c0000c186030104a81c0c4074882c0541070070700e011411440c140000c0751050805025282c032480946036040300d52807103802c0b1501b2180c1d11505580d102c0990b224910094400502d40300d004c64039982e0b071941e165403c044400e04031201484400300110307181d1a41941550100c0340d12040b20003c1244248030744a034001e442000d600500001859031650502070501ca002030100c0301410341030700042010802620075100e4481e04a100c0500c035850307104c0060003420100107008511040400454140200400c1e501b0807100301c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 178192553 1250 178191303 178191311
    0x30307050607110d02150c090a030309030302210d270305090a09090525051816020d091406070c0b040303020d050702090a15090f060f050d05070b07030302121801 71
    0x2860507a484506891305100140d000c01d100e00c00050036103c0b40e94210901ca00400d1504c0142000b04680c56180d402c00d80200e142000e0070000c1643c10003c0b0300903071441c01c0c0c00040743e407088049280e09200b4980054001c40d15000c1c41d0000190b51403640c0d8584082208001103d03405180c041d100fa004104164420740401600141d413002500071851025800302c00382008500d4100071100c400c0380c4290600310481c10100125890312017020810b05105400d46455a83c038112000d04003542e0110410002c64102c0c0760001c21064000c1c0160043d28903d0000321015401c0e14042103c80c000c120003d00528911200043c501d00e0000c003c005583c040c0e030903168501c10b4400d05075014401c084009400c103481e140046e19448980c1d200001c070381440502117029036500d082083c2664a98419616250303034404040004040410340c1c00e000309401e0ba09166a29200d072601c54403001c4a128400711940c0004158041504c241d04880d40c070306802c2c240310128100b0f03200b0007901300c11300c10f54403003650310b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 178193803 1250 178192553 178192577
    0xc020c0307090e03041a040905180d0f020606040f0f050103080703140a050d0506041404080919050a0b0306030a08130e01050108060d02061b07151e140702010e030307050607 76
    0x1a4001c20b5203c29040380213610f040d00d440103400c14041d0043e111000340302c0500000c00c084407140140c601071000911901c0b510034144c0015410039030000702e0402404801503d0340401c50b000b00b845a800203041702d000550110704844140034000c00c80c500509140342c00000b10811a61001030507950780656141524003d00c0310111010740305a41c40300021801c00c1c080c804d913185203504000e03440403000d000440e0000842074074030112030f0141c900b1140d98a01140b40009402c000035107242001c0c036070618102c054582000700310001003500580312241350000c009081510b0400c0400c01d280e034094240c0c0d030b5444c40034014500d01c000f6400f0359170b0200c0c3c00300000103c540c840c1c3c0c1c141d030044800030580c06001c2c40300c1d0708201c3c040e0b10a420414140920751600c0d034000340113001144c014500c0c04140d00c000d030241207004007224800c42e90394070030740ccc9124610031b03d13581d1052110040360101a41280c0d280014001650700c00c60382810958544070001e01002004000b24070503005400c1911100381d0245 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 178195053 1250 178193803 178193819
    0x20124080d05040806420f0307180513120215010e06130522060b03010612051506131d070f1805040206070b01031a0603030414090907090c020c0307 65
    0xc40c5104040c03e56100d81c0100b0224460410464604a00450842807050130800e40314412103070401c14201000c0000380c6d4a0f0365080001e00b1403440300e4200c008d061102c2c104400e880c996240d000c000454955a031001462040c1c0e103200030812150000340c00400c0c000b82c80c000035601d040d4150004042010b140001483c0c0105158490040ca00200741c000782c0c0d114040703000d00400c401494030340f035078034403c04403030101000036101194180100d0000c40d900003407505040c29a40103602040f240c000150490000c82c9020843e060406641800740b0965290703038000405c100d805c00001d102c03107442c00302900c4900078164020f40041d800e14098071709003a6240c010108000c0a0302c0b42200c0360184482e445d404000740c0e8021548117200900150406183d5110410041c400b40c104480d100001402481c038001031014066001504500452505c0e0400c0499007000b90842d15050151103200c001c03460548007031104101424144d1010000760901260003541d55000010760350180c01007050109a8003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 178196303 1250 178195053 178195057
    0x6040e0718050901030f0302100203090c0906090609010302060a03060b0d0204170a1520130303021902130203060102010e1005062409010c050a120203070c050603060916020124080d05 80
    0x101c0c0100385030040c1e8a5500c03400d0381000e068408a0449c06203601c00d56091610f44007441c0610900d400400d06410000148102404090003081c480e020300820000503913070b100200c07415a9030564803951540368a0300c00350094400b5400241d84100c01103840142c20380e9650140040390400d840080005076280d043c943c841c00701030320103070044804040d2000d60682d2038001607158200f44d080c00d252208003909940c81078100e00b200d481e00301d0340c2c02410004d0540c100841d0980a01d45450407039038501a0780003a503c03e81d10907502091a03000b10004107140c1c000c1d800003406001c404281c0d0044c070125640384004150840b8914443e140000012860b900c1c01460020303040e0021013400c0c81c002048005560400c13259604503110300c1030030380c0743d800642c00380810701400220f50029900c0b00003070302c0d100102c11030a0700300c0c6000d02000e10030044241e44800f01990001c0103030207008100c0b5083c01d002c0780503000c6409001070011614800341840c03203508525200701c130060400d4036581e03204d0350801c803164 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 178197553 1250 178196303 178196309
    0x60c1806121a010804020108060f030304030804080106050909070501031a040509010507031a06041e030212010b0102010f0c050306041d010c0207170705011706010c0c06030b03100209150903030906040e0718 90
    0x140c0044c00240c015405191855080800203020885508001000a1841c1e00c645c01c2124000c0c0041001c1003640024051031014020844d011030b1189800032402d0360b00c5400e48144c6041503101c0b030f5508405051607080c0c0d000c041d4003600c2403107036191410000d40039104c1079460b00700180c9130091500804501c680505007080006101c0c900c0c0c18a42150031604c4d142c0c40305c0c1c84015801c41c400000c01691002242c6011040840021440d0210507002a0131590003454000103c0d06001c100d170b4805070b100d000c40340e2001c400c9400064003402e0560300100f070300c80b100e00d200c0f466103000204034101e50000380100c129800401440506a8049022a1103500c903110f0303140813a110303031401d212248540400551128061400001b804a5a00c440c0d042e03689030303806040442c0e51030411102030b0809021500c030030118860709501d000201e4001c140034990b9280480504040403550f1350b041ea0b030a000311005113100a08a90315546c64400c0201c035400c1c181c6106010814507241558600a50700614040f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 178198803 1250 178197553 178197557
    0x90109030f02060114300a060510030f12090816050307090e0304030b070216060e10030507080705130e0403051b06010f12020103390813060c1806121a01 67
    0x100c0007018144806c6010009642c0c24404081030034007009082c40000f40101c0c0303d0310004285910749805e02c2c000710744018082a00a15860b0018070115048038600454a64440d2036450b801154440899842d240341c1c000c2d42c4036025100366044010300200b20034043c1c0740102c0641c1c4105640c0c80302407003220580000510b841c0c1017031000300040344204072041d0b800301c21401980c12840302c015040300c58844c0d1b0303045038011800e46103585c0c41508042e40702c8024203a05d42070410a900380302001804211009110000b040740003e0312806210808064000800000003509210304003458040c09540141155035112880c81c0e44104c01d0740d9002039454120358140c595510746034200080003481c0c050910050381455203c00e04c500500e8580410020030104075120340301000c140385140507036407508517600810000345d041070000141a0340b003450080350744148002102c150f4840d00344d5900102c0382d1001c8070199011000078425070000c51410095104000802581c01c001c850006071504080c0c00c41c3c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 178200053 1250 178198803 178198829
    0x2030f0703050f15130f0321020a080a0e0a0b15090108010c030e0d0801030213141501020f0102040303200717030306040b100503040609020307080a062304030804081c0203090109030f020601 83
    0x1086d03d03803220440c824046d1400c1603c040c02d030b2140d40102901f043e81001c00a50019815440f180d208020a4016262410501c560000c40b440c0702e60b43c101e14007000d880c041b9003001058024115040d144480100504205410f613519546a4000d10703051071b604010a007480300c1c5c540344140100d46210074080c2d070784076600307540d08540038884226179002500240503980c1b03004203c05d03c941c009080c030030f0b000440181400a10070303000a040020030402c0c1d09540e1300610062000a800211031078248032460802d50901c042c0c0c1995030301c0c040f60f5070300c00800d65a09444071101114080300452154001342c80c00e0000c001e024060051441043c0c444000003582800450002032154102003039003400101200c0395540c84080150a0004541003198030039644c445422462200c04081542c115220b802d05000d86483e2300c2c0034200c0c80d0001c000600d915800103281d181000d40b0080031088c0e98030b9410440d2a450084281d030b000f00510181500850420181d61002e9440001c50754143c407403d041e012 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 178201303 1250 178200053 178200091
    0x50105010203040812090d06091212020315090a09060c0f09050604140607020a090c020a03030b0301020f03130f0611041829010507080d0203040c06020a0302030f0702030f0703050f15 80
    0x646400c400d0b1b0007030740480c6454681c1c01103040d5001d18000c55024040f0000111100309001d0981d104142003025440d0040c400c1021440d05e144040b00350f118240e80154060b81d03103400480007459503400080c01285489440300c0f01603440b13200c045880f1941e88031446410b49803003c0050500540c46407a1602001c04060000c1d42401c0001c1d020342d9202a001c1600d036a150010642500d12003030301a00144e02c00c0440005256040c084c036502034a06900841c0f0700703000396080d5801848001d1041c4190456449080200441a208000c0250300090200000da808280c182e400340d209200d0030505200090341111030340103074440d030481a4002c80c46402a242a26020700c0031404105c3d070135040c410306000580c0412001030003010480d00409005035a442e02c0d2400c111058100d4000204544c0b04503050f400081d000400c8440208820520341c1e10382d91148002484c01010006038101c0d4090340000000300700c0b0004520410444d4002a41d031029000e18041e4803003c011603c0006607804d09100c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 178202553 1250 178201303 178201333
    0x1d010b090d02210f06101e060305060619080a0e010b0306040201081003061503050d0f020640020a1e151e0908010f090807060510050301140a0501050102030408 70
    0x5a501c603101429110010903d0694071400c0524061010015800901c100b100c1040c42e00c100501400c908032120445c0f40b1450700700c0390300d009a402844241507540c800725074141d0b0354609491031140011300300391f0740b4109050b00034004041950001c0743c03582400b080156505040c007507410001d101030010020b9039a250011199800080d09081c428820b10300088041100707402203902c488200403840c8952032a51404500d0714040c0e0701d86200300032000303070040132813039010800c1c0e038102c0544800c49880c090307458000e00b80054802c0d00441034402881503207180c580b1912240d52200c0c000c0b90044041544c682e08c060361105840d94810301c0c101c800109011411122424050340c809925050807840000b003201c145a880a40023040411600c0380c082101100900584079082c0c40b0007001e1180049654451025004401005002c1c41d11b9038000fa501505400c014401464010001e000c4e00346401441501d00000340c402841640c00c2900200f401c0d40000100c808541500000f0285180c4501c80 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 178203803 1250 178202553 178202569
    0xb060702040b1201061706010611100509030412050d23090d060f060b0d0f0c050414011101051305100506011407050705031e150408091003020706061d010b090d02 71
    0x5079030351198030f00c0001c1032150b000340b058802030558121381c0c00c8440c1d014000185001c1059008004200106018865004020400c10084040f85001060a4403200146411070107aa0001200c1c6038021313103404140f10f4001880e081c3c2c035005841c0e00c024282c020b0b400003043d400802100054600c20008509039080c07034140311144500643c0b0010b010608190041c0070b03200035911010060703002051082800449109007a0060001c5104200004040307101a05a014500c144443e026121216000340e03400303003000d00c403191003610007042149000c8459100d10040351b4400d45030b034801d00c1c0604845618502c12180500e01c142c481c403072400c0300c025011038107074428802114540140003000400340c0342003154242c01e9108107241e11101c0c0c03200131035500d840c03108160545e19401d04820b00001c40c603c202241c180c010184d6122000d40c40c4048141d0280c42001c0008002c10b2a0280026513000c0c07229412a008002954114440e41c0e1002c0c500054000d103170300c01c1d521800380ca14200c0140ba00d490 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 178205053 1250 178203803 178203821
    0xb031024021c120203070915050412020105090102011b020706030e061306090804120803060f04091101200703080912060103080301120f02060c06010302011e09180e070303090510030b06070204 84
    0x6070440c5070140c50002d0f401640c0081d0341c804007081d64550b00f031200341c400008020700c820722460b00d607003410b24003103020140e2040d82c0c901a050000006020216910079000f5154600440400e0b9901c0030003184c2c020b60b03a20145c400c1000103803903d00381002e624004a05c06004154401114644003429240d56000700710400c800c4910400400001800031310903c840741740c040c0580400f503101d01d803000602005c544a42c1009118918041000d4001811161420007492003840c1c544443d100040599a100700c5030380c0d11142c40e1055138000070030820100d0007444200c509032001e130484200030211981e21902800010400c40c81880103120f20b960410285034460300801c02918884101d03000701d080e030b038020049204a0303000349005005550b0413280c001004158080303c01d20501181e1030081006107203001e03d48801610030350405501006030080380c1620f101d10300356801305079a460081c00d05400d51144900540261490f40d0100740288505128103901400c013078a0b020b1300d54200002070079510 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 178206303 1250 178205053 178205057
    0x6021209060a17010e0f01090504030503041103010b0a080717031303150b0405070c0b0f06150c012a181d0601031d0d08010515070f0c0b031024021c 65
    0x100d03125000300c0107510f10700d0091495011025182c2401e152080c0c2c00a0140c021940c0c0e1806d00303090100081d40441140da00c40d82044050280181d0940041c0c003410340750078941e601055071140450115000310303c030401c50380281d020400c0740601c03000180c2c4a000380045038003814a00c110400120f29142c1000c00d000d01c146100240015016001900b00d0300d0907220000000c030010200407c0081d00e10484e9004004210b441c02186020000100443c0014189001c0210301041000400c0800d4120b0602c11101e0700c5200c000980840c151210030022182080006500e22807440c5402c103400d2002d015107203051101d1041466440ca494420a40030309680c0c109035940035a110310707142026244200c074007041c003e4010a8051310006007411810307041244218440c2d2074030303102c2d241c1c0035084400e16548032441d0b02e201911814441000d103180e0740444c0e1080400010000ba4600072814581a90700440303280c0c0c11139a804002103850300649001c500035900444c41c80001000c10400307001002d0140c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 178207553 1250 178206303 178206317
    0x181b0509100e370e101a010e0303090907020f070609060c0303020304050f01050709080d0e0904020910030512090901080f0a1e02030102070501050a140f1b12040b1006021209060a 78
    0x800e512083c90b001d10150280d8159982c43d65001001e400c0c41102c2c003031780203d5014440c0d000310318419821140d01c1e6841505208081c60500d0542d01d05009440848070002d19080c41845e102c04081e403920100c02101009010f0140c01282c1c042c020b00d06030090360102d98640d04060760594080d00290700141003540c061240c4406004045401d0017858456903d07136545038075191510061619061000c0043d00911590081402d000d45541640d2a48590100c0302000303280c03101400d044070100e42da08090424041c0341d191506442020005110091003552440c0c1035a0740d8558280c0c482031300c030340354070181c5e0065020310303000c82c0300d503140c481483c015000c060101c42d42c25400282240d015003403c80b01a512901007140e42c032441c1c4a8002c51010842d009102c0707241c410074880c5800b10091030036141c3d002d0380300502810303500041522918000e12160002c2070906040101d403482d0103c41a250541c40e009020450a1012807481301c80f0443d042c0e02801d08850200b08103454003c180c40908010350 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 178208803 1250 178207553 178207621
    0x60103110c06070e120304050d12030204050a031b060c0201020606010c03020118030c050606030a02210304030c0e090c1507030e0f0405010608091b01080703181b0509100e 75
    0x10511a0b18094440da0716405900d1001000340040421281d440c51a07580040c4002c100545030300740d1595003103a00440c224080e038042c51050340240901c0e0406034022200c000044108040c0403040440d030f02d43c1510325003402c3d039a444c080312000701d503081c024016004480401c00c954041d4900d241441d110380004110002c804070b4044038840d0042e0305600180c4130302403010501a092109540140054003d0003681d07030b00d40c010031122200012165403480f02e2001caa8000380f02802510040d40c0c0c0005101101559405292514036069401608502415648607014908107004d0840415020000750601e9000e0720151402c40303a20503482d070401d04400342007220fa50345100d0f0f180601481d0b1102410390424291040c0741940503000302d0512078050001d044181e030008031966100d24a45001714524070b091700502e40d110b080040c020310300302e40001030b601d941c944151078100352001078448504680d1850b41800300f00540e48210100359440001043e00068000415808400003a405c0071900794 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 178210053 1250 178208803 178208827
    0x50105061c140702030706060801092a0905011202040c020105040c0b1b010203070c1704030b0a11090d06061d060a0905090a0c080106050a0506280e030a0b0403030b0d0b06010311 78
    0x111480c0005810006d518410000a44103020284c80c1c0a8001c102c54025a80d0f00c0905510007091100c07a444800001c00c1c100307020350103040c0540071101003805196542d032080707040c10880590407032280d41800b03609428240705203e054407994104040f0b00c542c9241c10044142c0e580a420550f02001c0d01d01d689400f040403d0000314020285503032201450700c171505115101b00002801e500084071b08200c1040420507288a903900f00b041d516001500300101b0040c640e02d80300b0941c40c160000c5208109900b4070005501240498180805156507204000107030b86002c8000c4401c03561204c07080714240a145a40d5108a41c0710b0103070741c12200f0303070611500c9a05030700300c65911015850303446010600c031900700255014004c2c0003c0c0c440b54100801c3c14004411044142155035549103040f00b070241c0700e4481c80454180c104040c0588551020394204900303500d0007100c007540440c1c24001003402509025603105038403600440c4000a86d1108001103000c2e1810044882c03102c2820322a01c44a11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 178211303 1250 178210053 178210091
    0xe01030f0204050105010512060906040e06090109050601050103060b040b070c030b1003050d0807021519060605032502190317090607080601020105130215121f0801050105061c 77
    0x60049603040001040c0e0320402c4207a9070140c000340d0411a090000610b0890010038040d0403a008442d4584291380d0203010500600c2400708940403403242c90284403074688103500408005004509440b0643c0c6c80b4001542554924030a901203840f00b080104015102c0f140500362031f038401d07460303003402a6490f16000c074442d00c240c6444880600d000740401c00c000c420070202209000ba030411082c50701c0e01d020040e4596a80d2141170a40c00c801c00300264940b5099205102c4030b03e000360701001800d84624004000360000c440e10300c42c074800291400b18112b0107038049210f204082e4014110b100d1a510094901995070307100f1018490104020544502c450b4aa00d12805005000707000c20f240041c07005210f000301625180c19a45000140000102c00060b041082501900c2100b1580740328170740302200e40b140c25a0142e0864280c4c06010007166000d4030201d00a0804d04c0d02103900c0c1d103416006089130800c2c030070705601900c01c1242c10061550f03403c0c1180106444080000d5420f00d282e040140c403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 178212553 1250 178211303 178211309
    0x50607150b211506090105040507030e1603020418170a020c060a030e1522050c060705060f0c03070801050d0f050f010507093203030d09050d120b030601140a0e01 71
    0x100c2d48110300d1000302c000420401d40c000c00354409400180c240301c0302040b00d004060243c980620b40301d10000d440c1c207001c2e03004423a040b082e5008540c00d1a0100d0794804500c07440b404102d10541c205018400c0200520000f0101035400900e0f180b26000310241c203440c190701c049480b80541c05180303d43c64140e030b14400900003501994402080c008000c0c240c4900300101c44541041c21008281072000c18000480b81e0305a140c0100214842c1c0c003480e003015031901b0402c0416640c81503000524100b04207000c40d895028205044c00708002d519038621295560008980890014074810010402c1f4900001103d00d218041c800038845080580c446505280d28071000502301c0e03440d00300b8230500c1980800c4850003000b214032800e2100111000407a040001c040716100f00101c034500c0030350303117940038004c48060202e002d1040105207510b00c3d090743ca0741b0400760a0701c0401c4000c8909600b03a0051300034014200030045c0589026800c0100201c5c04424035400560405440d40022413141e403108101c9001e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 178213803 1250 178212553 178212589
    0x1103030702010617030703140a030207060204150f0507030f03050c070602390304030f0201091d010311060c0a12140d020903120c120705031315020610050607150b 71
    0x100d4100502000001c0c182000807044d0ba008208000200381e01407880d2030107180790403d030766480c404440e003100a4020044050502840040e0006140103c11021486480103407284605c8200b4040141e5040c0200340d40640030508034a544c6180510a9004503817044800712000d0828006496800407a08005141009103861044c00c81e803585086a0072000300b464500b80744050040c0b402e80030740781c1c0540e10000f009008040c42c00070031a0300440045000d80740440111580c4040c01c1100348180b030080c8402c1d181901400c4240c401c90038140e040300c41c40d1240714002c040450051340c481ca01400d2280350380003000b41c6070450303a0050384040001d0220782442794016860fa8649003c040c200b542c0d54135007041c40201002803a451800101d4410704030703078920488580300d4415040c01d80c01d610407410040a515803211000c01c2015041c0f0940c18034403400d03400c42d400b0ba65140d090090006c828013902e90300803004c3c00f00400151003000180c01c0401041c5001ca07030001e0340e20100f030800703a599030035140d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 178215053 1250 178213803 178213811
    0x3210203090f071214190302151b2a0313260c011202090607080301230901050d02040207060e030c06090c060306010507030c0c03080c010e0f0c060307110303070201 72
    0x8a0a81d0810032044480c404a024100f0380346066480c1541141c00761006001e0712141c1c0d07555803600001d0041040040d080c03034103082400e407940390081d1281d2140c2686110b0644040220740d80c5c1801e41c90580740035100c01d03202884c0140b14031481805060b0105003503c0c1e40101f440e14000c0c81d00c180007410040c00303080603c082040c00c0c0b010302c040c92110b00c036541c40c80c04990a00710004030000203158040320402e08202c031103142c245855001034803c0000140d009200010304408111001e8010341c101c401030580441051105d011060300146019961544020400018401e034903122081071515803004100500d0080c407650744000356480b944100e2030582004c00e1080805800313020a50b4418592030103091030850120000e440360001802c200d04005000c0380e0740c010140a11002c241007900318440d2110181c2da85420004c07940400b00760f141c10b5090011004010200051103502c04c03013100054060100580300b8070107690001031021082140e0000041204801400194006d201590000c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 178216303 1250 178215053 178215061
    0x60d060306021309020c03030a05040302070305030403030905092410090f0b041409091c03060902130812040302010804060f090215132304050c0c0708010b041518020703210203 77
    0x400f460610341c0003184141c0104007040400901008032507001003101000a21501d032418224907029843d08000c08a100004000c414503030400d0300c040854404541c00700305a580c84c4291103001080c051585140d19200f80d00d04d5041c9000070101c0307001241880c1402000d44c0e10a014001901aa80841c10340d60780040c050259041216000001003000d41e04000716040c070171000f0355911101c0c80440d040d4850fa100610120307220390402d1004100b002c405640f10f584491115807e070445102d1410035102c1d420448880480e001c05031421203030161a0442907035a11b858070000b40c07070503050f564445135039040c0c200c0044c1c2d11510540c03143c0c2007201c06135840f00442a1040c4110400e900300254184142d65440c1d81000810030015074540305440125054440000154540c060840c40c045075005400707010403903540540c004001d4240848080c40000d03400803028031400b000d07020701c008045071099124048101c0360002c150f1140302c0e103480300494810b1001050a902038a0200c60810780000600c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 178217553 1250 178216303 178216327
    0x10e1504021302041206050c07060204030b09150c0f16050a1b0e0c0712090504053d1512061212030507050319110a09170c1e060d06030602 61
    0x20403028000342011032038103080a00150710517101c0f120041c0301c82d403180300042040058030140eaa030355510440664179240c513850b1940d003000f0b040310510420320078203405641104e40300c031002e070294091414440c5440f000780e0218845a2210001d21708500d0706a81100004004102303200410b40924046240ea2005440c0ca4820b500d040d403111361100210424070402040c503c040f5540c00b54020b42500d0945e4001000792a44062980074991040c13405080140001001054500e210400d80d04c0038420070740000403606051440c1008544e411101e90140031424240740448500552400c2010190740c821144005807001e076004040600c1d00398200808009184802d002070701218202403080d49084030009025020080c515259806042c114410048580d070015442d00c3c0c00c1d10510f90784802160f00940441820722030203031142c00300200c035484040003040e40303c15900c00a103c034542d03680300307907100514124000c801e9900000811100b030a0b00654070441c4000c520071040036031541313019501 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 178218803 1250 178217553 178217569
    0x20601060201020703090504090f0f03020c0f0105030f041722030c06020307111909020309010e0d0809030702060703030204051009030605010902070c03020d03030b060a050c060c0702030d0e0102010e150402 90
    0x3181040da80144004000250040070030416100d054400256441803810002d560003401c901c05042c001569000700b01f80350780462041c0c00d1400030f99010001500200c01110300b403100716540385082e503014010a00050130100c83d441a1b41c012822139043c590149100480c4bc0c852010080f100e1842c4c150030400c10004100b01c00c001d140c64000b843c1040056180e041804ca0910900e138884c00c040c0710f02c802c00240b0210484080c00a0350300441d202c1c900380c1207090013052005203070010f520400140c58102803040d070f40c00b40b184a00d203000c0c2d402c00300b16a003840015080b00c40110207150f002c1c400400c854880244a5594400303075510007901d03900d5400c002040f00e0060300130017041401005404081659080c050f01240c1c3d066800f80030f00e030140c1c20100d0091205002e101d030300000002c0d03d103c82da80c0c010094030481312020161074040d2200d400d010010300c500f4900a4058200800354810b860081010140301c10741030001244016500b0b44546c14000701d0940703005c0d2142058248420350400e0a1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 178220053 1250 178218803 178218809
    0x702010b180c0a0f050d1107020a08120d020306010e120606100201050601050f0f0d02030414011515050d0605090711010e07060c1e0204090b04020112420312020601 72
    0x50300d403205041600720902c4620038070b8101014000070181ca68003640c400c1302100c50074200241c0800c114082c03016441d80395030002c40e0031b078419440100041980c0030041203e910b007103440c00c1d4143c40d000c0401103c03c0070b5040100400d06200301e07522091543d803501091952040c2c04440601307603600d480d10410580d1181d1707200c40021a0314000802c602a6004022103c1c807039a02a9115100d11200310032042034410382007904241400401840b04004000700d203540c0560035440217100c0080031400b0100000c54612420b100710b8100350388012045e01035030041011013014080860480d80f1500440d41031036003031700c11400041210194400084080c414aa0441c00740c1002d0311280380340c0307180200958021f9801500040903410711a10901030000510000d581c054000d0040c11818201120142c10403142039020410004071103c2c0c010840c402c90002c5000c1c62001c1c603070706500303110180003038461411804021100e20702429040c90313440380d0000198803498a81028640809009082c8041a4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 178221303 1250 178220053 178220089
    0x115050c07090222060f0509040f060b1e090306040209040609020315060307050901051f110a0f1709090408031b0d15050108190213090f05010807050118030b18060702010b 75
    0x101003840717215031103420200c00ba2168035000d629121034400003030041141510203c0030710305d080d00001d1b409050001529110b48002c3c660004107100810000180c403644041650542004002400503c0c0c041e01b159045405031200081480c0a0b6001c607191540d1001c180800b208038004010281c6030410840020b44000e50301e0700e0341c5514107404a00c40b80880f1201e121583c0c0a0000c010400c0d22a203860b001c0c6a08017012500f81c3d00e414103200380d11940440301540d900a800b41202c0d68040182d007280c0500d18068441c94443c1c0c0d4507160a01d6035003000d00088840c1030f01c0012126241e058401500c1d41d900724400000e160900700110300d0044601768441410300c09100e003000542d170120542100d240f0028000035070344106007911310030102500e800c413062503440d0200c0800d641907107500481c142c50000048035945521000152002400b000d62541d0705400d1007800e2000842d10801543c21500c8900c0003850785d600e407030000d0700b4584104c40240050395500d070a50749a10744112900e400d00c481d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 178222553 1250 178221303 178221367
    0x10905060d020105070605040602070c0303050a02010f06080c010e0a091103060418051002130b0f130f080a0212070b0708120105012d0c05030406111c02060115050c070902 75
    0x10340e00180c1345001303030300001d00401d07a9030000900780715064046641c4541d1000030b501c58142c90349809030a5421a00d4520010341ca0b01101800d00c1c1024440c0c2001e9413100b00007040f0040c0780718011a1310450100803e9045510301600280041580c0500302070030000340a01f41d00c03031804006101c104c5d40202008100702c43c8600d412800b098020401034600540d0035400b5998029115640ac2c0d41542c583c403510350301c04001103010024800b040544134111103020507084440d503554481100d82d0060050035002d8020b07041c001d006241051150130a01948020b072840a551403520b00307e1038000c1c50040d82c2440b800150b5030300c0e020a1003003040c09408242011942560880c420803001240070b85409020700c4030603142c040890240c000840e0070b592181c1241d90b12500d039000248803800e1845081100d02c02c5141c2030362041404211856440704c0eaa0080078168a03080c03042200841d20410f01d81401400c01c00420304481c1030201401a00d22850050b03524290844002d038110150205c00040301d0301 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 178223803 1250 178222553 178222579
    0x6121802010e0d060204030803190c03060806070f02120f0903071a1602181501090503120a03021c0204060903120503090a06200c0109020a0f03050d03270b01090506 72
    0x2c00c10100c10041e054441c1c00c4101e801c2d290030402403040303410203880d10101204014100464240f5503081030321040041c807420344841c005905540c0b040c002d000702c903009600003410282c403410a141c8859514412656811010040009240d000a540c074840c2d0748002402c06641c00c0c00c002000042c502240cad964050300c5007034101c2c0e2840c05004080b0007416040210101550f85403020f25209989140000f8a1820706001c4400203518420700d080c00b144801c10001000c0c80c001c1a0070180000d081c03c0c0c649030540c801012002540049119400459960f00801110419102600190103107841c0c1d44a018114108214000c034617200c121700b04001001003040e68280400ea102600d50f0010004c04c4400300303a110400104031803c40054003010100f50a407480005400040c00d140c000e60700c01b01290b8540100030030803507181c000600036500c03003035020382410300c2548004e041004441c0d814041114844038020b0100035200150350300b142540040c48410114814950444000c45505a141c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 178225053 1250 178223803 178223807
    0x6120f042303030112150c030509010f0c2106082a06090315060105041d01091d06011a091f09060318030c0c03050114040312060f0b0a03150612180201 66
    0x8014090030481e03003401004a81004042000c00b4010746d00e08605225101406000030020001182c1c01d0940d51300303120705940140d45a04c202c2440d1403807566200300d4840202c5031142c190211144e910300c4107607071703040010b41e0b400300348040e1003d0078480c01c9000c000e40c000f01d80d0444040207080050301c112010003404c10650340c005940e980c10b24800c0c4000890b40e45860059505000700d43c05045c80c40c01d001f011f41400d1b0001e00f03583d41030344c5c0844020042c0c4100e002c40390701c50000c0c50b01703000015404400140130598188401d044c182d440440700900c4c18000d50b020944142851510781c10703141c07424014480b0182c1007030381344010701003030310b8108092030840d802e25402018605000d401d024100c00c1e000240410b40720f40101a541010003884440c03000010740ca06131f88201d40c1940010f48103024104110a64021030088030340300c0320340d03c800e9400e04009140d0b81d88000070079030074586d0740e00352189a0700300c1e40d8084000b0075058407a0f03000354900800b44000d80e501300380820381e54094204c411005030f0f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 178226303 1250 178225053 178225057
    0xa03020f0c0916020f0f0717070302060702120304150302030105090906100b160c060819020408072102040f1b0306031703090a05060f01170a031d06120f042303 70
    0x128403403c8841d0240d2400a040c2e00f4917409201c41d640a001d5620380103c4000c000800c1c1d4101c680d0324003268410200329240030740716421030000071362000c1c003008100054902880088249416042900d14050b44d40d445011020f240e1340303101000c20b40200040080345400c603034059104401001a00462404940948000c40716003c2d81c0031411002c40c0d100d00401e03051a80001301644104041c0340c09496031000b420407841290a41182d8070418420341d08001a8001c0c0c2c0c040350742140040c5031080c10049070301c0b80302600707020451848148100d000003603511400f403612918006000046d00004941da03649240780140491300a25092130002c0002581108031641c261408103402501c03a12515061424940004006046403040c5020f000040c142d0062981c103d550000d480489804000d01c441c0d06c2e00e041201c06000b04d401c80291402c401640342e2040208135009155510385081c1c40342010010000782d1b0318110301c425010400c000c114055103c1d030807040716411b411030303008140b001e11943d078 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 178227553 1250 178226303 178226311
    0x9060905060f10170112051e2107021305090d03090f120c02030604030203090102060622051017070509070c0b04030c030302120a0506040621060e07170a03020f0c09 72
    0x80c207078640d54401840c4180c82c1c041e040b090381c40700e014032942e4406d03011a41940c41c1d030b01902c640c041d40c0341201c201c0e261044400c003220f00900c0036089070050084070720014103000181d007068001c1040718000503a100520b10030100784048000815060181c2c581d854203006048480c02d05290400360710100ba100104205810750191030812813445a4000700d0f140041c454000f5014420402403208158021020780b008501c281d080380d0040e81c1d00d400300152519034a94041e030449492101d4405800c070703078100d164040f80c2031841200040e565803000c280c141c405030044440d504007030740911041c9492342d0515003006051030003a824203142d856990344084040e00c000c0070700c01c10040000c01c241c00303501a549001a060541d46c2c062800c805864043c0c401280c0311b80c420b0380b62100200350510141e510140e81c2c1911034076081c03040e0f01541c645000b1310981c41780c13143c02d201c1e132140010316000c81904048151400000f03030032030442c14a0041d18010310f920300c4203040d0b004052078590b00d85500019a40c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 178228803 1250 178227553 178227559
    0x140a0b01090902090a15050d1103010b030408031b04090b13021213060b03030403060902030f15010b0a09030204050106050714030702030d0c11030f07150816030902190e0109060905060f 81
    0xe50003c03813000074500c1050740e001989204140396880d520303179000030103000041c28490f401e21000d03200c0040c1c81c3d03c502c024010006940c00c2403022a0111b400700001d10361080c1209243c0303c612652090005150f08942e1014924603110601c0640c6400c003484501106807800701c0a6027024807a0f40702504004009014508511010b904881808075681003428840406800d5a42d50707601da044c0031014184608041e8068881c211148040610001d00412a100084e840c1c0c1456402e00a0f800e0850707000d0290b03102000042c11002c0301503507861250318001c1c103c0f0385035241ea0b04014500300800550b5204504226002484a03801688003c90551002040340c505081480c500d494500d0841d42850b141e40e03010300c03d00c400210000300c0080d04605444510700d0743e40c146282c04008803150b25080300d5840b5480000044000240e019030044480c41d8802040360f030a054402040c4034000040e0b07032182d0071a446580040110403101e01c18000030701041e800600444c030f401400704048000075221140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 178230053 1250 178228803 178228807
    0x1061206150f23031006020d020703020f0612010e010503011104030c050103020a0c1a07110a03090e0405150703050a1118090402041508010b03100b03150a06090e01140a0b01090902 79
    0x4882c0d01c58400003003100020041107542505003c40086160002c5440c0c0c5803440c000b1802068080c00010020402c502a600800e041410350b030a00c01c0c0707a070340c4071303511908243c1c140301c0380209103048002640a00000c001403011985013204260039128030040d0403403019410882030005c01c10b49650714003517178800e003400750350740100403030468014091010152220050880c09010308401120540c014070096480715011944016002d8441400810090201b003603401c0802004d04500b8080303500601071b00645903014401c40c4003031050081110314000080e5181c1c00c204104516100d01c03d03c08260f8072038203007010411001c00d82c240050010192080040340c001500715550754101c0c40040454401c0d051169998080a80c0a090144007480c0720340101c400c49110160648210715170008028001c2a40a83d80c0d8018054120080c0111b01c005840c1c5001103038200e4540100208644020000600c0201501388000ba074840501000c8485003854202040c030f80e80030350003000340c4011318001a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 178231303 1250 178230053 178230077
    0x705030c040302150a1202040f0612091b0608011a090f0a09020c101d030a0f020f0a030e120105060a0b2b06031401020702060706020a0e090f0106120615 67
    0x30300300380541d600003540241c0444085281c104070a0207081001190344460325000300300c0303c01409a0245010b80c20a40c211510200f102c64440c20342405115000400011086620b4407908009104109003041041036540e0400c602c03a40122944c2c0113045545600310100412450f8000c40e101d059403840c801d02c0d0740492140d682c0d0310280361a001f4212408115601c0100d414103540ba40d00510440d0300403071078000c50342e0180082118411041810001a42c0303082c20010050b65018901d103903080452203051442400b00d20304106800d8100c0c000e0312102980c51032a01007018400e822144119164106014401030b81c40700b80401058400d83d050458658032186809403004139a40c214546a1000b0a260388100a450f440403040c1c03401003d0301084000e41410440c280d100da400000e400c05020401c501c00705003940c0c041c02660055241c0841ca00154500140380403009450500c1410707420b000400803d500224520041e800e944001d202180c90300a4142803189415110024400032003142 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 178232553 1250 178231303 178231321
    0xc130507020f0106080105090d0914040c110303010f0e06120a030e030a08030c09031203010e06220c17011502100c030b1c02010914090a091401090506060306060d050303070503 77
    0x4450b00e2051034000c01c003083c2d6030400140a0300058907080300724040c4d81804072603c0e1241d210300c000d4903034402038110744103244c5040c04020441021100d080000300700b9000201402400114000d05080035180e01e03440c1800e034040c00107007024224602c2507002000030400c0400220360084481d405003854000701c0705620200f820030000c0720b00144071a05c00000c0052018064014001d49041a000c4811b4841708410081d0710380310a000b151551107078000024440c2ca000080128411031040c0400041c03681c1c241c840054801130112207010543c41c901000c52081138500f03060042100380342c0c107940c04400c0440607455034861603401c80c205440f58502c0901c41e00a411003c5c00c81c20140907000d82600942c3c09514000860f501240040c800c041c0000303140c903048800c05250780d401011000242c40750750200340100f0301c10008484408810903254050b14081c40380000144c02000504144d1030243d0030981062401815284103007540314101d4041480003050701d500c8285070038040c1c0d4a880303103600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 178233803 1250 178232553 178232563
    0x4170c0d0b130201030e0d0309050c010918110f07030e09060a050d0f140607050a0201060e0c0a030e07030507060302041403030406050304020d141219090305030928080319020c13050702 81
    0x700102d54483d802e4407a400c90703030589c0054209030041064800b2079034424011500c0d0703141c0c0d11030880d07248559960408070005581c491015002044140c1d4640040740204c129250403420040d404603031240c0c1c0181e154101000d0181d0310003001c40d000e98949082c00700003510f00c00f41c008040c00c800c103038003145020415513800341c080e907018200841d8440e2030310003401403465000894101c010f5003005000203a0b207002503601070046640c2c000480c200000151308600901c0b64100406d5244140703803001020490901c00400902056500982d07901d040001c078100c0f5a5001c00b00030f000303500400007000101d40c45800c0d6500541d0407a1019140da503142046000315090b81c0d80c00c2045e002d40311020f864003000c5402014034031024061006020010003059907513034118400544250000c0001d0469842d203c1002546074981c0c25002c480d90001e500041508503058010f005190b0000404800041c010152419041c2903480180f5161009030041900c04031002e50101c42c1c141c46174040303810b55000340700d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 178235053 1250 178233803 178233821
    0x90c0807080309030f01090201020d0e06221406070b07031e020a0203070309080a0c060809010e0a0c17030304080f181c0b072303060103090804170c0d0b13020103 71
    0x46a50181c0c41e2011151640d12006903d03109201d00a4400d0032404103016440303501d5016006000c1038840603030f00b82c07415034507200700b80ea0061040042095007011030700c84851170200090003045150403d02e90720301007071444810510919090190708006403d612145030700520302d242c04144000c031031400d140030020503840303181054008a004504650300002404005000340d6565812030394891a060f1510031b80072001e401c0503109030090190f10f000701c0c17265070800045000000c89280b20a1340c0c80c01d0501e40182220f0741c006070131701000014440001458484000f8002d50b1440c2026503800b02688186840f1002c0c001c40814006061002c800d42d40d03a086a01400c1d00cbc403002c10b24001d61007143c441c0102200c281c20490080703021036119840e8080d501c0d840168055141d90340321010141e90700010409810075480d0080f540008110b08003510092030307001800e4211503000582a41028403101d40c65004500f1020030102107411018641e40000c9400080aaa40203500040b0040d0001c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 178236303 1250 178235053 178235069
    0x20c0c09040b0406050a0606020d080916060c0b011508040f06061a07060c03051302010c110303120712090807020607032003090f06090315130c150f0e01050d090c 71
    0x42000303020342c00a501c3d110300e00c02c3d241004142d640c00d041c1804ca6040c0e0042c40b00503407064184120880c000c2106541250324a012908024011200c1074200c403125000f2200141c03110110300d04101c001d01c0300b6405407094034800704604880e5075008104c0c90700200050b01d503403d02241c41040c05255072001001e0801000c0c3c0d807000624151007650795510080007210050310b040c0507501e00390311900c54980242c08894086842c0d00c002c1c1c0044400500e070784010f07200340c184001e5050307840c0d604000401e010340301004941c8262406400c0a0300b0070548036102c0e141c0d981484c890400081900c001c4498050b41221200d0b104e000c94181111103440000c014051843c00c12a05000010000060850318800302e5401844401208c18000e540c0103110310241c1640c4103240c075940010201d949070380d0040d03182c005900c0d01c07034554481000203522940b20402e040e0702c140ba01e002445c0d210790307548006411802e007901816150b0340001e2043c41040400c0c08216940c22806003000311108111000386841 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 178237410 1107 178236303 178236319
    0xd0e06010f23061c02090d0f2001020a0321050405012018060703021c05071a040b040602090a1205070905060a080601030f080d0c030606081315020c0c 66
    0x5101a2801c100e400f0300c0a01c0d610786951112247c0c190090b000e84c903180016050082804a10320365015a00b64121070305456a600001c0c0c05600c1a4103150141c2c5030070b0010809021407034607041640505003041c00b070109209054000206103202a1f003404103480d9010075503071444c80b402540c0741c820620a0307a03110541c54401c010703040d028000e0060f201101411030709900180280c2d0491000f0420105084091110340717488684130103072540122249041c1502d4041030458018402031405c4d8000a011440b500c60140b030000500c00c107240c0385201a0f80340313007468490a0500841c0303411490103001801c2460700408245c115008540500000d9080d0b440d0319002240405003613600300020030200f84110001d11400228040365076001402c1410300e00004d01c000340262170150040d18548035034010a035500403001c1c0d101c0d00c8240050340e510381e9552440c1008241c001c03496101e902 = true := by decide +kernel

theorem cover : BRFrame.Cov 178057553 178237410 := by
  have h0 := BRFrame.cov_init 178057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 178057553 ≤ n) (h2 : n < 178237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
