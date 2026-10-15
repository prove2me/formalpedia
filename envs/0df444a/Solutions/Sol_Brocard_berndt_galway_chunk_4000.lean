-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4000
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:17:34.761786+00:00
-- url     : https://prove2.me/submissions/338ba5bf-c5ba-4f36-af84-b9d91cf6ac76

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 719244604 ≤ n < 719424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 719245854 1250 719244604 719244629
    0xc0607140604110f1e0103020901050d05040f02180f0402061606050709030c05061204140a1b0f0506180108090c0409050304090f0908040e1b0c0606030706030b0d020f0604 75
    0x3c120000700008403800084030042680d1410741c003080980501202d100340500992404070900c0d5010350003a0007145014101036042004500c1c0060450320111001c1d40d2040501444006500f002c039443d42c8030f0b42180b10700c0402d6150050b0301110f00c000181c40240681800100312403d2030b282c2d15017840096000609202c0d42c01c0840b070050025015000503034142078904000211352810b90225081940d0712415840181e80f591600705072aa014041c0424501441110000046150480d02b0071140d4000d1040300a40c205440390001c0d0341d19800a40c00780304100074450615a01038260540100c0c04d00c0c01201503901d91203400e040070303415240c0a0304641401001810401c0102c09401a5a1020310402c420071000e04401c059469000014091484c10401440030303201402d429540055a8141480101d406180103540396101001304801ba80040d010b105440c03509000142c01800c1c0c500e01442208e16007400035801050094000744592025221502e06465000580300107110702c11804c0f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 719247104 1250 719245854 719245861
    0xa0311040806040c0b1e0708070503041d0f0112121403090d032301051002030c03072109050a060f02010b060d0c260f0c1605011505120c06071406 64
    0x102d66855050b6001c481e244207200d404503019450200751616042c3c0281d540005465100011040780c0c0a20811b440f1100200142130228070200020401040f04030340c6000b9081517a907000c0405400500b640100316282801007040348503800a0304860f0340c1100078034220031440c503010b0340c04018000e080026001d02204100c8001c001081c86402003804d40c40601c1444905900343c00e803001228418004281d034000140030324200070100c4401000917004a03450914102030a40c03650308900c00851307001c030a80c0c0e5011360105022440c0710090020707003400c5440a04000010701d080c2080c0c0206010854200d0512490078402d402840040e40081c100ca90390b140701003041360103400d024010300c000c1a000d0341110340c1c2c0200389041d0440401e00c20313420f14031a1910850b070440d0007800780c21b10b01c0161007445409800e2882d01e1005c1d84283c81000000340c0208a000043c02140b2541c0c8800d1184400d900c00140844011030ba14012004c220b0f500c680d5072035503103002100e604021155180912561040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 719248354 1250 719247104 719247119
    0x5090a1a0106030f150306230a0506130e0a022701090504170a020c060304152307050c0a021011030f12160203090904060209030f010209040c0f140a031104 68
    0x5140c1680c005a0f41440120142c08144e01511442c03010300700740480229007003000c901d40740c3c40300041d96032045c040d54030300f0504c50740c40b03081c6082a103d03864075035510000e0040c18a4a2000e003070700b80d034420600f0300503144440700e0152a44000400039000e01b02e50a40080b11080508c5550581002404480020f5840c0c180740402804120f85c02ca07800000b4400d80d0140c610341c803003500c071400403981c01080518684010b0107044c0c4c001a204440c2500d0306103034504840541e0044245950403003407420030000440c5c0d840b88003104094045d00038400c00300b1540c3c0031580041441c8440e00c2d0103403056030812403031101c1100d0040d000e84407511240008600741c54540c3c5890005c10300e800c40421101005e8541602e910700c0c40c01190181009a8420402c043c0181040008181c0c4540141d00050500008401180c240b0b00c0741c2200d81d40a950004901c9010300e0305c1e124030300801e81c0c286089544800c1d400800f43c40c5d03090a200188030004007003031128069100703402122540e0340083d84107486596900784c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 719249604 1250 719248354 719248403
    0x50604060305040b18030304060c09050405040f0c29090a150809010608071224020a03060515040510080405012c1e0304050613030507031214190305090a 67
    0xb8100c89131848000070407a03191760000d000d0301e0000700001851460325250f031040c001b440b07840a8081440688040000d071030b560b070704c00c07584a40c0c028000309a000301a8540609132560680001c3ea82030b14a1009070403000301a401c0d451030318050b641b1190b89142c5400020b03000da0b071540c044400140300c41d03981c410480e40308a00d540aa200d100003804181d0b00d44c00e11030348890050040004071105491303d003000c5030240c036a5070410010104d030b0088030f03c405c282d4901070340c0c0514a9000881d448aa0070441400c1c80d5441c1400500421606802c160400300040d4040080510350300030015284c0102d404e2200c00c2d400709013034610ba40410030440b1840501c10b0351080e40e005078816140641d40408817103070034042c41d4918040398a8003551409007041c04015050b0170110100010b10740700407001c80010b60401c45100618014082c841400220300c0004040e17010190301151840f4040c4002d0030001180702101d8400b00b40c906003c5200e0b9103011540e0b2403c5041c100240c00800c540c0700781c09060f17201c0c28 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 719250854 1250 719249604 719249611
    0x6040f0b041511102c0d0905010203030933011d0a090c09110c060108060a050106020a050307060902010302190804141b060a020307142407050703030510050604060305 73
    0x14003040541c0d849007410340300404280b0a0b1005600608041c4ca0180c0140c2d10a50f409000203069041d904807000307044040c07001025a0050075070000b070600940340e0704030103210010082403004518620b842d541d065102d00d0401c3e42d50310706880c15002412a54401d8a40c0105002c810311030726600e6940c6d03032400450340b0514100c010442c0011021418400481c0600c0c0c1d82c1c950000b0b00010314904d0015880010164001c281c000b41005000901001405015407030003050040e0090919041c0b81c1041c40455406a001c00c06650280034041c0020708040107071170009400c4280041e40e0500b600058021f44155110400c2181c0c00b44207004990707821841c818042c82c003c0786181200e913200484d1b00d69568003954903441507065040350700590310b003400042c0075071101481520b0412000769500203680124688495440d048035110111000380490511000c01320085102d10b0341c2004400900503200700da002804040c0c5400000d403029590014200c0101030242080b07079241d0f551003004009210a4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 719252104 1250 719250854 719250869
    0x1403120403020d080f0708040f020f06070b0103020906031f1e0e030c1b130209191212180e0a090507060210060b0708090108070e30061b0906040f0b04 66
    0x8404505c0b07200c050201d01e0b124101c0764035198a9a02e80c1d0b10f50202070010000201d03845048041d4050558440001500e8000e1280e9001cac42503505601c104408180000c01030381c00396200c1c1400031850500c4105000f100758504400180741010304a4240e0001c43d041c0b6060089424820712061043c8000001d040e82c070401e5066031000c949251072a440642c20b411000d90100c00c3c20300310a0b40402036401013010382801011584800034094005403400e85070742c004c1c040c1c40b910500340c41c24040c4190020100405928120a082d88421030190b059007440c0294591040240e0020301c50000950044105c1c40c3c1007011070301425603411009540c0c1d8181310042c2045800e2050003d0070b0004042a561040d42c0840041d0410100100458021400815038810040c0c44c100c00821600c410035200405a4401060110b2508000303416540e49003035a0b000301c2d664418810030420006e02c0c00c80c04e202e10f2180710125582d81e07244001900350700994000000c00c1c0040c4100251240c6d0360002402219040e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 719253354 1250 719252104 719252117
    0x315031903020d0207080d0e03070e040507081209060a0305091906050114041a0d1b03030203030103120f021509120d061a130504090807150e01060812071403120403020d 74
    0x500004a8445406106d4018580e01601c070050800b802141e007480c00c2e5202034101e42502c0c0e9100c00d0100c8044040d42d0681303d41e008403034180000c5605103c240e001027280c1603102e03d030203000004650640f0070502d81c0c50806507201c0108142500900103049074906c0c401682202d40894101113000f00028841e00303c00e20010a601c5145042c01d000300c0a8002e2608010034004c8005018410b02a25000088505041403880e0804070801c0d40780d040d02660081c1c1c0155200c0d81149081100004040c00041c18040d40c10702d100e603410303400207901000140421800034582c45410340c283c90001078016a8148220101b028515500300780e2050b801c41c0c0e40c05114001e501c8030604c08400900c1601c82d10142e1107142c600034000c0c0c2c10309800c0050840c2c0310b9036404d46024031584a01c403d0301080314611009035185e1300303160f9840c2024000d41014040d45406004004000303920003070706110b60740004007140707038581075820000001c0c019105121007103805942c2900d003902d030007500c4424142c440404501c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 719254604 1250 719253354 719253373
    0x307061a1008040803070908070e06030706030506030c121024050a230a091b03110310030212210409050c0412032d210203090d05031503190302 63
    0x1407002a01c50380111945908072541c55a444641c0c550348000c080c0b10512510301e800180030b160400c1b8110080c01c0e0315084400c5800d20f1002c243c10641a40c0c010420181440e0602082c2d0783d02044040b209541195201d48042c1600d080506101000d5880701c02d0524264048081e00c101440520161100d0303004e10800c40e4891081007103078480f9001c0d050119a4981c5410700003a800901d43c0403101006041d032003096079544201c0142c62800020f00504004960404030054142c010b503060f0301d0b402c1030081c0c158500b4500c0b01c60100d0183c40701a03c2220050004801c803602030141001e4504241010781c80c121040c00a814658081c4c031401c2d20302e41c070b40341c0004c6644002e00207a40c192101500d03d030343e07107101c0e0740c400321504801d2170000c4101e0000c085070b26201142c03440c071014404405807111302101e071501504006451241c1000514103004008110042e07030046403865440d01d83c1d00f8416125201c0c02c980101d80c0c01001d07000758040c442c00006504100c04005081000d501c03a40c210386c01810b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 719255854 1250 719254604 719254609
    0x608010504050f0f040c0306050709060224060402070602041206052706010b0d1b180603060308040b0f07050109060b0a0504150501050c0c0a0f060908060709030f03110307061a 77
    0x200200e43c90304660158001281040301084510b540060040d50074906403074803600d65a0480d0341c01d8031808081048540c0400210360180454180c0f40880400c408010003259a080d0207000020143e6204130b0f800202c14041003144d5054402408070900c135510001e982e0f103401c0005100541d4510820403048030700c0684140220810001044e10102030250350340303445503192590308248070303c0700c3c025140c541c002e80300966504001181c0c803181c2c1d01e0b0451817040340300c0c801118520f60401c104160500005201181c0c52004550444590843c016074501c11001804030f01c2c090f4640042095080009040c02d000341504015240c400880c3c0c103080c032036a40c004010880302c900b4610051281420410000c0c0d41c06a0068508006100f0554405000c0c0710002510032040f9080b0b42034a9002c2078080c0442e03640711342c1500203020060024216030828840c0a0700c4201e040c84000c0010f00c10041071000c00d80b04485007400b0920100440b611181c40745002c03000b078407100c0200d0401000406264010b032 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 719257104 1250 719255854 719255861
    0xd14010f0501030f0912230a140a0c0b011413020307081303020708011508060c09150c0c0d0b0610050a0c081e0f04030c081b06220f0608010504 63
    0x224000303461164824a031000550103801d41c411030144103a900c05c3c009021600104507804014902d680f004018000c1c001d0b0340e00341e2064510a01074401c0144800c50a40740c000095641e0f02d0759807401c2c02d440f40c1000301e046800056408009180d44059400020b40e454944280c0307008110840380b0007000550a01d400302280002c450820019840c0c00120f0406982c40d040c0b00c80d454002e03c10303903000f41d8a619180303007540e00400800925802c841000c1150303210a02020f5000704440c5429460550900001807040070403003088030640000040040d0084010005444400d202030199810b0a540e410601590607040700e8150142100041780812984500b08540e00c0e800c0a84420721411741c0d41c0c030340b02100d401681c13860410b5412038002030560480b030300103800c500500c40d8615a5643c11840c102010301c00980c408010f91f4400300c5170f0220f00d8040003940516160079035001e500c9041000c00351010884880c009841d41840c3d0001180609004100ca0300355043ca40b246107031a640c0300f0900c8101c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 719258354 1250 719257104 719257109
    0x1180807030b090105091203010b090a081915050106021f0f0c0c060e0a03050406051605070b19030b0d02010f030209040f3c090302030d110a1724060c0f01020d1401 72
    0x780401023005220810001c00500040d01000d8440a015038598144030300c1c083c0816001011b034400c000303042c402c01c04600c00580e51918000018006540351000182d914041452484003038074000b210060915031660110a401c16809800d105415015201a0100801240944025080c032003e0301080c1e80020750580380729803607034450780b07890328140341100d05411651400e82e060003c84007420108800b04503c0c0058410800d545079541c002c585c07560b00444c0095078810500d400e18a10400e03541e15091010203180d02030800348048040749004800030311548180651003458100c014940d10110b90080b4040310490707801400c4115100c03607403502070030020060071032003ca8a003001c20425564000c10280c0d8441d0040340d05004052011000391000b8815041a03200d002c2500c890650b40807444100100303403041c40811500300356050703030b11460350078411a021500c8003c06180e03540b503e0080f2440342c482075095800300481c1805032400f0b9448108502e400328100254812103002d01c2013540d04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 719259604 1250 719258354 719258383
    0x604030801061e170712060305030d15060504050f06040e070c121b0f0203030918090c040b01080a240605040e0105030105060616030c0b011410030b0f01180807030b09010509 76
    0x2040700020051600304c0500800e4001088a041800f048050b080d0281c40007840c4104041c51712030022a0f000011120701503c2d4585000300d5000400c1515040360898042d60000c1d60012048500e01b4013090440c0314640c40202072050718020403483c241d1209210307141c07610401c40d201d1084105802121100b040d81d020841a070011181e80000404c2d00ec5002e000710700c058180c070b08108445000800e1149001a000140b8072034500f004040c1c4c900303101c043c0b0011011501040b64503c1d02000900188000b4030030322702d0f240d84140069400d5a43e1040c00203a84051074034103c015100da80c002c1c4903807c540724580462601c0800072030740c0c2c501802118458070000d44403505003252402c2a90b000041c00d2003d800340281c480304400480c51900030180030b800d420500303504c001001c900f4004540c2c0d1701c02c08101090329000c1000b11076660003100301e00103c0246020003071406099404c1c1c0b0010090703800315032140f18800c800010001012942c0f4801c2c401140200003d580c7d0b52503080d00c8402c4480c1176007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 719260854 1250 719259604 719259617
    0x2130f0c030545030a1202040b030f13120f02011401081f0605030d0f020f01050609010b0703140706090507080604020d1220030d06240c0f050604030801061e 69
    0x26030b00c40b00801c555150040729400a03114a10fa4070402c54030f030301002210080f5080001d988000f9600031a101901e00c0d691002146001d10f08501c0d03401500001e02080c2d060803025022401c500024106140070a4112008101e411071310701c2c010301140c0031406800c2c099424446038940001e07030545154102c0da000b50141540c0a00041803505200c4442010401c86a8660012503941c904000040640c0745540b103071010001010800780c42d200301c0121182040e814281007007821b480344c41282d03044944c60303c0340c0c94a070011440c0545a4a51040048211901c003103507000c00d122031908201c8a6500480507a00010f44035904c01e9142c0c4070450340690022001c1400000050344106403a8011a640c80c004908000841c4803020860444440c0c990366800440c0c0c0146c0c000c82d901c100801805120b4181c070610700c1405610307048201d11883d10080c03010a07000b607000d000103a965441070030b5011043e140145424a400b9080403000c0c0030310340c0012142101040142d0b101c0005124407803090f2181e2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 719262104 1250 719260854 719260891
    0xb06040c0c0f0302060106110609072304021809130302030f031005030a0f05010e210f07171312151116150e030910050d060302130f0c0305 61
    0x5000d24030154000c00012040150114441c0700c1000103251003a4080d20184d450200001c05543c0c0300000544560030550a1142410300005d44500b00c0310109620312440038440c1d000144820449105508130340000f41300e010314190307040010f401c1c1d07070111468030349505e45424040e4910701c1103c000340940e00c00c001902d140c00020703010b540d200d4900c588828a01d900c50780400d04000000e03404481e16188056000c1c200882070081108651913a002840c4685044180500c960845c501a90041100003000d8601031807090481d80e040d600407024248903103441c0310030004c0e54400c44800f0581d080008000c91100060680e00c2d49454014040517840c080100030040101128140d440f1915410000c82c0d003209403502c60186441d000d058a03080c001d607020600710076a00c81982c49030b11600100402c020950320701800c038401c40010301d043c0362600e6020103404014481c1e9040a90f0000c160404003010303075441c1c2c0003241c141241d240305005040e64640103800f603d1003030300d4000410080040300c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 719263354 1250 719262104 719262109
    0xe0105031603021c080d110703120b0105040e0a0605030d020318010c0f140f060901091106030106090303142823030a02160c0801090c23010c1128120b06 67
    0x2810085d001c1c0407130a01c0c0000ba81418411924625501e841012000c0380c001c06154115803c1070a048005030144024842040020417030321841c00b07400302c07160229000c1210408290722401c06000c0c00380031030307036480784655000e5600c1d00149000d401c15060040603041d80d51003100c404003503691080004400840503601c14020030020b000c1c080f518882c3c94121540038008201090190000c01c0000400f4820380c1841c140c2400c04082c1d0500400301000108125544820f100f0300b2240c062400003101800f20b00c1d040c0b068403074030650740c6060003241101d0500c0c80e0380440c00c0742c00841507101d0300301348503243c03030030305020700307140c02104c00040092000550603030903600288101c540c0381c5509911000310303641c0c660203503855030825103560790743e500c0b840100111f8070764000203400c0340003003e000c0d65420100083c0004030002e01a041000c4000402c040200c54040300d6004000200013503a0390203100c00482074a10341040300d0349000892800094607004c03058940520603007200c01c0c2903182d0350b034105 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 719264604 1250 719263354 719263399
    0x19050a0c0204021c15080f0601080c040902180406060f0608060d080c030403020604121112060703110405030303090c010f0e0a090b180406141008190204060f0e010503160302 76
    0x200300202815046603482c040b21380c4250200c002503c180700f0b01c1d2034206600716140c41b5801350720703030400d178000c400600045100041160090324112800318030220184007040801480c04444060100700b101480104104c60700714409440c00c404e07140100942d1510100c800d03180c1514110740043c4c00040c0003021075114401001e040038000122403503e40d82c3d60108041c1d81c400d81c0704621021031a07800390f003007220719004005512002c85513260b119070103280032516824042c0c64001816501c0706200d0025495509807001008020706403038907031038841e80d416207440b42038280a0000f042a00318204203802514007000054010307100031f60184c00e0011680051000d02c070b04035400031058007035450450401c1d060311311441c45a8404a451425007030f07400ea0b2190080e121541c4d03030013145d4090100f1080000c6003900c560b0b00c0c62022800000c580081001091b8582001042c021100000301c2d9000081c6038450482e0b00030307012909040c5075484000d8000c442400029130110385072403841216105483e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 719265854 1250 719264604 719264617
    0xb04020111070b071b0603020301180213050d11010f0203040f0314011815060b0717070f1506080708010e061305010e030307121508030d1e090819050a0c020402 70
    0x20442d02000d072600d022000f0741d0080c04080f00d544038804c403030700ca0b61184000c040f001059981030950565060441c21001c0000030388901c20304d03e602050956040540d2280500108400713480f005508685041c1080e074000802121030101c4e854685506805200004803005c071484044014403140c00c51341c880303903140b019400001c1d0310342d00c62126080382a414094004058403645461003107114107010305c0b0564640e68031003907100409001d6100495000e11140304c0e6100f0851401d0364906e02d5144c0303025a08000b080c0608113991a440c200010840e507401102920600c800f00c60a1a41d5014941c0c00d888412036174464980124000c02e10703840780c068440d0006441a4000302d0b4101d105040795180d1317041129000000780e01c02c00d421407003501504c06c1f80080e120788104c000d03055043c4045583e0300d00c44e5100ea1419903544c1e0120005c891484549030a01044101c801d108240e01c0c5c2c00c2c1004260080005402c0901300850355414a82c010002c645000c0b0f00c0c0e0722800383d00c01d1240c0811001b9004003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 719267104 1250 719265854 719265887
    0x9100c0b0708280b100305040308010608040201020d052209020d0b0303031006080c19050a03061d07140408060f0105030c01022a040f05071206140d080c0a0c03140c0d0b040201 77
    0x544e0302407642e40e1800354191856043d50790004162800342401001b900044e840002030213490001e200150b640450300044400940c00d0455071a503404444d1242c0c00f0410700510046840b512002c6030402064005040800e41c10b4002c2c00b0034008402095200d100a5a00705041594140c0411126003d0180e90340e00040b1850100d0030030303030100405401d1000700e0440c90000794000544064035505441200007070400c180351003001d40020340042c1040e45000d0003910911a4a2a039600b407001707180200c502420001c0e0650b0794a05010300313004102d0b41c0038013507503200c3d0040361022552940300141500c1c1d041e030f075511041c44640700c20240c4040c05100381c6240fa0003940301c000c5903824500d24003480d4040d4000c1d6485c250f030048140320020440e01d958002a4110038821100b00e616501e4180f075035641e54014612035600c1c0302d1000000d05e001d2503003900900100e41c5881c00024000c000e503542e50600501c00c1502d4407007c00204000c08401c544a0003000701605501142c05940704d0a451800742840 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 719268354 1250 719267104 719267111
    0x6030e0327180f07180602030720040f020418020c07120501140906060306060919020f071209030b0109020a0807050702121b03011a060301170309100c0b070828 70
    0xa03050034040024048400403642000041400680c5071710440c2d05505004c4a0707420301003c2d0818600a459200701d62015000c5250080100b03902e103400e0700301004080006004108400c9040c444101070b410910031483d4011403041003034421a00b90007250f42503c1c0440251240c0744c200289045958180c1c242a06c9a6680d0105400c03084140c0903041d0055400800500443c588041054600100107101c1740c040c1c03c1d02c405024501c501c40c0841c8500034103c0c007000da119007644010000d40e0181040141542e941560074000c15500031442e0300540380a0b0650030703a6a0389642150f41644150b4004030000303040940090200c9200304040d04c01d042c4028881071b807014613042c4a6290007590360b8004050b1000600c1c651300d602c3d00b4400d2078140c1074000b0018120095840001d807060105118005500e440a07010404440c801c0c0115500c9450090407402c018903c40b4005001844600341200c240701d0708808031f400c05005001070b0384682100d6111100c18000c1030283c60b0344140507010f081c89180c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 719269604 1250 719268354 719268379
    0x7031401020421021c03050405010c0f020315090712081c0b030105040308061002060906060d031707020a110402130521031204020a15080c070809060c0706030e0327 72
    0x40c43d2040c403031101c0082440e5060303410380b03004104010361010303001c120002000c1c3c800e60000780c1040c1a40d084401c00d00b81500b41101318142114112440c8a0095150103440113034612008016031480c0540c101c07804854100382c454a1202691b040344002a03d0400103100c1c841000e110b21401c0414140e04400c0070529041c80740129081d1941540d04601180080f000c0144d0341c00c0001061480f200c2c113100415107420b008007103544404014040a001c0d00c2d07804080000e0500801c0300c14004030050216407550b1404413802500c1d501c1420048880c0711100c04158041c1c5803d0003607403089000d030800342c6007072032812041060445030168003521b10040c0c0d060303494880320709201a11201007000310900007440c0620402c040d4507000e80021080100e540500482940d000d80013513409202c482c4503995411090030159814001d00304159070000d40003641d06c08840c800b02e0a002114074940702840340034034401c940c079101c7c002d20100e0608481c1424070342c0d5040c0d080132041405034002405100f00ca41 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 719270854 1250 719269604 719269619
    0x1020d02060f0c0405031905010c180e04060b030609010b1c121d0a09021b01020f030106032406020a05060a060605180d0c0e011d0403050702010c111c0b010f050102070314010204 78
    0x41d02c010701800d1203483c0c0001f00e400c1c03101c280507010a115251070442043c21004021900e50380144c01000c1746201e212000400308055540030448800008080f110b0391300c1c00780305e600d001e03200f400312080c042c0c20359456849038610718452040c0710075804501c00103c00f5001504984290406148c40454410340704900000e89070f200201c0c0c090001d0f00405a07039003001c60345404036802c6040c21103120368410409020084030710410b50741510034034038006c2141402c4600b04000040c136246903940461450310000b031810f0300061003901c1944a4800e80380e80c0e90b10400d480d0708840c802d110f640c0c0403420030801010f020301302141521100100414001c880002500c1d800141700c0180c110100c0644040014048280d44c0204050400c1e1031034030100d541d150540e0020514050011700906000e51481200704100b6480d01c1e4030440c5102520b0320005048000c4031498004a4410a0714280000000072620b040c01403d844c0030f540068006090311072031a81ca5030079001c413603e81039178695402d210100e00c01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 719272104 1250 719270854 719270863
    0xa0209010f14060c0607050a14030a0b0f100f050706020f0408010203100b070f06050604200316021506060a0519051e090108010312050f030901051501020d02060f0c040503 75
    0x2064031201d007455042c00d020101c540403002c0d8001900c192401e102107040b90000040b05035000030103242443d2034261904040c6c0315007e40d14102c3c0c000c08000300c100002d0384469070205080c00c40840c3e24044001000c405c0c0000781d20902c201000040f0b80503c00c00d61140148010300700d20340300340001440c3c4400c103802220f103600150021141a500007045c0051000300000c94409803038102d024514107801d81d81c0d4500901c4950310000e2000380c4a500003107030b0340d8407980064a407843d0141158181510041c00b0b0010764400c43e110a143d100300c3ca100000d992000604003420b809000d807007421078543c0c1040160a40041418804110007082400c080e482c20405044009070941c80e0b03039885405031010182c2d0302000200380c9241001c24030401c1c09581e4499070140c1103e410400d04d012001d00c1003400c8600b8461200d1001c04240004213010101805504c4907101e00d00f204001d180d0920044012a02c400125030450f00507404140420003001014160580140e0480d0919140c80d50b01c03030100c0e041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 719273354 1250 719272104 719272109
    0x70b0c0a0c090c080108070e0703051305150621060103020915150424020319020106120c080106080705180907124209021c0b070306091416020a020901 66
    0x40360303d03507801c030151541103c03240b03014164035000350400300c0c01c0224040f40e52500402140800d44c9805c0032074008520460507480c49070b000030945818802d41c81d40280d1000c000d0b100c440c0101a8134001040c81000412081c0040c005080544881c0e40703903400300400c1810142c210110210001c0241d40c0341c1c1d6a180b00c0040c00300151849a4860745045a40110309401c2c00402c02c40119048079205810f501000721032985500c2c8015040d801d2090070101d00600c2944c00030107040e0a082114002c1c0640c0f00030460440d00000003d00c000d6850380c80b840d803a444680b14803604000f640103030347c12100c041002a036001c0048800c03140420344e14520b200c40c00810b0581600e0700c90341045000c01c0c11032644020315400310b07014400500742d004007080c0d4081e280d00c0e480d802d4400d6502c000e118111759a00c0200703600f0001d0501d98901c0c0c6102ca04014600c1c61090783c5c1c906c0464030300a40003a6806080c01425144002120060b030f155403225403e1002030950703450b240450290003e6640142c3e100b4580902 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 719274604 1250 719273354 719273369
    0x60a030f0e0703050607030e19020d03020115090f06050418141204060c030305060d15020a0e06030901023f060301020c010e061005030307050a1e0c060e040c05030405070b0c0a0c 78
    0xd06d0909050240c00c6901c0c040340d103044c0f0f030440882c42d1098441e030a250280e50350b041c0c8003000050440e0a0490041c2440c40051408070491000001c090070590080300b410035040b4410000c40383c2d10390400007100c0705d0b003c165590100c143c841c4400304140c1c40c0544981c1044201340d64145200d0328050015030300c10742040006c07402c2d400180090560603c0703510b51007113082d1200340e031440c3d0700e40311401641c0030102e552049076000900c9840031440350800103c60100600140e8481c2800340000d4040c1d082005030007203504102c655022050144039000d0140080c1d58a02848101ea800309505031041c0204403075059902000f24007032f00702092142c16401404900541381c81e060030b11260004400507030209109610a0100501040d0701050303e100241d4850310300f4031044011001c1d01c681400d0800b01030040000304400188040d00a03046548243c0116420080303606104425115800155001390159001c80018400c4445a1008040e07690030f21045803070306070840e03a503441092803e03041400c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 719275854 1250 719274604 719274613
    0x23010203010f08010903090b030c0717040815252604060b040204061409010e13050a0507031a09040618050c0f060f0d09081e090a090b060a030f0e070305 67
    0xb002420300168005407241030028082081c0544000301203100e0340c050034584110000c0440c020824400c1140d1405500c140d041c400d80d5900c2c02d402c11581c000348103012603402001c610082d01c2202c800c12034410040e038108030608212921217040458000d0b0408428000e00024080340d5000c2c1c6201e043d002c4420012050241c680342c5001e405840c040c45e403040c059801403205000f5150005410a00c4488480d002c50f2140d51050040701d004014504840e0401503a0003a010000119080030744102411082880745480c0c180c0304a003200d07041258405444107401040742c061400484864009006550104101704001103003170002c0b1064404031100e44c00402c0003406401d00c40410100080d048075058241100758100c40d18038814413038481541e59407880c40d02c00304032007542554100100303061400100c000c40c0c2c0c24100b05a202681591140f86240400110304c0441e000c0c1d5000d0071006000c160800944000660280442c1e07500030003025200c00541c9400c1070200400c4000714012002030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 719277104 1250 719275854 719275859
    0x6041a0a1206080304030803100b030405030d0506100507060e010f05070f0e0901120b040309081f1b0f050f040801140106120603121b0b012309040c0506072301020301 73
    0x81c0840c90140d40c00c0404504040c4100821403010064604507608070b0b296a136650b590441c010031000980d00040310b008804024031042c060004094000100940400c02c00394031078404105a00313000400000002e84108000300000d50b1340d4000c1525407103405c0001c1004500a40050305884085481d6000030b0f40c072400c100e00c6d03d60b0001c0c84c5900c076441540c2041031355041022602d01040b410101501c189000c10208042502c10f142540c01496140251540000340091003094025420400181103081000c98006001c111448524131039158031a0540d144901000707880c0c54000e44964240c0071010300000490304070a0145000d544650030100c8003560403c50701400c0d4140384440180340c9071400c0000c0c0b00080b102103881e0101e00c058104010881f00c0d5036140710f01c2c900b506a0003418908200d00000303010680c02441c0201071070003a0321200080d809800c2c40400381c800c84000d0a18418010200714a040c02e1000300240340c00b43c141381c030070b0302519030403480b60b640c0c00d40142046a5001004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 719278354 1250 719277104 719277107
    0xd03020c0114030108030304032303010e060901080c031c0207050d0b0103060e120405060d18141209010c120e0604060908060c04060806220606170601090f1406041a0a 73
    0x81c00d0901800800c030b1410340d414600b00c20360764040140010700b40a1402101240032040c4008000128403030804a40d503980c554406580700201a2021030040320740000105809401041d0116410340180042c4200d003140c44950b04e8480c840506403096008403040442d803038031030306220310380a80103101c3d85806501d0340c9801421180b00490001043d00012840781c20410050201c40c201c4004407002e41d201c04162034444010000940c41c01e17980305945215000b04036800c0c5410b65040d41f0407055503694507c00074110094820500309500140208029200141e182c108070b015070300007881c000b016684080e000c181590300c95042100498041c20003001080410406a5030083e6402c000b681801e103051030207403100d080903010031301c1010b031a10018245a10301c0c03481c40110104040c1840782d00d035681405000c906041e01c0309000181c010001520301e501542284085414124100c9540b0386400844c2c119802900e00c09940210708103c0001c0614a501c0d100744421400341415030b81d051089030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 719279604 1250 719278354 719278367
    0x1e0207051605010504030602070812130201020f010c170c12090312071704080a140d1413022d0301020d1d0a05061501050f160c080f0316110d03020c01 66
    0x900702000c054940144081e0340d00500b52130842ea8040000b44e240c02d00c80c03825030843d004420490804562f141e04101c60380220f0025021054000c0c0c0a844406400e54682420303105110302d040c0100e510103544c0c2d000244811419a80010842001401d0101450b01000810403d0300c0d5103050394008281c40b440100c0011459400c6002400d0010300ca640800680c8004080140b019041800218400d41c850b030042114103c0b1901c3c03020131942d90030802c0072450040c0448100140030020340b2002031080d0240c4035042100f02c0d0002c00c0ba29406090070748640c030028410700f400c52448051041c00a658500b400030345101c8201c0e030740206000e80a6041e11344d03040455483d5041c0e560051000c1004108013003040c5d90070000706400d407e00318800c1c4006854511601d44030400465001443c0301508219122400050f4404d2030340102d4142d558460941e0340310354501500a640040043c0c4194050f40c500080c4818480c00f5021030444070100001c26890703a40030154003507000615580c050350384c0000f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 719280854 1250 719279604 719279623
    0x150f010b030412030504030c05120406021e0a06051f030503091c0c05040506060403210207050d050607050a0c02100306030b10030b012d3809010c02041e020705 70
    0x5a4603040d86090b49440c050f448841e08040b061541c3e400104083c14030891584000720341260845a160704c580700010800c0d0311502c030f454018000e14100c21501050004000110381c0c003100109038100594840070010400980580f0307600c0100c0c1e40f480c8100707001020285c0218042c10245484440c0c500501c10100c121040ea40981c05049251800090310825403030140c4200f03aa0010301691500d0208085100703a07000034201e843d0500e41c3d0000c2500141c40e0040121103582501c4186540708240048040300301c40003851904460000780603941b041c80070380b078034800038540158010200c2c0c0120301181d14491030711001945a03007040c420700030754449550b082040395552a40d04e926548807000c642e80b0600800d06c850403031906c40030501d10f07691050a40000744140621380300c0e030b5176040c8008004d842d0303880c407a00003000751400180c40c107556140140303c6103071010f4130301c3c1000c95070045403000740c410001c81e40107030b40305500300c0f0088400c6100c90340040d0360540181d40d8401410315516202c40380c3d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 719282104 1250 719280854 719280869
    0x24020c060c4305030d02070c030606060f080c13030807050f010b010509060d0b300c0604031205030618011811031b07050c030105100303120528090203150f01 69
    0x68200b07411200b0b440b009540d01c00444007046520002c1c82c1a60940c070820400501c003e0001c280101801601b06107202100e101310805c0150b160b40e1981590b14100441c2c12202080701480064400b0850000802d10790701f40306903da10f1180c50b5030300ea603000d4001d4107003641c0e03a42c054602d450003003e09101e0f1040080c400d00341541851800c00015029118551401258985401c10443c0b561a8804203449180e0b81c03881160007000700b0980680d0300300d5542828655407084203c82d40c3c4030301707008084406894102c0a00d094146640b00700f0f9a19a00140ca0303d40c00803081c0700c1182100d08ac1e600d28501800c162020551725441071041041a224000140e244007134040081c0003d8210300d400c0c00030300c0041c003d4260346421850404d2818440c140070f03440d405500303140420101c00b81c030074503800a482c429258007003a809441d000000700d44045403c0800c424946080020f400c03030380d105c3c203031490340c508501040d20381d4164082810846c80400d0280700d92031314400d01c00301108030b0a80f5405001d12 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 719283354 1250 719282104 719282167
    0x804170a0c050f03010f060b210c070209130c030507150203130504180507060e0103051302010f11160801052e03080d020c06130605011224020c060c 65
    0x2034035540001d45040c41480c0c80703840c500790100340a0f02d0a4010b0083d464001400304402e550b1030048905540c0450140c500c6c08060714420845c4040d2000158081d011030031145080c826030b9400d0043d6408054000451540d0b03110f540790004088500c0032018510070009844540d242080e40302c0c128908440110a5410038003001c040302c0d14074a414012224121070200352002c0c4c02c46600403801a00714082c02078043c040000c00c580da040742102038480001e80c1c007081340f0340e2000000d44110501803c000e0001b07000c2e003820b644451143c1d000d1070501c91264280c0d0449029003034031403a800060740c8201d8090351204200310340425107844256220565408040b06000d8540b03061740c5081c0a4000100715840108801d440180158181c1d4103000c4460111003160810800c0800f101c1800c400c2140e43c00d003400004249131400c243c5a0751140d502c10742400380c1008490382c1d24141030700c006014040ba6428841d10203092010012180107407034034010a50b0328100114030058010303100602c803070005c2c0c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 719284604 1250 719283354 719283373
    0x281707050d151b020c030c040e0c0d021309030305010812040e0a2004030503032a0702210105070f020d0e010801050d031e030f0f09020303191704080417 67
    0x203440324010074050b03100b07039405454080e4540302001040c1ca65640101800c11107051075110b03400080410a42c50210200ca080c541c0d01d00802080e9a86280e003500113801c60382604c54030341411000c505101e4801049150410001032004046446959040c0c002036182c100401c0080c2e400d0102e4010500032890076072416050501c2d840360201c0c080c002484040c0c0d50210012294481d90301c60804865040d90300d0ba8a82d501d080c51a965001551885c91410319240f1710a040000c00f48205401403a501c4060b00b03013940c0b81c003006101c3d00103406c039101828a42c080000140030038407d0901c02d0f04940ca900030980c050b288002e06d00a81220000e052040c21045030f04140c0c1c00c00c0d64541100c2c4202c82d85004105940740403151085140041d05002c40c074418014081509074000c4201449010030400125000b04840420340d07402a001a4046d0820420f41140c0d10000100b40c1448000d03040000e644151050b0a4010010841d000e880445010506100040d01c600c0c09150f54101903004022110303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 719285854 1250 719284604 719284609
    0x2040f0504050c2505030a11010c02011b050a0e090106030615030b0d111207080d020c090417030619060c200a090e0712110319030c0206070228170705 66
    0x1c0b40b03910094400900c0013460a810380104c150043c110740c001e00350780e00e42c6001c00c40605100101c500420040d401d04864a0000c0d10520507548005401021001c40d62034011040e10140e0240f010203082104000b0504010b842e0485c40d6070080450b56070001d13100e49424030010aa841000c16041090300701760070125180d94506c0304c04040c035002010306108a01c0400014251000c010340c2c1d0007203001c0c1200000e510350000c20340032000c1c99141c0a0b5400d010544003008801e0200320390003014a900ca4100004074501c8002460340b00101414003819000f900d403100941100c158400750000e400030038008108010148032a00d0410680350210155064000140d8441510300995940035903880856120160400a003001030940e4039038200c1071100d908180d0303c141802103481d030007071003103d010444001c50f410001c07070a1901a0f440d02d0842140c0e60801c5680d521046090f80e004034081c840016030003004a440110b80b1428540300070681c540b02019910940b000c00b1030465030401c03001003100781c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 719287104 1250 719285854 719285857
    0x70209060d1101080c09190f060f0923120a031403041109041b0b091009180c0e100804051002041401030e070b030c030f010e0705070204020a02010b1302040f0504050c 73
    0x20341090801c203110b031750b9a4819182034058400041e0340b003002e55145074042041c02100400350384003428030072496600c612054900d00345907a400400141044001c0203031046406402c80f1003140171203408036404034800010208040c0d86905585500441c080104140c0c101b2071510001c40224030b01425450a0b0b25103032000722426507414000c43e04540040d080104064500107091740480c640c0001607200c1e40d0034500d82d0040c14440b030027123503031180c201002c03402150201c003200d21040089020a4101da00000a0100c045c001414815a41700021082d07171001400ca126802940d90030081c3d142074100f951074682e4120b1191145441003005008120901600c0306a92000782804581101c64038805031030314400b80d00107100c50320003105000c451581035000f9801400040e418682a98803080d054181500984103030000c100104201401410903030003a04d042d120b207000018180b2005000701c2d4080901148044410b80c0c0064140420b075410500031014000c01c0e60200107602d007841100555 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 719288354 1250 719287104 719287133
    0x3120c092e18060f0c080d0e01050a0203100b07080403051e010f0c0f0c050304080a030e090703050709051302091f02070b090f0918030c0c102c04060503010908070209060d 75
    0x10400b000c019043d013203000d0f8032410026a4003030340d49613440080081d2100200361002c0c8a0105500300310106a22131807038001c1e64007421500c00c042c45001d2910300d00c030300e199220078001c0300c0c00075041c480000445c40138020441500003000e20000e51403211000b02d8212111a91100c64041c60040950480d980c03081c038941301000301d030070300300d94141c09400d000d80345010b10740c03003480d4510802c040e1500301980a0b082d0b00f404201594038000ca82c86802d0198213940341260310f9070020381c0d0075004204918010020003116034a10500526004280020aa844000c04420042075015003031824500390f0403c0034500521109210310305280c040310002e540e00c1c100515642c407850000b008552040d0a054000c01d03034101d44011640d5a00c80a40b10503200c613442d0240b944203043e0f00c00402d01503401745418241a16804051504100000b00d804070100d84050015400c5a42c5a60106198400340f141841e078900500366507442e107007144100114407600403c0a030240e1000d02d0701d10001554030f00003404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 719289604 1250 719288354 719288357
    0x20c0c040b01140d091a0103030c110a0e07020703050d090803031305010e03030a0608011401180525090e06010c020102031c0221070f020d0203120c092e1806 69
    0x600c2010280101d540c460014481c0f1059803000402c0c203451069035005040d4035201d0484040c0f084444a00d11182402c00d120107030200e20301c602043c00003071010841140c060030051540440d1606c1300648121500e0484800025a204040500a1010401c00103004607800e103840159241890f8880d41c6a010141c900030440c101c03140312008008083d00550800103150045a440740741c0300101d45c000c0d24440c42030448079442c2c103202003554001c0308040ca0689505540148002001d130b504c200040c80001c160101d81414044054070b110341040c40040a18030958800003024204501202d4501c0e0141c12141405580811000180d80210650307c2c0303420408400d0401114998400000e0710819044548241390000d0b0f0a0486190512850141034955221410442c00035416640c0b110a90320a40140c4c0c01400324071800b8188503080b0307030f000c409a400d4a013482015000304485da01c100540e80d0301c0b96400340c240e1000003522854480310283c00d20300b440a15042d801c4883c3c07813240340c0c0500d40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 719290854 1250 719289604 719289611
    0x1020a020d0f080a05071110052d0309010b12060115050c0c270601090b0301150c0b0726040201051902031b0d030b0402071e02030f060f011503020c0c04 67
    0x7090114540c0030034039040d0080e09459640320300c1134001748030b948102000c490802400d510f410702d81c11700b100c041c0b102000c187c603102e16244001003848001c1d51a45680401814400740484d1380c1441d04000d1400b6008480c00850240800030130042c040003440030450981c1d000000421013161500340c01c80030040107003011541c86050601081c1810145d00f01d0035002215070514541005002454600e50140c1340f9620840d0b40702c800044408080034411840c5000003800184500d140d050b4107171000e80003070309250b0000704d42c84d07039090310400d011528100401c02208041d560a9048521014660001c00c025051490f1550001e4001d00402c141100d12100c44500c04600d03034000c0080706c075030303030a04401940c2e619034014a03e03a540d900c40941c4030009040c940710103c075003000e00907142150b500401c0005481000d03031040c281c110010340281d80c14400c030b00101c4040078091033502e0142c4000c1017014440e60410410f501c415040144100c109803040014004540c4045100c4031440070449010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 719292104 1250 719290854 719290879
    0x605060a140a060509011101050708040204140f04030e0103020c060c1b0307031205040f0f061508010c021203070207050a030c030201081b030a050c090a080c1f050307180b1218070501020a02 83
    0x403101f2400c2d50820706019881d0505111841c2c0d00058064419031080710188803203c100035002030950001e0f545064000003e42c045030000c0e0140c00d00d0f01000c0f1040c9001400c008223104c0440c64941c041e5100103010100051241040c40110480c0d000c05a80d070004501e0000349170b40003060b4010000080c1c0d00307590341d0070214080101617001e161403203810000301207005904e400d1441c0101003082c40801001e008102c00289444103021394a107610594000e0016070444415102c80c03540010840000c60203007040c0807a02c0d0303446184034400b1f5030044100ca0f0341c1030b01b90700c0050320200300075143c0d8a5240c0d2140052941c0709e040c1003202c0e4004120040411952106001c0700400d008211941d03920403900040800e0700b01c8005403c5010b0401290343c000c0390903070000e03502c071000703407142d11035001440410000c0c100750700510f01540d06002c41070748800703019a5022440380316004101c80a6000209078240402c2322102035011038591180005014114500800030356a0044054024014044080f04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 719293354 1250 719292104 719292107
    0x210020c0109020603040b0a0606181a0f031609060206010b03182a15070506010e071206060e010806040501051e0f130501211505041e0605060a140a06050901 69
    0x82d1980368043d020710b44908241ca88003401c0d260403561800840d291800002c0c58602c10040d008810083c2050300e44050f007040f0002c51404402100300b624a1020800c03c0c440f245890700841c803807035100da0761103544c1e04541c0c00141201d6a591003041194080d038014811101c0308001c89400c605840c84615511421160b480c0c1400e404800d03600c500b41c90707100104940305902485c880e2452040f143c80003268440c0c5032002c8a4050b00b04040c10f030f0b9001c50018403c41002e0014140c0042c00e07800c001c0560712400b9940f00c2610183c0c0c100300c0c0081d5144034010035039600700d64400c0d00b000003160709004a6042001140129568140309202c0c420704d040031620940301e00006403400d5001400c20a130041d92003101c00b0103030800380b24182c0c0d1405102d800c0722280d02c0100c102010783d507015000c0000d44072580407003400360501a205071074002d01c143c0028000a00026000c0701607100317000124807890030b0802c00c80da0000c2d43e4070801c448003544250a40f0365842c2c40c1c20300c0944200f4140a51102e524400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 719294604 1250 719293354 719293361
    0x170a02100f08061c12031d01060e0a2a050d0f020702030a060c0c08041526040335060102010c0f080c0f070209040803090c010924050d1404150c0210020c01 68
    0x30017800105811800803111585604840c0010602003000b01d00c03581d07103c42d00ea081324143d11940011240103000b04d100410207420640160388120040060100000b1102140c0001d007a05600881c8000400026a00f00c40c00345841c0030411100031802e00b00307a900825203414507180300800f4075984900501d0898000c00c1c1066102d40c1000d4059180e03030b01d40c80c5900000c2141071051021691841d40710560003100c2206000844d404402d0000a40311581c0a6500100810280785a172280200720002005e0400785900150032031610401d11b410208006801c503035000c1d40c10300401003003249080351142c0080303030250801542d00c00307182e5985000711a40074174069198001e520003042001d100030700c145080998056840b04041c0d444a02030b81e4010760748024a1320511280b0800070b0600200110724440101050707800741010343c6000d09890740c1e10115103403030300c01e404401100d8052200b4841c18660600ba0700d0300aa00412007c4e03e0014080e6441c1d06a58242403d80c1e000901030409010a41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 719295854 1250 719294604 719294659
    0x30906110406091a07021c24090314040602120309030c030f0a0311120105010f020a051905060f221a070903200901140604170a02100f0806 61
    0x1035449031a280c5540c0b00400c644070380c0c032901c404902414880140000b04030704460440754020312107d000414002c42204155000405640422a881c0105044042c9079100b210400943c100051982800d24015180583d0030150841202c1d05000602015400241c460041044080d07050b85a540785005980365101c2c858466486000114402d444000010040e0001c810680c07000e004030f52550700c603580c1d036000300700c0b400c031018400303c004201c554028400c8920001c0b01b4810359000c008580c807070790701d440d0144000c800c3c045c425080680034824184829900800440c0c031914440c00d00c0402d800200c806a01030b442d0468100d0000e0040040240f800c540018800c655101c591500c1c070f030081c01c400f002d80300940b10480f03102042841c08099001e10034080e440184800c8081c0d00f841c00900d440c140084420350004010800411a004030501003505201c08a0080195203071610500c44108a1071584100b4022011282c840f19034001000950014007911455400500203001b09401c030187d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 719297104 1250 719295854 719295881
    0xa02130f08071a030c0906030a0f0e06012c0105010e03070e09060708062706010306030807050c0411070519061425020d1407050f030c0a02040624030906 67
    0x80e0000381c06080401c2032070450b0300551101c41420700d60714000c521440204c03840c1c0b80700b07081003040c2c254901d040409140c006604910016904120040400480e06c9480b0510b0700b6074401d800400002c52161841101d02c0310301c030b204070014299800300302c4080030103015580c140040126078281d2a02d003005140700900e2030f4140c46005060001e01c540e1030300d00954540b000030b441d000009a40d030030a00008511030b60039000b0301520f44000c881d44109540094000b85c101501c070000040441c490074041c103420390007100509510400c0e002004211409503852613100c2c40140048004150f0202d007090420040500300851265207145c40c00080000c4000300161a8903030050103d0140c0820805000450f6900302c00400c50b20202c0c00d17070f07031062280140000100b220700300021085c01c15001d4141076205108560390010304001c0346083d900a00e0100300705500c505608425480d017801504000e00825000c2d82c401c0031001820340150845021110501d51560b031048c00b0061164031880d00740050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 719298354 1250 719297104 719297129
    0x509010b0d060606140708190521010e070305160e0d0b0a09170c0304060e060706050c1c05071403060112062601020406081605120c030414060105090a0213 68
    0x15454144010f00b100c0c011400010f507000c07048151500600220359805070000021820f0807060706481c142900610308a00400105201c618920342c1c42d5010b0000301c59000d541c0c0c003510360414018141d120802481082014108000d002c0441741e50485c0404410540c80c04134900b04040300031900ca03040b511002094080d040c410001a10a2076022201e0144100011060240e015641400a008810042c0025001008200b2159005000ba5008620043c107103600308038007511580300700c1c2c8041305c81c000742400004108413840c110301c8060045000c58182003201d4100414010403003d11900d51b644801000404920247c3c0903200d0740700e1800340100f0038422603803917480c0000c151403081a10301d000d510680342c1004004041c000d44050382d415075134107074990781c0c3c50702121b42102c20144001d00b8418200700305e0705070410500c05a4070071042e007080250f407824203140206000800048400660700302c4c00c0107211954030580c010707070002c401240c0940c03202020782c0000b8002d0503135032010703d000390b2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 719299604 1250 719298354 719298379
    0x30b0301150b03100b191d0f04150f030c0503070f181109371a031b04090501030c09150311030102040f031a01050109030f0b0c09042306010c020f040509010b 69
    0x18640c4c1d250002c01b800b0303501d46130410034440c400c450002d503414030036034050050218400c0c142004d07484440c4910344100c05114840e40d8500c000d890988982003030302c1d030300c03001407007032015080400c036000c01401c203201c00354078561a2402000024201e9400801d143e030701c51040305800c541204c180d43c400c210007031035036045001c162000e0340c080c00c1016030281d400700780c81e203d074610064689017a001c40c6c4886404a10225409000140542c0010543e843d01c40e107103071401c513508007140c002c3e0000e4294142c000a031541941801c01248803540d01010b0140d04040031502c120006510fa802160742c00647d16002c6c074080000a80640240d401400d201c40080710004144007030384802d0b846000071155124100d0b40c0712401115250002d000241c5002c507461000c80000d01c0a0450310352004c4e050003000d003402d29810000b010707a8a211001494041a180b03a004040c3c00c10341030030b03002002403c2400a298145e800b288402e0f80c108003a81c42240d0303600015070030400c290032659048100912520b50010b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 719300854 1250 719299604 719299627
    0x80312060a0605092202120103121407080904050c0f0f0d0605060310030f0615060c0303060b04050307140d0204052a03010e0a1a030d050406030b0301150b03100b 71
    0x400403150584901c1c0d4040d0002401d900401c00c540d019640a4081404258401d1440c210340301d5160302805443d500300180c050100c0b0600e26a4080c511900c104510070103403080041044030031001030012030404201000005074800100c0b078050a060742d02040c65038a010342e0804c0c2d40602d0f034682906820000700708100b640c5803401411030340c00074207080008503101d40910105000403242914610683c110510110300c9140341400d0492240c400421520600450f10180882603801600481c80a801807010143c25001d050094840c0361146802c1624040010b5681c0503103104510b5100d11190140d4201d0301c0320349050348240e13000b0700280701d40c2c1024843c40102c009160f040142c070358034000c0c403000b81c114480200d9040351041c1000c0040b43c3c50f00f0f01500b00030b00386000100685003c2d0003011134940c80c03e01c11401560840c1d1902512945841c1001e01520b2001e90041d102c2d0749450710389602c413580c1d02400816a01080955920780e9503401c2280d5583e0320f030f0303001003240400100301c038a03203130 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 719302104 1250 719300854 719300887
    0xf13031815031b02030a050f19031436030c011109120106141203360103060506040e04080c0106090c0f02030306010c0209060301112809060203030118060803 69
    0x39030707242d4080081d8502584038000302403442050b2001038108000301c08000344540c02074010b0420f0164a1483c00007070b11081c015500c4d4008100000c0398407441c8840035040c008010f6940120307441c403c5051a894600c0580c0c00c44007441c0d00803400301d079800ba4000005820000d48030b02070707003800007003080c40c001c4403040000da084054420300c2602582c801c04540d02c0180101700480312801402140900041c013001040382a1003510700e50703880b0500009200e61920340030350800381401c509001c010910300703200b0808021a224144d047c5030610000b003089031946000c9408644095109016580356440e050701940b240ca1421031980d03080101c080b0380700c8083d91080c101e100c95030b15055000c514894060b03850b40000c50310240071541d007048000250503c0201c1a5002d0001400081e0b003d0b100c0014101d590008c81b8207440c90390703e09108203001c15441b80c04105846450500494491810000941c0d80c0b00501800f84030300e085203010718402045410010181c000c4070141ca448174100303c07404011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 719303354 1250 719302104 719302139
    0x14070f0f0506251b05100f05060402070b0411010507210f0f02030702041d030417010e07031e0203010915050f060a0f0603052a0307020c01080f130318 66
    0x86002d1480840c103041d55001090f40c1d0400c50400001c03803800c0881c1d00303407801111100d2074881c007101c0c1028240014802e1000d011040440da000003a1400c1b07025960003100c90003015940220b10402686001c6400750041e00c3e07005512000700c1f0382020b1143d0048807540500440108281071803400d090396518140b5003169002201d50b5010200d560034903040391a035201e001c0040140c0c004100100240c289274001100f1100f010308200d11515040303203441e1a5501540c40080070303020742c1c0c100e410703031f42e60038004c481500090400604429007035480e008100f86088040060710703506044003000f152000e400856040350080141b9040002c3c1044080145c501241c00c0803407034030030b0340000da02071812081c1c100647c1c1d021a1081d0350a820319006a0040c600581818a81840c100c4203c00c0e08036a520200d07201d01c1c1d01c001c1c1640300d08001402902d40300d905c1c6642410300c40100100301e410f8080c010050340c400350248101c1050011400d00303495020041c0040250401da20320003184d9001c034003070301d40340c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 719304604 1250 719303354 719303363
    0x30807110a0e06090a1d03091903021522060c1103060103081605070e130212030306220f15060f0503040b0a15080a061b0c0f020114070f0f 61
    0x41000500d020031200d0180d6014201e0341c48042004191541401c03149964002d4802c0300004400d10b5240c80045080c1d848802a85268000950150700d802c091045410100d140392006a5050442e8001109000034101090780700d40003040c00340300b1800c2034600ca140140340590140d600d5880e0b400081c40542924030507144102c82c1400c031001c50a002030124103d03074210a80c1400c00ca42c1d480881c0c42005481800e45840c460400e0200c0c03c1c404085c00f4a00034002034000250800d00e61050200c80d2800c280030304003a40041c4200002c07511440c5080c03010130103c404203032950b10711201241c0181007251041e02c0261030043c0a45c009144c15911a040d28680d480d52013000f40d04840c111490f21040303400a1003a5105404500140d01b2a00706204602c00715102c1c104454a809201b80303042032041c0b0079a1080d803030b0700400c644c1e14142c06260785100c00620744406104000e444e94502d800b440030300281000000c2c4685000d680c03e1109591070a68410000b01581c4054241030864885081080e603 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 719305854 1250 719304604 719304623
    0x3080403060621030516060617150106050a0e0a031506030212030c0a11120a0317061509010e130603050a20010807030c090504050f090d0e010507020d02040e0106030807 74
    0x90b81c14242a00f41d084412003007070480409603991360448160b04061076070103011415401c403c001409900440340500341130802c00c0046407609031241e2030451225507001411540d240140300196200049514038495400c1616032a19407401082e18403001e0340c40600101c036035030610354481600e90031501c03c5a000710340c1d01e0701e4500c035410b0312034a80c0308419111500b41e100c50850300c002040344c030305500746503c001d103110000c0703920050031814101040c00440c00501d00000421820b8604900d02e5000384050f24900080c0c42d1a0076511681d10900913032a06201d0050b000b11016940c413003403400f00008460062000b25541d14005a0f103084490080703a00d85c0d048003034244654244814100301d400305a451602e035482e4158161300400d007040c0814100691310b580452180c803a4003a560042511007246001881c103000d038079041c00c41b000d0d0144d01700b0010320441100b0fa039200082d101c602d85c045400010056a520004008140c2e20100d68410750a001d000004d02c200360002e05140c41c007810120 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 719307104 1250 719305854 719305859
    0x10903030c0e180a02040e01150f09050a060c05070819020102010e0a0c05090a0e06040b060f0904050304060f021609140708040b0a0b010c063e090d020a0f030804030606 74
    0x80d02d10034040000c040d0030200e40309180c1007401a545a407078001640c1e00b0010714040c2c0390300c02d205110809070400340c80701c4095515448038540c452420701204800f0716002c1081c80c1084002180c81c501c6115080400840c01884410709c4005d025600081151030704580f0960308500c00c10548140000090340076502e480840381d004000441c0300ca078080c3d4050103e5030346030b080c4820081c0980020f00900b01c400d6a6411a02c410f14040002a000b24050701840c8201d00d4004100508408095049401102c1075001d110001d900003050b6801e41c2d815042c5029903003c4014201e20700107100009407038490a0243c00210303c108c6902c006403a200c118081e10150740c500c0c4042e20015001c0e00c0080c048031050002a15052441e070011040c1d03d0145840d580d00500e0391291000e075000220700882c000880f503040c00000b00e103031014920b41000c80086411000550581c505240907255959001d505100c48407821961610035850190500f4010108403603240c1c00c0200c0c0d10b030450300040700e0721450460301 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 719308354 1250 719307104 719307107
    0xf020304050307050105130f0b090a08030c1005130f150b03060103030516110d120905010f020a0b0408071a0604050a0608030304020d03031509140c07121b14010903030c 74
    0x1214141d0704080c0c01801964502001100c071a4001c50450460344c0c120040891100e5000750030000030050092040e44420001d01044040a5070381d1103010b50342d200308656400c105007c5070000e00440c0e201c0c0000364a903112241d4403c100c0c02e440f4021b140802a410701420002c1c2c1c02e540e00010710b2040f404103d51407541d010300d6a6401d00b13000160100314144505154500d803944c030980300610921581c03411a000e80082400c4181c1c15008072a042c03918a24850125845101c0720b00401c0309103002c800300340040710042d44a003d40d050103040c0b8a00d01c0009800d00802c80102c81800e98810301c002410020100704801c110802d07280c1c144101c2c24040030444541090051b1400d907101000a1803854035030750b080110b840c910740750817010300d604c55176481e8081c400e00c0102c8000f003a034031002147c0e01e801e00c0b0390700724800c50060989504003010b20145000c02e20018103440200068200412103014219181e60f000408170340c000c002001c00a89c0c21032001040d04150071540c880d4405020310685540c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 719309604 1250 719308354 719308357
    0x80c0d02012a140a090504091202010e061306020903070e0c03010e0f040b07050c1e0a15020f04050105030a0905010203180c010804050c0f0114030103240603050c04020d15030308070f0203 82
    0x35620000b89000c66000c02c0c1803050f80181400c0c00241052401d0565410100d002c3da0300c146025204c141103403000b14140740d0203000751091040410080c241c1841c2110050f0400b1385400c0000c3c1046501140e611b030700c1d403010000d40d4042c00c061903004403103280c05241c54410358001d0003208407919409001c2000a1501e1030043d004540c4402095550307500d0000881d025008810051a00d20682c50440c1d0b0501c403c411010045000070b02a010000c41418880303c00c66901074009074151040102c2000002007100f5241503071800d181a0f03030780ba00c458040d54042e1440210152095100100b07000c001c1404010380314000b002d68094a841110100042d0707801c03141100c0141c015001003d00c6806460280d0040004841c14140ba1100c951800c2c880403154000b42c00407a0005205004000c4040c0310501100b0107410960050041e1800c580c4ea0544607100d009045025a80201d095482c00240d078204413403000058844800d03080d540c0c00d004040310302c282e51800202d400301301e54003c40e030710210 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 719310854 1250 719309604 719309681
    0x1b0c1213080a03020d08090c0d03020d090f0503030d0b191d010b0c100e120d0e010501080a0c03080703030e010c120c09031a0a24300f080c0d0201 64
    0x2005060b02c2d0040c201c01340c954031b00040201419000b1440108500c0d921401076100c524041e40c002c064071034014201030100205a00711441c5d1100206041003680d400204490381c610002401003280007100012608201441844042c44005100041198158040d10300030035010700320015500c0c9d81e20489007505200e850701d213256503007001841c03d00070006074104e502a40030b580200c400700c800a030400b600c2600800d00d403450440d11241c54100241c3c1c01d02a203070140131000f01802c512011566400600030140c403008005c2c07580480e420b401c1c0b600950107440400d01810007408a102e8245008140e1010340c20300c05d0800c0c1c500307004c502e66035206992000c240c0e54040c07071003044038940e001e80c1e410140b0000c0c000c0c508292103c00029640c042030303404081601d003c482c0c01c200f450912490030540f42c020b4131444041e205000c456102d4440b0168824021600310080d200c1c02003550030802418810020008010301c02c80500d4004542c2c15402954090020800459010b825960701c080d03444142 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 719312104 1250 719310854 719310857
    0x50c0601270902061218120c1b06031504230901060b21040819110712121b020306011e140f0907030b0a0b0319141b0c1213080a03 57
    0xe02c1440e5895a01103841744c0c00007a110500c481100c000142d0925180c3d11008014188101084816140004004000c400c440300d0030348800d031a601801080c01c9000c010b00b100d01c6150105904038032620745611025405078032868040100e483c2060840c40003809444501442d0300e8524001240361115040d00c035400e541034a94502803842100d80816402e0103007003030305ca10b40c1c2082650600b594280b10340800f60910f071101c0d45080e01c5540d00c5400d1110f654040f108031051124098001a8440701d89007190010b400c00169400c000c10018010b20182e02009405100e224000f05000300d800c900d0005880c01031511a0300c1a40b0340d40c03901e200d10001d840c2d80740c03c0403003445104011324040030a40d0f48180275140001d10940f40c48005907080301140e120942d181000014040c00400c40303409109492035200051003005038101d100c002d84a4010045241200c0701da804496480d6248200c51100030300030215a1a452003454400750740d80b22402e6802e0217840d0200010304003402041c060390b401e03010b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 719313354 1250 719312104 719312107
    0x11060f04020a06030c0212190207082b05090d030206011403031305060726071a06180a0207081810020a0804030618051b010801081f020a050c060127090206 68
    0x9000050b0003524a41d0034500642c001ca21890110f244847c014151900c08580011703500400140c010b401c15441d03803c4900380d5000420b03251b0315003010500010b9200c0140218880a1035420f408445a000b03841c207090f44480010000000d040c1c0c002126811380380e00d280603001000880081560301e11130b610002074030113490f00040081d4508807026200c00c0d4021117154282c148a500015040804000a1750003000c01107044018001da008000f405013160074201c0c00709040443c00240341d4203148424065203a40b0100052103614140c041c1c0b10640c0d0b11220441e115104051005040b4840e12070380340c06080700d00c0e2252101840083c074034481781d400848152501f81140c42d0700d009400c80e00c95413040000480c10010001d49c0410040082401d8401103500c2c64018900040405006911503800d0f940701c5404001000304001121010392660400140d44c0d95003414180c80600030101c01c8034981c02490000036414004030740401800c00d24480014141f030b034180502c02111000e54001e500b0560 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 719314604 1250 719313354 719313359
    0xb0412080c09031e0a0c060302070b010501080c0d0f1107030c0b060114120603030f0f0909160f0302071109160207151b050109050304090204030b010504050c0a05180303040611060f04020a 82
    0xc000b00d00c90500c00344413058900c58901c640b1100c10304a103913031100700060742c002041000c2c004021021400f40209113401c0150b420a4101790000c1d0040e01c0e0f00450041d80d134102c00b0910134031a800b08042001110445440e5106810b0141c5120704000c1c0a0703030000d42060024030a5841071542d012a902294120b41c180b850b265491060080002d00140c1c040c4800c00104020700d0440024240c07511141e100140e4401443e010700c908103c2c0500040c8a08260368003040e030640d00104282e0101e5640d00d401038480c1c180342030200c3e51030003a0410580103800700c5c060050180e440c0030503003000d03403441d001c03640344690f910701d414042001522880000f0b544001c80400e8a03140c0710b4900641c0d4060000454080c04d1a2a4242103a101c1c1e1b000018103a800941002001039810ba8140141b0040b181003080c0e1605c101105941c1c802c90b680324081000010356401e090007018440021480d021701125103441d1a408041d0032001501d0447d03815108000004400d502c003036030041d1189a01034840601e592 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 719315854 1250 719314604 719314633
    0x1180b0a0e041127090f15010c0809010309031b06200c0703081c050108030901120605030705091909060c1d011e0314040f0201090806010e060f06070b0412080c0903 72
    0x1e0b40c2c900c01609001c44030740301580da03a501e001446c019040e601c0340c0322050510303170b448401e483c0011501ca4140301d4031f52519804100080c09407041c02a0038200400e980c2c0143c80e044612040e407000c0e82c41038040304007a82060200d50350001408120542554041c5411044d07210040d01503159418110b910603901480000e2111014000e09416a201e2200f2560300f1708401c01a200d090f044040190303c04121b42442e9a446210f41074421b000d102c007049024280400700352140002c2c01194004c07030141c808100080e070480044070f4800d420034020008440c6604c3d08501810a40f82150700040c1150203103208000c030325415480000d016100d013130700400000900e103010950719030104103059030348614a092140c801a403620444c880e030200e41e001401c81c8005008500c0a03048070b0384d1548460300510010b420380900e1340d0400da04a4524842e404c1400005d0040e2240d80b900074a4005100d09010420240b950810f00400c041d441d00b521507600c00c2440391150040c041c1c03242e807642c4408403905024 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 719317104 1250 719315854 719315887
    0x60309060b060c0a050d090e0a02071103030a02030d05060a180905100c0e04060b0f030114030304090914331003081605010506010509011d01180b0a0e0411 68
    0x4600c542800305101c840c030000261150003004000d9095000107081100b000410320000840503418108010b40c1e90038182c4c00b141c00d00c001070006410960002e510418801c0c50461400d6105000b01241e079120f161404c000d440390050601105682c1c10f242c00300710070745002c0b022501541d010082080d560baa042c0e00d200c010b040e9440041c1e845000d810881c0128111602401545503040e4441c00c8000c203280c401e0100300c03040c2d079204041091040c810070710001942c00c1264119a1100020300c003144404000a00303501c9280c1c040141d0740d240c001031008201e80e404100d90390400c0755040c0c5141d40c04590b82e00e441e4503030340703800401c50034101103032046000440246260024a480c042d20066600d07a40c5845c2541d00504034980704c0c0a583e880801040024061540d20036802e1801c2030a0003601d0300082c2003c0e1414800103c12200401c0650380b99100c0c580100c2d5010f41c1401088019a035180207003201c0d40001d01c40130000d200489000801e041c02d0203002d02c0c000104103c2032402c18542205401c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 719318354 1250 719317104 719317121
    0x403050a0306030b0903070b061e0d0503120109060602010e0601030320030d050c0702030f01230a0b03060106090f060207050d0b0615030702060f090613030e2b1e08040603 75
    0x1e142e6030780c002001040f600e002240c4034010701d000541d42d52516052030164200c00070101c503c1240c41c040c90103010007100c0c1607014848416513942c043c450452500b181180200c500b402813001002c000080c070320200d5003003001111659002005095040b8800d103440c1d000901028012545480d84204900010b030b01050150980c41c00352420a844011044280c2d0020380700540078890104151066203010b200c0b0080d6691400000c008103c0003040121034555000e100c03401480740100090020701c3ca5411034001490b00400356902913844880160040060b07008003410f110071440c002c00d1880c000103201d03085c1c07070004080c0b40141e40c1595480c010418002c01d03258100f00610898004441220003541c000d0003150003400b8503140c40c00308249000c0b0300804d03500196100d5028442400600b07107650240d1034040c54030244040541c0007040c0c171113100307104884a00040440c050707900d0042d40402e01c111885a41c84102c10017000328003100c0c5215459010346034000400003000703d0340c080d9100691 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 719319604 1250 719318354 719318357
    0x10605090d1a04031106190b010302070b04140d1805040b030102130e162604060605030d0c1511122a090102010b03030f041208070c06050a090603060501080403050a 72
    0x10301c440a640d203401d1402400c0540340030542001c240310030503801002e08403442d01c1080003051140b0f80f00c0720040911112a0101820564034980301801c1d034400d4046907a1241c10408030750050600b40b810f5003408405000b80d50150103a0b5143c43c000c1380c81003035800040c80c044001038809908060800004000f0058110362645d400c0000c041d510201204041c001c00303e640c1c130130000d1303d4820554520481b004004100f00a100200c01d20880c1d030381c1e00075070742c205107145040c691550346181c003000504090304071780d9140c031411403460340041d40005501101481512080045008130004505488252004640340081881903505040c0c491001e03030381c04240c01c40c1400c030f610903c84808074040586036030208810790000b594a41c0f0358090052015000055005500e44030400c480021140154020080c54584020955050003480b00580380500d400c40e800d150388558403c4041c140794132280d401008a038904100180741400cd200d80f10442d031060315007200594541d54100c03901d03441001c0c03180 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 719320854 1250 719319604 719319619
    0xc131a010e0406091409010f0501050d0308191803020c0a080a02121002040306020c0613020906150708130f0e130803131a0118050112020409020310020a0f0f1701060509 74
    0x8120aa5010700c02da040e95117020010702e070400640290035640403540f40c03509281424010059921150741c07901c81c158140c607203038010361a80c020140e40312440906480c1818105202e00c2160108aa581154a07209800b203c500d40f0100d030900178100560b02c01c08041750000c020b840f002d0b041184c044845028824281c44a4030101c4600c18101d07041904255034050307022401c41c840000800845802c801d01e1071414021809990000d0705102d402048540100b5005401600b03444079101607840f4079602281c02c85d1603200903031050200c40c106102d81c04404030401c0c070001e031706802c1c0b19045004010143c0c600b503140034240c840015503440038059008862805030500042150b10781c030820301500d05001910994901065003400b0201100019511850040104859101c2480341d0a0b46e0382d0680e0046002203480c00001e050542d04015918850b0000908285c11640326114540a0000351150010407002c008121500c03c0d000407140e455002140c014802c081c0514060a003000d001131115 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 719322104 1250 719320854 719320859
    0x1802030718060903020a09140402040b0a0f0b07120801030b062e08190c0c2909060f070309080a03050621010204170d05040312030b060a020c131a010e0406 68
    0xd840a51442e4448400620302003402d00440c50000c20b5480200140401802a52010981c502c800140600000d20803a03880d211380000340c842596420041000c40805004c41d41d0720303d80710380240d00a0004944848011003c0a1b840d40107401145c1a01d42010b14007140e6038400c8280400421810905100c100c48101503034200424550a10010f40441d540d1025a05080c05418800c4d500d00d04c5104046060500041801e944180c1d5143c406410a481400110402074941d51008042288510119494040091004001404502658210b80641050f55454a04030100ca40604008102800811124540508c039400907900103100821100c101d24202d060103280201c420200030b2180d4004c10308100a0340f001c034040c02110707524805001c038070300d007590024664071a40c0802001140c002c03802c00c070028465800001c01900103172100b603035891000c1000e5034030307000101141d05c28032030316008003420800b600a0048000c0e96240e6464102c080200545081f50040c0c0400c0c2c00c917994a100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 719323354 1250 719322104 719322137
    0xa020f040e0405011409010606020309090c0409060303050a0f0323090c10020703020a0b040302090f09010902060d060503160e01050d060b04020703201203060d0609120f1818020307 79
    0xc1d180100e00c51000002d628102200c0d10f00340710310060a035030060f407506070200145038011003110b040da10708a8884400e50350b0400c4200c0d40c1d0281d60408910285003520210806030400000d0040302003075103a502110862000c00c42c00c0d180301141e0002d1007a84920340542c00100300101940000800059902c174003541c4000c83c80e0b0404240b0701d000103a21a400403c19418000d800e54080c041a016280c541811600030038101c1f0005403010503103004510005180040a45c02000703459801020680d4450040303400300003030541806003501c00e00880c90350000d0109083c110380308030740e10480a0845617280c98100410840740c103800303030f9100d9158440c980490b9201e200401c10349102e034541c2a00143d01502c43c410089000c007080525a00041401115241c0c031020ba0341d001e002240c01000c20456450030b200905400100244000107502404400c40c3e017001404140150b40e07906c46141d0446004124981403841c401d103800aa200f1880204101e1182c0003140c1c0410300381051204550720300304 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 719324604 1250 719323354 719323379
    0x70c03050c0316200913020904030903050d08161b080c070e0112030e0303030f2404090501050106080a090f060b0109051009080606040507020d08100f0b0c0d020102120a020f04 77
    0x303085544d00050200400c40c3c0a4100f91510445016220280d10380b9140740c8410b108a02444061310407903030000064105842014000095a07024003501e40800710040042e03e0341c401595480d003514000710880c00c009200e05010072864070b034102030390071294803038481d0b02c025840b29001504a02403800c0100c0c0d00c000761441d07a4002c00c1c181c01440b00c9210316090007001c0306d400c107491034403a0f0420014000548411070351590001d0319240d116001038001001000100002c41086401c42d00300904003061110661141d8100c640540350a1001c2d61403142e4141143e40c804030091011541c014454040303441680a030030000410b05004500c6511500000c4229095918080014110780428010000c1c00e001c0150031000c16102032019003011003020b92500219001c0604000328040001c54018090140e2070085c61f132000c0100c4155120300c49824a070340700d42803040c05449000c5403080054070500c04c807040300445846c81c007102e485e203041c24030281d070011446070b4001304103000200f0146400134 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 719325854 1250 719324604 719324647
    0x80609100b16060b0315010b0d02160b040204140720070504060e0403030b1806060703030902132304050706140702060a0503010603200f0c070305061503060a0203070c03050c03 77
    0x492806680c03500d0443c1c1912020758600b406508054080c04030200f500310315a0640c0c0c0c0251a454684420348841070090140207011341c4c8054040191710184106a1a290300803030003030b10148a0812074004046072104143c43c0728001a41ea03440128081035245601c1403003076881000c5d91181a518400901030342c9a5412400010000701c0500c010542c052103956810701c0140c6034440300220b602000a1314030b000401c2a401150001503490805209611540c24203034001d10b903071944d9420200348401011003500700c0000300312060031032121991492815200395032020040000a01340b410840f0001c2c007400f29512650f0090144e100141d40e0080038000780c8040740d8a841d102e42c9806030040580784c1e1608600601441c0f40c01102d04828510b0845240c2d88451100c0ea90f6000740003085480c00c840d80d40301800b24055034050021541200301052501c85040742126140c0e114155030303808a100990300c45000c00c1004451100180c041c101030f100034065042500e09200390288641d1b100540034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 719327104 1250 719325854 719325877
    0x103110f130f06020d120b06071113291903060e07030b01140108130c140f0604080a02190f030201120603120206010510090803161b06080603010c030903080609100b 72
    0x181d00c400e40281c6c0404510380e030340100001802405006000304200b88909100981124280070b07a00e80c480d240c0c19040440140901d40400c00160b400c41c0401103018050f0f00c40f1045108007a4100e25490440c40000d030514112510150041c074560304d442c0100312015004080340588000003000c6000b20004a00a1010004d01082017140c0b10005103c608010090f0208055010f0b200d4003041c500c0740c000095030b0800031105502d246c0c210004103140221240e040d405540064007184440000c104400d4461080e5001d81c00541058000904d070480c038060200c80400c4003904001541c0b04215070900ca11920500050140d1652500401c201c3c107079043c0009a406500100700c00e040000354040894110319003440c045040c41301483c1c8074803802e002c42641c4408200dd0304184021119245030488541103110b6139550344400243c19420100e030914801d518000e034411840d40a030107072000859043d074a041c0d150351040208450b1003000340000250380b17110702c1d02003680b619000003801c030399003074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 719328354 1250 719327104 719327113
    0x6060b0f12060111060411030c0604060c05060105010509100c0201050d05040f030e03010c020705040f020d0608060a0e06040f150e010c2d050a050a0318110f0103110f130f0602 77
    0xe0640e41d28242805400181000640340742ca50b441c60000c1841508140c0c0038030307441e54070409200000d00d045821150203038440d40c00500000d100c3e80094600003024494010b070703240d5a070303941c00654450140420751074101780d0100503200b015100d0700725841c1003481414014105000700e00e40a04542007224221038010300804c5a105150308016051503201c0110000d002c00600702c41c000303444001e14401c072405a5103c079015941d021050301030310b202c071000c514100f00c0290340c0c51040b0360b00d0b101a241c0364540c0c2c1c40c02c240f034101d40c507001c148a03100b00e0300308141070840504c0ea81c0320704134501c06801050681e90b590002490a810a0260560521a554a0503026800010103c1805480700504200c007982c000d00c1e41c520315041000e40d050800b2a0030320b1602c0b86d07181c26040e80644072403901c4a00c91415500743c001045014540f4220148d000d40d0b00c3c11036032411400642c200e603248481441c40701001e01a414490400d6801058220103020322421031b1652101c1c007040f058805e400410142c2c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 719329604 1250 719328354 719328367
    0xd0c1211030f0a03090504180f2103090507060f030e15010801110405030d140c031306030c080609190605131a01080c09010810080d17060a0308030105090406060b0f 72
    0x1002c000c80000031041002030b001044a56901074928901445128002c648a034050645280e015803048003040e0010304040c107103051803034260f050320904841c1c14510340f03020300701c00045d038840e101c0d102d9403550040082903a10f040c00c00656044140000b420100354030341d150000c541d43c0030300500c0c1807000942c00703003a4036505161149080d1208404a40b84400082c00104043d9900151007102e042480c20840c0340c0d0a400f8014004038841d189121000e0701c000582540c9082003860000c0465900b40d03410072155030f110008903060141070300c1940e03010700b016001c142d00341d48030b511846824621301c20028000c0c3d41c0300d020030b404a1a840d0858051070f610545e814a0b5505d403200d0712420744091a0210051424101629460142c0a8401d04125a500c000368030302c50306203035603006042c001c4c0848540d240800c100a021402440c0c054040b000410b02040c5541014030b103450580b94059046411070303090400b441400e0100030401c1c2c40c540c0c0c4540c00000c4181c40c1100502800200c40401c0c0d54450 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 719330854 1250 719329604 719329609
    0x6040b071110140d091a10050108070f020c120c040c080103150618051f080a150b0303070201050c070306060605070c14400c02070e04050307020d0c1211 67
    0x850907244014030030040b0510003010750340c104941e13100c070022800041c0c2845a08121070b4120106030481d0402e07038141c1c10b0000f0703d50380c0c0503100d0881d202607a034180d49581d4004103c941e0381c0140381d41d502507845107800d07183c5c03882d250300003032003403280c0c60700b11045201c641002400f65600c06512401180005005205010100054110403000041c0c00d0040714501303050010046254a8030414945da0b44c004594041c02c5045080d80c000031001640c00e1007600d5084c404d898a400c08c20494181c0307003000070744003204c1c0345010f6596149030040c040c3d4100700464006503006d601000028165001e04100400020414032070200940041c1d6240d6442e11a645003080c40c0307260640080f044a41d00107403003402540c5000c540310703040541d5134440000700c0000350060790700c8411042c00020b104210f040c8082c829040d03804410541c006608a950442d40d54040d071035000c100741d0f4090311903001005400c0240c20b00f4600c0d0540c1034860040c210700303a0741d180405d685070150700504883d900c140362007404492 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 719332104 1250 719330854 719330869
    0x506030f1b0f0d0c0e0c0409050a0c020c0315072f06041205031b090f130b0a0e04080703050c03040e010b0d0b062109280201230307030b06040b0711 65
    0x8030042d00e4200e642019a140c0ba95113140300d118404015401500180c21440002e0aa80c000c1698a1060049040a070f484002030701007412043c00620070310003464142c4c078000490301d01d00000655090f800d5140d01404807040d03185e200da0f0440600d42443e28194908250300020b03401c0d0f22000c090500d03810107161040320744003090071103010400c051050040d9034644600005d195444008030565442034000407540a008080b242c9902504407860700707200810541000da42c1c01011100380142d10b44407001e11030703180000e80d800f4000038000d00001d00006d0042000b4006035040104490030300703543e0000640564003d030010500a000850b80428500d400d000d6505d8090f8102d8a69083c145002c022410f41c01c00d02c40b2609580d1044c0c07021070b204440601450210f0454280441130307103880c0805c220400b40c480c0300708a002503e04200905a0000b03000b04080001c440c038809841c40d241d0001c2100685002d407011984098100000503602c2d95003402000c000d480350801180a00000e400c00084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 719333354 1250 719332104 719332129
    0xa0c05030f0607080106080415020c060708060303040303090b03100e04030c050d210c091203080103050d03270c1d0a110405150706020405060c030c070b120a0506030f1b 74
    0x455201400f803001d0b0640103942030f41942c0b49490003c0c45030f03959051421445510b0030304039118030b1000961740d0a10002040041c820020b5844940407500c9407000d2650302c2c4240c1c81b0103800a1041c4505224081910008580240090f440d070300b101c07615078152070031062042e582100030802545021041150600280c403144110b42003080f891280c00031404810041241039152003a598106c290806008903e0800941202d10705043e43d44e48519016100c1e260a000650320f40c490100300b0800a4403034040c60280c04414070095408c000f1800300f0080210074001c045900d4034640401043c8072048401d80c1c03170031008030006103200d070400645100c01c683d05401c03c1c6c1c0300311200300428080e03500c0c3d00e00f80ca000038198098855844440c2c1c10b080c0c00a02a5400143e2701c444006805501d0706000406405c1c071004150071b40b04001e0f0b03039103d01042e5214651140c0c0d505030400001490141d0b80350f119580c0300001a0030b0f1824004881400d0b4140700c4030001e50310004c0c0b16004007240500704041401d07003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 719334604 1250 719333354 719333383
    0x316050904080f0a110f0304140d2402040501140c030405011b122c030c060d0b040612210c0611120a06080f121b0703050a0b01090b011805060a050c0a0c0503 69
    0x180909002c0c030300303c10706003051a02b0f0040300d03041040030401c5451008640f040c080a08040c45c850b81002000e0007070360040c400d60f40040d013110b60aa02c0c1d0f00c601d900f102d6503604190010340ca840c0c40c0000655580313a1068541040e50448882d41c004502c4d244c201c29904509030b0ba81300308084110b480b043e08041d045040c2002007168520700e08540d1000500751115441c00c5551a031201809150980a0840c1c1403130b02e6007140c1014800106618030343c050b401440c1c81044c8400c1407105481800e4a591142800c0000140b042c84c041800b04507076600c8008000310420010f4074042100c1d82c80100d80c1003c1d508aa8800c0d680e02d41004000b00c14864400080030070005840310103040c080d03e011600a6413220139510980c448884400002002000c00840d400019200d0940c0d441c02d019256820920443c01d259052101801c490342c812410504802030724081c2050301410442801242d13004001200e0602508001c1c50320b20b00c0081000c0744a59110301c14110040c0c7c103000a060510900f12034820 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 719335854 1250 719334604 719334607
    0x6050109090b0601210908040501230d150e040c09052805070e0d142112041b0909020f100906081909030513050316050904080f0a110f03 60
    0x4201442c00c5401040074a81130010141c0c1010b00d49440c0d01c88141070416620301020241003107403030400341c1308442098894004801542d0b03191001044031004802418204218010121720558032040d142c2010841d2200825180d8102400c41c800c03d54003501e940c1d40752a810410090a8003901d076108500e00c0094855000954260095124103150f44c1c0b10749803038100040846104540880e0003c00090101c2003451090130101c4844148c1428515070b0b0184550081080000f000c1102ca601002c40784145083c80c0e18820314001500500708490101d41965905402070950755910083c28603c0000100d8140d03520421180002000040d8040c4180e14040c1c081c86402c148160300b214200e007000e144940d2840c2d9010aa40011442804203902d0540303100241a030043c090710090400c11040440390307071114101a540c50151440040c40407080c0018011030074031a50082c0c0080c410800c581c180100c490211495401510b02500007a01c401800b00c00600e0800051003025280030156 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 719337104 1250 719335854 719335871
    0x2208160606062f030706051602150c04031209090218010207050915090a061e0504140c1c0219020609100501081209060d050a0b01230a0e03120a0201020706050109 71
    0x1c4606a900c425090b0f05007010782c1c00185900e90a00031900d629038800300410192400308408460106424001e10051040740003849060104608041c00b641200c82264100740c1b540c0e5420000801d654500d0707081008403900007500c03d50b68005000d45550030401c0c2c406100001e80024a020640c2e1f010383d03c1030300a1018031511094042800320020415102e4204595511400c440604550307485a141c6104511004511a030b040081d0b10a80b04100c3d424007061860006030076a10205603000318280100b00103840d280c144102c602052050b00c01c10240c1880c81c403c00c41b08480c0342400414016802400400103002014040303040100040c40b003c006550400c00720a03540c0b90004840220300c400041c0480761542c0329000c0d81c14004403900c007071100e49040006280138001d00b181c954003150311401c1e00a244580d417100c0c03c0c20024013040e582d0902105a2044640004050300c01d501405820721030780c240b900100046c01240c000f9000580e4600c0c851400e40115141644020055850070844 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 719338354 1250 719337104 719337137
    0x1030e03030112021c0507090207020a0503011e0509070f0e09010c021c0c0c12150b1509090c12010e01050a091812050412050604120201060608220816060606 69
    0x10911601603482e20703c0c0d0115421400001511000b0107011442032800018845042760010710176148281c401d0140d182d540c00a25003a07c0c82d2190008071b4620701d04c0c21591a41403030744241d0340015110112250a41d8540300c101010348c080c0c0000301c80300b0348101040004802401100b4600f000d52009101e25101d403611040d00e40c1c8504174a40800c200400c103c010b11070b682100030050030780c0500400c00c0c10a0361805042c00042010001c07003103410004d01d24850303e400707080c05491202250746185050140700c200700780240c2c0100000008034050081855040a18030340d03078042e000342071642c071940d418030041055280d120345c04035071554103286288110401070504003030f22a40c080070510000c80c1200d020790b03281c044e1780c0200e220888039407003040034450f001403240c3c02940198854000302c0c190900403402d03500c0501a240c0031806074408518402048041424000c404181c0c3c00281010b55944203c164005024a000e00c441041c600c4207000c0c1c1e92003018000c110760b003420f20303d640c8951b11 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 719339604 1250 719338354 719338379
    0xa0f02040f240f080c0a09050603070c12030213090b030a1e0501050c1e0a0309150c080a050115080403030b062a150105190905341b05010b090108070501030e030301 72
    0x100c0e002c01e640104501084074020000075026048c0103269036200e20b0900c600130601d00c001081520340c40c410345290000d84c3e009100b1624000c4000b411a40e0007400c18201c0005410251066a050722406a181c404070340444080031141501c0b403115481940e150400509484015001c4d000341d40c01044003240015074030a00c002c41254048003543c6504143c102035000b015100800342000d400f151011b00100d501364455254140a900e0b00c8059443d03005c0c001c41190024041d80300c50f602d074601041c00250003141407641c0244646000301c2c5155208011501707a4005d400e840140d403503038012581552022030f0900c00740c009054010b103044107801100c84100c9a041c45010f018802d010402c46400c1d981e40744220141c40100c2090007039040c8080000643c00c4026074100482410481090091410702d4184595040f176a80d41c000c0703d20703003950a040d4250b980340c0031100356584030300e8600243c032003030051802054440045c0c1801444e20002405685580b02501c155810070801071061546244c07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 719340854 1250 719339604 719339611
    0x301050315242103040f0b0304050a110604090e060f070813120e03012f120115030209040f0608010f0c0813260301050102010609060e0a0f02040f240f08 67
    0x1d4a40b00119100b10100395041500f81c154100b100c60301c1d000600801001006100b2908190100d60a0540d07a001294107400151001803040d00100300700d02c0402e00b815600e19501e035006101910b8940e440c440d91040310303042c81c0c80c003020360400c008200303100c2e4007001d0541d03114400d410320011500e042407000340c490201c208000c040c800540030b40a042489440440c100080181c0200701c1181c21801e40d8a00301c02c100c509500142400442101f0381d4940026500f001d103c01d04842d03010303401c0c03009008056013072070100c03800c15900b03100140300ca503104c0c0900445000310103000903c032400c16a040d0b0130342c0c03a41340c141c011050521891f17050709603000010503481004038008909120181c80c120303021b013024096082d48002d1498001c503070b14034014000c50494809070020881556601034000984043e0b11480050581240010ba603020f140c1d040049004501100145003948910001051400d5908141d41e50601e0b4800e003141040807108440c515130b1a8105602d51200c02a0014007211004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 719342104 1250 719340854 719340901
    0x9100506071209062a030302040503030d0f0e0a030f0806040207020d080304050601050913030c0f061d06090706050d05190606120e06010b0403031103070611030906070e0a060f02210301050315 84
    0x45c41c01c0d0342854443d81c1035601411005041d0381e90b40c90402003800150038020303006d02d0840c1c40d01e44820a80342d000203010404c86e91584030300c4107840842c14160380507000200a9a0029020015000182d0b40c00c0013051099100e00b0783d2036124109424201c1c034014050f08414000d21844c4203101c42c0c3c040c010202091580d0500d460f0b41da0900d2850000d010100e0184014150740c149400f40b980c180b4075444c04d003c0703400d010044669540d60010b50301c3d50390409110703010124508020704611481c0c1030b085158400e210280344085c078000c41d155141214156402000003660646900203034542030f000e0710340501303542d40052038154144030000e00144102d10008007849101148103c080c0b6007841076554590b00040c0400901c0900541c2c400340340d2045851501a000d10340c0000c0245010304402a0708032030207000c0100709400c140d0195084c3c82100400720948c42886030010042070751128004083c15140300d0780d43c81b54907200a0500c0e0505000d00700c901c8901240400003d684100f01115100a24 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 719343354 1250 719342104 719342177
    0x81f08100908130803030412020102070206030106030e160e0901061e090914010906050403080708040506010e09032505160806040b0a090f061a0d0206090910050607120906 75
    0x30714004020340f0650720b0403d9540304035500025503410101c081d500c0340e8042d58110041d1f01410104900300d101d000300080d4000c43c14401400b0f010310940c0142e400112000c01c0782e10103440240d06129411f25a88602100d00c1d03a4410400212402c0c080c030f10041829440001216641c0d98a001080c0c089002e00010182e5a400344030a215400c0000e01c41c0e00c003481c001708010784035814808054102290180c022404c900040b90b181c030310030065144243c1c1c001e005008964200b000c2d24141c000050b04d0300005200c00d000240c41c5c0340c00800d1040701035420a051111a4001d440c21609014004080c4140007840c14800c03c11040041a0a54030950000c3e001300305542d145403031781c0281144940905031590400000782000601d80c0402000f15143d56041451043c01041000022004000941141b41889080c2c45c5040400c005a0800c0550441c1140962264045007070f50300950410b03201750500300313000f400142d000003040c00a8a900d14043c03040d60400c1c008404214590140950b11015 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 719344604 1250 719343354 719343371
    0x50f0303070b06013506121507050f0d2003040b01092a080f090c0604140d06111e0306010507110406080d0302071a150105070c080706081f0810 63
    0x21a6041c0ca843c100170300e070300c0c0e034250021050f00300c81403652002e044000500c0c1c00100e45245081c4644480301c196100c02040c05001040b18142070203400340102c4241f000c20b004a002c0c000084018160035000d04c00c0014205241d42010422409000498400c1c000e0070400d003c0071650a0f0740183c156040b00b00301003948410404042e041303c0200c203054050412220003d1a600d81c001c90150140c4187d00480b40b6070b849505480303880342240c0e480c2d1984003504000804c921982c0c4e80c0b03403050501c4001c1c940118030313502d51680001e55001c4080305030074800003c0c03002100c01481010005110603005040c0c11482c1620020b4054410000040e280ca010149041281d40da1b5400000141158000f50754901703000e010702602940194104940c842d944244030744400e91000304492003088041e20a0740b02481e80b200540d1290f10031101035800c0c960448010034000c0b07041001030011f0074513036a10384c01d070b2500c00d01101d0b0080d440c0c504000fa050f2003c40800c00d41c3c2c0c000501c3c080001c19404005000d04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 719345854 1250 719344604 719344607
    0x90f040f0309030c030b01080607030e0d121b05040330080603010914060a0f05100e1308160b0f040b01030210022109010f090b0711040902060d05070207050f0303070b0601 75
    0x1040360b10080c0028900c3c130001c400c1200465000d4102c070f00810440b81c01342c031490415801e0303c528500c5964661b00c601c640340f4440344a4089030a02c2a500003000860343d4007000c145202007442c440c800b0114000050401c200400150041103800400d078045015125503980105000c4560384601c04101049020800b03d503000c1d80b01080c116030141d002450101c85880d2181c540104550440d0000d10341112070310500c0791030003401d01c115540d0341849c0c0d01c40d09150152001038005414245401444034611000440301c200030f2024a40341c00c00100c0305d4500340742c512000741c0300900e010301b0a1842d034188000544c1044c102c81c1944c7c1d0466680d031800c4442d0320b040340744c650031000c10241c01110381000d8540e109040010b10824400380c6e500d1002901402c410740c2c0d004c030144503480314000100000070104240d07141d86c0e810344500400116445005800084540d00701200811a199440003400b004c9a010003403a00101016161001c032010740c01e000988034000c0714000382c517070440c950006009a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 719347104 1250 719345854 719345867
    0x210b0109020a0e030a0302062505030f090c0a030501090b0606040b03061e1c060e07050d11030c090406020d050124260c040303080108062401030b120a05010b090f040f03 74
    0xc00f0090112a48407500c3e0400940d04c3c842513900002203800e10407100b407421500c05028503542041d4a0300d5103141c594580c010b009400041aa1381701d0702610560174426941c01c604000294003400010071644c1090500e410111005000f640c03089008010401c4401554021f80e0762041d4121560101480480080c00c113560841030301c0c0303600030800000614030820310b40b20781c80710f6805820100f00d0076984885003641d544140c010345900540d21007602d40060444841c0c0801108098160b80c0b41c801000d01243c9801810b642c2160b907140c0100d9440c0509006100c4c030713401080303044201282c12090070a566810001c4200030800c101400701403400003850070006100e80701c0301d800640902c1c5000001007110ba0043e0204078005550000000b400c13180004e84180140d607058000d0700504c03e00f00e45010780c16414109031381495112442c00c0c0341c82e0795500c100a00414144060510300f402c926105c0d08489036258003606c12141081400030690940ea003480c0c3c0541d100f806051840e400d81800e586c030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 719348354 1250 719347104 719347127
    0xb090c0327030c0c030102070b0c16150b030d08040201052226060112230c0d0c1712090603072109021002030c06150d0804090501210b0109020a 63
    0x20032040794001184a20000000c192003103101081c1d4050794200303001c25090344100780b4050548014032000c54450b0809100628900d5400300c5940c91402040c1d0b6040e00150303454800360003080d035130079408005003428440482115113901c0c140358207144c140c0c0064454020a8144118650249000038455819450401c003a00c1480441e44180150303180c01c51441901d80c00e00c02c140d005460001030200e1146101007800c9900c1000c0c0d24070f0411b102c1e0500c1c010403c002c2201c4207440b03802480d03a0991940c126603e503e0b8010100309945038140781903072120301c010401540060744200390b544082e030780d88015240390401c1211595030781e80324820210784001d00c40703100210140160702e240d0315802c00c59004c5081d0500c25110a1801d69546e44141c0e1240210400340e8126000800090b0485161403915104407400030800e604d91800d54407174001d5a00250841c4144540e60750052100086010010010540007202d143c1c1c2c40a16558170b9001c4a01842403007511900803c82180c15801003d07078044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 719349604 1250 719348354 719348401
    0x140c0c0c030f01050103020a05090c07030302090a03021e030f0c01480c05100e13150308040305100203271218041b050a08060d0b07120f0b090c03 64
    0x684000c4400c043e00900302848100d02c00d02c1030b86400242420107403001da1260300b20031240d07070402c00540c406801a520203401e40340e01800f14a0003100690319809416802610764040544910b62a0b041c90f00d00616401140d038543d04c40a00c000807aa4000c00351050b1003d040704c01c2107201e10300302a0960a901030061000d01c01641c02c0c0381c80c00d030058810021a62800f80d900d000d0381e1030350750b01400002c80d03c561611000844065120006090a111440c50031060510004484014030400034804d0b40c5a00101d503d2100040c04000348201003003034ac0711000d140c000443c034500b44505140c6410101c400060b41c03100c00c8044a041d0410140442c030441260640031b5999030b400c1c21960f800c200e4120344200d2080d0b26000e12647e0030354843e04024125903007600d5681c540300b0f40c040141d0303001c04024102a4844280b0700d5050008030351152142c010403071600c5000c0c480d03942502030415240d461414001c468035058a841c110b5a072118065008405000d80c81d030390391030b01004c0590a03900d40c02c0c2c101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 719350854 1250 719349604 719349613
    0x1106040e070503070905010c030512040c03020a0b0c0c0f030604020d15060308091002071a070623100e060a090b010e0312031e09030f0922090c09140c0c0c03 69
    0x7181640080003503106820f13a0b92520f06032921034005541d5041951300c003900094042c0515011205d03241c40050300103000301c80540b44640c0d2680000c04200c0150400514102c1c00b007003902504204104485e2068021581d21814008440100369030f25001040607206403000d0070450107100040505108020076000e05000c100c0c1c503400c25142d582d101e0400749024420f14104001c0d101d10200c0c203407040d5180c007201c4004920b1401d5000d40e56400a07401551900e82e121103043c000d00701a2542c3c85603c003002d6801c0c08529000c03a5400750703112036510004045809004000441c0c0e200c4003c0400d9a4581c2c400107a1681c003540100c0e0718101065040da01840742c0840001c52501943c09948030f03640700c19080b60b2644140e00300d86a846002d0751180381c10b5105101c0f0140c02944031014265041c0d000c0e09155920040002d503110002c00082d070510141d0b0340d42800400c1c029003003821005419584424412840e1141c02c41844c501c00070203808141201050f000344000d000e00c06854501001012507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 719352104 1250 719350854 719350861
    0x8040f0b070806130c12020f040902041839090e0a0504050705011803080706020702091306110307020606150d140610020c09010b03100e0c09041410031106040e 70
    0x24200301e5003900c0d03e0303100b8100010001e41d007200354040e0512180c00c503640c07240006580e10b030700000380d040f01654a01295040c000415034500c10700c0a00010514201559072114500d00e020085800c14190386203245489800400546080e610720001c03034500010128080e45802e00c116000246500a40600030900c0140a4441220b402c12030042d03000da02621415a506c0c001551510500a0200306c4c10400320810404940c051010300b80c960f00030000980f401802d5400601d4000c401c035642d038866164070401320b040c05041e1080c2e940b03c0c0815032203203103541440540a0354075030700104114450507854a140100c0110361055a845c20000c4400f8030018a0420a800041d01c044800c140210102010700000d10720002c1c4000d0342c900081e10a40480e4240301d002011039100419070400c115520b600010950b405015a0f445420032284050300d600001c02000706a80f0001c41e1014400d4484040c0641c0201c0c00340c080c030449a018000e0908044640b011400170b0085a011151030076080081 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 719353354 1250 719352104 719352107
    0xb15060403060c030e0105073903120c0c0209060d02030a02030102130518010b0a051b0316020108150319031106041103070b21070e040f020406030b04061508040f0b07 73
    0x2042e0742510f00e07142404482c1c00c1d040c016003200d000b01d0340400018804c04980340a102c844003076018801d002400c1240c04d9002803443e045040c0b244504800040780c40c0c210b5612601d89100303d11685c0001d1908140c038041c1c83c3c00165429501500b21441404801980e0742190340401070340c011903502900a64440302c00c0c40d03a03044464824401d85000f1042482c069000c840156156816200b04001540c10480c0700c00c03040350182c000004074a03040c1070300c681c0048010000c2014203560302024002c0714450b507141c40010b02c2440068402803900c105000c0d9180140e1b1f0200c0c50003084040b400d14020707004094101103400c2d0005100d00c040600649003400b0511140122841600c03005404454009a03240103070301c400e2050b8000380118000c0d100c039a4000040f40d00710990001058541201c0317041d0b5240000d011916a002c0503001590b000a040200035054016131020750340488041103034a00c1c002880f000b294440082e0340070481c9401c0058104080b050030b0780d070115000082c042c024074204e05c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 719354604 1250 719353354 719353361
    0x504030302130b03010503030d0b1503010806150103051501030f0b060f0403230c010e0d05060a0c08010603091502160b010b04031a220204020c011103040c0b03060303070b1506040306 80
    0x1003500c500e6202e05008203c80c0e4100084a04850000e0001d42c60b160f4844070f003000410b0104030b181e0740030b01d00c0c0d507030111510308402c080d5020b0320038000a030480303050000300c0e45446001e0380602410b040c24182004980c1408401d0900381400138200422080d0103010031400400b1900c100641c084404209800300a81ca040503109030703440340c0301b050302280092000d040044100060780c040c50344545034400300c951142c605901400d1000d00fa02c201c40d103c1e03039501400c181e4102c80c900c1003d41e07102405000964000441401082641010081e07544980c40c0e1920180c0848504104641c00085032a581062024041c070b4440c0c10078080b019958540c5e041c1c80680d406071100380e400140c40e810409046600a038158080c51064441c2c1880c4200d00e810001980816441641e00640c00d0151003c3c1140070f0066000310092641030503034a117011702e0f0207185447c0c660400b01520300d0500410085440000c00c071070240313410a01c880303038656510f0301d18400208007074503881d008100400e000003081590341 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 719355854 1250 719354604 719354617
    0x92e0810020403111503040f05190308041a100918020a060f14041d060d050105010801141f18020403061a1806010f0e030106120309050123040512010e010504030302 72
    0x2a81180d59480080400ca00410358101c5c001c0201e40400101700024070140c44e44106e20301c10001d841c034000500e104a0000c0c03000784810b401040701c0300f0030002044001c04010401d6002c2402c403041c1c030b0900f40312400743d03d412401180450b03a990400c89151a10040ca56080164001e0003e0b83e191b4403000001d000800d50450040407400d181607402190300c0e01419141503402441c0080c45000c0710452200f000f08014001c141c02c805d6401000300810030a0041300d020341424000030825000491650304880c0004149030382c0100c1d0810324410300600d41204004844480449265514400240c0002032040b0346c4001c1000d1f2800d60014a121103240390388460340ca0450b694682400040341d44e103c0d80f401120300c580000e403103245500f0000c1c0119039482e24800b0180001442507110362880813040e040c03d5003600030819481c0108115a4000000134004040d400103464007101d40711000450f00940c000e81c0d2003080554442d044072700d82588000c900d42440c5000344141c1c02d01e1304015000354000c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 719357104 1250 719355854 719355863
    0x50a0221061003021302070807210905060c030a080402150d050106031109010f050a27080c0303070c0308092d01020c0307050a38030a0506092e0810020403 68
    0xd00001c1e001d01100c070009003101d4010702174550000ca88541c540080d48000707412170303000070288903001c00310301c90021003004030004809a042007507042801900c0c0703d07180e60003140328460030071007001c24201c0070090303408580580c01e01400a071640c1c400210b03030a41600c00b028a1440104141c0e003818400c0d0001812109652401c10900c00c0807802c28030148694100c4034041080b000151500030b11860050041c103e030f03132800719035079401340b2420040b481596145601d07100d5281401d110b042e070144000c25580304110011460004140c0e0346a0200c0460311015100070740c007155008854640100c0c00401e4000c4c44024182c841598490036400d848400005005218042d04600c10341000030380c410a0391801400c0d070601918107516014100039068950f40c0303450542d040a02144110305c2940907104441c08807a803649010644e98080703460050083d8841c9410100340b0040c8040708003070254086050303041041d03031381a403140c2e4107080409601c98002481001200280f00d40e5a41c050b10549108 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 719358354 1250 719357104 719357113
    0x20a03050c0c060f150d0f0215090306010b030a02071a093007080739030308060108060a030b01080a150b15180603070309060c03050103120c050a0221 66
    0xc000741140036002e41440318203103a10000105140b81c1c50203031000c0d40480050540142c0c50180d1000c0380c1d00c040c2c00d901c1200e40300f40d03400b20b950031440c1c058100701c1c2c40c08094103c84e0a0070740b0500000c0d5116418490f55450080000c0402d1407819243c040342c0800e500120084034907070b1141000521620100d410074064024070340c545090314040803079000c040740300c414841c680118142c0740e000c0d0366014910455004200304030000015880034103210310701c506142100c0440b10a502141c85010324059000280e0750912000e100090b001008641c102d4400c1c03038a407007a540d80101041201c40c0c10340026091110400000509181c0020302e019000d01c82c0300304015262511071010107440700d0220040d44080b98880b02d2103004010030150808e0511106020010514170000c240c142d8820b46140300020340b1409000103100250141a24242c054a01003080e036140d515400c800024a8030824100500721312414203201d0100552001103030020200e6000e0200704c90307080f002504010000c00c0c103004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 719359604 1250 719358354 719358361
    0xf0403150504030905010f0e1002150c0f04061b020301090803061002030702100e1908030310060216050f0307180504020307050a0b0901030207081204060b0307151b0f0510020a0305 79
    0x241c01964000e82e4561601060f050410b401912445280c184880811189003110b80c1950303a4103e00d072003941c1e807136009045e540ca040d15504081030750081003030041e0401005003200c10070200e4100c038211422440e0a842400000241c045111901c641c043d5041d820141504c0900040358001e500510b0308650000510040c00c0b0260388070302490340080e50003d48a800140d4860007215846a1884001d08494204600d000307020315140c1250061603480d4004005c1110341c09100d0865009440e4030700040804041c0c1d20b030041191500d0340030755070184d04070308506c50a9444c200442c001030200040d0541900104c588020002e00c1c00f22000d034400d20800d00c0c00612404c0a400000c00d80b0a060013592030030060400540203540704080488455204124801c8110902201180540e00c0b034180414040300c120304043c941030301500b1096032510724603068001240c100c1c035552081d1882c000541c1d04440d9a0030030451689444001400d2405000b090351080c150950083c99690010b440130040e644 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 719360854 1250 719359604 719359643
    0x80a08090d0210081014091303020a051c08070816120f090f1106040b0706020a0203090d030f02010c0206070c150f0204030b041419061a030f012c0c01050c01110f0403 73
    0x202d206c4815500030300c0c06004180d070701822111b1010403600900440b0760b0103500c0d554540c40c044d846019514014225007014240301c0c0c1c84554a1b4020030145031007034650510500b004180710102402e081805204800d05021318105c0d00201651a09040c0c01c018444950421003011940408101c40a082030b00c250340c0a0714002c4107550550b25a0f911903420440c15a0700d500c0290b02c400d014100750311003840420082c1d81c8034902c0c00000c0b8460354403205100d86900d0080e0950306442600c0c01950002400c01c8542e5030b010f004240a0741c0c001d07804680c01742001c1030310001065402c00c403020742c500005011051081c010b0750a400340f441100480c5004441c0c003429911621a00300040e5a84106002e0001041642c0c00c00440358140e011004581c48802000030310b03101c88000c074408940d442d00400212034080185190f00c161154800b145041c0075040c10507280e03580c42040905000e004102030030000425401104900315892060755a40701c045101c010682091104451500b160f010340140710 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 719362104 1250 719360854 719360879
    0x91503060606191b061a0316060e010c0c0f080d110607080f0a0b0a08011a01020a051011040e04030c0605150916050f22060207080a08090d02100810 65
    0x1506044440d6400904400c103c0740840c41141c1580408140d194031130101d801441429440c0d0b4030104042c43c610411301c103060030000c0e4110080b5190b002e4039000c001c1070b84c0051250200301800d02e0543c00d00c20441c0380c00d0f800c1e02603d8000300040300201d035010030247c0e0001100300700780d0525100ea40071109a500800d5441000f180c0001c00240410049108603603210030080e082101c0c6c2801080049000002c03411040443d442414103a44580078981000341241524038800c00a101404402c0b540d612029681d5401c6840c111000c3e84e520445200d4461490540d4054596a034035412107007028100201401508941034a1252414002c038986a861001316408908050602e400700d5441c2c41c000c0d002001c010044809001041040d04441c0320910300074140752950408841c4200e041600580c15540d640d04040150740c0070f044140400c440000e0030b0300d8140d50004032996200000c80c0420b80708124032074020740084c01c030f00700590f075141c11940c07061140078142c03003070f0b001140c2d0340302c000300c50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 719363354 1250 719362104 719362117
    0x10815240c01050603120408120d0e0114010e01090b0108060d02010c140a03140a0c060c18030303020304050d050304021c0f0c1217090f0f0d1406041202010b090a1a091503060606 78
    0x3107a10035460f649e400490f01014003007840b8080000142040340d01c007030500396117002d0764040740b540301200117000440c04019403e0140286210422803513500384000391020402411192081c0b09404600f401c43e8410012026a41c1c0c1c003d043e20003240071313480010351f18103072003204901140442041c442c0002c201c00036102c0c001d04940d103281050445480d010010300f0726100d0002001940c54003a11034861242040006500c6540c0050b41c038901410302c40d0800186140e00010400d080060201694071402041c0d180b2812802407001031505243c00e032101031140708001c052980095000812056491140c40120300501c014280042d200948050621071441ca0310791015922490668505090301020205c15002d098405050003e8580c05034441003030400c80302d00d9101c0001c100401c054810503202d90f8500e400244801342d011000030380700d040000c144030301807503540100c40540580b0381d203046251200a00010498101103000c2c440b0000f4044100c0e01074400c00021070f0090600c402140c03174 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 719364604 1250 719363354 719363369
    0x60912171314011b020318040536150a050f0f0a0e15010b0c070803121803071505091207020907180803041401030506010815240c010506031204 63
    0x22040c103640e02d0301d2094040810b4409559602e80f41c16001c5112041c40c3c80d2290b480d50000c2d52941100101c03e01c0501e908000c1c103006904280070b000c20700b070302042e0a00b514160088c1c01c8404113240141e81030a05040240323009588140081c005500342c1f0b064000c1e000798003800040c001e6a55420351a0041c03881910b12910b0511030710b001a821182c15030101c412140d00d5030641d190301c80d621401400e255000e80200804400015449000000802900b00100030304005941014410a240101c80000616040b0603007039020b280150440203004440c1c440e81c3c0407485001c80205203a01c0402010101c4040c0c3c02c4e40318a8105010740c807030001c20f44a0040d8001d01c01c4400351fa6840c012a1000d60492015024003840c41010030031130801d2015001805c1c043c5a190034412601c4001010f0340d0b00640030f94144442c0c1014403c1c4e00440710203403c0e01b8202514085014031041c0e8084030140783c1800c424040217001320300c208240070190010340c004c3c0c20403001c99036001c05c0b16440c0141d6100d90300c50b108 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 719365854 1250 719364604 719364631
    0x5121c03020a030209090c0408010518030301060e01090b1b0d050426010b030601060807021e1903050405150c3313080f0c010f0e030d05060d06091217 66
    0x52520030340007001800300a00c0c01600307144420010a40c252011354103441c409402007030071300c0240f03002d1048a80c401d000f8030b00c0448004071000b2051b180c2c401030140c0070030860842c0b450b031880d034000c140600081803880401c1e40d13500c1c101c4154003500d00002001d41071500410351f135410394900c00c4c400c4e203059a00c1942418030b6006482c244824180341c80b04110410f5483d0302e80304140b40d40c2448201d00030500c64a82501c0e606d00b038a8000d00b0041010034501711110030f0a8403a10368500001d22106401124101014003d65400c3c2a1400c2c040ea601180e41b1150001018102007480d40140c5085143c1c0f108072081c40001c4110481100040900c20b403801c04007121142403102c0d42c000e1181c00c0b04501c080f500f100e0035540c03100c03075080d4440c89401c448402d0000d074403038030880b09210b15406040354240c00c00c009030300700e11401c5d20f912400c400700c0e0b111a10364000c81e201d0703a5130742c4400010036444201003003050500c0c5014205240d42e00c004401003250007081c0e9404003000c400c1ca5106601000551 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 719367104 1250 719365854 719365903
    0xb01090501051c0504050a0506071b0320060703060e13171303021003141b03070f11070905010617060d02040e190606080f0a1523100512 60
    0x448954101080001540c641c888080d0f0f07a501c11480381d203000d6070142001d05003200389420f000345441c2c0c018001008101074400c2082180021201410000d90f0501d41201c400803040000c1d0303506141102c01c80441e0150000f40604540c15900c04011180c0780803a5080319500d00741800b00c120600400600004035a02c0c424036004002c4009140d15100015580b400716126008202207a00c400001b40c04070781d4800c0c00300c42c201c01002c941680030090228404030742c3e15081d103082c1c0034000a043d800a0082c000b0201c0d80850045005001020f8401c0480e50304d9980c80940c40050002841400007149400711381541c043c84055040d445900043e0218440140c16403d200051018180302e03110b6028600c00d20580c002c60f900c008008500580010420030305003e050750800403c2a80c420156221802c4400020b1b2103981d40c007a10440c00100048041c111181940c41d801280c8007c01030f08110010807001d8500741a4801c280d80042d600c00300000c1c090803441d0380d03031250141c00854007440105034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 719368354 1250 719367104 719367107
    0x7090614060702030307060f020324010c120201090516060806090c041a04031505010f05030f0a060b031c0201020c070b1c090206041d01081510120611030109020705100b01090501 78
    0x5007420b61011301140e24000c217a4807148222070500380042c0d002a0000140154060300013401c00c0641c49190701d40b240070760b0410000e0322019420030010300c0700a000001070300702c074001e5010413101178020302580c0c410134028540340080703040350113043c0100c0d5501010610500385200294807480950451521341424249605422015592520a41c00e800c01c00400020f03a41c42422401da00e020502289550500204e500c6002483e084903000350300a10400c0c1103a24009002c4801a81003800041c80201c40000310f41403014a448074203110440342c00040c1d41e20b0b81580180601c840d15810b544095445d000b024070141301b0088590030034501210160044415588244151031004100c00d2a00355100c4400620100b020268012800030b1401001000428000301802c136513410280c20240c9041900000020200e004001c40c400a11000303004100607640008a424103095000f42c4035a5258100030280d8406841100c40d8050f03054086152501390041d04410f4034147c440101440c1403000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 719369604 1250 719368354 719368357
    0x61203050d0f09050312090c060d0f0f141501050a050403080903010e010c02030d05100509071d0619020c0306011a09011b03181203080a11121005030709061406 70
    0xc410881c141d407104800d00300046842201d41640c851406103886641d01007003c507840900500c544042c1e0804000407855640341c1c0211065440b00c403000184039030740320080c24000c0500c520385043c0b841c0b8185207500072011403609184140741c4817503241040c030148001143c042c052a521030000c100140030a0000480d400047c003090080500002030703a140404116007961448400600542c03c0060301d202c000446000e580c1c3d0080d8070080f80b580c90351408002c54032041c030062414080006241000301c1c1282101d240c4901701000500c0785031503500d586103000803104000c4000d0003510a910390004030b4240810714a0480704041c541280c511820310304152140d22100b410344c10401c40491180c00c148410b004407203043d00030b0b80e03803089545092901241030000c41d041107000c4601401c82c4000a54043c001c1540b10781d03c4034000c104002c0d000071000040c040c078041d034004450503100704010380d100503038020101c40048048440003541c8614081c01c54401c0d0242d1a0703240c109030320603500703810700c0c50 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 719370854 1250 719369604 719369617
    0x16060e10020a080901030c03090b04060e0f0c18040c0905010b09041b08070e0607050a0c06140f03130311030a08190e060621100902010e10081b090a08010b040e0106120305 75
    0xa01050074440343c7d86260343c80350308407030403682d0329600c18484400304370400030180310590450040481503002d0000810000603012400c0308405140e00040401c1294a0108010080d01d041400b0307558581c080803020340c11010496000b00d161003070030402101802c40c1c18003a8109074a80111903261114226502c0c810410003d4200800300481d0000070380811030010054041d00c82d400000741003000050100c85611140c08089409008a1040c076800c541240d403c10003034003100709012120b00d030507107100100c0951002207000100702c9100301038003e10f04070f01c12010880d04100e0358007000c48950882d402070039803445a90021000802c142082038800407240c1c440d0b404410000044034849140049044c030340d8030380d59140c219440c11541c11005d60803000a084525100102903403030001c1050310001d000075008210094110f0f03c00310250120745007514040d148001868507440c1181c0a400c00c4001240038a1402c0781130841c01e00103200711420f984044100142030344160310700300d4450f048907 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 719372104 1250 719370854 719370857
    0x12140a09050102250c0e0f0a02031f140f060c0a0212030c01020c1c140a030b040b1521010b070f0305090307120605100e0a0e16060e10020a080901030c 66
    0x700f15054540b80e40c2c00111844c080c0c00c0d00719a034603441a00e0203d426070900ea0118003492581c03c107015844030100306480c0e00c02c110a00051700c0341d451240351072854100d644a50740e0b4924510011500012441b9a01c2c0003c00a4070b1100484078440140150792051b8995074041b0380114407076600515125240ba418914100101d0703041108091255003240d01a28461401da031000070600c43e6851040c1e052503060300f00b406c00c542485040c1c11304000c20b00c0f50140460415a032074200d10055a10b60380141955480a00911905421440010102e034080c3e400544c0c240d841c140c0740410a4220710300300c6d040e1240c4401d40c50074490349580707100c20b01c0030a220482c1805400d1010700701c1c90328100494801800010310280352041c15042110031a100500001c1582101150a0000700b40000105800250340080010410700464001781490200031a690540000c0080000c4103588840c041c948000708540340d1600d01c1d11110b003603030b13200000c2400811200052000014560080e4807640c0000200e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 719373354 1250 719372104 719372107
    0x91218170a0804080601180b0f09130b01030302070f1e05090601050f033d0302060c0703050f010e120703080c13080d0206150d081606110c03090112140a09050102 71
    0x11a0b0320070007150400c0d04054510b5201000401c0480301000c03051a150401c0c03032080109a072586c3c041a8494600e1681d035010b42910030103e20f401c009002c45e0b5403080d0b00004030400d00e50b103925009444080d1841a031000c081683d0010921700c0100c0701d1800a401c1860550001b1458003007403240b902e1004200f241400020f01403420112400c40007503110382d0745071402c88114800c9610b000c140101c03c80080030321407544890641c81119000203a01038a40454400f43c0b60b03180030400a1800c49580c000602501405001150500f0150006650341480d1419201094061554003120b4019441c003e00011070311800306242c048440004d080030403801000340c92041c1c9a00c0700a241c80926420180140d0020b0100a0070306807a1108000c5810201c1300850810529103400c000d41c0a022075000c003004a84640b10304010740740d80041c840f9001e02040a1700c0b000c41d1040c0c0c50301d1b030308112503c41c08205040700041000c50207100780410f0850100c03c02056480b0016039600600c0340442c22540742d0350 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 719374604 1250 719373354 719373373
    0x109090510031506081506030a150b1003140901020a051204080f0c030d0b03060912030c070203250e13030c0204091704091107111e0a0909121817 64
    0x80700c0039080016103d444003140321460311030110310704103480000310007545050b0203000c015540410301341c0eaa00d802c20681020610214003040040c48114070f07c1e035100305440c1400380c1c01a0160460703059a0310320800040156035031210702c0e09034451222400e0006004001c00703100ca0f980c10300d1094001d03010f00401030070081e03c5000089207070b1020348040403e60000c1018a03d03051207000d0300c00040c1e03003540a032081d401c00000c440e659001c42c01c8a0f0004e050041b00007140426541c003604d07580c075001412240c0004001030b0b92107020403a0400507142d032813a000b011a8a02d076810071540035a003401445c103034081e8152012907003104560b80403030780b041d2148150404a2804140e5580312080399492660b524a0401c00c48101c0e0403050780c0c40c07403003501403003050b0200d07800d40140d80400000340c2e50b0484a0b03c000900344100880040704641c80000b17900081800c5601d1380c401c0101324410f84080f480c100d01c424094520031000d61400e42059940c0000f071010ba8810112700210003200c40441d1034451 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 719375854 1250 719374604 719374613
    0x3020a200414060f0301060305120a26010509070c020306130f051203010501090603060b0304030309050f070b1801020f0c01120b040915060b18100e040515031209010909051003 77
    0x110b10810380480c141e401c00c140181071520444402c80c0520440080008503c0c540d141900c0758201c180700800d50002240c0184464010140d507003114420072100b4204603000b007a181440c00c028011240201c29207000900c03c10301030510380101603001801800555030703c41c070100c3e1a01c114607044940b0811070b030301100011002c11a13002e44041001d1915100e60424000401020456000100701070600b0341c20001c1c13000b8070080340d8103c0e4040c507006c5803094460900030b1600c0c140c2880c0c98418800c54400041010041002d480c03c400302840d800701d00c3d0045c41c012a80c41d400c0070360703802880d0086210300030150302800c1d41c052600c10030600130540c5582c400008040740d00b00c01e420b0b203000c0c40e503046c41148262548580c0c0e0181c0307200c2c10344600300340034031034215590342c007500c0003034001e08035213a040b440d16001c1c520421a110340140b041c0701c0c40c600013103106a1024080c1402d4001e02c9050380d82244c030741d160011388030040c1c07060f514501132510301103900c00644005000f1613020f550220002c00400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 719377104 1250 719375854 719375861
    0x405190f14010c0219080414150a0201062c0604050907080a030215010e1b0f0403080a121103090a1b03020a0b0a12060501090303080601030b04051512010903020a2004 73
    0x9107640000a440741e20b40034043e0400800102e8038010060a00070000021955002d440c00e8421582000780c5000c0d80c1d00108031580144034449082c0d02c004610180400c2d815042441541c0410f207002c400c8a07070010b68801c0c00e010ba22201d54174401c07030364006020303400e19600c40c039840703000b5204481d12155910403035400d01c08800401e0380145c10151080540310141600c2c280113006c402c2e445c8045180a010541c10440301c815440100b0b41c0000381f0890b110b40d400d050300c01542e0000401e690341c01e800c550180100704201d8407689c0c1d01c0e05290001c1004803030f14080c0c070310030346040300500500d00c0c2d2603650800100c09200d41140113030a052011025071a092401c10140c40889202607540c09800b0001d010414505030b0307a480382e806d0000511441c1d903c09086d108903541810400099107a03100117034041e004a186013500071b89403000f04a008121108a40c01c100c000360759610f80340b800701c01010309841f20000040c0269102c4107248002419000540c0c41900401010644004240d00001e059 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 719378354 1250 719377104 719377133
    0x418091a0703093e0a1203020a051905010e12030703020f0c010c032426011e0b04061d0f18060c0403021c021305060102010b0a0e0417030405190f 64
    0x503070741010000a84a0604c1035015a901e8640c0245404950300058031185860054400c580c0d45060f4582c10503000f08420348040f680f00c0140e415040d20303211010402c00700d0080c107a901c1c2d824030b4424044c03803901003411504500781720310399491956026800d4010b0b501c4200703000803040f0204007503045080c0038881d4143d501e10999000c0b58225001c0780240501010001e00c1c0401410301c4000c00446400132045503a400280c21100303c0704542c181d0741401040b1039020580102e91604002c0c0b04244950301014400400711000c0000ba0707161044129600c24622038441440c036645c0100f03004000504005900540c03d1580c8038450300300200c09030415000b40c81c1521510004541030045151000d051546107900c0120540c06082c80d030000380c28142e1900c164071070160f03a000031030040d034802e41140140fa800074002403a0143d41c3c0700560b110035012181900d527140b940b010401c4905240303044a001d0754028000300840b001d12803c0c4c40d50490324410071100c000f6003c01440004a080d04d00f54130 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 719379604 1250 719378354 719378393
    0xc12070e0f04020a0e1312030b030a050d090605091302071b0f14010e030303070f02010b180a0506040612080a0c0b160801090e10050405210418091a070309 68
    0x7080c01c0500c18440c2d0840c0c1500652201c01c420810003400621002e590f55180d900316810300d405035070200040e801814030980b140e406008000110090203400905400b4280c491368821003001d0341e0718822039290184410090f4043d4034030502000c0881c0b103801815400b0f010312205145401400c051460201d82580718007640300702d048081040c010280d40c2c400c1906d000b82040c0305003c00071400646c032807100600440901c074540c040c02c6000c034801d62145069401c040d081090703020f03034410b2010240c1d02c100c0350383c3c134510700340400035006092030301498080f24442844240d0140040c0c2d0b40d00225007003a40c0b01402c020411036a880450703800800303a801340164a009607044915904020517540058110308041760410f600c03d00310a034000382e19001200f00500004040d141d519040d0700700301103251400e04071105d4156810785100b504004104840d41c3c540590b03408820300c00c2d4101a200d0418000d88021201d20245001c1400003228561100051500045050b01503548402d01c1051255696 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 719380854 1250 719379604 719379631
    0xf092d070210060e0105091003060e0a15060f03020d08190906180f09110f07080c07061b0602030c0c07090501091802090109020903030c01020703020d080c0c0c12070e 73
    0x151190180107480c0c0d40540040c041c8401d44c1041426200c2d02418480e06016000000000d80a5540032800202465005d4400e204004200806640d9060032880540317400c0d044200d1101044000d210f400c00b01c4004a520700100d6145808000004600d02c0040e10031034020070080c403214610b4000c102c0c00c03041a880c0d0341d404d24103100d4000c18543d2000d282c107002803e1620140010150340e07541808480160501150724003598060f10820301400c41202808103010440c00100f00c0f10304040c24a0300c40d00b800321107401d6929001243c1000d4000f07004401e4980c480101008101586c0066920000030180240f0703044104916920b060b21541c00140c1d501d65940040c440085d1134010034400785146041e030341c090100783d00040e00c400818811003407800d90009010200391806e0054580341c0041038000c644400c0d884c14041c2d01e44503400c1101001840d9003001543c410031003000d451015030260000e14080802809002881403c440300704190f01c80d00c030b8001100340380501e120340701c0c865028120707 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 719382104 1250 719380854 719380861
    0x1061b05060412031d0601151202130302040e0721060618060911070c0e1003022106011715280e010507020d080708071205040302010e0c0306060f092d 66
    0x4045461000c83c5111744200301d103550441c48000180c0394150303103810030060403885180d64280c41013661f02c038462024a001017020710020504144da28200c1c2d000f65001d20061002e038080d561a0903340c0901130024840500440d0581c1c6040d0a00362590b1040a002880a46075201005981c8074221864030320307a05c0c2d800c1441f840440740200b22084180a01050a002e403035039840c041104036006040721400395000080c48200c0754002036000310340207842684540000680a100c083d9400741c040b803988180c81c000118540b03a1403007010035841200242440840c1002070450046001e400c0d001500d02034a0a5909030080f102c01c074050040c004400501041140c00c600d00b5540e004100300123540041c0c000fa4a0315400c84140c907400002071400140a541d0580e0589102140791074081c122403030704081104140e0150301800f040030003002200c121504980800d40e503644110750441c0c0040b101100c40c4042e043c0301c03030300680000c10144001040c080315200c444900c0400c1130155036182044060 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 719383354 1250 719382104 719382107
    0x9060204030b0f0610140a081b0316091203170402010c060c050a11030910180306092a080c0607020f040510050909301c0213120b01061b05060412 64
    0x2103180881d1801e245a444030720301440a2a40247d4030140d0500012070002011411004450045140c104940316124100403407110f9100c816441d500c0d0110349600f1020840480741c40c0021280c5030306603500c10541120341c251505030320028004a050003e15074000d4005400ca000303105102806503549501c5201c1100c000b040390002c03040501070ae400400580201d45c450401a400e1505c9900b455107541c4850003a00d21010029800a8a110b00e000b03c00d1041003283c107469003401c681007030400225000040d045c210407250f4440c610040d40b0039100390202c1d0401901600c00369000809410f400301100c0d011809480b4112000341e400321401e94180050f15007054150b80080c9000024046100c015400f07141c50b140c041400c00302c2c01205c0903030382010301c1c103c002ca03410f4420000218a03c03c04a400c0c4601940018074980340e40881d10401241c44004855000c00d800d070054800c40c4c00e41d00c1c01100b82c400b90f071140036103c01d606001503110042082040024020340c031a00c10b840c0a40c540440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 719384604 1250 719383354 719383369
    0xc092223010f0209060a23040b0301140102010510152f0d11060f192901031e200c0a021309120e01090f080106090b09071209060204030b0f06 62
    0x3400c11842c81405100a5501c85c101540c000040c5030602d408201076481a0300910794043c042e0f0383c58048000340c04130b8007581e15405141228805082200400d401100681c00c0c2c0e02e0440e103001900c80b0f04003042006c0036200440c8810b4040600302030000e80764000c030240005c07800800b41410305842051024401c04204500b0745020610700e40070842c0b0b074031840580c0d00c550011302400340c80b200f100701255425640d06200042c2615200040100004608960302e51506e0700300e59000d03003d04032085101c5035029020f10001000140d00200200c9904259600101929180032404000d800120040c224098000704a0035035100020107442080f4030420030300b10780032a0b610362543d05001160300002e21a05101c4c0b05070005051605130b810407c070048030451100d0744006440345134000d0005401506504c1042545c490a400b4800852103009001d41414240c0c0c00b00d00090003c0b515503405e039000d500042c0080c1c03141501500d003907039a480342c280b0400159403c0580d83c4505e014003d40742741204 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 719385854 1250 719384604 719384621
    0x30a120b10260106080a0905031c0b0108061906050d060306021b0601050118090c14160201020c0d050c060a090807030624080d0f030b090103110109080c09222301 71
    0x200c2e0a00d960400e00001c2c02d010b03000d0101540b00c0c0e01c0c0c401070340c100034040c41070310007042d014002007180d080060070060180c100003000780c5c0420704000101d0200e0030034624140018896408103c0460325250f022604c91b446242d10011480e5140d001000080740d43c001450341a2402481101d00040f94010394201441a8860703030611031420240e0007240042d000035030807138446010002d44403001840030340f62200c122a9608000b031001079a00c4000c82080c1a0903040d0b4002e030300f1210014492002d021100e45021005041c42e0300c80d0040c0001840d106e00144102e42481c07418100196407416038610f04680c83d00115019a110810446a0b268100c1d03000904140c0c0c0d04000300051400215984036103030300c8403100c01c1001940c41499064000d4211503540c2601030150000c41d0b03900d0804c200c801041041c181d0016110100000c0c209000094843d01c185000b03107a040d081d158031504044a80c880c04e01c003207008441c0c00401010411040142d21031804a082c540110b00c0c62010540c210361424 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 719387104 1250 719385854 719385917
    0x204030b011512020a0c0204140a0606020303042a09020c0c12011a0f0d02060706020d0b03031305130f02120709120302060a020f090a1503050f0405030a120b10 70
    0x1d03040b255400758001c000e0118010780400042c1d58644804040b2000c1c1006000030b0340003420550340421200b54200c0043c131030840b0b00e00404c0032945441049031079100558001d03001c4034a100d260340100301c2001c1c0d070b00c05010b207164802c50425616140c800507a0442030846d045600094451021810807200e01c074203a01c03220b0300802541c4000402a8161404849118052886500c5d8a00f00d030f2503a448210010350010b00441d00d56805282410295012044841c2032900b4901c00c28510308000082d10044c005901508c09200d08040074417032042c000c03002200e4119202c0304986154217061009018000843c0ea00f000f080c604440080c100165592001d0894201c03411441d020950101d8442e4010000c03010250f587c030500741c6400700c5801001300c02940800801d0000400280e034110300403141807142c41c244141c0d030b94040c1407400804115005040303508200b00c0600e5661080d2412282901c00790030005040301c2c4140843c0d0340421442c103850118601c4032050901c401300c64607160030500d42 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 719388354 1250 719387104 719387129
    0x1106010b030702061503031c0509101e020c0a02040f3905070f0b0c040e1012080c16120308180733030b100201090206160203010e03030a0204030b01 65
    0x81c2c81c1c001c0da616401820400d151181032a1104199414012078002000402016040c200745803030520080070165080c2840d0b100701e08000c0101800d50282114550081010f481e4500c85030300114081e40c804007100d401400b54030f0f02d0000503622132290452118807180005095400c000c3c0403550302c9512511300d04025002c3c102204050003050b01c4072182c808070319101d038403486280341505003203442050007420741c181541080000c03000b9001070000c80e00294200780d0303c0c2c1c03100448441d1041c0c550040b40b002008010007140481c041070020f0131800d101108031030000501004084402c42150084042d2002d82400841030691024080790000d000744402c0c04c41c1007543c0066a80d824141c400c2a81d080c1c002c07030300b071038240c06090300704600d00660f030803c1f58070704800d81c90060007000010515440b030070000c1000e8110b18414171407034480300d5010f40b1325031520161001407115900301810499140d074a80038248070005084c0040c43c00344150040c05130305c40341913140100e2070401c140c00800541c2c84 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 719389604 1250 719388354 719388361
    0x308070b0f0f13020114030106050319020c0c09070c020915030c0405010e06120a0b09070906170a060b030307020d0615060f0f0f030605030109113d02030c0d1106010b03 74
    0x3218000c90341041200c0b03c00c0d07904006620050f2003515020041e080307590700c00b00000900f2034000c0d00451207408051409010300d003842210100724040c440e01e2036102c1e4881c0900e00c0c50340c18080c0ca195004502800d01021001c05c5d54002981c02c001110824944529646101170701c2c20304000404002c00d044606000a40c1442015041d20354000c28481c8117030b200d24400c1a41c244c051080280b0036421060360380c400e103000001140e0b5050540b10355440c1e10b18100000030a04000d02c40550341904980190000f2840c9031902c40c050703d50a0304440e40340c002006600d005903250844007021520800011940c000c0c9885030400b00007ca600c51f0b400d2000c0c04080010159105108461040f01401d10044200700d92008038014561030300295059841c00841c4000d110740c284000410b54000c54018a81101101e03c5105503100100c000c00040d02260307441e1742e0942d050344480003440d000e20480e401d15203003108013440d01c524a0307045004107600203151041c505040c08000c0c0074100b8407840519504 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 719390854 1250 719389604 719389621
    0xf121b0e0f1f0e0303031003020f01140a271e0f0f0e04050114010308030a0c030204060210110c1e0d020109080d02180a060216080109030c021e06040308070b0f 70
    0xb50250200080c40700030030b8001602640002481c014050126502c0e860a8001007013402001e001c00c0e44121140e1036510a10f40c4609900015640000c81d66400c03c034084209544070109480c0220301c02070f00c41c100810380007104840c0401008419070800f07040c40a200c010180d0341080c0c101858140f251113080c00030303016801c481da00301d84414051402c10307078131400d000b0700400c01c820709201d0040c040d100000c1072102241c050350045203805c40800c40c80403500c405408903c600c1c030606000d078006c40210f0204a8550b40200380c540b1402c1c004030b02e0208915243d07803c09441e11403148411081440610700b1190030003400c3d2500100d40020400c138440d0b40c0394a03601c1e024910752040e480c0e40002e5080c8418811051108400101030040d41407e51500c0d0060344400d04505809006110704000240c0f64405006914020341c144d25004441603440d020b204070f21042450b0120080301a400c100c0780d03516280f000340021030285c1440c03500da40b010320b4203450819010700202d140100c244c2c24401c3d0780 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 719392104 1250 719390854 719390869
    0x21b0d0f08100504060b2215050f251412040909050309031c020f0604110d1416051309150e1203040c151106070f121b0e0f 54
    0x400d501d040101180d903a0307000001e15180680c00040e042801d000c0000f81c1c2100d4a0080d100e0610703120340402011012490258400c8402d1140c0a0041801c07140c44280c180501d006102d01501d9580341447c06c0c5a0b2022040590551800c662020410301420014001100740a907030030309403100076041140b500c040352a03550003140140c0c2c10103035481e440041000020400c8070b4a144020781542d0800d0711a129501c4050704039071070701c0d0142c054010107445030000030407000d00c12948800794401c004020418810401d91280d012142d00c0303540820340c079661404000b40250030240101418100b4107242c00d0105150ba02c0e11030340744450401c0c07503180016100c607010001c281d091080c0050010900c00101b468038080d80f030840c00e07081000040c8014007920081c103000755a40f0110090400d030008004450044141800c0d8080c0d401c84c41c0420072a80c031500e0a56008030701441c18645031500d800d40c01c2c007120710915000c03440b02082042d072020b46800100c10581d0180c22290941e180c0c02e00c00100e42c01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 719393354 1250 719392104 719392127
    0x6020f0d081009050405010902010e0301060501410c011104050607060b0114070c0302040c020303011a130e0a1b0f020709050402060f04030507090f0b0a1509080d03021b0d 75
    0x103001440c0009421603400050440083c154144180b0081c02c2134207059008040550003640051010310441c200c5040501072081200e0301a550f01111406a2441c00303041c4614105456040360f115010ba8504540707080d5034007008002e51102c2e0b039500759101c0c0d16821503c104030840c1304240240300030046541ca05060b45d1a4607006140031905080c01030040361031107940c40b03601214440103d810818007141c0010481624800d44041048020040c82642c0e640000d01c80c0d441c003502200100040c010880b400760084030591141a0b58040c0c4590034410000340440da41c0c80d40c0c80d0b03681058840028900209044a509804c000501d9041440000d446071f1080c024511125141c00200d000c44d10750303d08840c8140b040324141e40d25a926440c00a4440c040340c85019107460514221b02c3d8a210703540300d10081d50350010016145c540c5004542c450381c0e902441d007601800a0700d5070002e07402d10240203480000c411650010307528000480c04242c40c0741c440d14011204c3d40000d0b404c500c07854011051400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 719394604 1250 719393354 719393357
    0x30d0c0321020a02030a090e04020d0212011e1e0603030e0118080d02010e070801020f07020f01020a0210020c10020a02130510090204060203130b07050601062f1606020f0d 75
    0x40e400c0601038011006101c00c071014101a10028900d55440c0d8040003604030030115903640214581d139040b01c0c00580c10700790340103503002401800d05801440d01044100c0204580c100115080005400701944104040051803000e81c03906403806140c10001d2196004a650800070881c4c10f045460040170442e034594158140018201021803e880080b081c03401445048221030090828600090280101c200301130814400c06c0d0000c94540d5040c000e44440c9030910640c0c2e03003050403940811500d003004080040c15400341a00580151701c85c04000e043c1142c0d5a001010080c08460500c050946400007460841d005808500c00594642c00d80350b41d02d480090303005c070303c03a10399400600c160503190b801050064800200015210740120181010041c58005c11f541140d0360b5402c00050300c18041c0c01481500090018400d41d4055084082d017a42c88030361401100c00b404104803075100c0014150a9a0381c0080d02c019516841100d82e40050182c500c082c04041c0c2c180c1c0c48103a69a00c60045010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 719395854 1250 719394604 719394617
    0x1090b0409060f05100f18081603020909060106021002130503010524030a050c0f18011217070807060f1e061a0703020303011715180c010219020d0224030114030d0c03 73
    0x2502c81c143c202030070003d800c020303064684900c00018410b2701428684000c9000b040641d00080c0e110a0205d0719a0481d8210f4000d00080c4002030018002984140e16044501e400c0400c041040d440034440ca902c610b20b6003108011200171058420308007603c11464500c60b9000b035481d04005030020403600d065100c00d03280f400001c5810303000181d60040c0c5111517544030900100000b41507064500001686008243c0c40450740100160040e49208525024188a42c2004044001019030b4010b0510185408000031080a1510760364030340c09441006200c001d884510520800703d40f0403221004021002c4100e1405040d954040e40360300051050402512035216880c8504506000817568202d000103650791520f01f15290001c0c0724100341440b072040c4201c1c10400c07800d5000040491001c0390700341403041c0105499081060700055444d040b03801c000800750941d0050103e90b0a80060715040050780d48035818030503d0303a401d00300100c03054032942c07107001100c1000b500950b00d982250780524104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 719397104 1250 719395854 719395877
    0x1051509130f0e0c220e03190f09060e09061023131d1609030209100602060f04150b030304080f1f0203010f030209040201052a300901090b0409060f05100f 68
    0x42d4114020030108c0c0d4084541c81007180c3c41030358001e11036040410740b62a80a0201c1c0c840108450b2400058400c1d03400c0020803002c02c8161400e60002400e030350841c81c107241c2c404a880780a50041010078411807002c440416000c1c22010702458800144c11441c0c14240300300381402d183c5e2060000a000004002084021040c6003449011490007641e0050800b0f442810f000e0700e040042e4000340300f0480140030f802c0104c4d100c103040c1440e04d40142d803c444800c03141c2000d409084001d00582085580c144800c00c00000c80741d50512903004030103055005002d2510106180310b200100f4208040740391031040005104108001c03031620142d94050312140c0080e82e9910041e42c00e40300d0986112920341d0b20f6100101c0760641120503410199a10041d203070801c00030382890f4800b003100825419101d41c1103030020551280d1201070806010b0515159000f160303030344003008860b802030300445021501c40405000031070300c210200009050503203900040a654060040c0400080c4641e6403c018443c00314 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 719398354 1250 719397104 719397131
    0x30a170c0901140f07200f010806010315030b010b030108070501090f0b071716053c150103080301061b1a0402010e180901110301051509130f0e0c22 65
    0x1910b04001c001c8001c2507640045060011a00c0c014500d48180e6801d4482400e144c0e01f0300400c1e01c01d00641c10b8403440b495071242e10055000e041341d12070300e02c80343c1810f40c0c0010106108280050007010110003030359503941001801e5042030403a0300070f54140318a1172010000c1c2005e40d07045004661440c20352540f40c90407403609030140040800c8041343c401001c0303624100001c5c0b410900c0303500c5118070203d075110390b0010348000d8110241c8040d00c4514501da402c881e140001d104400d21516100c0b419114040071310101e0a020000a070000d450b0001d0110040c062a0b4110b141030340d4400d10402a201600180c2d0341d050070103540d002d00340c4402620341c0049411a401000f80a944850052050070344440031900007409040840d0007a0040d230800361400c3d080700d5038904603810b0360b00182040e04011034541c00e041d0b0707542c0701c2c0d200990031183c0d400380e403010080c40340f04076804216825404180307402a00c55091030401c00d20f062034429240c10700d0340408a032051608011958600e00003041201d4502d00c0b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 719399604 1250 719398354 719398357
    0x3080919082116050c0306060f0a030b1306020a05040f060203040302130b0f1309060b0621040f0b0708070e040c09060e03010905030c030301051305070903031b021002030a170c090114 80
    0x1040064025040250020401c2c045003a580b00c2c0c50607411142d1f44d41e1000304215101c10280030898020001680610100d20303003140c1250311000340c11050b040100385507107680c105c0c1d0100c1a200300058012400340444046032501c0c01c01003150b0302c01141400e045070000b5002d515100c1a103941c070303942c44125107100c0d200d203514071014040003070089512100308500c0601500406000f26039840c0340c41d40c50030390342c9002400e0720844c07190b214580d0803003060005040d04d000c1c00500b0940b50703501203500200011714021140c910820541e580c1440c0c600300700b44090308041c0c1d40e00d68548620b0509103400c8010354802c1c050380884a06280003014500c000001c240145602c00d000f520a00000400310860b080010086040b14819104200101c4803400c214044070b07002d0303d4100c0001c114680c2000460311845125034507800b40e4040d95000041a030000300301c0d40d102c00c0b050004d42c00202d54034a1098020030420701e1400c000c4003003812031400382c2d01400d85104030b880c0641032010000f81000076450b0b580 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 719400854 1250 719399604 719399617
    0x60304030c0b0f01141203120403020a17090a090c0c03080c0706050411210a061e0c1713030e090c1e0904060f0810051906030809190821 60
    0x8049038203e0070041804000701e0340034013540b01190440c0c03010410b241041c06000e031038003a400d4003071814402c000b210041c090401400550071031140c0b859920104d2030405000301070003444c10030669505800c2081c00318035251580050701e0f981c03500361074992440d0040d4481440f03e034980b0700744da0380e80d480c1c44048185003e0f00340041c080901d40402c000030401c01c0c1c503075100d82c098100d80b81000994010010030042221140002803a000070244c3c0000517520307080504080011070600c2c94070b801000f0404100d4801c000180002892400b12101800c0645c2c94a81c04c40c203041003181c5103c240780c40c098103041d02e054005000f100000001a1400001010b403041900000714059802d0010100c10105403c00c04005109914104000a861070300301c1c0390004a410000142c036110078889886801010020a003001e00040c2084044080e03d0a11400d0003551080c0ca09035107594952050000c8130032030b1511203440005213038041c410000001200c01242480346c0901701c031050084075400c110701441 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 719402104 1250 719400854 719400863
    0xd09030915050903010b030601050607110f100e0910120206031e0103050f0f15150a0b0d20030105010c080d0e01060312180e070513050a0611060c0307020c060304030c 73
    0x1c2030140c080c50340319000700018003080f4001e010841c03c003c20580c48410a1058507400b42040000314002113404140420710304008290011040f1a000400c5905952002c20301c002810300d84c000b01030341717001c0c9085500f055000c48200c03040c50505d40040500d005680e8068455203001c0002040000018411031034101103140f01016940d40c1c0c42c2c9580e903008045004251409416114810507000140c640b0301422406400c141d070780c4841c01300c130744814240500150003040c07480001c40d28203880d2000741035910350ba0400051000c041410510014840011080c0101d000c1004008607030380086070761311598002131003035651007240c5415801001502c0711441c2a50a240c0000b00344400304840e596444010748526511407002181c0844ca440c003805650ba00c440c040000c101c0a40c42070010300041c182c80450b56404680315000a403a201d21307944220f000445070120143c442c0ca007488840d4100702c40d851038500f0750030440b6005e900c60b000c41080710b000e00030100018092510a12aa00074240c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 719403354 1250 719402104 719402129
    0xd06090f02130b09030a0b06122b140307030203070c05060109050a391202180a0501080115030b06070803090c041512020d05030c160302010e150d090309 67
    0x400e640c20003035000300341403404480c00c8181c0080c004030740c00d084584800c07005010f01080281c1d5590401014000760520303410407101c0070520740744c250400000c1014a031004012020726507902a00107003065194a100800142c00c80301742c1034900f100c003501e400400e542005078503560380032422140d0a081c0c0102501d948641c00001402481a0341708038080c0403155420f10400010610241228051035180c11007032525212404005119103182c2031001c0c210f10b0041c00626201002c141642c2002d005111a50741c42260113256103801004000181070a092030140b0b98903016001110b5000382d80d441d420b040e282c207400d00065540c44225052958881d82c52074407810301c1745656540b07102c0701031068022464a141405c05d0341400a550080710080b4210081c0340c901a4288460802c030041c04442e2440180012071940c1e0302400100350b00e103548507400c4000ba01e90f000041445a01503405805640c0d00c0e15068107002d10706c0300b1644004001400420300420a00e0102c0e1a90a160320034050b61f0750 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 719404604 1250 719403354 719403371
    0x1e08010911190506070b070c150f060f1809212111030f0a020d09120e0901080c060f071a1033020c030d051b0726072c0a050408040603020d0609 63
    0x2c01c0ea012b000d100040000c104020394441030301908848007406581c1000ca00160031038881c0403580c10622500f0310401c10680c12080304400650688100200c140202c0e03040001c0b51020307105d0072540d640c00d5000392030501410a80c000041c0c03052101605604e0f41d46a240000f4241840540442e4149020194108203240480c240b5200020000c54101c00207501300e0f03524005403801c0030205041e500da80c0c02030501858048100405544000311640d0454000e210041c040351520041034801c0c5a1801486090301c4c01d611200007146860f00204440000413101740c440d081880d8110140030101e010301418030303d65010030303898a001300d800303a43c0c58806c00c50b409006a0f40074001d0300e5100300351010500018003100345140c4a14172402951500802c1d070001c9650800302110196008003054140ea10031601c418400d84901d0480d040d2042c04000c000c259844019040c0040b98890302e100c0c020811403c2c107550b100664412485020201034020400e8440c44644c2d41c840381c0140b002c4201000701c43c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 719405854 1250 719404604 719404643
    0x90901032019090c14090409021801090207030809030a020c22050108070503070501020f0a06021303050d0c02011d03060a020c01060e100e0c0f041e08010911190506070b070c 76
    0xc442c3c0600058241051030220089000301682140c403041c1400e1181000c5203a401e000090070080c5c8140d9004508109607080250b0a5140394043c00c021000944e0b140002d0401600251010380040034951080102520056000c1507451b8600d10480d580350010000c0340e0304e04581440007504035201460310300001160640081c084084460940687c0c0b60b461b0794500682c2c42d41c0101007c055146c104594101c001390140e8020030600428100d20310b8440d4494a485142000b00818480031072100c0d01b0181c29581c00a103e1082e100d0610705c04180d0140e07800200b074480710003800b00303003007241c0100d000c5803111802c0d002a0301410300001041001d2604000c01d64644070340388146881c0513486004144001240411190841001c0c10407500d49481c220084900d00b501c001140c0f5880908040421100400c0c000d038951503014030003010701c8181c12010049840071240180240d940c0001c1b0070450754545000b82d551003a08581e201c00c980d81c0300e04083c1c4081c030702c1d40c2c03000703041da1450701000103401c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 719407104 1250 719405854 719405899
    0x30609150912040509040606030f200f223b03090a12020607080318011b1d0411190806060a09050d030c02120a06050c0909010320 57
    0x100394030540c00350103440300d2114a40b1041c0411880c440c1d030004000500890401a0415401511800001034203d50f20740744d220401d424035208841c01581112400c012019054444600c003400f00c46810300081024001000d40491229000b0342d08070f42c003503030702c3c0000b5941c0c40b62500c09507401d09541340b40702070142410201612191030310345040355580c031a40311030000141c0d1030800f00038010b502c686040105640c0306940c2400c0c1242e012508115000004603150091750151070000c011041e20100c82c0c10b1107003541c0c4e2442811070900b24009018004c15030240011202d205144041c90030983d11501050141108401c6811401c0f000a210f003d801403001e074001d04000203035a00001c1c2d481d81c00070002248503585048000620b413003010311081c6880c00c4920800b41c842d052849240c4a83c1d80800d03608280d0095252142d046400c045051040602915a0140036107260030315103a00c1c24005401602d043c040580003104011503404a81e4445045404940f8001e180c40b801389050004002d48 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 719408354 1250 719407104 719407123
    0xc0c0b0a2604031403090106090f0c260c07140319020f07080d110f0d120b0a261e030702150306030721020604180c05031005040c03020702030609 64
    0x140400500622411005811080c0c00340d54550380709640f501c1130b02d0403a0241d41000d0003504044d56102c00004110881e0308c10000316001c2d0440c00b0444010030745020300120507066162007080781400350504980c135500c00581d44101116501500d40c040c600b04681c01e540360710310503e02d0b8030000a5210303031103086000030131400b24103500f03c0300c2c01621501c54030340f1080903224800c22a408155500079160103100e00d00150090001101c5413807076903441c210b240490404a01020840c000c0c808407810b4030030301078041d680c0740c162400b034002445c003520305c0c040e0074480940d0350490407059180c440a400a0140080116601e01a0a41034420194140d22940680070403481a07c5074407455001840c2c0e041036030f02c00c4d0402409052082e15000c0d4512a2004114000305181e60300c1d0403030300040e0364403806040601515070400060031410100a012140c090048a0600005000700202c4804244000d420389109a4010501d003c503a402a000781c003481e81c0003940f501541081104a403800641d1500c0e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 719409604 1250 719408354 719408387
    0xe10080a021e0f13150f0e040209041401080607050a1d06070221210912070f030302100606020307080a0e010203070b012301030c0c0209130807051f021204030c0c0b0a 73
    0x40742d40d240003d86401817500028400f140404c2c040307031102406820003c0503800702920140c5001c035000001000c075004a00d4003070344003804d00010f202d80001000f849500040d00e083c0503261042d003140c081c2c83c55072400a5162480b03c2e1203a6521103848010507100b05943c040c01c68a078440414440340c001011450303003980c40784501040d000e0204c00c12692104199101c2c55554a03103440c030024080c1098441e0179441d03261041120010b18144041440350065010354040e0040308003000481c01030701c2c0319034414400c55000380b0040b00030070405001c45014105906001c180d148006005034218026400d026054034040f100000711501c0214540c014007080c440300401c286013031001501101c400344102d200050301419085c0042c01c00842440d001000300f0040b12070380505a8500030b0b50b0380281400c9410307411410b8070074064801d60401c0181403c00308401d41c140402d200d400c1d60000d070f00900c0035082010103407600c0140052600000080e1910010160b0394072032480e00a015481d0788010080c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 719410854 1250 719409604 719409637
    0xc080601151d06041e05100e010206090109020315090c090a06141504090911030610051206040b07030f18110307060503060a171204080d0e10080a021e0f 67
    0x4001d4140b60b041411011008080c14101401c00c030889100380d41c400c2140a081c04501c8012441d907990f2400b000340e440083d074559041c401440002030400700085d00c0350629a0501d000400140d90224510700d03040e0000711400340d50b0f0354040b812031409505094150308800000c0030b002c90a10700b074205405844c00c5180c0f2000410740d010501150000642c520314002d441400240000c1145412800505008000510034021004002814510180c80c22465090091010425400c002d540800038a140344058161032801d81c80b030303041c02e0704000c0c9a0010503940300d5413806c030f20284d5400030110020900c510300c0c450300ca40c80c295a11a03000c60140740300303204002c00000d886118100702c80c4600d038042c10610f0807502d480603d82c0580e401095180342401503088081c48803410502a02c01070030550000d010790b1301c0c0000c0141003454861605805100c917038650a8103140c0004d20250001969000141c0d164500e05607d54401d11400d404000020001001504403a00c200908a81401041802c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 719412104 1250 719410854 719410877
    0xf10030f111008062101091a060405090a051504230a06050a0b061c1103101412030901080c130b0306030709020a120f06032f03030408190c08060115 65
    0x140d0300800c003119503a40c48062541c05084001c1102040c817004414000041407030042c0f580c44481241da50180c620068031240c0402c07003245001e0140c4d030f40010340000070300800c0d4455224a92241000c1e15540800d60b0550042401c11074409c030442c110400c0c40716030320408030f030707440c1d46640710340d40810180c2d101403c14000c07580c0c104107445540c002d0034004180c0c40c0790101008111900c0b450b40da58100c5444d60300c13914000a910b00c3c0000314803c03140308281c03040060501c861180d5a0181082c2039006140c1142c41d00201000042110305e43e507000d00304400d0b40e91f04c4100d410440e12032400030703032103088c540710001816060740c01c003450241c44100c0644401686409440d4201d0051921460000d00128103201c40500c003a0f11140741d108546d5004255a40c4030380f1440800030302200504044030420700c02c4c80c0440711105e0f0380003002c0002ca014500e418034040d091941c0f1403012082d80b08a442c10107510f01044046441c420041c00a07005440c01582e460001b01d8401d0806051580480c80300c207100c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 719413354 1250 719412104 719412107
    0x60506010e01090302041d01180b1308030c03040c0b0a02070e130812070905030a0b07020c040e03041710090303090201120e03030f06011205040506101202090f10030f1110 75
    0x380707003081a0694584a00310300c1c41d02004040c21490003030110200b10b000020b80100700a01030007108411404601586054034a40703086c01e4040100121902e4a0b1083c2c41030009000104803500284040301d100c0c2c81b0346a508000454a0b490381c0f0000d40100000b0b40940c1450300404d510045821a442982c1d584d0346800d000345602000c210001d02c90f034030401405404022074080150424040d1401219980e1038001007840d00034040c5040d01e001e1111f00802c4002c5504001070b100b450020381d014041010035012040d80ca0149019070201946580d011007100c020400180c07119819030b6106010b07541003828054000c04402200740c0c00900600508a0500b440b4003c0340084030030503000b10301c0e564603912012042c54018008174100105420580b0300d03c17150780103007800b8500500181c001c5041c000941205c052255002c2a00305880c0c442c18005a5902080036900c0580100426190354030382d441c04101c6182c64100074101400100000c05000c2a006c0040d500703007081d40d1030a1480c40c281c10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 719414604 1250 719413354 719413367
    0x311161809080a050c0f06132d0303050a0b15030412180501081503030310090b0f0a031106040b0307030905010c08040f30110106060f0c03050304021f020a06050601 72
    0x1070242a642d010030100744014802c1c03004026940720203090310751899980301c07214200102a50740c480002203500e1440c00380601050511010060000740070700d5058070a24010581410460140506d5582c00004907241c215401c040006240104807801346460144c1903c3c81c4c1d001900d098900300b00081c03045014a01401ea9040129150944a81a030b8034100045444400c018084414814111044040c640707040001e1070042c08074940c00011a0b082c4103248040382c00500007039129030036640580b00e290f00c40070070907000d0303c0e0803400303103001c2e807620038049072070f503c100e622403022010000100491b4507891b9100c1584a481074000b842204805001140d80040940d0090f118088680003500080c140101002981c1007141d4220300c050400302c0002d507000d03c0303020300a0114204119580300002c00307100f40c902400c12424503600103181c490000340b0f0840310034801814480d000010a041d03554120041041c280c20051055802c001c40300000e44403100b00c1e50842d5400d0406000c82d4141d0300425 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 719415854 1250 719414604 719414621
    0x80a060e07140a03081305150306030114070903140102090604030309080d0e060910031103130510200318100902040e0d390506061003021c0903111618 66
    0x40405141c3c0e03007142c6802106911100c912403440381e200c40005a1902e46402013184041d1450500340c81c2e20b00102810b007914011700c000440c0d00d01b418100007985401c0019002030325000301c0c04d100d00884400603503009210b100a442da003c0b1001c2400020036a110704040c1c01e40c3d1894003900d0429058400940c4d8043c403c1040365400301d02030200980d107040c0040240d660212030300d0007107000c00b680c1da070000181e441524402401e0310803a070002d0900c03208108007055003508041c10415400f51800e52281641f8036444050f1401002010612030f18544036400790760803000c0c0988100c4100d2282d00c800408500004900031030414240264409000c40e8240040030b01da10b40700f06c04101c60202d101c1c0840503512620682c962076030f100c0004c00c1094100005203110b40000c000d2414043c00b0480e14141c034081d07100030980100020100d10030280d5500808842e001400b0803040014901070f141c680314041454600e2140074aa60200c5000080340030443d158410119041490003008000303840092 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 719417104 1250 719415854 719415859
    0x30f090a211403031902090f13061703090307170307081207032901050313050a3009060c080c19060c0e0108010e06030a02060a0203030a06062f0106080a060e0714 71
    0x514a021701d07075a20f50003c0c504400010803142e0691409400a005490f0082800e0b24540d543d43d000d0100d03480040c48111004d031402c0c001c6d0304011640300000e40d00c181c1c0d4003032a03c142c0d000600aa5503140d080007a5010164450005900e46d4422241149110f4040f0b0700c101c0040d04160f22072106220b100b10b8100c800160904118200022500554240d803000e00026040034155515801003002484013600c024411400740c0000111824008880307044100c4045145070741298400c80240c20403180e8045813100c4c200044500340c14140360040d4010307690b40d01d01c40d010b00040402c492600310b1200b1500e6102c0e000800052034141d0341264a11145080e8601140c0c1410051018021100d081903126800400f21043c1c1c50386507010405c00c0e003080580c8000742e880441400000300c2680211030103001c0c80e140040c8841c03854410028000101420003c2d080001035111074250f40c20f4000b030000d01078120132100c0b41c5000b4036000c0c004005542200c405402411404110707a5800c121168104400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 719418354 1250 719417104 719417131
    0x20f1602100e013207080319052206151d0123090406021b0d0305130b040201032a0905011e0c03050c07030209010609140d05030f090a21140303 63
    0x5101d11018001e4005034003003d18440480f0050074032013a0002803c20620404085449080000c0d4104080c1000011602d04a00f040200400d068010218410b015a03034840c02a801100b4200500103180204240c50f9086038520702042080501c10703c007500040c4015030720714581c2d0302d54042c1204003100b131444080e901d41020905040c90070070841f5030407900404006107804042c821a014900d121484503079203405c07801050341da4a4040c460243d00100c1d0300001d049190311903846400e403410081c0002d0606550704080300508040c4541d0100c02d2404600e81503290183d01005001c03101070384141c81c00209154420301c24401c042c14020340f002c40710b445840304543c1c140e40c00d4130150031943e0114a036100780840040941d0b10700d031409001b08041d484031510346080250307072014034840e100180d000340303506200440061000000c1303802a90784080650b0311041540000b910300d04041d404002110b8402010480c040303c10322401c044c0c0d600c50070032030b00814101200644c80380004c8402c102e1203220f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 719419604 1250 719418354 719418377
    0x380412051b010f0f140a0e0102060a1406100309020915130b10080402060f0d05071209050d05220803130807060e04050c0c01050a0603020f01031401050d06020f1602100e01 75
    0x582002904c1d042904008411340c54140e425001c64021000f400006584140fa40959517014050241c000d1251003003030048031079a5800c000c8003d00074007018020609038002001183c420b138007071003c80b07600401c0001141480c080c05060901d5184101c1d2142e42c0500c10000e025460b4455a0300030400a0082d43d60340a00c030300240d842410040c003c0e60424002c000b48201c200c2c0c00002482c08002903000000c007030400c954024211800c2d240811181890100487c4c0410b00008200c4406d443e98075150f030384c03090380c83c2202c2035040790368139600008203614802048880001c0017030300c1d4a0080c030500d0925580e580314030b0b035912041480390001048a01503018810700307040e005103900504d181c80151802c1d10b400c408a08540c03040340c100b400300d0342d50082031045241c290355601c1c40d40001d02e0300b8800c0e680c1003000e004a112041c480c0e2486040b07144181410020960141c542100050790020745400405500f49088429144200d1003030448007214140c440c06041c3ca1a03d42c0d0041c2d65074409040d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 719420854 1250 719419604 719419607
    0x5150d02150c03250c062a14010f0b0f0603040201080c0c1603080d050c093d09090b0d110906030a0b0c040311040501380412051b010f 59
    0x14040d10103900302c3c0c0070402071415209a6111081901c400034211100c1c040b065060602c0031003410340001c810800c5621200400050703402111491928803c4560030700c040900c0c00c140740b01e40801307112610f5406c1c44120a00f2030100d50100a1454040d00e44401101d806805c02c031040c40b0441e8000c1c042407c0d1b0011402500c010400303040c80003100c004450003c0380e452400310030301a071076200703c4610f100040e50340f494034114002d4580141c1c0d02c0307100d50f042c04130300e4001071250120306040031140c211503a05002107d24601008120810010340c130201d4a1140d400100120320301e00910351101d003070400c011080c4c200440f40f480344942011101c400303032103a50200640e40c4000391120f0b070705128000420000c5015030740712a010f1142d900344140c1e502c9c9986841211010320344d180f284110300e4400104a141c0340204240039004802808135403429282c20554410342c161800740300e01e09008140420032a83c0c2800e400d05040c040d00803904080c028055006010004d0001c0034009040541d50100c2303035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 719422104 1250 719420854 719420857
    0x5031b0405090c030105032a150f0f0a1e0c03050d09020909030a030605030a111002070905090705090903070f02120f030d061d01080a1b03050d0305150d0215 69
    0x4a000141450581e4071800038828400c107a42403150890000010011807074100008910ba15003441c000100e02c40090280da0040c036100a084c1c0205007880c400b0342c20740c4d48502100e415482e10510281c4a0130192413114090f045592408007103080720095070308002c001024500140d1855861040d00b402c00d07a021038440c2c01040d080903540382c43d081c1d070f0070040e551100c40030b101d0302615004689848003140014140c0f8042d5005500a411890a000c080780a83c1e10100040c2010f0381d0421070001c031a10700300d1410001e070340a42080c81c41d20041c802c1910b004166841211021240c1c52100c0d1510001140c86e0b2091010041c04400080707404001402c2070320700c42401140c01008d98000c000c3c5520b14900b140c0c4400e403248421540c0b11000d200c051420700c1d85c0d5118043c2c00c510705d02903604042c2256550b40c0d60b61000fa040461a81d10100c1c000100741b0030001859000c02580c031103400250019010b07103426514030b155503087d0341041606080480e070091510350010700100543c02043d803c40e045 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 719423354 1250 719422104 719422141
    0x30c07050d080d020a0305071d010504030b0c040f0e04120f1209020a05100c0204060e040f0b06190b030f070311070813030c080318010302122707080102041809030503 73
    0x10280c05010490300320f1500e1015010180c9542c4000c50700d8078042c2002000b414075014030344402c0c1103100f015a801d90b032040607901070f2944000c0c03128203a1500c07004803409011307507401102095400754011a0700c1c0d840b40c0810740564401c1080c1e00101021032415100c05100b9010200002c41255104c0020811500f10800690000c0c0086030000d07100c00101e0400c412a40000700810320300048041141024402c1c0801040e0005091089040c40c0d0344417041d51421580140040302e601000c28903582c1c5c0d040c0c0c19022041c03010241404281d5030348a0100c150021a0f08101d102403200005a140b40a80503855941c0da0440c0304501c1e20286a403403034030303e4010402c1c50300507240100c00440040e17a20552303400a0329034003004640301d400d02d140a0480c5181100d1050400d401840b0b540000310701196103a4011901e440204989800006058600090f80241079058407500c140010003007019401841a200418640e40e14210115180b6081e5406001c0013000110200001044840c02c0d4005050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 719424460 1106 719423354 719423363
    0x3061818070b0c0c0108100902071101230f0c03190e100e090a0b12060a020306120c06032701090302010f1415041a30030c07050d 57
    0x72542d68001302c1c00e060198400118070a10319110034003001e00030440086445060b141443c070441e040d62018917020500b041562980500050002ca84d03000c00301d0803103031500104c81740288950b0f00008178903d250005110340c2d580c031400e0b50050f0b041d06080e9511040ca201c550401c200001d0070f0581c410301401103070301e01e032240c80d00c2d0383e50341c11350045c15002c2c00148505140301103408018148042c0001e0f0290130704202942d4559405903009810130b5880896860030107540c03655618a02034400c1c2e004406100080c4915004242c0b00701d006412001d0411350075081d2800b900390740041d001140943d440d129202c500c0000380c400c10303d0848024103100110700340035250305040740414031118011912084820344520700c030b003021f00c0e102c2c44c00b40010812200100e0009800c2d4407107409030300b101c03903040c049449003d400025620009084030180c0f85052811003003102c0c60031400c4007200c = true := by decide +kernel

theorem cover : BRFrame.Cov 719244604 719424460 := by
  have h0 := BRFrame.cov_init 719244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 719244604 ≤ n) (h2 : n < 719424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
