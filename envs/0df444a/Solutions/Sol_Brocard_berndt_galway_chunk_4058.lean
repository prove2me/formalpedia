-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4058
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:26:46.373346+00:00
-- url     : https://prove2.me/submissions/081e8124-16a9-4777-8e96-f7d939832633

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 729676258 ≤ n < 729856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 729677508 1250 729676258 729676267
    0x315032102061f0306180f1407060906090e09190501020d1506121d0a080405090109020906030a0e0c1309060606140702010e030c0901030c061403040c030633030201090b 74
    0x4102030100c0f0359110092003070780d4480151031040b032140b4480c2070580d04240d440441416904240800d41c2510b00560940d000720342c80810381c98040d00e04803058807225900c11009a00f86a10074403014006800c40b80c0601c221507068070800080303448034650303901c00c10001d41c40303064046280c8241c81e01c28003500750818031810203001681e40003489562201000001041c05204450040304000d0f04001090082c003c40d0401d4080c40b0000d0300803c100d400c04d68082c5c80d03d070f03030310800c80089011318034070b82e64041ea040000c10506042d40c0c0001c0c0c041c2c44a00c0c1a102d140c00800300040740c02c0c3c41c0c241c1400a41c2c9d1141166028064544074490041a1a0610b42c40701c0007181801022741c402c541c0300905018205040c05103540b000c0001c81140440a020f09040e940c49003003145507030341d26124860000d51a1568154003000c0c040a03a4003c2d940300c01c070340020504558076000078001006412303060350084038a036083c0c91002c05103e180d010b4040300341c40c0f210b400c2d800010210040394106041d400340421 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 729678758 1250 729677508 729677551
    0xc0d050f030708130602032707080a0b040303020d060e01060e0f030607110109080a081006030e0307062d0209010e0f0a0b0f0d02030a022a060106031503210206 70
    0x2030071250301282d645001d5034540d850b001150000000d102014002d03038400300401248104803850140303490030410352a40380b0341079101c01d039a481002d4051010290400c410306800104000d49841e001846400d002d4284120303085600c0807035180b40d10090280c06081d00402c51140c02150881c0170300f10540d00d200c49101c00c1c00220b9524000507203c0d104026400b4036440c2c0c120420351102e80301c198082840c1e580d0303002c50764000b000c80d001641c80c000320007480701d80010301d02d01a20818071b0407031819000c0d5080180d203071201c0c1c005143d071440120b0508400f20001c05a0281c0b0303925004001d500b0480180c850307040000040c00301440c040d50034001c00c45074482480c00c0c0e58581c01313039049034901201540c0d903800d5641208200c1c069400c0812040d030000c014048150b807250090328010055200c4140c1d24550201d40308808081d07800000c0c82c541110005004940c8282c00c219222070020f181510000c0d902d6640d40b4841e202c0e00807109616000c0060064080d0f41403010359001541865003401c00354504 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 729680008 1250 729678758 729678787
    0x20f030d020c090c1216030608030711100909090309170706050405040c050f0a030e01050604061401081008030c030301080f072301020a08070b0a140c0706090f170c0d05 74
    0x1400c000d40b00d0f034004400140075010b18004c0310550b441100711000d107400c08601500000001c00010800319041c42408524044000280c0d594650040c40300c814484480003440094940200c003c2d080019251000c122030010740160b620b03a910a42c2c0f181c80749460007a14107942c550f00000c002d01900451303070800045034400d050f02c1c02c1c2c40d803c580020b8242012142942d09115000c030388401107030007180c990603071605030344590441c00b1b02030001c0c0150364800041204483c4540168003a101000080b004a54850010182d00c2030200000520094031141c48507d1908014003441c499400000184034080c030600510350210030910042500703900b40900700b02404108165000500941000044940c0c800c00c082d009060304002da80c1c1d42d9641c18103142101081c100c0d944c0e00a1401c001d007510641d4a000700641c0305100e14502c5c1402c0c03003001d40e5444003801c0110f80985480a444032a40007040504030306001d800c01185003580d95129841001c2d007041c03c011403030428003605001d420302080f43c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 729681258 1250 729680008 729680023
    0x409051e0907050117060d0c1e0803030601050d0b030f011107030905040b060703050d11130806060a180b0f0603090706090b070b04080c012d14090a020108060303070519020f030d02 79
    0x11705c1d01401241c1e80c12001c43c82032088814003404803001e035603000808224102e42500e0a03c243c5c20340002d9243c48600e515501e01c8141e8055000400c1000503040c05100d50307120505520b401000e60b030070450101401400d682c5502c2d0b46c1204540b00041c00000c154202c01c1e01ca008046c00c1ea400d1040b22850000600d00f4001d100c0058144040024100400c41c600d40c411180d801030090116221462102c182c0510000c50080740740c188510780103d1507a103040c0044500720b5004201e403000e2980301841c55800782020700d055580082040c00c40c08800d6030b9060185206050040003008040e2600c2001071015550303900405905034200310503404103480c03100c119409904034035010b9032081800d035400e00412101200340d2484889181404601d03800301054104140134107410300c030111a108003000c2401c402d84003c251584510040030055010704400c03036110070300078103890070042e40f5241c1034141442d40a540f6841c486142040003180f03400c03000c10300b508600364020170880745001d102a640300780 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 729682508 1250 729681258 729681287
    0x5041109040320060105041a030601090e010605030718050c0a05220513050103031d0609041a0a0b04080d0c05150411030307030809070b120a0906020409051e09070501 73
    0x2100000202414000c000c3c42c403900b403049022007011011022034036294a400e000c0d03d0b20460801000300c3e61601c0050726140c03a90f6008014002c282d190025440050091108201c1c0b03035500c0d03001c0051a550284014002040640d0708007040c445a070b00c00c0002c0b280000d02028126009002e00ca655650050940345890038109812681c03950005820650803459407105510880d10b80c114144110a5000705040768800d80380e810740284c013550101481d80da0f4100c0190000d0080c030845445141907000a0001d043e1100050340d1000100c2c0400c915802c0340d000780000f8500041c0c1001511010008200d40d40344a1400c1c1502101940c2c80303c1e01c0f110f082210804880c11f440c0030506001003003209a11b4040000c044070b9881c0340c0c1d494003030011002202c880c2c4590240c0c09000131044032413012984030840c40d0000940130340d1089403070780041120204c15100c05509000c0171a0100c0c0b1841914020b001c401f070f6a402d8400180e86130035090303500414030006500f14442c100110f0740c001426007041d40c1c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 729683758 1250 729682508 729682519
    0x403140a0518040516050c0712151a030a0605190207140d050702060414220606110f06190902030a14010b22020d0e10050108070f0602060106110f070618050301050411 73
    0x1c26038141f8910340001600304401c03098000c2c1302d5408000c0c16004504803890202018000080000d14110f03101e8a80400346406402c01921400051483d5000301d0744002105144010900782c40c2000d81241c101340012618000884000840c600b800c100c00b1451007100c0c43c0151404909034007069281c061441140680c051040303180421b030755484040400784104402e001800344032020380c1000f42542d4401e4a0200c1c05c034030b20048080c1000b0030010000c2c00480024000703615407a1412444e200b0070b010002d4490342e11101e03000140da0038400c41f484c07180102c80380108402e40b080032608403078400f092148544c140d82e241c0d200b114503030340c0f0380110610540c50058a95800c0c401120140205082c03039100382c0503230010941401c1260340002d050394040c0044035140b940343d00c0c0070040810103000e560050780c405801040250700c240c00d03452140d5100810b50f1b400080100b40145803207110340119000c07ca1250310001c9203038001c0818001424124000d00c110305217511820501c0d8902d114aa0050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 729685008 1250 729683758 729683767
    0x19050c300906070f03031505090f150a030b160807030b0f040b060d0204030c0e0f130204092301050109050c07020f041d03040b0702010e180601080403140a051804051605 74
    0x60340c9032010f03070f0190740e013100000303100400900d0001c00400c14208521039603980c0907008509802c1c80c1102d18800c800b81a60704405440c0e40b50000c0c822014242040e81c8080e0000c008070000308034006050040410f840c46514038040b0785000350001d40c004200c40b08140c500503505a0503035030341444012003807045e100050081070710310228006203d2811120441800020f0001c10030852520341c0c1d040364040803401c2c6d2551104100c055041505440e00b1074040d661003099030240c90254480b0782c4862007901c0c120009502481c044901142100d0040c00a965031001000310019034001e40c0d0303000340d070b0030005850050b00b940020f800042e000059070042d0740c1e90780c0e044680030008a040fa00014850b04032515682d840b000018582c0c400a412400a5810b821440990074001c96aa03c86c8141c0d84224035595102c000441d41c016004200703030100400780d89211400c0d00c3c00e800800540381240c0d03425a031803105400101d00c0b13521103050329000e189080c00b0442ca02410070b04a0360445490b24019030349 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 729686258 1250 729685008 729685027
    0x604030804050c0a270203010317030712050705071b05131a0604030506070e060702100e21010b1c051e0312010e190c08011a19050c30 59
    0x101090882e01c04c1e00120210300c007080280c071a4109107843c0515203a21031494000244100030b0380800c0c880100120004003000c120381c240840a1355015107079241182c05056051011b005960741503803010085400080c03100240a201c402e0401d0201091070441c000e145460042012030030288a50003046584000d0b141c0c00380c01ca02c50f000c92801c030043c041a150303522410040e8030352000340d0b0b40c5d00c0451011f004491141c1000015600c82c2900100504020203401d1340c10b450b80c103941c90725107034000041007090b0380344000328550200d4000040c000042030b99465084c03102600c0c8010006007014a100500000107500041c1300c0010040d10800746800050200b40c58a58081c46081141c03440c3d05500100381803859250452269003145034150010449a03050000ca403a000d80036000a40da00b0300501101d5190132442d0f1400b90099070480c0760058021080295024442e001c4e03000420004101000160400c5243c2601c6400d05140d1181015000380d034818015855180701c0c0c09c10041400d158 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 729687508 1250 729686258 729686263
    0x9060e1b1c0902101106070207120201050a020a061e1a0f010e0303040e0403120b060a0903020120010203040501020c060f010f030b040305070803090f01060605071e050708030a0f0f11060403080405 86
    0x2411030b0f000d000c000c40045514000f4240b10f8140074441c0a602c1218001400709200165040031100004400080d00c1c801e41c00444596001c0560642503110350924540060414485c1660002e03401c1498942c03050081c02613010780e40c101002800e01c4001041c0078410759500d4100320003145090814801c0030290201007800c50069922803040741c80542e080000b89900460111104180c1e01802c00850000740d040114500404120704009001c01c4010320044d4000d40100500c0c1ca8803818044d0084036413655582aa80104c9044910740d402042250140808000140e00018003a40b0f1050079818184000b00014040c440507101900600100341818000d5013202d210755040f440107aa23a240c500d0815a40c0c041e100c152515035840d1100010340c007449070b4181c40100b83c1c0a40d030b40f541059000300c4900c0c4c1074128002910035010341480011841c004000a00d68000d982d15040c4540021601c098001c1c000344011105200c22000174058500010032041c0d440707589400c0c0030889449900b4070a1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 729688758 1250 729687508 729687521
    0x1090e0703050d02070303170c07060b1c0c03062307050d110c06090c03010e0c0409060219200c0d0209040c2102031204062309090109060e1b1c 63
    0x108680a40350180c080f0541c00300391340060303c0c00313900d03164840302850089800203003040780d500c04c03023090600841000414030b4100104540e0700a004052500390b6214808200c0c1c5076841c100d4940308203241c20070401400d40a50000038401340c6c00c0884901c019a502d0351481c9006040408100c40090f22040b4a001540075002008001503401d443d03401b2415115a104400d680040c80740c8114409509503140500030014401000da0250112a9814003404040c00300700c0f000f1107115030280a44203e071942a819001010340c15038441c914003100f02042d12580c0904800c190403a0001100d1841c1d50701c1d00410a010300340e065400c2c0c0f0b6a650340342000f0302015000d402406034a909088240c00c9030420340d17807100c010750007101514041c01c0041060402d80c03285105040104480c444070035204c030140c44680125040652280e440c022106000440c1c0480c01d030440d0101541d00c0e00e09000d2400311030011075004206409a0880e544d51413003d00b9180200340b440e0000b600503502e800040c1c1c00030781125 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 729690008 1250 729688758 729688763
    0x1a040306050c03060909010c0504120c05060a030203180f120d0e07060e03190209010501080702032814091e030c04090501091a04081c0219020f1207030801090e0703 72
    0x400c110304002e8058002a0700075902c1c64403e07440d10002c1480c3c050103103c5c2c944401000d4030390b207150524010522001c504440da01303491280c00030170009236584491005240301c00a0b1f81d401a030303d10f0580075100402c484030b4454402a40300d112011070a6030700181c40e000407002c41c6055525030b885802d00f90098001c0ca02850b8150150b0900000d055400424a9078022411025200c024910014092b6200150307000a544038860000400c56540600c48881e0040440d1050300d1800f0000c003880000900070907208081035440a071401850303a0b00c411042103003c800180e0b94a0720300d89100080300c0c14a00213107410950b444066001a9036400c1041448255000e04240009903880c200750307001f06104e12003516074103856040480b5401000e2441c5129660141c4214102100c0f000741403000c0300c4042031401000d908200405500000300190106880241c1c000c00c44803c98001c698140080d81c103201c1ca4490703090110301c00180e000b001d028155154250b0000d100d01d074101110b8034151099001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 729691258 1250 729690008 729690011
    0x5210d0212040506010b09090c07021504080d0e01030c0e0103150512070905100609030b0a02040e011202210a0602090d1703180604030e120f1006030b06060901091a040306 75
    0x19407a840d41542041d1080d8064000d50b24544c0c0c0e65002d484482c07081d0b400361036000769080c000a00e0080400c020f8001c050002d018014100d4650003a96480e030b211741c00040055000c204031140295119112100d042c0c42842c05010726501498090403410600110360b051503102c407001c207103400c0315045e148002d240c0108034007003030f080f0000b0160320340007540100f80310703142841c0000304104003642c140e80c00c0b210b1540d82c0900d55817454a51311700006002d07055404181d002c000c0001c200040010143c0a01180001580303010707103503c100039424410030f410900f0795560041d040c2041c2800304030880295086080580d8a456120010300c8007403820300c0c0140545d005000c090b41c5c0140c01c0c4051845103003c400e2015400d540c101465941704000c540080005002c0c426950a6003001e0030a051748084800855019540c891000ca0801042c000707090001c40d40d0700ca040003800008115286c004401b6503110b03240c080d03010002400d010550080f41401048d030120010b4901c2c0b00c0080302e0045410420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 729692508 1250 729691258 729691267
    0x120308011412030d0213051516061113080105070903050c010e0301090c080f0d0306180e010923071a040b030c04080601030303140705180f0303040503060a0c0f0c05210d02 75
    0x18004002e4000a500c6c01c0362140403880030a442c1410320201c002509035111440c00c100440c0d030541001c40e41104200c5241c4e4a500882c2c0e0064505006800300c0030300c0c00001c010306410940d550742140c7c0300821fa901040070103c4100f004c500c0100c3d074007036171000038a4121240d0380001c0109004d018840d04c0100401320f000c0c0c00240401c80415080604610201555003404a100c421001d685850040107008507118456103603143d0fa0b58001d004002241001003946440c81c2c07940c0046031071116a200c0e04000b1800364903020324040c000500030b0207529406003184102e0b02030a04407400381d4000d03418038090020225903c40c440005072001002d40004440d051f603120301e030041c090420002c15680980c4500d02145030a40102c01b5650b0408400030422403901c661010005401c1c210344110340c040c0010800407840303813801d1082c03070301c034201820010652460190000b04050302c0c4011090401541001c60400103001040000395401110b8038608000c500c1c408102d024414618029141c510009 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 729693758 1250 729692508 729692527
    0x1101050c06100503061305030328020a03050f0a02120411030109230105070327240203370c03060f060c0b090c1810030609051612030801141203 63
    0x211100d003690001d40503a11036803106c6582000c22204424010000d41050000a4000b004580301c0d0f14428001e5a8625036049880c041d80100e0307000010302000aa220010402002c03040e40101d6001100c6030411840c01c00e80d502280099803019000804108880c1d0210810740d500750480317040d09800c80d0403010300c01030780d4800740e5051240390061603032542081c0001e4103880c02407045025080c840718052448641403d144400c02c46001000c0310350415540c21000400d0041440180b5100d0300d03100143e4a003003810000841d039521010704200c844556046a68801540d402c884194005105c045103c0c007003600240c01030306442d04404203291100a0024203aa40701942443d00c5004502c003008540302e400c1d2194031003144103425500110000c950318102c0300c1e05803401e0761006050501918282e103076500c0c3c0054581001c41620703a9030041c1d800941512818440d41e0083c07a415003989218020f503500681060014440c5480203442c0722040003454642c4180f26948081c5c81095030390314031040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 729695008 1250 729693758 729693781
    0x152901080c090901061d0f0d020f01111002070c1212050708160b070807021612030e0406030507180203040f3504060216232214130c031101050c06 64
    0x601106d9903049807200000c241c1e040900c2e80c000022000351030201c408203146c0230b0001400c43c185480c0d04121020b6804c4a036001c013071000c0d02c007085140c44056a981c039a4140780050340c09942000b4015208005d90500141e40350b807091010500505000781ca5648600b4010b103503000d03c40320300840104d020030f01c00800c8006075405200301c8460310340c03a9058665034400c9030b580c640c0d150001504c7e07440d0b4400b4080303002c07a1801e00011901c00d180c040c07402c15428000c10103541507644202c810b0ba210450510a0030040c100200f0344d034082c000110b0943c40d01d41c03174009030013120000150402c60421262040e40c4904001088a8611116640310000c2400100200d90780984078050041c09100d483c50155040074091404035252480207880c1c58940c5822209120400c0d0300741648488100318203110041c01c01d0041070b001290348400a0150301074640c0f001700940081000d400041c117548042c0000b44100300c12401ea940105185100e05060001642c2d035105400c01c2016a11400d403c0154082e5034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 729696258 1250 729695008 729695027
    0xe1905070f091d0102030610030e0102130f030501060e0c03070f03060e281404020f040605090c1801080702151512060a0c021207060c02070909152901080c09090106 72
    0x200c024940318101903d082d0700b01e0000391055071388010141004400540700c1c1c0c202a50503e81c001c001032501503403000041c4198401d521100c0c1c105051681041400f0080c41018010304000c80828903d10b0100c0391407501e80701c010f02106c14005424040c034802d82c4603a00103000741ca190508155507060807141c0c0210b61445945603c150003811303a10142c0002d05014648001481d9011074000d61119404c100005a500c080380360419a00e400014240e500c1541d100d0081d80c2e0208003079541d45071150b141c055000120145c80c180000c010502000c1980002d211010035000000c1c40656102d0080018076610b882d005c0e680e018031141c4074040010000b0415601810001c981080380c0c0450381030990322000011004030805c24144407101c08104242c20041c070034140e030300c1034405441d180c082c083c0031190302407025a40c12080780000d140c4120b9074401e28001000d0341d2400101c0250300c8524101e0104e4030704180c1d0410440001044180d191403090303442d8903c0040000c110b40da122440204520704 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 729697508 1250 729696258 729696281
    0x1706040228050409020f030102030103080c011b050d020a1107140a08010c08010b032511060603060402130209060705030a0507021c1a0c070b042102010e1905070f09 72
    0x66040401d65031011254400c0c80000195808028a442e000801c401002e403080241c0e000105580405040c0d6420300c0214080c500c50450252a501c446448500712040c219125585100054032000341c15002800c0d070744004095040540c2c0c810391444200d50702c8500c0034200e0042e100f48440400c801c0d030406445010b180055600c214504c0d960900e81d03080e640060100004075281d00c00511800540c2001140d00000010aa00c105e600710070301d8210004c0503070900000241940e0528041c0402886010f400c02c0088004040a08150700010003c050140c141c90320158000f550568686841c005c3c1d0ba4410707040303c2035a0700c07036039850800f41c225440440200c1c800e44502d0020a541192010900c1500d604000540340d0140c04a95440e400000a0280c44440e0320600100e400a14103000c0c0ca44030300e10841c140641390719180840500d0480540e81031043d07904008128a1000f00020050103502c60070211014449881c1841803d0800a40050ba00004041c2c0302050503201c40e040407042c4071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 729698758 1250 729697508 729697519
    0xf050c090315190903140307080a1107030e0402031f08010e0613032a02190801062106150e0702011a0f030303130602090a030501090605070509090f1017060402 70
    0x851140b0382448400c0304a40d04002d0441c9200303885110310140d400103010601c603043c003101d441d801400c01d880d40c0e0811108800014046010030000003541e01842d12040e04408c5100e0078020a079801520404524601c903024aa02000003414554a03005850f9818000456400c0c80394a440030240a0802119015007904c0b4800c00f00f0645c903084c0c00b034065541d070996240080001c04901030003102c003101e120700205001d0010300b40090b81d600910883c1d4a4225485019040e1904d1040d030b0940d4100e83c80b20a0702807400b00184050034400045c02e807001c1d4840000181a078580700c03454080811504150007103003040c01000502a0150f0202503044201e0614202902842c0308211580340040d4966070945c10601c04100b0600349243c0d000b900911468000d424401d040002c50740d0351030107034010707512a23454540c00000d000481c4206a0483d40b5450400e240c00c0b4144003040c1d42c2d04003e810409842c2c0300704c002450381d03078000c01041d010b00821076000000b590540c2a01d03640c1d140a031820b0b8880d5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 729700008 1250 729698758 729698773
    0x90615140906010801080307030c061527060b09060d1112101a1c0e01020a031e020c060c0a0e04150305430f0e25080a0902040f050c0903 60
    0x25130061010780c3c122100c60000398a01041687c0480b000b56841d20125403240e100c0ba030385403150340c00b644540007070240c0081400c1c507080508112071040ea041a0101440c600d410f905114081c0d443d070464003015000d840d501d5030740e21a914004010100081d01e424040e5010401c800e003036502144042c025003014021017282a1101c040034500400340c9001d10b40803400300300500109081c00c03540342d500400214001140340300c004445007079078052115000041d541c0c107074541c54220078111515160283c4141142003c0a4080ca6030b0748000160060481c11300200d81103011601c9110300c4540950084e00c14007001417503640d102024541030200300c0342401070703810010100c00c6080d000348101c9181c2540d4036482281c5040751000201c0c51580c0d02c504884000c0108807004480b509600520f40c19842980a1522244102c2407003400c503c03001c036000c440d41c007844049034003146c82c2e600004c00141c0041c0031101480041c0041424140a0034a18100b008001e504030024000d407005081c29000c3da20035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 729701258 1250 729700008 729700021
    0x1c020708031b0406051c09050f01021308060c2212060b0a1509050418060504080c0706090605040639061a0108041b1802070203010605040207050c040906151409 70
    0x540914092040002c0c000e00c8410030406e00c2c0d8040d900002c10441340011500540c0d140c0504199043c04d411560360b4000030701000904d5220788080040c54681c01030700b11340c00c10402c82080c40c4200e510031009450000c050184001d8000c2c0c42038011701012031904040f413000c2c90508003a201d002034552054100300700020b007a0b00d129030604415519030381d5a07210207050404100040500d40403004801c050f200a0780d001a20070b204442c042ca00a041e126182e04000e400d881c0740600a07040349081000105007008469000070947d4103031016401c1c08110345200c64088030055090418910b54044503180d6402006e0380581441c95482c040d03035050119140b00c501c410101c4191a910314000780c0c0a000003004a20700307200c00c8585841c04d0b043d000d180c0f61fa4071070f404004032408041d5206540d00003001421881e0034480c01000300f00c2a24190300788001d544500b9280d926510602d07000b507464031424410030049a020750719518074602c0940140361120850f88201810798580790003185a80c002c05c66 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 729702508 1250 729701258 729701311
    0xc07060c120e060306121c031514031522030e090606090a0603020f07060507020f070f0e0a0b1201151a030c160c030203070b030403030f0b0a06051c02070803 69
    0x101142c06400149103807036a20601803618600303840381d0401d0094600804a088001c01c2101c42c2c060b041d90041180d80144004039200c1450303a00c2220705100e581000c03649602c0100700010000d820621112041d07481e002010f00c81c0b240415400d809e215500829000c054010000d003078210805d40b401080f44d07699100f401035500c00e030280030b0352000c480ba200b0441c583c0b00c4d4008000c0f544c000c002031420f01d0b409a44075003d858013518201c0150b0800e4004d1944290704001c40d5008141c1c40c00004551842c101003003103900c1011b4507200455854448428254880208048400d940d010003006120750315007041c0112040ca0003461802c811400040c000d1244a9041d240121f0000d9040d505c1c0a42c01c08801c0107030702c0c24079801c5840701801d12000015a0f001c0c48550000d0007811072032903aa10b0586070060454154861200c2d009203884002c2000351201d0401c030007920080c1c100340b81d88000d640c0a400000000c00180c8080600008840c010071592a0280d8000e0b4a040424032010810014440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 729703758 1250 729702508 729702527
    0x10b03090d09032609270702060c1b0309030703150f020c0709090309080d121b020618010207050f0703060b03070b090f04090501091a0604060e0c0304080c07060c12 72
    0x10308100c03614015080d4500313040760584018510700211854150800302081801060282c10b010428101003041341c000512540264070103035510107840e040c501000450010b01031181c0c581c2c0c25144580d081003440030100103c40b0340c440010b04680109680740384c0010f160803007400015200342801d03500d0404007102d00035244c00c01b00640203130042c00d046c581901c00400d5458016405c0010307a900005001030103114400c03450100c4d40c0c844403040001050201680c6003003507149c1c40816249442c01400790301040076608540d1415031200800744070241c460280c050380c040507180d804ac0b52042035044500013943c1c021203100c3e010030701c4a048000304164840050b4400c92000c1c0ea01089196502e24000c005101641c100a00c00500c010322522400d086030000f0008503910326010994041030103405030309952064045405001f014284245100420b01c06490080003c801001040c20044014156040007001c001100d8816a41e000300400e54896004103a408010b501200207400d0310030040403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 729705008 1250 729703758 729703763
    0x1003051b013b06090d06061a04030b0a0f110a020f15010315050703090c14040f0501080c0909010209120d110102121303020c04020a030b09090d020c09040309030803010b03090d0903 79
    0x140482c4a0700040710307810300c0011003410781c0705208014004003070f640c804484400c2401203030000344003030500c041d402d45252412001d800312402400104000340302e110410781c3c030102ca40004611000803a1a00700a0074200c100c01940c2c090204502c10202c0d0f00103036141e00c00b20040100c544410461007804440082030101400481d207000d40341101c07413280c2d000160030120601c1c000580101c1601d41400351465500281d2804036260004451494039000b540106e010740079003040319500d04402e0070740d596058200c150107800e2038400074804100a5042c0c0d0f21100e0050036104665621560301a00c51102107900c0c008210140e4402c2400c10052081d110400b280d980c05490548940030000303c03c040c2c0500460031481000c0d43d1140035151400a00810030060b2400304003807422038100580d0300801446508560f002141300c00400c0d0f030020381c454020800782c130100032581361400c017200c0c2074041d0340010381242000000040e005405900441c400c1030754405407444424001400c458103210f91101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 729706258 1250 729705008 729705077
    0x6060b0a090e09060f04050c1e0f01020f0601140d0c060905090a0e0a0f0213111306020c1032090423010e1005040908070201030c02150f1003051b01 65
    0x244401e0745c22103c0940207401081140c0c1c080001c0310014200c4580203c401d000b02c9039826150700241040c83d0256807540c1d007400500101000300f42100c0d40c9500500c2070140480110f000c401141d11607038400300d0b41c0e81d0040c80e041645a100c030380c0607203000382510070240284039000000380e41503040d1040800c551000b602400d044012511500c800300314500003a41d10180203940450540c01602c201c41040c41103154031074880140b10007a1408914507803051003550041d2101c0c180e26a11705003800070100c0b2505111811200a0030b03a51a50b0340004565018a44480e505090108416018050700d61046506010110700341c624141d41d441c030841c00e84410030514005109940f1310400c515805403500c09000c50041e41c5000050a503007504001761406080090042d05650f8940520419000e03540020812506061580c1000c00b134001c02884940c48010081604540c0c00c038111030045401030105c3d010100055169000d00c42c1c2e42d066640800c03e0795800d91168040c915602c507015990150 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 729707508 1250 729706258 729706261
    0x111e0402030c0c0609060402120a0503160303090807030225121101111b1509100c0501060315020c060109110702042a021506150403060905070306060b0a090e0906 71
    0x902020350009800039000550a0080c10f240e490200440781c0305180b078400404040c2054014000400700303200c0f60b00d0481d0029444000403800c00022a030303840c550b404003d840c6081909088004001202c0010100344000030010b080c5a80000e48000d0317551010102422184010303034458028800b44980407081c0c20b4a118a0003041a80120b07403400b41060405c2c0da0010300842240c2c4c10544000f061311102e8140124091481c10071881c241d41c811092295a89444080341c000362030607070500c02c0c15080100500d042001c001d02074002400039540101c410001000004480300650000b00c008401c80c820403000241c0e40c1c0f82c600950003100d600f0041d040c6490019000d10000c1c0c41481d805503440101080011018520440c100c1e002001560142c1400c070000e441a501c0580082c1ca903500c21007000101071080c00041c42214122540207a00040390310440c41d02d20f04040d180d0f1310141071945080d80024840b20000000c100010565840d104220b843e400c4980d10400260b99804103640100c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 729708758 1250 729707508 729707569
    0x4060803040e072303040f0b1303030b180112060207120801060f022d01060b0c03131208040501050703170114100c1709150304080d060b0c15070c0206040e0411 70
    0x400544c1c00c14080c5c801f06035a103419071205a20b001c02034408509040302c0c4079500e01070642c03500c00c5200c200c0085500219544001c00c07507030421001170045018a0b0041e5181004101c844d5044851850380030540c074907050b04030640989464401d100d2100401c174120090f03500b036031012464010580c5440105000a001240705901496401c4400c0501d50741c0c41d80003041c404100d001420311103038040300455685914030b06081f60207a8590000c2107940d06114040b0010304403009450a440082c60803c0d16904d42e42421580310361640b07110072030074103103100102c0c0074500900548401c400590f9032415910310201c1c1100c0c2407c801c0b030041c1171524031400085d26448210300030320071901300514800203040201440c450759403040d0f8080b1100c1301c0005000d00402d209003c0c00c1c0041c10307002500d904040142400540710b2000f4040c0a44120140000074280307400b81941841c0d00d034014117119200e0792682d40390040140c040d1829152040d12000700f010502e017540303c0b03400500704500d000c0aa0654039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 729710008 1250 729708758 729708827
    0xb0909030712050c0712080a09050307060c060c2703120f080112081207120c05040605090d171c06080708150c0d0f020306011d01050a110c04060803040e07 68
    0x40c48140c60500070544009a8004120f110341c04060041c0801aa2394000500c041c00b545050f40c8a140290070040f400c004060300920520303d901d40140c800f240d04402030408482007400d0030008100039200c07403103401c00d100e0a21003050680344141a0042007200ba04010b54214003026414400580700134018880101c01044040d401c81c0f15603126824000b4025164070049421140d00300019400d03c40403d8000040c0101600c501e41400e0940c5084d04214000f0103a20440403458001c90506801400300a000e078800740798003842d424044c0e10780c007900b160050554080030f4590512820700d00041240c0d81e004c81c4000c116041342c0000c10a0108503000750341c2144006060021001040c0f141202c20f58090060360b407a4000709200503074901e40382c40007511142600345031070038002d815407125640b43d1f00030381224040e04450400c0400201045507091030480e01c4600103801c90f00308440011800302c000080c005a5101e0741035140c4030340e14002d00300c800c88807140c24859030000a40060781ca001c0103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 729711258 1250 729710008 729710017
    0x9030a021306080601080d090f12081608030c0901110c0603070c0501060e04030e011814120102070501020c07060f0206250c120f020106050604030c060f11060a0b090903071205 77
    0x4220115202d03603180d00c0141410030903800040f003500030b80740d10200c1d05d92103901e10001e030402e03800030142c5038146411522000c03070407034000b070803004000359494440d18060414100300b0303840b1050903564680084050b2594101c0c4a089010910b4030f4410040440041170706107422402400c0c980c219134421104540396180340005880e2556501c0780403540307d000c01c0c8864405c44c002d440d00032006810390001003c00480c20f508081d0312451410034450301600001c03d58003203400f05c407065440401044003e00a11807250014003640c800a0600c1d4a240d01107440403c55066032500014a21b000030300342e0f196001140e090100003800c0700e4040622030480032440e461121850301000c524007943d1401c0042d9541e0041b0004035a01c0c079450f0201990900802d03014141c16120700f428a03255030b4444810546a000e10b0702808840341031440301c075225a03659240c118802c07007100d84d54104403241d030000701408902140a00c15002c005400490004115000180d10003071001840103c032a0407941c6800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 729712508 1250 729711258 729711289
    0x111090d0318030f12030c081f18060e091506040203043315060e06090d0c140a061106041106090411040905011205100218090403030b010f0509030a02 66
    0x80362180240704400c1c816800c0c01844c403d01c0805075800c0b140c2003100c840d58544003103e00b01030404011280303066001ca0349542210b48540343c10150340b40d40c2d0b8201040d032480d800c02092407c11462081942d00d15400020880c0c5651091301f401d51103401001d9103801150741c00803020303110040403e805040550007182d110f4044c1d044c101d1100c14036415108054040c1416070f0100e44286142c0620140c14803410301d800000d4441819607500d40300d0040c0160080d03411051003a000491446e00faa20340b2011600a158080145550b06417141130240741d413500111814020b0011000c00704400b400752410400180c0c45800600080d0765542da07001c3d1407c280b0641036017207001440b1608064456004900c58141c0d003520143d00d40c0c2c1410ba80340c0480b0016030100091280380c4c2c140e4ac010510120f07914109040e110000350b501c20040311075403510b0b948032507030540043340d480c100018964981d00401150509a071003842046005000702c40b540640000c46c0d034560000c0007602e00514203510708000101 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 729713758 1250 729712508 729712517
    0x207050a0f0611030403020d080906060a03150e0307080c1204050114090d080d060501110c0a0e0c090310020928050f0f130b0108010b0c0615062809080111090d03 71
    0x54205000407540007505e00f100940e0003140c2c8030017000d810159440c1e124858600510282ca801d100190954240703100180446106504031610f0060304e400c64001c910140084070b13560512850800c0c45580036003e010482e00443d070705102000f000300216070407114140e48000c0303500b51590640c81254052411282c1c0040152260000034081e9400780810b483d1150b00000c40704e2501c0009802101c00030b0340c481c89030700300924001c02a0b1301c1d5012030782a00c0704105804450755402c803020300c903842214a1103a25105007008803655a00c0c0307800808549006072103040522078541c4810ba9210440591081124204a0184010b088ca8804900e80d03540c01040403198170318041c0401c1c7c00a504030f54442a554403840b621304a0f5800480f414018114048520710b0012001117090b1210000b4040103d104400b610600140d543c41040e00c41c00e82d091001e01c1408100b0031342d80c803c08018840b0708408240d1890001940b0340c410320540031910064084503261001d440e003040340b11020b2000c00c4042c030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 729715008 1250 729713758 729713771
    0x403050d05071b24170f09070602061b03090f030c0a0303060501031527020313050715080604110c0d080702010b01020a050a06020904060f0308071104020a021e25180207050a0f06 78
    0xb00c4403a1403081c01211340e0070b106c0c80b02e81001104103060002981048055501000600c83e00000301d8171101d25894075502910b460303449010003181040d10940481840b4480407620114022000ca03c5d11002d038030a860410455a485005509a0f14032810402d0300105107401000f8101003241c3c3c61906d80c1500d419044140c4000312804100d030019070300700f28007a200400c41402c1180400801d005007112818010444c484035400500c2d52900905543c01941c42e44070762140180f4800c10b4034400c04600d42925031030282c03500020403000c0111881d100542c24100d41541550011500b0140680c00c4800303041d001c20701d501d5080c042d51004140382e42003903480c00002034104c082c4140801440c441d6614564030401401c02245c50300000c1c084070310403031042156000301900051120030447c00108403065180303050450504007040300d243c0100034083e90030200840c900041e2058180d506000031003100b400c200d01e002c4e003280601c650007030080e4005114a40880c0f40100241a464400c00c00882c40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 729716258 1250 729715008 729715037
    0x9040f050c151209031213050c1507020a0f08030a030b06090a0e040312051005010c0f02040f0617031e030c0408010c08011d07120e030403050d05071b24 67
    0x541d0303a00300c0d110b5851100420020362140e68900b040381c100820a005600f8140c544039801c3c409000601896081c494090764a03080110601c52141880001018400b95044148209443e944141c90032840391900440c007041d12000405550300f500c0704580214200b02008202b50b00404040380b0060b03009400307100300d00c04c1e5580d0304000c902030004511225414101464040c09407007403101d02c442d50a051074200b18600d080c240440e400caa609286c00c1c04900e4040c10882100d145d52103010f50001d041031120012691550000c0c0216181c02d1501c00440400c07013243c0b1344900420b1040451201050f072801d401800c8030380690380110307092000c68901039840c0c0500b400c46038211401c50200700400d00400584d040d100300f00e82c0c80281c0440e0b2503624648407000500f8240b80c01210981c03103980b41003100d510142001550041c6600c0390072240a400c41c01d1020301582c00c00507049500340d201003003c1240740c0c8054a107070100c40f0f820445240b03042c1e071454610350a0100c00550401c0003040b0040990 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 729717508 1250 729716258 729716269
    0x12032d0b091e010605040b0711061b010606090512071203050412120f0f09060f140c1c0f0c03051606020313060e0f070524030106080a0c0e09040f050c 66
    0x1444840c01c035442941c4280d80340b030900708016480041881400d10040202c80040350231190266170200d0501041040603000a90900030005150550105140c421211210540c401d00c1916003648400c15003540c2d503001c0007000060503600c241e05400141d01009003143c103004540403a032280c1446814951030750450790524440c0030082e11001d0001c030601011980201c40703540d65450302d02d8554141884d039500074280c200e0a110300b808201d11031540081f40f52150440150b04241c6030405669040d0904403541d656a988a021001000328000004818083d8507884264581c61b2507003c05010b20381c03000e80d40f54006200c801030503190940480005803140c030041d485244041c02c542c415203102d05201d4112017042c043e03600d85a0151756020001e500c00a1300c482198001c56010448040184851302600076041100020180c0440040b0740740390003a12035842420b44030810012240035000455105c400a0b507120303080b88000020801144940c0d16481070705006108440514014001269 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 729718758 1250 729717508 729717511
    0x1060623070b041e050604290f0705040b04080304050901120b1501181e15022802031603060b0301150e1e0907031b060e12010b1c12032d0b09 62
    0x45c1c0c150014020081001070360303000310304a502c80c8090118100c0400c4400704072803502400301c482880c030303000003d40028419000c85010f041c00d800459191580e601c152543c0350402d0040c2449000341d10004203909800c1c5d99040c0e0b107290024101515a00c03071495a0110743d4000da0301c1410440780c0200c0c0140e082070070100d20014602c070603a0320441804c141500c6001200d581000b0501803c0d050711071040c03a80028855010034109c40b00411019112100b81442e1a11042c020340600501c46000c80b110003c2c0500070440340201414884510004c00701400c031403e412041c011103008910500441c0600c040b01580440c8126a07a410a505c6515565200c082111052426401803105200b040b852113a400030709038900d8403a0f06140c0c00d1a0000d440c4060311114603010300c84200074014110750940198082207005098014a100300e00216074501c444044242c0703080c504aa2411010780c8244076184140b903001c16402040100301c03a8150803c50a03440079400961180e01c107030a030341c1d161030071503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 729720008 1250 729718758 729718763
    0xb10051c1503051b13110910110f1501260708010506040b030102181215090601090b0d05070311040603021c0b060d0807023001060623070b041e 63
    0x1c6544602e1032419904c0c0c400c410030340c030341c0d00d01401c03810290030784070707180c3c42d44400380f2030000810005103042d01c4100c0c60140b00c04140c0d2160342042000291342d04000880b010300c0102c404e035480c039000c0481d00e03541c901415441c1503904078502c0040100003600c640700220316440d03644c4602900003044240d03280c070441c4c1e0003400d001d0350740f034080c410240380138801c0501044050703000358107109116500c00492054108441e00443e40303990342030140442408015407141d400380038140726003800340ba01c517a914424041d030000c261400f03040c8a00342c42c001c4494040180c0c84002099882c3c1141d940b03021000c0e004809a81003034450718040016500e8442c00300c404100c10a103000c40400605000b60079940181489019032030300e050070710208144004894050350150b85004442c0140c60900550038002c4008110301c241c0b00036038284600d0190000f600302c502542d070324200700d6406a01d4505505000020001c085010410720300000d560b1000a513120b8000d100301440c1c107030303030411010500d45090001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 729721258 1250 729720008 729720041
    0x50c030d05190605060405040b01020a021c0507120b07032c01090c0e0c07030503040507050a06020c09010608010612230f0f010902070b0c13031203060e0a0b10051c 72
    0x100b00d11840352034182c1c00700d514580c1c401d10840745071a012070320368030484c00343d140102d032034684102881e4000c0082c409110b50282987e40080038075188176030f500c61200d074100c985004403000010b82d100c1c00303501084c0154000d441014603480342a010703001402c85103040c5a100040d604218000c00641307015000c1c4c944544000300707085803030340f41000100b9107603000f480300340b980702c000c0c40248403400095500150385800c04a0303503621942801c0c7e15250103036000036030101c140640494565400705049980f08802c3d603140c03600740d0b2140004c0c0c80f0310000b400b0700400500080440c2d020341c64550003414006610000e146200c05944010301c4a41c1800c50365807240b07201e039109000380c482485107081d004102c0400114200354443d500c007407134076201038202090f07040e010902605003140f50b00714200843d400356440c880c0709800386021300644480e109060124603803800160040d00d0501440d59003d03030013440c420340d607920303002c054505400548661004640c440802c0003480a00c3c420a00074400a254 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 729722508 1250 729721258 729721261
    0x1e0312020d02070527100503010207210c0203121e040e100611031b150a0c021501050f060a2c0f0301361b030203120408030703030c050c030d05 63
    0x4010f0320b44070342c681c8082d0050700c004200c00c44540084540c622107400842c1c03a05c8003a00e034006086240f0301d00380c000c1035040d440000c0d00d404010310b140329410803042e4000c0948804500f403609442c0e500400001a41581000c04821401c1507004001c1c01070000c108000990102407403640045600b298105640a0040c40c0610a64542c4041031500416552928001d600c1c055001c0607160300a00d0f1a43c466070f01140042c2000540601150318410380c0300e4098100303407824920741c0c0c014000303001c820300150080b0042d0201c900310101e40c880c140c4401800104014031190300344580e9074000306000040001d6115500c058005003d404617070322403070710307602c070100031060701005480400034005610a0385003c001411071144602011125441c0012050909000507840d49103895078040007440103071404102c0742c1307000e810a00401624000d4007200d102801004a03807009100e9800f07803000310f0f4002d100490009101780c0050004503400e02d841c80c201807800c2440c80c6950000b100b0f502c0304585980 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 729723758 1250 729722508 729722533
    0x32105131b080d0c080d0f1a060c0a020f0609220f02121b0904230108030c030f0a0c0b090102031501030c0909020310030212060906130803011e031202 66
    0x3240704060300395107698a03450b050402da5150407550500061010042000061103481e005944014280780014130000400c184600000d0441c0c00380f00402410100e142c00341c43c180041070311103849542d001031024000540030008415aa900440da01840c1003041400c0c5440d054424042c03200d25081d018403101180420320141c0d40d841c00c0c02c2102901c18013840720582d0302003135032030340200e43c0c0d0004070306c0f0201c440a00072444c8501142603400c1410515010704524407200e2000a00d1284600381000fa6210342010383c8910621100d1040c0d54070501c032a07003002c0400e100804510f5024148881800050b688015030114201e4181c81240d501200b005610207078003d07910700d101000d1800b0000045028806804000f0f58014804034030780c08000078040ca0452680756003c1c41d00200a01605860202a99558030086928601a0241d080802c81180b00480b0100205a101503181d0a680c2003102c601c80448290381c80c2240b4840103540040400c0c1001910307a418000340c0d002d80b00300003100303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 729725008 1250 729723758 729723773
    0x801151a1e071709220e120711030105010806061c0606060c0506060a051c050c030102030901021e03010b120c071203060503010c26180f0705040f0e0a03210513 70
    0x3d0112256a1020009000c0e1640c034242d00200351503900010720141141c50014000400d0741a190002502c1303440d2441c0403c2d030554019102091040324070301c0c100c00b0340200349400da4401f8400c141c07056000c000480e5441c64001d04048080e4110f007101c44100070a40c40d00e6054420030751002001c5001b1515240c05c0c0041808900e52112040e83c0c0d070082c05141c1000700d045c4c1c0343c0041d20303428140c4400d844e0300e00300300040c0007000c1e03c0c0100a00070754a82c20000c034424001d5211240d00b80744c1890301c4002d988a220020281c038126400d42141d5410510900d00414a060004151440340202040a007002560150301c1d05a0010f550b80c0009807a0b0906d424142180d65207038102043c03003407000794003220800715124115540c001664100300e035103521075140c0441802005151a030b00418803e280082400900340040360317003c5400348514092031504104548c4124100005500420051008280511100710b0025100c0d800c05840c225020000d8003100c03029924a00c0c0d40c92513110503010b00c01e15 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 729726258 1250 729725008 729725033
    0x501090b0307030b0717011e0f0812070206070602070605011e0308310905070206010e060f010e0a1a0c070605090105041a0f041e0801151a1e07 63
    0x211641000395010301400a07079510990b200c010841c20341c032000284818441c1030070002c00003400e895811156151902d8170001d0103038000c1d00c21031a01500c80041d1141c1c0300880c45007101c0150380540721001c06411035444e82e500c89181681c118108101e50b000050007032005090301805800005401d50510442040c40d41e101025000c010021041c00e0010520b1001191422882d483c3c540301c0b55518400301c0075082008050069100c200c04030009402c4026070049441074202d80d0036500c0d2030307884d08200050008140c40c00c030342003024070400f10059405500400a28507004100205190351141d58408401d11201c0512100300301140400b0802810400300001d002a41030042c24030308180c00080c0680200d00c11030b02c94000070b404004480c0b07181e00842e41e00c543c451811558694841202e0100000a040c42254000c0b20810028101d00184110030b040108040c443c40d59a1415094031148803802a01c14100e034401c0144c040260541c01403550a52807802e140c40d00c1c1c550905000800004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 729727508 1250 729726258 729726269
    0x106050301150509061f0f020f0105071b11030105010b12060306060d1e0b0c180a061202090a1d0108070905090c04020304050a050703140d0c2d15050106030501 70
    0x4081d100400d40200005550a03a242541c904c91590b8544001803090340008601403482e50f0102550a4655408070b03450701c00128035000ca4a45540a0105500700c0c0d008990719000078044090303907030300240581c00a18405004031400c00c4248c0c0719038006400c40d1300a0b8080795024000003600e03502840d0754020786a0000b011006081d03c0d16004c0c01080402841c40002001a0140301d056a219400b80c16000481a00b0010f07501d503502d4222900c0c1e215511142602c1e0000d01c01c078485000710301d0314401c3c9030150342545c0e032002d921045c0500c2c0c2c00060f40024441c103600c070b5000500824941c400c017203590314101d102ca15442c00c0d94580070801e8100b110a0700234081850a1804004071b4010000b11690440350070f4400682d40d03916401d00034240b4a00d404018443d0240079000824003a400200100342103404058560320322100344161508003024500a082400c00890000c502c828000b42c84000d843c080c01403100c611007a0b40710010b141003810011101590385006001e0075900d4030882d030240c80d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 729728758 1250 729727508 729727511
    0x8010b0a060507050a0602041d2d0901090516060809120712051b0105090705011d04150e0c030106080709030b150a1a040e06030105071403090a0b090c030106050301 72
    0x11991808221158201d008503828007070300098640802c90704108413011240c100004540740c6460300d010514116a0b0028030545010003c00b1590052140c1e24011813946010a40c50f89900e640148100c3c0101c001e0825580d5541c3c0d43c030b04d2012510500c5080001c455040c6a41303100c1d0304041f00a0080d66025140c040c07e50b2203280c0840203c0300e401d04450311280c210400040c08141081300302c030b46106003000302d241034804400c40896000e05410040c062031555044d07074481230320343c8011180713044101c481d03c040780310001d54248642826400803aa0f40080c51006441a4581c0c1a80d407074070000780c03465180c0080020040021030750282949030860600e01e0500481031554484828188000c2c00e0003071100220b44200380c1c80e9480610841c020081e80300804e034a010401d01034001c0343c10501ca00c000780b100a90010703000e403074180b14a6215134280e48134001c5528090308015040e40000340507240030301c5080303094070220700e291442601c180d950070001c00382103851a09043c01e544090303104a00aa = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 729730008 1250 729728758 729728771
    0x10515030604081c06030311124b04140d021f091701060e010905100e040302010905100b2106070509010207090903020a1b140f01050705011d070801 65
    0x90394007148040e000b0750008109600c5080c011800802c0101d10300d8014211441c01400208050b080b070101f0b035041c01101300742c0f0110500d501502100703208000040082d0000c100100380c00c4a2041031020180ca41c01c2c11101d208810400404205200008170195001c00860104280700346550f83d640c07c042c0030f507144610103c0780e90200b5884080e0f900e42000c07041e0040240d00805101e0383e4907100400c1007802d0044072040d4115524020319080c05204440030074180041520309507401000d00603182455403a002918000c0440c010100140080b81107540b9001d9a0000c01e404000040803400303680f0000032801d00100411041e0b070ae0442040f01c42d00c200310302c2c0c0b04d410f55000c901164800b00a090241d9551443c0b0b00407810700342a07070019003402e468415900c0030f050303002481d4100a48038004100030009441c41801070051548100143c040c201880c4c0c403654104100303590900c0d14103061090800540340e540074296050710003540d0f02159800340e14044080208081002810313543c0081008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 729731258 1250 729730008 729730051
    0x6091905102d12091103070312030c0507080d050606130e01090e0f1507140d0209090c04080601180f020315040516092105341503050402190909050105 66
    0x2e001e0b02000e1200381d0349007510341c18401007175031488150074000c0a0700d120584a182941c08030450310b0b064070009107020070301d80314680680704840d01d80e50001400e40c2014000440100a000000c4c581a000304080c442001041d00c4903440c0009000048061100c0398144075902044900002205032039038090481000440303000b040101c80400d2820b14101c86a031921000d4410301a80015486070031800601c1020340105035020300000c0c9011104440ca03501e80007040e50842c0582d02414a0640045004002c103585c034060159160744001070114107501c280207240200c2c5c00849422800d801003080345001da24191140c030390b00c0722440c501d0a00c820001c68001f0456020350080100500030441038110042d100745000030788aa0100c112030b1005d5007040000c6d0700c3c3c594000101100680700706052140601c0d1040c0c01c003a565561000300c003101a800084000d040050310070b070703006078030b0071800d142c0c82e0145000074000c1c0c9441c810100303549010380b5146003120030040c121141c00d00c640301000003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 729732508 1250 729731258 729731267
    0x20306071b1106090616020a0b0301030506160221070209010e221b080d080a1e0b0d0219060810030302060f0901020d051008010e060606091905102d 65
    0x148a40c02080701c1121101c1480460a24072822240300c2d44080b000c600088541c115500309080c8907c00c0c0c44040c4081c0d83c40103240000d00003030100170304a4100c070002510b0300c44d681108800c980c0c0248101d404c4820030740114420200c1c082e81501c0081c1000034241d041d420b00407002801011121b40c0004c0e50701d080d030b1000540c100700241f0000d442050801d1401030150384201c482407580c15401c1b8025840e541e044403550b4403160300c4000301061400001604181d07d03841402c0b800c5800c1c08910101c02c80b810401c1008059180350a64003031120410303175016031a11100056485269851080d18034203000b80a800d4048c0107100070701e0083c620409000090380403c2c0643c02075070003000b81300d0a8035291005400381c0070b0076611402151030302c4108040345000303561400840b2581c070000c03c85100041040c94917141c048856941111041000d02c0103418000715040100c126803001d1081a0b44640004403041d840e1003130000041c84a194142c01309000311054103c5103c40002c81122500c030071409070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 729733758 1250 729732508 729732557
    0x60318080f090102030d0f0207031e0525060501090605120106050303070339020f0d05120306030a0b0a0f11030403081512030c0d080a0c050f0706200702030607 70
    0x400030360102e111916a4000c02c2030741e000081c007050611424144c8440034000750031200d401d81c0010280c42d80300200d00d410301c00e5818254160341e40c66280120100907510700d00c4940407865061006982c1040c0800ca051240034083c00385804045070284c0317404100403010b418000d00b1442c90b4984201004140e600004440c0069403600b0200c0394840c030480a013140d440c0400c0626001c52404081c6005906050f2611395028802c0381c803c0c800c103500310244141500031140c01442540000c101c0840f0110748406143c6c8000c004044407100709481ea2070282110003a54080c00072a21045030030400381c2140030b061b21070342c0e0b11040c2e00d040d86816240203190010180540c01003174070b203a110b48066100c00e10003001041842e01141d5580c4007402035695030b5042400307101d001500d40000f0504803155801b400700d000d009a5206810310b100c140381419990b12088003101d5480d580c0f04040401c2c440b088590303503200908030405072241b005e4010306081c0440101301c0000c02c000440100c0c41c0c2c111503007210 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 729735008 1250 729733758 729733777
    0x20705030a15150f290304030e2106040b010603021c0f02130b0d061403150c16081b0712030c02031501090614090112032a060606031808 60
    0x8149426010004010703c4400d00400f81e600941c00f0220f0f0350807080c4000000c45080c1c00030b588080010069980b6500c02d44954480000800c0012a011038481c140400035610001e060a10710503112460250f028807114102d10f0942003401040700f8410308859081c01000b007801d083d40380c0002800307140d0104682c10b5650300c03111340c0c88508150ae4601541554180054040e01142c401d403601c4900c14030350010181140d0440c01c11101144e07014464450305070215014005082e0303890704000c58a0b4050740200901c48445050000510381c0500d8000700b070081c0c0c01044041d50b50b0081d2a0707807200000418000d0740701c0e0f0380b21140801c800f02d407141d02e4003085509860514a0a00c0510009041c03442680c59409845110307000030502000b6584100d04558042c0c01c05503641d00c0340c03000e11003228401d108d10f002c070046110381d03031000c07034081c22038018400285280244010620103282800300508201036440584c0e801e01800b0841c3c051245001142e040400580e40c4007403a510404107100d0301058 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 729736258 1250 729735008 729735023
    0x70e04031103030a02180406050619050f030c07150506010e011202070b01082d060705130b210a0e0d050d0b131a01050f12040201110a21020705030a 65
    0x40605105080404958000806890f520700789200480c0c081d410007102c0c0c4552205070703800d0151030b1a01e441b800b800c0b5007016040f1030410003040114920605294500070600808020501c4080701c10350095102d05a03141c01e290b180c2d00b160034640c0580781600b050304022480c000074854181c0e00315030707441d0301c0034000d01c0c0003c2d58a24150b6030b28040e0085050003040c8803403060001c242031101181c2c44003c955050041c1c08140a0040705501d413407000c040001407604201c1c0425607071441007000304050030284d0300d0160110b9440840203c02c0c0c1c4248004c0c4c22407a1070b4204a11010041c000030354000d04804000d1140b4032650103881d482d01000007c0c20240900000c03d4032036404c01e40c01c1300c041c01c01c0003498046405150307190517000e001030000756150394441140882040d03000e10305a6000c1e06c031445050b4107004001c14800301405001d082a41444002202141005420008442101e200e441c0c469819803100e40038090786241c0702075800564007c15418000d9803400a03d10f080785800404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 729737508 1250 729736258 729736261
    0x61c110903032a03130b0a02071a09090a09020915040b0a030506040606060216060e030304180e0c010305240a0b0403210e0619030f2d0905070e 63
    0x1451000d214503104580c05000100c1d108030002481e240c40c483d040803020125000e943e501442548034880c251024910b10044d01050203262030345001b4001255541c0100d4400548030002102d0100742c0076002400d620300068070800034144412042d4000d4414107003444030700b40d164001444444003d005000c070310210303071150040c3c2d515600049641071002d0000b6403150340782d01300981c0b9071408039420384a650a200300050801d100081035011580101880c04d0540d0030b014089604c031481802c0180d05103c180300100782003081c004d19010744081100009440b4003003e000a060490300d00c5080d05151410003040300e505907070b04ca02d00c410100484021107800c03013900007030528002504000e107c0800401c011082180304840c0d1190340e8078101d141e804480000b2021107040740c0c0d0352a01c5400050a000306103a040b640400e220b0795084c10f00723003c14000d02e00c404940c11209000c0700c00c0b8200248000041460b481d40001000b00d86113000c0501c40b200700307925259035400d464499014070648020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 729738758 1250 729737508 729737531
    0x4060f050f042004060e09090a02060a02010f11041d0f0c0c12040806060310090201091a0c010924051312050c010e0a032d03110c0109050307060b061c 66
    0xa20200c990001603280500300c022882a900f040d400500802000c103007a10341524403440c0c16001c3c41e1080941b00020008c6148640c00c0c0300d041e0f0000602d0f00c042d9900d8680c800c2411600b0b02501070f030301404c240000e8a0b10714050340866014041c1401c40090b00c040f400344a205001807010980c0048480c4500380d454041c40c0400c0d25000044a809184a00c00301d408540d04c00f01107041070003082d007281190400d00084c51190100d805242c0024041104d445003004000d4402d4035002100311500c1a6509060030b42560f1800d40d2903e00c411110658030300f11001e140010495072041d10f007003a40040041d4a400d60011003600d03480d000280000c1d40300820000030364826001c5620402040c002803102030b650011407565481c01413402c402294440d03000d07403010200e18071011114220542180d454000b4054181c0050001c1b04000c007140340100000702038000d0901611101c0c0b48607030001c540d203d000f8100441240c814440380c40c8070305820040d030310304102425907100c141380e001d1000142e501c0c88039 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 729740008 1250 729738758 729738761
    0x71e0305060109050109060e24270702060108030a05090d0606080714032a19080312010305010e0703050a0308070509090a02071205270f09010f060e04060f050f04 71
    0x1540000d20038429040049000c2ca82034010301d048541d080700c2845919120b202c850b088640840d01d162484620720314000e032500f00c80440002411002c0c091081c141d100017032021540a49195003a0441111010300048650400c41c0c6801840400095400c140180400800c203108004040c3d201e0000c81441e0030078403c2070b510440041c518081295a400e5990140d070030000c6a21304000d00c2401500c8500440260500c41038504040045200780c03c0003500b000c00840740003100d074420004042440210fa0614104020490f0032044030401881f5031540c6429400d680080e03110b025150016503081001540c0050300518081e410300b44110159a4190304070350303d010744107015034081612428000c05480c141e0042c0308450040d589200241d04100c8196264131078880f5084002051078a000742c01c1e80d544c480c09120042c000d1000040b1800100020404242a0465600f03416540010001c058100d0303c4052504800d68040c011103181c00950030001e40c651003a1800380e0207070b0008200503940d9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 729741258 1250 729740008 729740069
    0xb1b031e09040f1b0e0316090e011d1f0c090b071e030309120315051e10050406080709060801150c120e0f0d080712170403030b2107 58
    0x2024400c101541665071441080f20084440790082030b20f814900785e450038081445070006240400600f03601d4904258040109180284056a9540c0e462120316400300000714025494544000b0310001c0005e044e20714032011580300007030540e40740020417810203400140c0203007120003000c507040c0c681c805403c00490aa164144084000000450b030004064040c2d2045234041d001ea105c003841c0f4500a1020380c121100e18204420300d862040080107a4138048204180380d510320100e80700c0308a04500815025090500808042100400c052203043d5103d141240c3c03000407454110240c42c54414050407240d8180102000c400861598410541c060042094995440340956035203001c0c42c840204000a10014503100d82d068014490711841c008031300c00b00560704204002c0c6007110680e40c0c0e003408488440301c1b0041c41843c800c40b030a15100d0102d01e41c0f05902a4901007890002002001403140841000e62485c0038580003180b2030720400100141642d082007401510813030701c500c4034a4241e12 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 729742508 1250 729741258 729741281
    0xb0a031e0f1407030c0e150f01050c1605040b0d15090f0503070f0309140a090c18090603290a0c051903021803240c0909010b1b031e0904 60
    0x2c01900d45190080002411002c0385e0060222490450300e42e50340ea006080240e4540182658104c504145c0e403400d4442d005c810641418154900303101d0485503400d00c8444101c020001c0c1c04050100f00d01d040c280107258910034201d45138008142c0c00c1e510100c000b0041e4501d502c1d1039a507032462a0800042900709400c2c0c90b0488111b0b0b46542e403601d0301c1141c1d401c800314110300090a0010000c7c80c00384001003c601102c000b4030256020b42405504001032146000352000c00c544440119003160707911034100040d2903564030114600c3c1c20f40c03c5c0600e0f044c40140482c010380c0742810040004140c20421030b5000010711602003102062044211b82501039155a451345c14130700c04104141c280c25500801d8411482031140d010495184105038441040d007441c03c04800c2d01d12806681c1d40030b14455140d0100031001d68508043d0204041490150240c0082c00c1e0b401000801c880f2884140411031224000b1100441c0390821504801c52200003565603e0540e40002c546003000703940d41d4110012044d07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 729743758 1250 729742508 729742523
    0xa050606070804080a050d0f051b030405150417070b07021c050f010b030f060408120a0609020d0501090b0d050c13090f241406060c0a0204050a0f0b0a031e0f 69
    0x2600c80e0b200c10344881c45c41c3c1040f204d600c146401c048510b40a080d100203070000d43c4c2c648604203076040010001c0a440e184820115000410000c1542d54400400080780f8180006040c3c0b00c84c1800c120642d080e0f682e54a803010f99000c07110400c10019000c085528166050b11f054002403801030360b02c0020741d0100d00050a90240312a02540000158004c444018044045410380083d24040903110b0b4002e44010b0b0000c1d0b000c20070351100b1006403c0c1c0326048051030b02c1c00100303a503845810305c0880c0c0210301400035441d04c0d5401001001d425000b282c042031421140b0030f03100516591600e07940e500c800303600b07801490301c07000c01894034249510481d80c1e83c0d040320080122505503d01020030310f4280030583c00c81d0907480040000500184184500010180e10451864943c2d90030442e95400c400e40454441c81110000801a11340e401068080c224001e0041a444843d0ba03000d016120b000030043d00032101d1070700800210b400c01c3d80c14070320030424040355580b1028505101c111504001400382100d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 729745008 1250 729743758 729743767
    0x60d0c030b03010c08040209180f0708010515030303311704090509030307090302012114071202160f0f08130320030c0919060603020408150103020105030a0506060708 73
    0x80e0150000450084120000c101d100d421100540c4e48030010345010b900424007200088940d80e143c101e03142c00c850200c08450794030100b020800d2504403141c000d211203035140c100f0311041c0490b04c14012440f24003100079504614181d500c00340d02e2902201c83e5082c0080141f001c400d10322a0102c88045681c0050508110300200a41d95596900038819050503a16240c0001eaa0340340c044180c038096403040d9114400c46113980c004607568000e01d03041418910001c02120703c04000b9100d4a20110302440701038000340307003580b00506401400c000b2000524010031003d10803032030705009000303895401020941c8862440c2094400d0052801c8000d081200c0000d6045c0032070b0394421141e0440303215461700200c0020403150940420328090080c0e4040e070142404006c20700c0d08204581d4041c038441e0030076102800b4640903d050300d40f80ea01140c00b203540000d0600c405401445211001000101980490b52440e80002c146210041c40c1902c0e0a40d80c401080309503880008031030895130000c4c0040e489 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 729746258 1250 729745008 729745031
    0x3110c030909010902041a070201021005070314010506043005011d06060609100e030f010203011211060c3a09091d07050607020303070c0312090902090a090b060d 71
    0x200d50281d0003062003800c41200009101c800ea000325015075072030001c1070044000341400844183c10142c0d0481c1540078074078444803581824406d840c440c41240da404107110001a054040d01207060708a00d0142c8410081803116036030f407503401402c03420300c80300c0300e85031020040000250441000300203006500f0560b8881842c80100c44006080b0f1880e8180d4034a5111002003052034454800140e4110b0482e2a038500c0103801665141e60590300a01031350380200c070003030840c1d00b203a100340c0140640725140c00891051114100e400504600b00b034419038a4045540e00c0c00755120306c54400d040c1c05100c0c0c0c1940740d40b0400c50092005021071520300d4a1645040110090043c0940b80985400340345400c071402c1301100c043d00c800c0c0a400801019042e41b500301003d00c0f06550040d54142e0301484204142d0380000d800303100c40c034011401990b07400007400754044018622442c0354030001640d801480500c8043ea20508407000320340703000200180c04a40b00011a00324015440d000c0b02d560301c0c00c019070f0302 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 729747508 1250 729746258 729746263
    0xf1101091a180c030a0b090a020d050f0c0114070b09120c10051f030b0604060513020d111e070c031b08010b190909060e030408031c0c05120703110c 65
    0xe01e00544020140304406045958403040c200f60a641035010b0070403140410445521940c00107508801e451103485181c01090f05858481411101940001c180300a0320700d042c0b00c0645450360918240700e8a148001c10302d8000d00518002a01c2560399030045078492408114040300e481d043c110254591601c510100d841c0c04200405090700ca0500001428042000e0a02d0842000c00500544100e041d038440d0032030b00c00001c0410360401d0b41c0b4280490a5654000c1c007035100a01d070100580d4480c2c1c0e403182c034400d0701d588407a00041c0381c10510141041c50345410311340ca4403004414906844144609020440481c20351002c0d00741e0749042d002e45904144088850305440e41d6000a2001500c40380070b1001d214400c1d4000c800b40e000050b014000c868080e0000119140107407004030303203400e1090b036903411540281e1090030254400a00078041c01c010006886100e06034802c1046004003180c0f0142030f61041220340c2e085800c10800203402c0034026031154251100000265854502d240400c0740d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 729748758 1250 729747508 729747511
    0x2030a0b101a120a06050301021c11190804052b0806031212090c030d2a0809040b010c05060106020d120b0609011d040f0914010c0f1101091a 62
    0x1908160034400324031095100003615149039042c188500d040000314903240312010140a160701d10744c4032100000c0726a001d00203880281424200c0d40340014010302c5280480c2c4804000e0980b11805001d035000038003403850300e5803000d810780c00c0210750b031780d160704d4051b0402c4260703120300c2c8800780c00f2941c840c0d4100f0b032080340401004190311034482c2900c40b00100341d515265490228a014802c0228540d02c803032020201c1c0e080702c942001c0b90050380507140040d080040101e08600061409208201c1c4516a03200300c11404a0041c1311403007403460360b111020907102d1900b00c94010750300e810031341856920407046802c800f500281502c2103540c5511009441d622005400800110189400030a48000340300382040000014a86860410503c0c0191049014207190701c4400c0342c5501c600020f0303102c5000d200c20a5a01d203500107910041458030f400c0d252200074192240c0c0e1b140010956507a82c1041c6c0300404001c0c0340c00c051540b1100240e0351805048000801000805007880b81c0c0032210082d07030001e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 729750008 1250 729748758 729748771
    0x60f07030e0102150a1802090103060507090f3c0603020a0e0315040314071704090c02010b030c01050309030c0106080c122b0302280806030307020a03080d0902030a0b 73
    0x8448044400d00491303941a90300b040413022034404c2d010038520402076000c403580074502c200c004244d020701d400103170042c08240e2095036565102c2c01085015030340500c0000c00f0340b009a5404280d50b0501e6045c910310501114048200030f0003502c607a40d030f50310003220f0158070111105e2030389505441d03100080c040d40101c10035001040810144d0001c030304d0041401d60002828400c0381c80700765102e85086840c0e500c214a882140c00d410002400801e1402460100c120750121810755120315058202c0c007140c120300505030440e4035180c0c00c000e442d0b0b80071400c2d500c04102440d22640300e4407500180d90440c45802c00340c0c0c1a541c41c1103400142004041150300c040c0c00119520314a080d0610001e54941d42031100c1301c1c000001214070320320600924501c0c0d811410183ca00141003140c4541410b1035400c4ca0080580250a0001544001c680c00780d410303540100191b000c1d5045c00031035804600140e01c527020041204001040501460340c0d25800b02007810b40080031161880d056041c015522001075424 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 729751258 1250 729750008 729750017
    0x20322050a02100e0d06021b0a0605150a03050d0c0309050612040c05120703030c03020703060e0c031615110f01090803040512030408120a060b0a020706170124030b060f0703 76
    0xf02c0e50407602400c1c00b0014140060800e114418046e40d03154000d510212009545002d0513440301c1035800100210140103100380400a0302c0c5c10058105040f000040000d2446100542814000142c0210305081c920703a035070411042104c01032406860204035070b00b040b50400d4010404401600d42503003514042c502901c801038a00e0780711000d00403203a002c10050a8258000c203c1007001038451041401050b0003071041d10016900d1740e4408007038036501c012496031940101020001e43c81c0500c2040c0b407101d200c19201207200d07e005983c42221000ea4814010700c55203410413002c03018107200c001101400342008020341c40c0903140c030880300e4100b99801d442074410280c015a0091000d13007183e00454010020074209520884103021002008050307401c80340d292100050710004034030207440c080c0c0c01a005052490b0920a00805800401c1c440d52010300c82c01c070041081c42e50740c68203c1c0d0b00412182d0310100c003101c000000c2e8041d0201e81c00103600410000360321000300030140007a0505602c00e070745 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 729752508 1250 729751258 729751279
    0x60a031e090302060402011209081206040e060106020706110312011203110a0b0c160501060b0d1413030c1e0c050103291009170109050c030a03050d020322050a02 71
    0x209103048038600c0c80001c0141c1e002c1000b190166000e495501e58510080b000441c0001c21a96178207140d401080a01580000c00401d00c900ca1501c0c1c001c440402c8914001000c03d50315081d03000359114243c0c86420140440382c85036640f41c420a10450307943e411074100b52181941d5400c15480480302c101c405800056590003158066000400c202241c1908014109456210449901c110368007440d40c1002001d202c50070b020010b40d0a02940300106107111310301c1c4c1c690b0842e4400c1d4041d00c18070302000e040e40702d4003400c002542581c20051103241d030b01440c0266400301e0600d00050301039032020391035002050849400040182c03000014080d12400c0e0703001d002d03030b1048031684490440603542815071341c0c450200c0c03503503035041408040c05d03c0b074010700d0160310251342d440001c0e500d9400c2503601c1206945490480052220802103a2040c45040e0000e103510340c61501c00401900444007141a181d80020104e10303003010540402800303002c03001e6036001102642c0b504c40e5544611840490040300f5410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 729753758 1250 729752508 729752561
    0x2031f080d0f050a090801090c06120902030307060f140408040612060602030702240d0929070f1707112a040203040c0b160b011e030f02030c060a03 65
    0x7880120700800e611010b202c4400040156015004082c004c0204039260000050031a424065940c405010340c1d0120081414200b000301007040d0000d070303900a5820041d47d500162000012500741e02e80141c0c0000d011f001900c0b140014100c2c082e0041890b841000900060103400d00003402217460035100d18551140307100c400300640e0510301c1090f000d40c00521401c809410841000c0d00f22403030701d60610f2460502004040c1c030301d8104031985812903039107070641030410045d040146060320031803d07410441c4031001d581e91101d40b801842e01040040c40d41d8983e00d2030b0b00400503031000c50140b0010800914041d03200030441c0000106003001d030311441d0440c828020756103859428043c5c9e907100880e404c00a05080c44060742c406001214018019200000d11984807805481b0340040c0d0600880002080d00f00301d040110103811520449544105000a0300003400c081403c0ba940300e181c030031003d4801c2c0002030078989040c0c803054001c080000d45070701e2158140d0144d0524110000144003850421 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 729755008 1250 729753758 729753763
    0x80f07020a181a090112060603060f020a0207050a0f0b0c07030510090506160e010f0915020312011a03011232010c1b03270b030402100503040510020315030102031f08 73
    0x44034856040210400140400c6d11040e00343c849860040d2800f18600d983c03603403440c0c101c03881c4081c0d0700c14603135011a10f00b0f03100d50705004000c028241283c0c2c402d01542492500180d42c044d40c8a040d501e0784001079000c008660074407440d0001c6808c00151802c00d2070110b00b000152818860440d8180034080c0000c030080a509070041804100d0f660741d0305010880001550704045008612090200c0101e000503501d441a00a10701500304c0d070702450329204c0a994810103c0d506800c90704a10008216090b82c08a100303094070b0448800301c40100750b000c1141425942c07108002128201c2c0701204602104880802030064001c0a00a00030020f900340160300b1510410858100b034452048074040c2800309108612041d2a1045060703403040070703d22031375a014000b81c1c0e03500c8000110000300401096140040b040062900c440c2040d40c078500d0195a04c0307880300c511021404009601101090184014000514410030094021940c9040040c3c06032034a004d0350100701121900e1510204811202 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 729756258 1250 729755008 729755051
    0x5040213090c0228050607110309010e0114030f01050a09110910031d010c021504110d031b05031201082d1f0c021c0c080f07020a18 58
    0x140040d600326041c02041000b07481e031502d22404510840d040940030103019204a8002c0044080010300305441d071400c079041200061a040030f02c060400c0d03e41440c1c40c040b040f030340e04403024600841404900380068801490f6014402009400802081500342000168038142c400c01c8407510390702a40d5000390b4090f00c0e032039a8985854001400095083d06150291032020586820082440e0b41010300400b07807040c044c3e0301131100740c4d141c0c1301c0505c0b40343c0c0510002c00000c07145100b42c041c1e490b05807104280044104201b900990400e00c524007410310640d14440b07907080300d83c3d00700003000050900d55a250408410301c1c404440640c00080d180200003415425004404a4580f03105038410491581d00002c0c17025038400d020340041d14030032019008036621b10505001000030301a0541134000e10384421010403c4207609103008172001c507038220a680300c3c0700380e01115881d43c1b144401580d003a50b002c3c100e002900400072040201e15034034000440050b52440403802c0152003c40b400d400c292450 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 729757508 1250 729756258 729756277
    0x601020a0b040206040b1c0e06070e12100608030c100218060a020c031023040201080a0e0a080d0606080709120f060b0306091c050f040905040201021c03090c050402 72
    0x8503548100240c0007052556006000400aa05041c0c0c2c41d01c207030030160b01c0341c00c0c81d030890444401c5d074020ba804141f041c0f92040c0b881000800c858940410040d014051b006210382c81000c09666008404000f0082100231401c1040e040c000f2968402c5041d540c0c0c0c00c01c0001c41c4850180a058040b0b900c250304c01e9039000e1543d51480c40c2110144400d024095002e8600340342140180b043c03420701c0d900d0400200d00d680d250654002010807040324942c504041400c0c1c40303c0c2441c108414040035030b074011600c41d0080a0428005101c07042010051b140c0800f403000200015030115040f40324410a40c07000080321001e49440f9104d55404008031411481d0307009810300340c222090364201003400388481d02c1045100310400a4080f0100c00000d02d8640304481452240d44003d1914000c0744c01440c11048082c0c1038104203003040401440100d40303000b00c2c061080456900e0b0005019a8820405008103035071003c4610300c485188980280600f40c0e800c1c0550f5060000400000c050a240c0300311401c00d80d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 729758758 1250 729757508 729757513
    0x30c1e012003010303031e1e0b1c0809030106030c120506100f0b1c1a10020c130c0912060f060b09090f0402151201051207080a110a0b04080303090114060102 69
    0x4c0c210b070380c2680100016443c07181d4201240c0346440c0800054801e0500c90340035504003150001c82c80442c1d50968101d042d0190245880610460740442c21154402040b5070054601d41c0360300390368012038014800c560024107403401d010300c002030b01c03403034450b100c4005401340701501c0f11640d03050b0001c4a030080c988200012501144010441002c5060107489125003040003030b072140040d8001c1c0429a90f0780b440040303031444007540c8044185458140c3d0890460a400507001c004003100000341982d681459400440f9202c4031400d001c0c1d0310034040719000e80304e0300c040d41040302a28184480241400b0030340d038285901c1e008022500111590503190005002044604140d6500e5903042840c100030344126081402c0301861200310030803d01524030300d98910b000e5003035503140904102040064084854013034004c42000e000b0047c0c0482c00f49030180c0c100c0c2c1c001110300800004204140034541c00821840d202260118440d000400107501842c1d03150028480d020b41c84d0394810301000c0c01d95207031b40543d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 729760008 1250 729758758 729758761
    0x5040e0a030309151b030b0a05150d060519090b060310060e0a081e01110f07020909160906030302061e0105010f0c060203070c0308091903050705030c1e012003 70
    0xa0b10035007250071002e125130142110040007010140580700409038041c4d4107260175002c0d11499515100f400400d94044583e01c00131032411010500310010700120003444c03040000c10382036a400d550003c10040c41c0103403503400207202209103064030383d050340035580986080a011f03030300c80d2030480e003901c0c02008040d0b0510141e915004090302d585007030540742a0000900800054684814011a01c01901e01d98090720f01b40a1040ea060840300d08840501050b5401e10108511b6500071b07041d100d00d030350305490f0800c454541c1d030700ca9444e0850740d8600456003003080b140401e0204181c3c00007012284070340c003103c4098507007503043c030703a030381c451800c0040e1000205004002c2d5610540b1542c008182c1803c082c840ca5080d501d891069a00480d420b50128652803600d8041540c4550b041c0d41c0242800c0207810080400036483d82015000c10015040140108140c400e1010074402c440c0041505000c8400d42d074407207028040c856076248c494039181e52030038031040003041d507071205180001780854030540781d0f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 729761258 1250 729760008 729760013
    0x20f03070c0302010e0a062c28060f0f060b030f0f0c13080609070f1202010302030402060405040e0106050418031e0c05060106050706061d37050402030705040e0a 71
    0x580300354480a8003103640317031044e694140034240034048903e80144404120aa0305041101044c011010a201d2140c4620500801d466001c0307103220481040d40c4002c0c080000640007004080c1c0384a1002d0403c41c0340045024400200c1e60044a030300441c4e59007404a030b83d030f40380c0d40c502c00d000495044c0c041840141c00200c485403560000c40e4006410301e0040e060003845005443c0d100c0664004100030340c8141c0500c0b1010804103c076030014200c51403408211030801e8007214072142003000003410f050300400030400315a20041550085d1201400030841c580152861a028250030302c00c850159103002413202c040d018980034450005c1e0182c40b200040c0d050140740c0c4d0109038442103117404014403090390b08005101806864003e03c0c4a59410392240001d084c03402c112541d5502c44c1104800c1354040e010010141e1440c0b07031740300103c07003050001901c21446510901c0048580703149002d00d0618199215100741c0e00040c083ca000790708540b2807e0300c0380c0a100440d841100c12080381e130300c600d044200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 729762508 1250 729761258 729761267
    0x1905011706030712030513210803090c270f0919060b090106080910150e06030f0d021e010b060f0a090f030b04060525050d021608040810020f0307 64
    0x4100001404440000c4e6568440e8403041c60409002c0f400036800140a04410300b41c0303c0c080001e41550400d00141c4043c40f5224215074981d00e038001e000000101c00603110b05014003941d81d264a019280e11030001d00c2400b80e68140c1c0c51044150403104e00000841ca1009100c81507038403401c0282c0007400d14540c1c049485080541c00300e000c581c1662503801601690300c4a5403594000d0016444407421424100300302810841403c040312031091404140d6880b42c5040c0d006401210b26400c148030b2982c450300c4c00700c5d040c0f0b018803074446c1c02c601c00e542c0303284c00050380001d200d580c07001e0030090501c9840c00b00c80034070b00740c1c0e07a1040c00651020f000e205620b000c5103e40b000b80f03d10b038000d0401c401c20325612051030300f0680c220f42c82911140c41030340402090081d01d010f815407020781c40541b480c3c00d143c070f24542884001028001c4041010104040f655104039038101d0b00441040c0a2400044c201490150143e41c0070340550312880c010350034078032594201c0340240e407400e41c2010f082500355580d4000485 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 729763758 1250 729762508 729762511
    0xf0b01020d0c05010204030f050c01020d1115071803030513060219060209120a0507170c01140a0302071505070e010219020f0402090409060507030c0e01020a0b15100c0219050117 78
    0x16004c1d5400c210000018002524190f00b49101c0d901418129040c48006405c24103803411139003d100180c01c64284061010031b80840000701c5a03109081911050340455540e401065500003200c801c00700413080c142c02001a24814100c4801e50100d42c0c1c44040c201d032180001a0561070402ca8180074100043c615009024141e20141c04c0b50091081e00990038039003400201c1c1600e590700031003c00c0c00040c4081c0d071a1901070be55400146000240780300003c2502d002049150343c144000700b40050032902c6501202d0b1080e8100b500e09146103501e95540009080c1690301c580030441d46004101d1950020074045000549580f228122500035000d02401650803035102d58040e038204107048041c0e490f0701c15202094010400001c1e40e29003076002904071810381d1202010b2106445401c00240e03800600700c1c07107042d4420400c0b0407940780c0701c048400c406c0e000d420090303200028061203001c0c80e901011940c480d900844464291810700084100e040c00ba07800b031580000d007400d20040d1002c07143c0c041d29 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 729765008 1250 729763758 729763763
    0x170303190e0d03020a17060d0f021906021f091a0604090803040f170c0316080c011b030501060f0804140a15020417060c030619050901180f0b01020d0c 66
    0xc0303141c00e0714440355402c01240701c0c1850301107035010401c1a8500e03440302e070500b80c1c4200c02c41c01608a050250010341c1c20460718000420b07a4400c0002c07074085440368411003a10b0f021052902403202d413201130194869644c0b0480c6070b0704030003044240500745164010003591642003c000303c0d140c000d41c099590b0f603d400914031500603454406480c00a09080d000307600c038500500e9010361180003460008054120000459002842801400d00445005c030489003032002c1d00c1c9003036032040c4c0c10b072800340144c0c0540c1030000101d503e80a90900309418071340b02900c1c82d100303580d000c12550b07803115000d9503062041100800050003e07000900001d450521451441d882c0d00200c40301c070b410503521040c10100b903820a6500c140c01080400c4a040e038203044aa40c3c001e0140903080e5807415654852950000424062103000b2410210b10010b500ca1b41e0075014000c0648805540d6844440c1044103001040901d9289441c00c070b84101420345907c034400302d80d001640030307015000c0140300445500100000a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 729766258 1250 729765008 729765011
    0xc1017040f020a030317090106060806010509010908150712090c141315051801150e21030702120a0b0105040213090509010c02070608040f1220100617030319 69
    0x201070259550040c00c0000b9842035403107415901c0094440100c0c0b040151840f0a80d07818180e00384405500f000034140c2c4644c0c03e10b0b20759103800390030004035807900c00d030f42c0510300501603192603004440c1003002c5c580c481c40d6143c848480702c40300c4041c00310450740900303005072214219010600810303010300f401502c82c2ca00140f4801c2d00d41d81e0301032240d0440d191001245102000072404001c5414440c2084030b080c01ca44016040031761604010b40113054078041602c04016041c3c0e6a04059603030b000c0000d24181d00b80205408400e480d60340e45607203500c81c0b20164803030842c0d8081c100130710b0000100280084d50120421201740d21b44014017003e504558025414500121400b15000402d4400c4c148906c014000218054207005000f9003003480b00e8219401b04241c0400300720120b805615440c8140d54010b481b6441818041001c496030f4150b12015540d0500d605c41c815410800080c518080000c01c403400c001c05941e6803550180020142481c030791a41003400010b040703410049844201030081c170f40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 729767508 1250 729766258 729766283
    0xa03120b03190b01050604030302030d05100b0a020607031103061806030c030f0a0c2909150412050c030105070c0303090c0302061c0b09040f0206030603150c0a020c101704 75
    0xe03007042d901100c0c60301d040c03007110301c004240030140c5412401010245c5c0d4481c907160854600a48900c030705a0604040c0392200302007040c944c40c00c0da95000400d035001400352224504040203444032070513200d1000190400044c2800710b60720f8801c69005910092110500d00c1e40e880103041081001802c090b031502442c0100350984d20b0602c400701c42d0210307400c080c2811895034034003c1060000382d00146484102c05c803c41800130949010080400b200d861800c0e100c0410b800015402c0281511513100003402282c00501d403590707403210740c0780039100da000e0b10b05c9540c100702414200c60303040310500c0004a0381013803030700400d0090780f04035110760145021b0103185440360017154540e4084010101c4040d4005a207a010320000d116600f00e000b0202ca00d4003180c1003980f0350003c80342201c0310107807282400001146480c0d44c1040743c420161141c070317032440b800d02d80060400c825070028100480940203680c606450342c07509502d02142c102c0b45440f4001c940d08584070304458910001d0003240d4000b039120 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 729768758 1250 729767508 729767531
    0x160302091806012903010e2a131d040507170f0312180a0b06040c0509030a05071a04030b0a15170d0908060412050a0203040b12060a0b04080a0312 64
    0x200c010b0103040410102d61184c5150800c142c4088213401000f040603005000500101c4400c1c40148e40265001d0440e08841040c188050200030106030062800e490029540c820799070390318481d80072240b180c1d040c0c040358415900b03010714110045400415941000105000e03404c4202880f0040503003400455840c0b90210380080d1442d480285120710800050040082d101603079a00369103220f42e07082c080d05d0303803012560f12601a0b80e0081d00d240d1081d42c84864006103036104805452882d10300a0889480014034182940c0f201071a008220000c100510000181200300040320b00700c84d8800040d0384640e80d10010304008168481c2c0b54201c0d1a118a000280b49182c1e14a40e000c1581e450040c054840c4054005050480d4a030721480ba1074101d1010000850303050000d504c110315150600030703038504801204030300318840c50b000549800408100381c0b51340c800a885940c41188151045040700781c65440e0034032103004600c00c0c5800c5070300c4681c2000000b4810b41039101d03108404100400d0041d60358 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 729770008 1250 729768758 729768763
    0x161101140406060515040807090203062817070f090e120403030302091305090607031517100c02120f070c03020607081e0c071e030b010806070e031603020918 69
    0x80c1d500352001c6031210814061450100b060108014070f0040052610b481c0081c004d840d4400c0e4414507140980c0440001c2d000d40310f000d028140c49010400c50400d8220ba80d09200a42145003e83c00b4040d103440c160b2482500c0000c0c2c024281c0f51307440c00070424035190413103150140810182d82152402401c900340411b0303820030060005148a6180540c4688860051103c02c4103036038140e40320700c3e080c142800568035004c00c0e65a0044141d1502241901c8422904181a8090307132250346400849400340149401c0071440c8194600759040a00000c0c0d141e1500320303a071341104101c181c25001c080150140c007003203038001807000b58801c401c21010140c7c1e940001d04550400d55081d40d02140c002100b185070000512500354034041e0301d01c100c0c00e19580c1103282d95a02220f020342030b100c010890fa440d041d00d0310b90007084001d56100017155515a1111219900c0e000140c61890105aa9030480c12444c074002c5050302c00c80c1107054900d00030710700d0f5400b046a10b02000d010340c0e448140c0d650804000c207105 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 729771258 1250 729770008 729770011
    0xe361612170f0316030b03011509092103230402061204060608030f0703030b041104180905120408060106090510050318070608070e09090601050d080f1306080c0316110114 75
    0x60203103940304641304900140036111401d0905d40302e1b9141c001e100300b481441511325420707a0845c10002030700ca81d0502e0711500401c2601c040c0d6039001814440e000c41183e00d60000d0360407034031004903889030010b02d4604a29100083d00c0082d40030809011001d400c03040b8804036503125016400201c0c000ea07440d007034541554800060800d0719480010a50305254140c060203c11500658080001005d49402c3e8030300e500550050034200c0c404a00c05e40300e160313044d812840c155a000030036640141800940c00d8810340c4a4841c07102140a03c000004125014040304c0c0201d42d030142c14081103480140c411149680000c1070b11408914043c0c0000d0000c4040001740007400c0f091315141d4482c10b052002034800c02e210540c0a201d001c1a0040121070640440c0320340c1101c00a580c071342c81da031120740b8200740c190140360b02c03040324218086440c4d0341c0a409407071104c08948a540303611070a91945910080075200860704001607001034109070203122b00c030710501c52040300c40600009281e08a00990100c0480 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 729772508 1250 729771258 729771271
    0xf0c120705120108060609222f0108090c0108040311030c0d180321020703290f150f060405150415090f0e361612170f03 53
    0x40200340110042c1d00005418054403024009101c18500440001c800b241c0c014250459101a0300c2d00e0890510382519880545500003805001d490140c603400c0070000d10060000140000d490500040c1e5024240c9103000d040c1d000e001c3c0503101000d2005441060380504110704110541c401c0707421171a01807001c7c285004411020300004200c400c001400120002070070915010501d41c1040003424200004455141c01500304145988502003a418004117030b04c00303054850a060030310400d4003500c6908000e400c80702141d41580e00c460044005015084445080302c44120060110720300e003034400c00708681e0004001d1442c15882e00701180c0e030b40198107101c1c0e001c540007041c14000408028000c2841c1d41240c54210081c62400b030302c5002c0c6c080301c1e20813698901400700c0824041c030400f50040b88801c1440079640c0c024084001d212100482420032401340f070180c18545c01c1d240701406c00350802c0380c00c50503006c0f01c2d048158480b043e052805540d280005002000582101e07058480070358400c12 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 729773758 1250 729772508 729772517
    0x130207020301050f0709050d080c030c0a0c0b090112050423010209180c042d0b04030204150b0a0f0e100c050f0703081c090212030405011d090f0c1207 66
    0x2509106141c00d50324044e15807440440000304000c007180d0700c0181182100c4044410350340c002924105000684100c2c0c0d0320a806010010300705c92001b90004441c15440e104a40c0980d1141d541c9002040ca03008518005000605106180c54807a51701c0c0c2045801c28082c0054802040c0300d41c901c2c034401007a60f100721003240d40104241940c2c1c07070074500c10b50212100703a024003083c1c40d1940c140c00d00ba1007940075210b500000c1c40340c103001d0402c1f000440812000a02c030586901d03034450369003050a070001c0c0700491280341014119400c03c54003000f01001c0301d20202165003801d100d80001d46c0c10701c0807212000108190500b0070030059684d8120001060860348580d0890100c13402d03c0c6003440d02803443c2951560003140c0802c0092480411100307869041803524250566280c6003c015280c00d09000e5849400b0102c04118010003000a00468000740c90b0762064605071f0404840681c0303518103099000d410b10700003d42c010f24042450b5880401c031984103107048510f0520245210080e00c8200019 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 729775008 1250 729773758 729773767
    0x614010303111e0a06020c0a141b060a0c02060a12020d020c0606010507030207091d01020c1b04060302030606100c0c15021e1905010219030905070b09010c061104051302 74
    0x1030107000400b42c024000b900729803240000b021851341d680c08200d00038012940000d0844421000740300c1e041c5c405d5031041c01100110019903000381c0e1510102c80000c0c40c0350504c00e200d00c00740381c9a4120b560b106c04540f10181c000c61942c003002000c2d00610000e000388601034488031405451440200821410381034010380760040d0043d8185010801418107041c450104104000b01e600000e4240c119102d1600c0450195546454154100000d11300700020358004107014180131008100a4a0078004070710a03401696018100002e6860318030001e9019000f980205400c3c3c14241c8580400104508185280c0612540ca014440f650313a03000c8807500c2e880c00304200036198103001181503850b491145082c005a80c14140380c8441d80030000f207800c1440e01c41030340c00f08003080d01510780a07030032070300c00d001c140540f207a000e8050070826104480e50b00410401041900d602d00a9a041c01e1060b501c40301c0760201e55481500815145104803035003641480300080f40d540b64055003400044580700507884 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 729776258 1250 729775008 729775037
    0x418060e01021327060f170316053706020d1508060406060909021804020f100906260601050d060305100b04050f0910020d14090a140619090614010303 66
    0x250902030507900d454100f13001000140481c00707459003915851847d031682c101c1075030002841d51082c1e44a10174140f4000b00c0c90740c284003002c03c843d40042e44412a800480a42d031b0521006112503d54103c440300050b04814082490380e405070031500703400e40001500f00c8003140d112481c102244d02c0600350798852020401001094015500200000e90084c0311010301d91f8002088440c00c40007844c0221005c1000405554034503010000215001c2d0840304242843c200c0281085020b005103c0450884408000303548000c070b414078907403030488100a0f020740740d60b0011521544242d0700c041d4416108c00c4003001181c410b10050a9030301c580c50700003c040e034425040c08262000140040e41400d20141044080407020a1600f100406041c0050f51030903a448044028101c40e00c0d030031002ca454904000c216200090540081030281031810134001c100b00100f0740e41d0701d04580090034140200c120041a08554211520480c480d00e00450168122400101d80d40c00990054000030254400110b9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 729777508 1250 729776258 729776309
    0x30207050111220e1003080d1808030106171623040f05120313050108070c050a050d030b0607210504080d09140102010207050c120a020a0902180418060e010213 70
    0x30b062098136a440c0e071500704000d103c1c2c1000f40c4005007162200117108040348a0691050f4100c640c00180c16440006509058086410900403000403c4d0000c0444250700420481c15109032610403100e40313100e0072400111005a072015008242c1c2a0301d40581107440d4000c4054009403500000f6900c19034a0502044201004c40e80008881c1d04100a9840b40d55400c140800c1038034020300707100c4031070b072244002100e0010610702c0280180c0140180d650801001040403482d0600c0380e90144501e00138203040250500c507010008107104682070000d1b100065036800301c01980070300d0070410304080d6641011401c01c2c40582c0c0d52400600f4486041c848031030185c02400003048288000c50030440140d89150341c480300304002e0f43c400c1e17076506e6020410000412501c610260f01418418815507200c40c0e06000c1d4000d841d011350703000b5a801d8002c2c1241094800e4805030b92070444040c04030745068854100509451080c000555000c0212003d042d016800b1a001014507030030045084801d0180d404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 729778758 1250 729777508 729777577
    0xf060a050a0803030f2a07051506030d0c0201031416090e07020705060f0d020a050301091103100905090a20030601090b0d080f070501090f140606030d030207050111 72
    0x184a00c10712002401000000000c0d80d50010401c80007444a444480075180c000a15100c80700c96201c203c0c040c8a8003900d40760180c45c0341031181e01181e406030324400c88203080750b000b00c40346a0503900c010007d1505030b20884940980600605001660040c550b000d900100400c6a40c1049034580b50481d0b00d01542c0254400700410082e01980d203603040145009440f80003500c02d00d8480d04001c5815a00e0994600840b12070815000c0115568000c1103409809034000344190300c180e0b0320f4658a00001c0c40d00c481243c1c46515041c0700400218140a00380703008000107050341507181302d82c2e0103840c00141000400b08881d4500384d10081075203844000c05141032030503008081c4a50602003440f10a88802d4030b40b951a0754000a0369440e0f43d00f19503216100e00070100d01410941c00c10b01d040051080451402070380c00d026081c94212054820001b030350703c00c01518801d405611030b034118031444d4804d501401d109441a00041104010500392800380e4000d801803a8441010031804001243c1590982 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 729780008 1250 729778758 729778769
    0xc04050f0108040c12080d0203160206070f05120c0d0507020c1c05070303080612010c080114100c0b0a110c1c0f090605130803160c1a03010306020901090506030f060a 73
    0x481c2c0600c0c1a98915000500d0b070300c82d401324420103d6200b010041118196020412409002c54807803034001089800460301d03045550240c01030601140800c0d1040d82c200401c00c00030340301d1358030b04182042c84680200d40184840301c01002808441000d03180b0b4080d83e406900c03d58020110702c90301a08000209040309011140e00510058910000b0030200d148012203426041403955540c1e100c0124040110104c61140c180d4685070740c00312502d4029400c14140c0d4602451051108001c0050040840c404420b005c0440c04060780341c00007035071a40c04158042c5003841d0102d031070710700c1064400480d004800880c0c4240c104001810200c0c0404207808140440d0340b410190540e040b4001074014408c0d40070300c2d01000320028551213521410072403580203165881c04c40c3da5500f1401d010078810f1100d120200c5401800c82c0703000178035081094040c5500030490380c1217461a40b840d52002c1c02923202d22061414040655000034042c1d503a200654811458450221882c7c50190100f140301021078100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 729781258 1250 729780008 729780017
    0x81902010807031e0905031b010615030e060a0c0509040c080f1f1703120403050a080114030d031805010c11010525030b0f0307081b0402160201140702090c04050f01 72
    0x60800c3c00c9000704c20800801442d060004042c207285c00c1240c118400c1f80384610f41002080704014180c00150b2101d0112000142501c80c00504914110240e4400801c8109954070450109801c1202c641c4010006940c90501626044c030107008a000d8402610341c48000ca88070303e003005400c0380d0040410354040d44203803141010000085a038914201d590081c00c20070103030503140342e0241e903040045807514514542c8180240c581441c000f40142d1004030b010b400524801d0001904c00710a2040c00712001008014001c481d981c000b01310700816038040d4482c40003144490320b2010580138440d42200384010303681d4214200d100c000b030380e007034130806061400440c02c95801c00c60900c1e46030842031111401031a0201d0b0b82a46500043c140209450400358035000e240700001f5020b00004952868190703003026400aa02040c0800049004011010040480c9200f40c440150b100d001d0006035900c0d06414981410310a0f00804d070362403c1112815400500007409200070b28041c0b508006492007443c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 729782508 1250 729781258 729781271
    0x20a09170a0b07090e010312170105011b0309090e0d021207030f1d03010f0516021c0c0c080610060324090b03030405030f01050601140705060c0f0408190201080703 72
    0x4603a035195a898050100b0402d000424501c511a00380f03840180300c81c4075161041d50310b1303013810404414600114804941800054041040f81d82c03002030481e14142c5451030341c061391804084c00d060001c01c00f1020002d42d848085040f81d22441150642e45e6010004c1544012620000e4600b5100401a00308120184010700029a0025002c825081d16181450100c2640300072a004100c0d1103041c3c50307155003000c0603002c0a41c22030b400300344142131841442141c0314104d0741c2a41c0f03420905143c02522a1400324030080c4d680260040903043e0303c0f8401c843d8a856988041c2414120180c0b060500c05510322000c01140b54140200402008043c031075244a184484251010074100d01c0398007901c2c1c2d2100003501c3e207035400b80240c40042102030161503880c401003238647c0c000c2100703c03040b902003804040d0140c142080a41a00d0748a54070200400c11602d401c0350b88081d540003212600c916080c20000441e1064041c08594415041e03179140b00e000e14070a200140698000403c10303402c01d8a00207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 729783758 1250 729782508 729782549
    0x20c0a05191515230f0a03030503010b16021206040b010b0405030307060c09090204170609010b0d03050c1c050c121306030b040b04090819050306010e190306050a020a09 74
    0x4019140036503074402c0020f2400c00e0880714400a6481e50140e160189001c0c6102c5400c0062110300030201001c031340c5140f030032164070200300702101c25000c01f07800a0000c1c0014065180007030300920b00348046401602c5181403e40c0000d1070078540840307502641d00400203120801c10103a45e16070150164140c00d03803c1505090120307a80e0b0250000192056880300d82217039900d030182c98281d02401020809640d140e841d0750840942842e13000d45030009100354000a038620506206800c84501e00425244581d4843c1d101124150803100d01e034091400341b115082c01d0040072a180482105550b126691144407000c501810700220251400c003035601040100c100c0040b44844905841f1a405c0009015504001240c001c0c01c0c1c3c18941e9070400d180c00608000c1c804104050012000c5220001c0d02c118100300b812210f500013507408602180c0000615540b030300e8004803030343c03550139101a003594960b604d0725820140c48041c0e480503009580010003034241c56100f0f003290041c2040161201d298071598 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 729785008 1250 729783758 729783773
    0x140105060d1101050a03141303090e0f0f0405010b06042301181a1207030b0306010603020f120a0b030a1b0522020c030c0a05010f180209010302040b03030d020c0a0519 73
    0x2c2d08442c10070000040180445010340d000740700c0c00d42e649040420074a410b08500000c84551101900403c04181c1c0004200c40c10007001845207020b200304081585a00d588038449010140085856541b580d0f0202c0c400c2d19401c1c090b0000b031103200b2000c0d2075034840168440003c414007201d141042001c680080c081441814200300700c0790708620340003200c0d035040c00b01240360040d0f2180300503e00c40c22042c008680c0e859040340c8440c1c80100d0130790740940d0703030380800790201c0c89940100d03041203109005100d02d0219180301654000030620b80816400c0c0e003100040d0400100840c00c5544100180f1004c0c0c000300e000d40c0d1710000c0c000070307038083d036070750b5140000414595603000120300b080e60006164542542c0510645400c45051012240078640303030b1034400c0c0070f400002807400c1d406152031070621601085065101806070040c2c0304d022140d01310f4003800051302d41050015054801005100d2404205200400e280b844441c09421810103030f01e4a00d050941494204106019000b480400308510 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 729786258 1250 729785008 729785033
    0xf0c18040b0114012303100f061e03021c092303030a0e070b0a09081b1c050309060408070306110c1c093302030a122304140105060d 58
    0x505650b250b4041d01d00300122179051221070202d294103580007181d10070301c8425000d980111054040303503800c01c0d201d500c051010405485100700260440d6061750440b0021142000440c83c05d20300036103483c4290812100fa441d1000001c0c078a59900c054003c140040b4402418520385a200000d828419907000550f60380405402c400b14aa42c820001800309820485c00d8018102d45401546500001402600307010441c0300c0c1c0c030814099050500b0100341c13204003481007210024010060102221200451131100c20401c445900c402c108072141540c951010784010301c0d001000f84a00c0342549818070907520316102084042405010f1400c4120b8003241a4902c40303d4903514100710807600ca81112001480c1d4003043c0d080c41040d12004c1035001d28580c100702c0380d400100e03082c03241942030b00c12680e07031081c010090000350f1340c4502800380625980055a20010098040c95013102419422400030015902101d1055407c40310400000c0203004e00d0f1707071181048403013103200801900d420140c1200b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 729787508 1250 729786258 729786269
    0x30111040b120603010902030706050c060a1506030c09091805010b030304030201080c070503120c031501180b0d0e01020a020303040c210209060409060c112b0c0507080f0c18040b01 79
    0x40c14400111079803400d611403007106e80c00408407450265503034000352503070b8020715010006000703500000d41c0100c614018940015805107a40000c5031425204500a04031440000b0070004d81010018180d0703050b0148020b8001805a200b1001e60940780107400c540840e00400d00941003800b00b04050303a0003141141c0c3c005c00c0c0e4180c21307945103064540b0134207601c540300e0303070801d05a07410381403080c4107103c0700c0994868624828035040b100e11303070b00c01500c910710702c141e541c00c0c11074003003e0a0040800c40300240c400c030490b1400c0400c05800041d815401d980248900300c1c01070344003004200501c90141144c10042c040105241d40020310300210715a0007220b490040c0c0102900d50104034540c9455204203c8250400380c104017004100d1001802020052a211200d01c030780d0350580e02201110280610464040d80114408a0490403d5441695101e401d551502961500050300716007804003400b25078038880035041c0c0b26007080c1017060812070b0030034803844500f22404000c0090350118801d8103480 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 729788758 1250 729787508 729787537
    0x41b0f0e0d0212030f0a050301051305040b0414161d0601090f06031a13060303300c0c0503031008160302100e060f0d050a0e0a12050c01091a06030111040b 68
    0x68818000501d517114600c040a01448000b5401e082945d014004c0d6040c1e6804031017910030000020403107000d644064602030700041c668004180020141c260f15400d6007081001da40b0801241c02c4e25440e180e0f0503522104c0381034100c0c3c610752990403030104080c0c0e01507000d0800030760150601c190740c810301010303005200905a0392060206c03244203074551604501c0c80141300104010103580c1403805010303507202c124082681503440060b01403148141506414442c0010703a125159101d160018107075440611090205184401020031000e00003507204915801700d51190910f001550b03490f10550008040842104400034001a903440c041c44e0b246001514000c60a410441c000074601d00c14440215200013000942241c030f40c1240d0015403280e030950600f00f0100301c40c2c00b2030948034036510300002c1885130101d05a0f54000e0041c0d020700f802c0148080001790244042e6549900e800e840611100f000071500200f1500c0e16090142c0003010302c00c40c0c40c40c2c3c1013610b813111407880c901501d891101c1e0030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 729790008 1250 729788758 729788779
    0x4050708010b0f0d091b080106320402160308130804180b130c0e04150e0c07050703140609010c1b02010e060f030414070e06040911041b0f0e0d02 64
    0x104501035809018486004200d910a1858004084246c1714035500090110b03a0000a403c18103114030411a5407001840414076600c0c40030f81c640048840000c4400300251028854945540c0f000d0030501001c030301e011108000505003c0c183c500e008203404006c41c01e1054a400058060058400325920780401c611989004510440908203041c401a0041d41442d9100c0c1008019008041070780c00a884140c0003d15880901c8140e400e02405d085046920400400001d81c281c0c214541c8006507004090806903032340d0310030f41498110780c420380d0040c0c200c940d00f40c4d1094090008035004002c24008215161a4030700240010340c01c002c020032002440603c100c01e5900030301e8030a118100051540d591142c81c2a00400150030a032402d941e070100785030000401610000d80c220079922180c010030560766500040002420704000111901c02c0840301401203034541380034020700c031204902d80444e070800503072008040c04041c0700c0003000c0005c035003090740068030341156200003150191f5088644 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 729791258 1250 729790008 729790027
    0xd0803090f06091024050d05120d0203070f051206100203070204050c181c1e060518010c05070b0613060305070b0304050c10080a0e1903030b0f04050708010b 69
    0x400c8088490850700340140e404002e09800c001c1340c4030b0741c8080c2c0720341304210328281001d5540e00d4001d4940303c050b800c030984400b4840d5203080180309600500c0b400c119400da055091032001c2035003104c82d181810f80c1d0040240500150044031105900100745017080c107008800848005070040980300380d0144c0024110140340750f100384201d2740da842c1c0250003409541400208085541c3c0000b42030210482004407845a030302c0e190102e0129010052401030781c202c880e4407484003c5003850110a214001c40303200c03000040340c0740200c500c00c4001d84000c0c0c011400c0c1d0a20b80742512040e1210300b080010070044000017039008081642c119800303544d0341c070800d450300720346100400c16500050700600c160200041e403041d1500045100c1d62280050315610000703034050110748469011501c2c0400c140c140000c600070700030f91124910722081021103500c1004000c0b09003910031208420750000f5115040480241405000c0112086045d42c080003030f868251002048000107000d240700e841d0000404d070f5030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 729792508 1250 729791258 729791263
    0x10503060f0a05040c0c050c090403020a030f030f091b0b130306020706022218050f0a020c0c060c01090c120210050a02161205060709080c010c0c080d05070209010e0103020d080309 79
    0x9014060030411900b2021795000c1e00850204008941900c10241200010f0030224085030188c0d41c1500101040001a0f40540b500500c54051000300b6139203048600e51103419010b070282080c01040d00003c0e030b2340b8440a08c1c80021007500000460300c0d040008254100005c40c3e880308586d049480182c4a85103031406034082c1c8604881c460810030040c10b807200201050f40d04e00125550940b10401044c808100710f41500c4044584440d10000440003d1000c8240e800510706001d014003038903000000700300021960381044180000c16035443c24a1702c208443c180d02d900141a0300c0c1c40820f003090103a030008624a0101c030b50441084800718a04035524006c0103950603441d000c8006900c02611102101115041844103072840e00c11031000c1018580030b000c941041d5407004000e021041040001590104107008049440c130140f12000a00d00009000b1070180f21202d13599607503140c03410300406c0344283c81a04280711111013400100016540e5510840700700d039000c011181c030f03550358680650 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 729793758 1250 729792508 729792529
    0x90221100204030b09070e04050303060d0302030d05010e160c020607110a03050d02010903080a090b040209060a0801110c070501140d050a06120b0708070c0312151802040510030506010503060f 84
    0x44030a00204020040095415180303104190f884100c5011541d0340004114407130b41035a026080341c008001041d014207218001602c20340c024011249003680c25140c440885000b640300d01421401c0405101030a2820004880c1d07541162812172981619a000910b00740303c0c10500070290114400c0400843e102d11740c00f0002140c10400384c1c0d0701103108401c041d0103411340603c00c0340069145400191900d00300c0c80b4040c6c0407a000401c5402c41e940361f41c284000128094441580890001c100144101003401056200a1100d92564840d58458503052070201c41d504828140803d01e680e0110228000043e81c00c4000c0c10b1178003064645901010f140240242d8120501e440340fa6400c0360140b0010701186e90080003503070390b4481c3d02d5a139414102d54841c28290000e00103440302c0009545840c0355000000c0c1d9a5011006c551040e0f600d0260101e071210f00c110414100c1c0d004242080a0b203041c5144600c10111410244980c0c589840002d00ca4403001f411240710b81085080c0c4640b0303442d00d100380d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 729795008 1250 729793758 729793783
    0xd05100506041b120510080616050d09200306072106030f110109090204060234030309291b01060f090b0405180c0907111c1101090221 59
    0x1c4411000e030000c020700c4520000148180c2c1340c10000401c0308006009803850881c3d01ca80f018286d42c0e00c62415000c0b4038441041c4440030014144039403c42e00c9070a01c0761902d080e2007848403140203014011400041d000e42e541d50342c4260000340400c1185074004c11410454100202010b80c203040802c0120018100303900003600d2525083d03082ea08000009045020300785003601d40040c0544d40c0c204d01e200341d200354004e4000580144d040744461419615001c1409042c070f41040341d5019480080c000d00c2a03140d40250300082c0008800c121181d00c01c280c28415060090403e0344c849407030038034140d09100c0d900d45200e01d00005410031104400a51001c00588409400e00010940d18076200d0060103071501c0e640d00c1545402e000ca4020007028030302c00ca000810101500d403002100b801c03c4241c2000914010034805c03200e040c041080020b000c0d5445054000c54205202c0c035000314011300b1810b2109030440140c0c5084034510150f501c28031010407074010740c008444996000c0510605040014000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 729796258 1250 729795008 729795041
    0xa080c0706050a020a03050a1506051b060a0207140115050909030c01140601020d02191707060504080a080105091b030c0c060103060603020f06071a06040b03030a030b0108060d0510050604 82
    0x34000418201c0d0010010b0131401d540503c2036464231098001100c41c01c0070140388481e011035040140c5c038000c0d0050403619059103c05541b00b06407120640c1094021540c854a450340081c0040030412840d41200e10404500700801001004003a0509803e0003405100d110b06802030000e80295000c00c1142d0554850600070701c0b040c000d400b002c15446d1400d480641c054000d2080100b00288005a03100059502c03600b116201000341d242d8088008810310051160030b41004080003007050350040341c4c0241e100b0841c02e541d4088404c0d00522038101a00140c1c8030700e10002c18080751114004040040849062840c0e981b600d954201d8580c610401d0b17000e1500b0b0096400000c1407105543c0800100e900941d1036004940d41e6104216051141e844020b0013002d1f214000906ea09400c20901c1d84a6405440012030200c44000070303103150000d200580c0003070740314104090782e5680802c0c1590801001d5501d80011511a607509407a210582c84c1103040d1039403000014020fa94039000144944051a030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 729797508 1250 729796258 729796261
    0x1b010903030b0906010c0503090d03051207020604260327160906140a0b0d1401120c0e011815030b090601081b060d05040c030c08030d0e0a020102030a080c070605 71
    0x4001d00a000920403461040084400003249540642c0050520a502c400650701d0a08a442080445d100d41c00d0140d0803c402441100d408484860b03956004d041c0d25001001c10f4a890300d0808484526001e64245584040002c203104000d04001c0e40d41100c42c0545c0001c2c103040040000c0305c0c0d0844250001e40310720503021000940140d840d0070304141c0e41f06050a02260b0b440741061141d04103031407000b0350030500007a0304100b05c00400018106140680d0400706003038415030780000d02c00340280c0050118204150005081008079503004c0d00501004105403e0340d0b14100011200c130000f44007040d42c0c6078035404000d01440e00d004005000e1540801c01d40898186000c40359034501d000d001d1264240324031076000d0700c4506100c0c51448611002003030949407040e007149000103828080c0048421842582c000b2000900041aa4000d001480011502e95100d594060140c900c140711141058100012043c00b50364044120741b25483d00e41401b1000381c480e40107208080c410385001a01c610718050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 729798758 1250 729797508 729797513
    0x303010f06030f0e0c060c07090c08091c02100e0a0804030803100806010302090610030b03010e030913060e01090905150c0a030506012c1309050d2309061b0109 70
    0x44003901618125903040140109080c1034100310391102e10003025560100d4074016091824500900e448990901954005641d801c40a000d89146422080201d202c0c17030308001c5121002c00c00c20945d0070701d883d400b2039105c1c00c089002c4e440e200441c0126031440c0d1119501440803034104070524015521400c45e079a01c980c2da00308014203420580394213040c0d103d8a14006441d03800020b455040c3c07500100049c00b1600c41c00304010103451607900081c1813548502090350703103960a1090344031080e640006155a200301408105084241d60f4208200134940781c0140a21a04900e0030b5041da24010b800180740003280c2460752800c081c046116a2040d14201000400e06445001d40383d0800300d51414015512040019101a441504042c0d0a0b2070000740701c0c02c01650104100d422000d020b0700000004845011031001e5540303152046e50300740d00000441d00059481042d0302c003041c1444038858151801642d44d1507051154551040c4544004584496888004203850350850410002041000c0d03032803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 729800008 1250 729798758 729798779
    0x512070614040308030f1005091302010f090b0f0a02030f0318060a090506130606050d061a010503012603040509180606040506181302030604231218010e03030301 71
    0x14010100000c0c04807903202070040040341030720240c95015040e24250307680e155101414980007801080c2c144542440054541c4401c0200c90007403a01070320300300c4031341401c2c0005001c0c40141d40c2400304000580c0401c00ca03004114080e5441e421003001d13482d5454a804904074503500519250a001807400000e110200c150a00200c4d07a80040c80196080c656602100e0310440b4071449000d0400d810400c00070340440044000301d07503a01d01c0340c0000590a44c032540850401c2d44100012100a555082400140c074200070448081c1c079000d107000d51540d03040c4095103600d0501c1100d808040b00e0900c101c3e06014505009440181030041c10180d0f2900d845d41a40749503240c8915060301501a0344040785407818240141d40c41650064424011940b030f820070b410805800801d80301813919071800903401030340d05010043c06540100c4110390310a0828404965103400298451b500f54042002c03c1c80b11071050040d01c00c404d88101814118810340c10040e5034003040b070f50b03947d685400300200208030b03540207 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 729801258 1250 729800008 729800023
    0x708040b0c0d020309010503060405130c084b0708010c0c1101090e01050f01021e030a09060206062b02041d1b0a030b1801060906061b0c050402030a060512 68
    0x881084071002e00d4011826600d0b88920200140020410000600107061903040035800500a4880e00c40e041c1040d11813400c600d1258000103010b400c594104408446202000c4450900102465801d0310030382c0042c1110100c03075018103880c45d960600013416044107101d4017000307100360740091002201846d4001d05202c0d035520100d030060102c9410549075445811044140c400e00078030084c89900317100c00c11188070b030303c265018114480da800c4400b400c6080d03400c0c3c2ea0030b4600c2c100115140c40480001801106040e0055000c561014041184a41e14144e07210416001c042861901c1107880480d01c002c8000b11802a400c03d04081d11203e402c4180e900b40000c21600f84141c4c0e010352440030b010384c0c101542c4041207901500000080c000b0507100700c511b50b0414000400c41d0280e0021620080c01d5800551121104544d81d900801110b0781143c00940100e48043d1a01400e43c05aa244e0748101c03201d02500307000343da01100103000500d6580c00781014080c014094110001d544280c10303070740d004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 729802508 1250 729801258 729801277
    0x1c0c110d090617060a0618030f0809030601080d0c0206030406060b0720012f15010306090204050609130308040c18020d0b0303040305030d021809010602010e060c03060f150708040b 79
    0x41d4601d42c01a80301c0c00aa80740500340041659003180c2c40c080003100d04002e4480c2200e0a11585400040024504002003e274280316801e8240c8802c004000c047c20400d0590060340c9542001200b850389550064501d08043ea045841640301c4d02d035410b00c44010501034000d01408100060b402e000e000c40040d012a00031904480e441000e510703603004440d080c0f01001200c0710600d4940c1075039443d8080741c9000c0400c0301c42c3c5049840246041d01905d15207042a841910b109070b84403600c00940c1024011650f0040c805d99104070182040b41d0002c54481e44010f0140401000d800031130100a0408040c070000c00000101e00914005480c3c0400250301041d041c40c0c0342d92030701040d0300c00c40c07d0200030388080f00c0c0c00501950070f2440e04510b075030295011449401c05241304800340f0480d0390301c0f0f600984c003070078484c0d00000f21020000b070140d20306080a021245600028400c0020a80d1980c8074440c001106032030018800a69810604203030199001c000c00c0f41002246c00b040f905258400b500b070b0900d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 729803758 1250 729802508 729802517
    0x203060301060906181a04020417210f0304020f06030c04050a120c171c09030b10180b0609060a0c0506070504081e151603111c0c110d0906 61
    0x280d46405543c1111560300c40d4200e25900c951400b070013011240d001120041101382010340311502c040c00201213034042d03086044020156003141004400c1007100307025134400c90258080c01c41e515216101d2074007c01c02e4550310340e4400000a03003103485042ca00c0c142000c018200945a041000100840c1c2d080f43c003c4c81d00513038050b070000501c141807901c01680203070040182171540741032100d1200200c0b030701031007102c042c0714801e112400f00b4580c0d282c2665410719075540c00007050a5140c9a0714a020240140c085600c1200e030500002c04940300c4025480740b02100042d00c107903141c02180507030040300542640001c1c003154222071a42c00098003000584103c055551a51300d051003070742c540c050350244008981c00344009448206103688407200c8400705508940d01c00c0d00802031000c010004840c50303100d80702101aa003201e10703010702486102c945800652401c00b040c841186c0c241a0f468020504001d80b00c2c07804445250140c100490010940001d440d00d002c40340300050000103c07449030320b0004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 729805008 1250 729803758 729803771
    0xa020c210c030c1e030a0c06182313090b040803010e01051219021201020703031509060e040609080c060a142d091c110d0e030307170912010203060301 66
    0xd190120300d0000e1004000c0500780f0180c80241e502d02101c01c080c0c41c2c0358042c811b584065010440c041c80e0500100006c0c1d440340f28820103038204c00c80a030801d501482d80400003000e003042c03005070303051448849001500c0400010491024030f07800ba0010500240c00d54008070248400c0c00001d40085040c0d4208400c2100c1d2039984030705001c141540f940501081d50040261000c00911405a032586035000901e441d070fa511305805298220f9200d4803049001c2036072007501e0518440c540e036101d001007596140c208416450b29442810490000b00010001c82d40c0711403140400c0340c0c00054901444400c0215842454500f440300010041d504600103100c51a200083d2989020042480c00340300b00c0e4064130528403501d82a00d00404040c2a10099009101e00e040090f447c642e140618005544e450102c0d1003c50045241030920340c101c0e05080000b800020300380da440000803500d803d80e1001412003034842c4191207040c94002c2c922541d5001000180c0324038000c038150051400f4442c101d000700b150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 729806258 1250 729805008 729805033
    0x30c0d02070b040306090f0212010c0801050105032802071205071505010308040e07170a0603022e05070302120d020d0f0515040c05040305010e03040303090e010f09020a020c21 77
    0x3580705902c00d400c03034a0402c02043c8001101c84d0401503e082c443e43c090f00040b003165002816100000319000c821381e40d24a80c0c040c01d03a40c41030ba40381c0104001e0030072510354209404404c1082022410003906d0860110031a40d0000c4030707504903080745400020750780c1414240c1c0d800034010b9100000aa400c030391400c80c5010003400134818036049075801281146400d15000d806444484024055014040488020003041041c013080f98032896007410f0001d0311608600c100881a410401c2c0b03045807001c0f4550707011074207000c0c502c0000003600b5410b01646400b40ca10b4100e00c1d05220010042020101241220035184681c0141c51100641603051000c0d440f140522000c0742d034112001281d03003080840841c11401c00343d001541a0413580b60540c03a064803034454500355000100d480c0c826620002e420800d050f40803650101422545070710300340c1d070f51500c0c1003040da40c1110302841518a50024056100324000c0246070340500002c0c06840003002c8210a01090103200d00c003a460314019860503940 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 729807508 1250 729806258 729806263
    0x110c120303090634030b0405040b090f0321180f0c13020c0d0e19030c031106130b0d06210302010606090503060118061802030618041e03120e030c0d02 66
    0x105403035500d100c56058010b20b0808000240320440c1c000034180d5450210401e0f447d203020311446a4000c0800300701a0509490003464450410b505202a0b00180320f00684140700e07000742c0044d075000305410034917a1204d5942e00d41580c0c80c81c8a020700e034407403400c01c03d111207000304405864481c102d5200c10071b0000d100d10601603110704068a09a9003041d03c0174140030340141c0c59a0035803800a4508074040c0403c40a00300c01904031b80040d02e4543d0700c010b081080004051400d07540342c80913039446040c400345c4c0b000205070001078007a030060000c0c0031603d5628641698001802011074000100d00755100c0348454085d08030a0b4404d400550a0040c04174100307000c0c12100e0204c44010b40100780c83ea133409142d00107001140b0344d003540240c844d200014202e000115503410b0700000b20006136070b8100181001589203045c1500b15011407840d04110216400741003082c041401d1113001241c1d00300030702c0c1c111860700c9103104110b1401e14009184042c0c40300040a400c0a0290300201e8500640000d0240c1c1d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 729808758 1250 729807508 729807541
    0x14090a2d0b04030b1b04050d0f0b100e010308030603122a070602070e09030c0a0803011e050d030c0f050d020705190b09060a0203070206120604181101110c1203030906 73
    0x2440d0280000116606030002e580c50400c17921408202400c05403a44002a9085d401d800151882c40081c170803401800810b50320660000c0900f401d03001164a070440084c02441c0500c80a4507a001c00701c0020103585050155405004591891a50b11008201e0030760b8124104c01440f040610011020b0401d00000103014058074199001048658606840c1c000e14281c0105804035074041407007118510301c03040014030310061003210510b8496040480c40801c0b4400d410000c16000602d10081005860302d2440350500c90b01407620b10260100c0b401c180c01444a1544010b1180c41070031194120130780e010880b10160b601c22684030075584034202a028440c6d83d5030113646000e110821001145103403200082241382e10038019a802c1c80101e40025032039410880440c0404140d80007000400d1519206d1510300695040c140c50140d842e41c1c540000da860340b005000d05109a140040002000c01c00c040c6580c60001403e0116030404100d205807070303400070394050b88184130745404524810071032401315 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 729810008 1250 729808758 729808763
    0x60e010b030c09061903020d060b0306070201060b030133032711190e0708060f0301050907030b060f031014090d0e0103020307030209060d060602060c090114090a2d0b0403 75
    0xf04082e860303610800c00d10404860b04584500f816000001c0180c8030600c02c80c4401e40a68400070700c02c1a070000381400c01070010213510859250800a0024416050640b4196403078041c903000390300c071000c555041290408402b5182990909030201c0220b900d40c018540c40342049083d01d02c0d143e8084058225100800030081001d00d51403c9401c030780c1000f01d04a40d03c5110200c0904da40c50b5075603481c4400f0395054a0f0600000e001e0f004100040c1810b07901c2c4035842201342d00811036441c044801c2600c03a2801c1c04010403c802c4030020400c559265295803804c144014280c464a05030303a200d40000301028114000d8045240c800200b031034a01007100741c4071a51315115096035400c85001140251710060105007415402d001d0740b01c650320b034100504620748803508001029402c090303010780340c04030041c200c1d441c3e08010401c0034a1a43e1119981e43c001601d10305490b21740c02d0311400600d52141c2504044081d251003254031040c2070003201ca8030246072203000848500c0e81c40304480c640c2482030740400b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 729811258 1250 729810008 729810019
    0x323100603020f120118060507020c010c03052a150a0e070803030f1e181203012706210c060302042312070b0703080109020301240504050409060e010b030c 68
    0x28403d16040031954041c100208038000500d004250b0030105560004200940c1e06a03950380400c031290780c04002d0302d8800315003428200300c0e080d0180c1d001400382c441c1301d0000e501c18168980484105030f807001014030644040051742d02c4103004a03d00c02d42400c0440d81544d1b1141082000e0581d1440401e0b64011f460300000654138581d03a61445032412500509403a9285055000c070040b130440c640c80b041e00078005a10320f1640c00009075042d81c500100c041080400d0325040004214001c0c15009003107a07011b2940c0e480c030794403402682c004000d051f981d02861050020700e205950080140a000071ba0f14461300082c0f107010707280d590450480c0a01d0040e01024003441d00340010204000d01988059100100721150061007464150704050166000ca11190404180c2804054111204a000d4004060218110340c5040b01481c101c5032403c0e4205180e0105010078000c091151741290701070a40a402030100d804a458900d00800000202900360b518007281c00b6014038000c00c061000c04001043c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 729812508 1250 729811258 729811279
    0x90a1104030f1b0f053a03020a12021c080f0a0207081306020303102c090f01020c0a030906030c080402040e0106210c0b0304030f18032310060302 64
    0x21029159a14110107803805540301804015100c40da14422019020b10310003100c40b80e00e482c0c2400b01c802100701d049110810700c1e1200000381d03042980c1e41c1e1b011900180741c0f2030841350389003816030800c103403804083d24594244183e41c0e009034002460014240c0e988140303d00c1594014400c4445840c11703505020001540400314000e000581c019100f03081c02102d54515000303481017029021451136120001680001c400c201c5c0f00700808640100405082400c55001b08502a00c8581c2854000c0351f0210943e402c00402c8081908100310101c2c080340c1d070000c5689440c00c101c0b065030344d4403000f42180058208e62001c5840c5e84603001c1c44010341941c1d01d6000b83c1d41c43e00da08001c0641112200303940c65658503440015044080d08181d0319040d0320b095041e400a05509002c4001c5905030000d07a140c071010010301c800280e000c3c0001e00040f03681c2c40c0900603542c003056080804c0920750b1014000020b20b406824a4018404041228010300c00840d2400c2d80100d400e101611024440a50310444010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 729813758 1250 729812508 729812513
    0xb0a030903050412031d0f031c030b0a08030c01110f0a0e01050c03120105150901081518010b0a080108070803161506151d0a060309150c0e090a110403 66
    0x30860041a4881d007042400e0607201c0c0320360a02c000f0303050002c0d070010700540107850482409105182e03d40205441030301340000d29802180e500c4050361183e8440761004c0403070601c520f101e0b0788083c0c80034000500c4402016940d0280b241c4c2da40002c0402102c55181480d40240350004000300d480c0b40900b402c0c0da80c1812013200064a031803000580b080e061160400044007101c0c030510003008502c560816555403541401d0a0140a1125020329004401c040204200b41ea810980f140d43c800c10030a028109100c5020109001c410700406007102c038060a000800c80d801454058454a42720783d6400680341e0b40d45a00c84c1d0f071000f2900c1003160721740081010f048021410810041c40314007034240d034812a070b03000617404122039040d40250301c00022040003200c01980505030b919040c560303640c1c0540c035034030b900005980d404040c030030703002495501c10070380003040308422000c50b441c0700c041c2041101b6207400f4006170480101514a500c141d40c0840080c5290a992080d040d039809440d60a0b0b00701415039 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 729815008 1250 729813758 729813761
    0xf030f02103801080c18031009060f052203140310051804080f07050f0a080c19170a050c0f10180b15040f021908100b0a03 54
    0x1001000114001d00d00700d600c0500e0540030b107450b124048081103010290a000701140556020803a05034a80704440484039680e000d070845810601912000369102c1304001b06820406200c00d03400d4041c0244003002c1e0141d000c9500c15203865001d100244410441034501d5421034000719030034400c010b01d824110340740304034040d03134100c40522030304000e0250781c81c1100341152900112000590300001400c00d0009050805182c04d09583c2e1003800d9116081c1a0780304802800703041c1004400750004550402030040400204401541d0351040c0c5540010505004003280c0c0302d101c50040b030380319040e6411090103483d054492119005100705900c0c15007110241007580c03200c503a00f402c02a0601503490060020300c980c4c1505800345c00101000408040c210054984502e01c800c0c1140003c4260008100950400341d0312002c100b441d41d0319a4071050000d4000d200f00076081c41f10381d01c08031f603183d0082d62854800d480c442c0262030710302c111707690103482041001c0d95000e10841c0d0101403191012040c0603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 729816258 1250 729815008 729815027
    0x50108030a11060708040b072a170a0503010b071e0b0103060501080f0c0d02010c020a090608010b0a0311090402031002070813214e11030403110d0203010903021b09040f03 75
    0x81d103030000b019006000c40000110910f8600c4c00f00081422503c81009042c2c841c3c0440340d2b44d0080c04600380a401c10028269000510035040d6890b400600341003040403001c80700c0280000181a001c0f0f1054900b07203e071010300240030484015240c800003181c004000984644100c580c0300007818000091000d00202c48400e00c070807418800c0c0c001c013a2006072340300c102d080b000e00b1a1280000b8080c2c9001c000d1401d580c010007000d07004401b200802d0011030b800500580410030151800541915584042450008440003031103840e803002c40c4940c10049104014094403150484e40b030103003034454482c1e280203080380c40c105007810400d48240e00013036900c160304096014801c3c0c4020398568205951300c409410700c24008040780200304440d421072480904461340038250300e0714228084071100003680d0307441540005400140c0581f5844c680750307103d829413900213502400078071550001e0329010b95541c400012051921104c2e00149606050044510b84101e4010f080054041c0361a02c0540e81e00c8032 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 729817508 1250 729816258 729816271
    0x609093e04060b0f12071706010c0c090e10290909030904150305011515050903160608090d03090803040209070c121d0d0c06110f01050108030a11060708040b 69
    0x11212070006040c0e124001420100b5134650407266250588001c031903013002c0c0100b28409010269440b05401e8040c03041c0b06500c424282444020400c0a041c180c83c1011150321109116040c1681a01103030000b0038000e0300b44a0158051080700510042040d00c5c45440c0182031904000900f04a40b130328021801c260031a2041042e24648001d01c0080381c284c4032030403031103240382022400401c00c0100900c1500007080076504400703442410100c003106140c0854180104000010501c3c0c041e07035134180120b5680422548102c0c0000f55240c4c4064607003030b002c860481007030140d88840c44011303000f0302444180c1a07101011929688c0c8550030001501d401600d540c00708804640410300140107848030304444495612030b1000300b80da45900b60303c12410a220304d0300a148031088503002602194598096840500b0805a9403450380141841d04c80c54805143c507542c2007070000a1403090100c000c1400e404180c0e9540c1807440b440346220764543d0181c0e00240001d0b000e20000e8085046034120540084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 729818758 1250 729817508 729817511
    0x70807140d0f03110a0804050f1c080903070e0a0e070f06050a12060e13110102030a091a07081902010b22050a1b050909070201140c1303060609093e04 66
    0x7104114203a24005005d07800721020381001905000903d0030001388600c82900302c6540e40c034076200b02e00c020840450504014601c4c1c80204100302c2d10b0380c0a1007800003070509899000c42d00c0c41d002071884e000d400b541c12445014052807401240403c1c03004a2442070f200e0603101d20f8581500308a08880c4001003020628009584042c0072414880c1d6043c618017408810031050703002481810305014910a140c03c0343d06540c410050003498a070000802412141d46a464080d610504040c6032214424071000500c894400140050700d41e442c801c40d0f0035038100c41e038002c008000a940900440ca0150350240a100d0303a40744070006003c2454000d0303980040e100d000800d808140c1c103070f1295444010310424010030404501140d0a0800b1078810764454282d10080c031041089040030600b440010700000c52625002a881c8035003001806450001e561018040280301c0d51109450010050003004984180307040307860031500d12540351a50b2000071003401d64035603c85124030021001c0074200c0381c1a00306 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 729820008 1250 729818758 729818777
    0xa0510080a02040b030406090525051203120705030403090e0402060d050a0b130b010e0d0804151107090b0f1009090e1002030709030219120b0703150305070807140d0f03 74
    0xb2607000255006e64800c90b07011505418502e041c41c10126001c424034400500480d40d0307454045010328000c22100203a502800e220b48904806040d40f041412284010100c01d0038000aa40d0080003144514000c0d922085503646038194002c00050541d00079600500600c00084144443c0d80119041843d0503400030741c500f100b0700801c81101080215510300c50b82c80c1c2c0346074031a50300319408030440700c000c40e200c2d0448101540d80c03407641c0c010350042c0c074000c0c000904100d078001d00407034442501030b11200032214850390b10240c034405403002a00c0a4001e40c400c54844125003070181004541c04802e41701c10300e0450510b06000000c0c0400220015140b04061500740480010300c01107001e80241d61340e1740030617802c41c018020744480140701e10018948044042000c4207072160610303045980803c002000340c82d0404120042c05100c001c54420b00265400041004400a660300440e00d01000351841c541e956550030982e00c0b100e01260390800481080340000a104020400400d8801e041c0740041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 729821258 1250 729820008 729820019
    0x2060702030f0d0902150406110102040503031b1f050a0f02070b1609030f080306190e0109020a090308030709140303130e1003050d020109021c03020a0b19090b0402040501050a0510080a0204 83
    0xc0c1b01c005100000e00001074288103003548080c407d0200d0011500a41c07601c0d1030180400c0c3c0c1c920507100d507005205400780a1940b01c0c5c5041c02407580780030307000b01c07810301c4142aa6403040040900f602c1d0503030190300e4903144800030303802030090300d00064029074a180c0c103070b460010091f200c0e01700401c038104011540f900840020006005403a845020b20704494603032402100303210b011000c0654101c6901e140c02010442d501c8a0740025054441003130001d80c45521403041526034911075003006100810100030801502c0e0b001e2082d6044030309031424803010014040c2030603181d01c503c0d060070000c00d5445905100030450784440c40d8020000f60503015041c4d03500c2c1ca030141803e00c00c03034100c00140d44804031042503140202000358041284100e0704031304041550b000c2d6640800d02e10040c004034201f000a144194200340c0d44500000c1305d2024845240c4038030b050410701e101207404a00c6a40f03898004142d03420700c071802c8016200041c01485c5030140740b91b82030381c80c2c41005000019480c3c081001091 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 729822508 1250 729821258 729821269
    0x1514100306120b180a1a07140d0f020409020703210203010f030f0f211202030115080a1407030b01110a0503030408070f050a08040923010920040e040c0602060702030f0d0902 76
    0x170f80c14012400080c403501120100d481c1510060101420042d100520302c000d00720a008840100c0b0341703440001a240d0003004000080c0c000c6901240301079202003409001d050308450040d542e848500c00c034042c07410400400c13078100d000a005c2c00c110027405c24014400210f00c20894680342e4000c14210f200d00010761b8808049200300d01d110001001c0e1032517000c54250304a0441c02c04080c000200b98150340c140300311868442001e0f88401c0c03c00040401040020106074450b01c0d14200c0308000100518294801030040c0c49250055030006a8181704c03c1501280402d554110a901202841c40e540b10780c0c0328484141c10845090b50300e018020040000210104440503040780b052000680f500e20b42102c440c01c4074408540700d1400001460b001da171044040c1040c50644903c3c010004001e454080c0e02c86940c50800b4a0004070000003401290a1080b503c1d060320461107851810070050325500c040303841e40001d030388100240c0e0051100c142c03458400c40c0605440c1c500c003140003a0076400381c0c00041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 729823758 1250 729822508 729822523
    0x309061803070e04030f1d04091b12120c17040e010905061c0312022511030d0f05070807020d12030e0a030207090509011514100306120b18 61
    0x52405a500a003031000e41400d01080c2c004000c4200340084a14080c0c8003d40b41d450400c4600e030410041c25070041950484000c5c43c2c1c030951020300300b008044014a400003007008554805030007801601c000080c95000c004040705820750140c5003c1c4080c20740c01041c3d5610030303080004c039a10f020019150320061656009000203101d000c4124000d5494180803104441d8058202130283d04290400d000116400100003e0568035240c05084041d030164803400038000c0458081030140501c1914a55244c0d000b0b1000034203005000c808400545801055a40e01c4000c1014022480310240c02d2403503801800a04500fa0041426500d0825154005026070998100c03ca03003400c0e0300c04011030a190300d84114074040c094100102885000c603103010750b682444d4418081e01c40c0d11240000e0b0207043c00e41203604c4000040b40c080e854641c85031300070344c0d82e0b42c2d20021043c0078006040035008007070711034042c6900726096071210030170082c0c003616007660304000201004540b90080b241c04082000410100c1c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 729825008 1250 729823758 729823777
    0x50a05030a030b061206011202130806040210181202060d05010603020703110f0a020405041a0c190305010506030403030b120304181a101805060a03050a2a0e0102030906 74
    0x4664074450000c1c090122034841e11031902030081404020050030b02060901d80001003402e2982c4003007509007241002e44100c041600340c0e01d107501000200e081c00018124060752084030a0b0414414040e4200c543e10070f040d219030604504c3c0c140800c440482000600745250020b8006481c0240030310540f0306480080e884000001c1e40090324006060340520806140d5070400094049586014046a0745089143c0082d200356542c0000c2010011490103203442040c01d008556014a003031940744070585c10403024004014400d081d1088070794464405d10b41a11030080070541540c64644040780148804907c441d000146a01c40420f034903001c101031710080c20520442055132000062400594402464069100b0740c0c0445030f0403507999001204c3c500c20b41d1454100141c1800050018004e49142e103d940c10680000f140c01d00c0a5050304424810308600c0010b0090b00c8a4074504ac00d0525511400380c1042140814001810300c94200807a40340700520403030b0305040d0b41c900028015884580c1e00b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 729826258 1250 729825008 729825013
    0x50d1b060218040e0a0b06101e030c0f0206062103133b0c090a03060e010b1e0307061d120c0a0b0f07080307050408030a09090e070b25050a05 62
    0x89512503d050300540c220016024068042e0b15034541d00c0f10700504004d07100c1403242d0600701801c0c41a521075161825011002c44010b02802e110703600240c01403030542000000105c101c895110128000541da600521029000100000100725401c03006a040e283c56002d80c003082010f5100710001022450103401c0000002407020480104030480c200140d00000140e207a075040701c00840c1c083d006242d8840c045d91031140d80c900d45000010400a001d40004000a180c00b0012080c0c881c158400100744105580f0440c2c019011150407000e10385d44840d865060340210b8061000c1d0b03101e03010707400710400103403040f5170216030580c00108001c11003800284503034001201e450492a240100000a1103800300d460f1034072012601138145880341c40d102030701c000c8000011610592080c4c08841c014a424801c0d01d0725080141c42c010200c0071540715611310b8600702040c84400020228403941150b8440b00701c9490907031800d4111903405011400000b00c803040e1000c0e040442d01c244810451540704801 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 729827508 1250 729826258 729826297
    0x9020603090c010818190614010f0915150e0406120302100510060912081309020d050606270418050d03060e010b0909060a1a0c010b0607050d1b0602 65
    0x40921300000c09813134242c3d44440304c0c000362071004101a00900c003014504a544011424003d001d0a40b030b507440346101c1e0011000042d03107550b480700001078807040c11040c0301c00903450141d14426a1f0601840300042e096081500001d8000c00307800350f01c240003a00114420359225038410b0517480c1d0b10700c150007503009484281131b807100d948a40c1c0d5200301c40121092103035091420051505030640244034004210014030801e101d507036030030b90b0b648241c0428840e009075110780045029400503100010413508040208840307190590035100007040816a14001140d2211031000c94504410310b142c1281c5e0b1418440000c42c42410f800442074007442c02800710f0200c02c03000030200d80c1e180d444001552001401485421401c1701203800710101100c8201494075004000359240000c0e0f80304004403d08071003423a03900c0c954a005844c1c005000c3c0000c0042000203018001c041c0f0075008010710f5a0030542a2500307403805041e0444010b1030005840c415860136940d40000c9900c2082c0000440c000c40c0d9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 729828758 1250 729827508 729827533
    0xf0301050d2f130510060c03110102041205150103020f061803010f0b010f020f030417010f0e011d01050114040504031403090105161b120c0206040b0903010c170f06040902060309 78
    0x221403c6440a19041142d440e0661960b614081103010300800c00c040a41d1500a1502c41c0e02e41c40704c0c40319280021075403155508118401088481c82c02c460074012a80c140d07030641e18000c00c081c100c0b50094405a40d81120004000065001092441d43c002c503184c1443c91544007403207070b81000b401d80c50002032110010750000d0440030000c5039071011503204445543d0101c101000751811100720901107030006000a2070320b809842074183d146d10b02480c1c0340b00c945940e83c0541098814800280c40389000fa450005400e098800902880c0310040f003151100360300341010341c403581d800790081c5001c1c03100b0064602d002c50b00c0d520554403000c0b169180c170309210520417a5000324480040605080e0182c2e20010f011100b40c1105050207420f42c034204210301802802145692031495001b81a0b55072961201d6005189410011001c0d00940c030305500002040e00585401a407a00c0300d801c1000a640c66140f42c95400f00014070080d00709441d840440c0060b11382e540950f00030b65040d0060801602000d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 729830008 1250 729828758 729828769
    0xa230609031036050a03140d0911040e01022d040b030c13120302060703090302010e07031406070e010c0b1017060609070509010e09040c05090f0702010c02030f0301050d2f 75
    0x6240d582846943c400c140c00034000040d5402510350509201c4100242941d40329181c0c0900f20305e480f142d6080813002020880d141c1030090540d07070211020480030750700e4001d0600302e014010f0000c0014496819404c500d000b0303d608142c0f400600c000c400c2c07400d62078001c24440c80d007041d40c08680e03522002c83c40354558002546000043c002101107500b4444054034008d5498401804c0003040c941d4645644040c11b100390880d800103030008085030700e125504c3c80c0c030b881c2d81c2d0707081d601900780c902a01d400318115510031840c242582d24140d5030310a0500c001e448105503588050100c2d0402c003950800002d100c2c0280c0002030720441103d0140a552812500340441450010043c00800100300f00e644120381c0c00100308030082c0401d448102c02c65945240842810405400065010f10541c041010114009080d070f072141420358000c0c000c0c44007900050740e907070080c000c0081c03880009100600003414800c080c0094a805054070f040c416840307022022a00c582c41c0780c2c0c011000da41e074000410b0f50800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 729831258 1250 729830008 729830081
    0x803090f030424030b0a031b03050f0a02040e0c010f080a02090a06090815100909050118050705031513141e0606010e060304020d02040207290103020a2306090310 71
    0x103403c01744009160100000c4900201b070000502c0d030400c09140100b80303540440c14901845c3d0020889031420f45d0b2151003655120200422407086003400300749404e076035011a0250442d4811707100c0c08500801c07000c1c2501c01030b000612816540d5801d1121117101e0b0388000040008003c143c450503000c1c0e0604149a05080000c4913500f0788a880000340100045151189800c482012034009038401d002c3c0f618a0150120014001c0456034040c284014407a0200340c80003280c40c02c4086444000c03080c54960b642400490320303803040c28124014200441c665a04030780032120b41000351400721003900c0c44201e0080d500d203807d000c541e101108010855811062509501e82c0c00c440c0c031030851501d030b03000074003036500017200034000d54000c5030910070003601c840d9150542c00304108460300b800e01d404c9012601502440140d110715460340002a50154114001c1001c107401040c04482001d40c006008550348104007a0350144221030034400b900600d44280c100e6000708418100b0009004a22440b82016 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 729832508 1250 729831258 729831329
    0x303180807030b0621010c050729010302061804020304061d0d171b161b032f2e0c0210030b0105040812180307080d120f020a0302071704080a0803090f0304 68
    0xad50303503818100e00b10711a402811070754106c40b001c1c0d440c4440713003d403903d000c400e0501c5034001d0300201c00e11081210580014288281c0c140090444140203100590703101c506110f4500844c680c1102e150030010021205039004940949240a940342c9506c0139035141e105403000c0c9640404c400050041080c00152041207101e0300300ea10000c03030706540b140818001024021a955503034448002030041600c20720707415030803004080c031103100c3c0781c1003c15038001c080043c000c40c0d000395107a107000020300034070642c41801d8000e001b52080a100000a0f0020007100920b941405401d00c400642e03c0810840c40c2e038035008201c0e83c603440344100e00309208030511104545100e40c11507941404800b20025001d1492111840d1a00c0e226480f425002e0082c0b61401e44032600718000641e240c00c081d0150001c140c100d10a507841010100c1c8010507401500890160150b40c0d0030000c0160f000c28008000f55800030121400c0d5814a40100100340c41c507030050380550058514030a000300ca010413020050442c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 729833758 1250 729832508 729832553
    0xc09020903010e01052e0f0609030501050603010507210f0c020c040615050304170d0c1e171303031d01090510110a031a030105010303180807030b0621010c0507 70
    0x510300b007521100000701e08060351601c031b40620f05415041c0c41c4500401440645060005036441d008024107201060000361950340c201004200036040500c1501c0c42000c080d6118904440c41c3c01084c1c001500581d0408011074441c21200c00501d440d10400c0f01c012402c2d0020000060b4420511055407125403010740c407200c0c19104110015002001c40758480c0d442000c001d000404c44041d442c050054840d0050b5092403c00c44800603500442283c4284414094282c0b902991050071180080c0c0b1905111034041040041842c1242a07003200d4242032180c2801300c3d400c18903035026000c5556841142c2d04581d1907120031401d11600307002c03200c0400706035a402e11090388140d1001450f4421010382c08105640d904500d2030f090349075014441c0c148002802031200e540d50741001862003100c5440402c05504c0f110001a4001c40014540c0480f50710103ea40b140f640d440003001310000b07504900040e44051840d2644103000b0a2180422044a98035016141c400034244003036240b110320481d06501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 729835008 1250 729833758 729833761
    0x15090b0d020306040204050618010306021216120b0a030212010b010f02060717040201140a080109050c090f0d020a120305040806060f01020618011b030e150f070810030c09020903010e0105 82
    0x1070b00c0202c0d009611035010b50380424582c54440101d800300042c01d411141d101c444e5400070041100607001403c00096007a0b08070627588940e02c1d0b400e003400308111300a01046c201641034240302525048501d01040c01088030b00801d0f81c94012602940c2c6801d00b00d00a41d5481c40700d8049580c112800030800b04003840104003a01e01407501411210403900394842c0d610b180c01c0000e046a2050020240d8124100041600c9030900c0701d006d042440300f8001c0d80c2d03106052000181d17024008400f6502c03c00401030518580110220511075030708040032090340c002e03c003000c1c08a4034203440b0050203900c81c0f0996407030f540ca80c5032031103413414800050314682c4a02c4c2001301003070041c0ea00040c00703a00a9407424489030a40c044c40c80e00c0d070060080e5210b00b14072001950303c0c40c1003103815521502103410040d00b52089100400c0d44003403040c07803c507802502c2154000210b8919840346d0116035200280c41030049015031603131101d40d005819644111406900000c050060782003e009082c5485001c1c1c0c001d110a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 729836258 1250 729835008 729835013
    0x40c05040e13021309150b010806060f28050304030306061e20060106181a16082101140405040309150201020409050907030b090f0c1003020d15090b0d 66
    0xa01c280035144104403994281d100d4159642d07084020703904240d16030100102c506034900000c4000f103e1b0b030038044142c60100c4012503075000359045445040010400c0d40341462440d014005a04000c118020841c1c07444100d45280103c107a030056480b8080c1c035001e03101d00c1c140c0740007816100301e43c0014040180f20214100080c03142e1504803d03072082818501540c080100011020181c2c1c003215210901c0786c03100014596802c0130603c4000089541c010785015143c107405001c11031074202030729a0030f904018400036200c00b07070141d24800307202d6000e203441c041002c4201034507250600c4000782c2c206080d4004024191440f0a0b2800c4540156014001e9180c940c8000c2c204040da8801e420901d80440010240c842c800e5044401400c4070000401150410850b03070765480815010860b406040240883d8076000001035408114003010000d000100468080c80000d00140ba10030b0141074080c04001c180100704e000300c40800c031a240303260580d00c5c40c05401e00140d5001038903241c0203903804082d40c000b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 729837508 1250 729836258 729836279
    0x5070906050105190e1509030706030216110d1505010512010b0f04020d0b1f141e0a0918090201120c0909150506070821010b03190605030109030e040c0504 68
    0x20100104102200002c1c2c0400e445c0c0322a164416988410a0414100c1280c841d4026215100041d41200e40b204c2c0ca5a80c00e070120711070004801c5640d03030071040000000308034900303002c46200080c000c0c1908114690305c860b103c400050b10541c40300d807618018002400e1241901c1c43d0310603000028001540d03403002007441c2d0b102e013074049802603400088508134a1450b410007170840002a102034841a42100348000300104d90300a00002442140218024080441a00d03107688041e8095404951200ca00c046181d101c0c005640611103003c00c006440504000c00d5011180543e1010807200346620004144101055030151510318000000b0301d1264000c91040a41d82800d00000d903c80c00d03000e0b02c178005442c3d0341c4013680c81800001c0510800c54124007900b403016100942c000640d005010150000800b4002d080c0e03403c80910001e85a01e036068100202c0c2008408001005038032a80402d0030358500c1407080d00442c02c0c0b2281041c50b41843e200b854003280300c501d00a030070541440c1c4d0845 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 729838758 1250 729837508 729837517
    0x1b09010c03030b0303190504050f04060e0114040902040203091f2306150c07062307020603150a0b1b0303090c060c01020904090f06050603070510030c0c0203031605070906050105 78
    0x2001c2542e40c0f4140120790b2020070468080a52030b114036440c4c0095810002c0c96940903020320740c01808140910308203418a0700400c82924070030a070740044d40e820310180070140d1101c0c40480e9840794031505441c001d07880c0c41c401580900210005840109c0e817080c09402542c1c0341d48140b004e403e01e00289014074400f850700085960441507801040c0d5201d002c0040e0620003c50031084201c000061a04460303180095164103c0710035803692514540080700c402e0402c80d51001c081c0c00b0741020048000146407000c01117034000408003140795008a1000401c1c5110b2064100d000130843c005210540e0305e5003900381d2001428850000c529528001450310348404504101d94000c0b5008541808584800c0d01034031601d42000c3c200300180705890500080c400e40c198410388003580b40c0004500d4038100410210709464000c0c010343c0d10784800b103034102c00a00e80820440104900e0b010100b005079400d00c000c028020580700c21006005443c113005062598642c0440b4100c0e20f003000c01c00003641c00c402500c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 729840008 1250 729838758 729838763
    0x1080601020c0411041e0e01090204140913060e010c030b030a020312030403050d0c020304090b060c1e010b090408070204051003030f051c09060903140901091509080d02061b09010c 79
    0xc141e108a607241200130340105d030031601010b00b51002c0070501082410b45041211441625542c40d6641d03603c9180403889035009580e02034a8005000c49982000075074123401000090181005401c1a240c040c1100c00389401007803c1d9458801c40b41a00c0e50502660315000001c4028200844d541d5000980d12103c2c00741405800380040700007400e050140003590710400704102d003840010540140251030344d2290052043c0c80d803411004602e681014010b45a141042c040100080e405002907085104508841d0481540d251003004400d03072103c4480c240070313521441c1c4a64a4181d10700c1000181c1e4001069815030072030b400801c0010a030b011707090621052031400c2041d5940c3e80503400c0070103104400b00c80028507080807064000c000160384050521802a660700341f04004a0410300518854101142d0008528420500418004052611002c3c8640c00c0407810282e50710405400d00004c2c800400c00344e0400003c016800d6800c2442d05100d126072003440e8070b00030107a40003a01c01d00c043c4001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 729841258 1250 729840008 729840011
    0xd0e03060f060103090b0114090a09030807031a060409050f1e0708070c1a0405010509060c0f0c03040f061d03010615110f030d020403110306100315140406051501080601020c04 77
    0x30030b086034000e6002c1d201042e004500c0342902d684680340c003511040817060351809400340b100017840042c0d6134840c880b5815890354400005441b464003c070080c00001c02c450304010000300f4003070704d40e07076401c001040101141000032685140448a08400f840c0092000b801400c0502c0f1940d00741c0300800c24560300c0551401c1c07048483c4c403060b001310369510f8400c070010400c4039013040040c1444e04101c1483d125a100300e00034412940c4030584940c4462042d0303458581003a09011080c03078009510040c0001005c100212401d140e03031020030140410082c0d1050b000320750300722060396241070b06070000407001209500034081a03140003a2a035220104060a100300500d4421600300b8480c24401643e04c40c2c0d14a00304c0362a8420f0307075503481c0203512602c0700f200c12603180c910f47c190798200815002d01c2080c1c50020701d8416469504d07014803502622181c56000c541d10349036180340e2581110800d0081d80548800a80f40c03403c69400707040c03803194464840c1400500c50030000c80380c0c0c3c00110030142e58001d460 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 729842508 1250 729841258 729841261
    0x50a1401090b0f07240221070e0109060c210e10020a0f062711030708010b1309170a090906140d120507050102030c030a050f01080d050a09080a0c080d0e03060f 70
    0x221551060651101d034402e580009803421101e020b268203102031030030800c003100007074950000540c9c00c18400741c1caa90125180840030480c0502a403c40741c0c500740128000404402146400002203500d8100c000215180700c95408850070800848030500c0746078001062119680d859400550041400c000c22607a12810028100c0ca96a8040101c0b804405810501c040321490202a42804e28034602e0103403041d00b2002800c2c074014080c3e079441c11030252926012040c00e148102c042d10180c1010b0318000c04041c2c5000080b5038030f500410345c001d003654408201606000303080058821039070107401c0081c214424260f4030f41d200c00c80d10148030307030001001e04401c0c20141c00340d50b6805840800382c0349520100030040304d481c01c0c200462241682480030042e503510280d160b09058030030b02a24802d648400d90078640c1601400040c50792500c203082605000741da405145103042e023400c0f01140c091280030f90820151004110842a82032203050006004540d5000300c0d98a25000b011190901074100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 729843758 1250 729842508 729842543
    0xd180b031003021201050105040b04180f0c1203080a05070f050316030f060902071a010b0d0b041512050d0e1c0f0204020c060108070e061e0a050a1401090b0f07 70
    0x4000443e8040c044d6000c4d002d0f403c0e40345000b0082445544c1c080c50405249150314034252044c108420322030b0265841e600002e1712062001c440c0202e040b5040242c19134003090041c0c1500c0305900c060310a030350740710461a01039044419500c000d4010418484e421803101c100c42c5c4c201302540c1d03101f00152500c400f00c40c0c01010442c0904a1500c44040756460080c020882c494142c00134092030340a08900c8031449000009d02c404130100348144a48c281c002c0c099542d00e44000e1300004040726000b4000b2500c00054110b122158032168040a0504c1440ca060300c1044400e00411b0451140c5084c50483c920074040414421811724000c22281c1390441003410070050b02c030540184454001d0011900c1e40c6944c008955600002c0c012203006118041c000644161b8100d2014454000509040325134111004d84981d8420f2200c9034a501c000701c0c07900441e2545449481c000189038000c00e485441d02400c00161108010343c00654604004020400c0381c0c01800048541450f40511010355910090 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 729845008 1250 729843758 729843781
    0x131d191b050307022d0c1801061b0b13110a0537031101170c071e020d0606140603011d0c07060f200c060103080307030207080c06090d180b03 62
    0x90b031701c0548500d003154821000d5a20008041241c001c880304444080004804100d14150ba001000501e201e000c0014014244280500d000c07940f070281121401001a54540c224000225010380144003807500041c02c2c04440304c840d8101c62010b0340c80c6088181000041081d010400c80040b84800381140e0601d191050f40040500c290a4030410060250710703450300030f84550400f4800c50011301d980100c07801c400b814a907840d000d4030310708404502c3c2c00d034295511308007220201502aa20351070b0201c1075015840d90741e4a5145030303200343c1d0001407160400c00340814041110002900070740013880144102c28082400c10b800c2d5102010703241c01c0e96034511100041340300c0ca00008098a050410060f042800c81e080841c6440070390045900e6041940c5000c0c01c14050794001001940c06000100045034800c001141c100034103190152501c0301d15150481680d10074180c00d04c0c01d9105a041001100c810b01081c40c2c0072a19107001d070783d11003d808504410034114014692115400400b0588581070f0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 729846258 1250 729845008 729845023
    0x6150c060e1e0618070e13080427270204090f02060d060e06060306130b1c051f020a08310614060609060708131d191b05030702 56
    0xc0e00c010340c42c414501c0c2c2c00d03a49500003600c81c10900700d5080902c02c1110004a1041d003a1011403003000615550700f6010b05400d47c29540c00d45020000b00004508600d0021407021f100720300c1c02558180019650b44031045803161050458046040301c03401d05c2d81c1804c042c1c0c480317400b43c0440d0003240001d454140100d44c0060004c1c000c0d03010710001490005604140c1101044540d0504c2155040d5207890031b00040c0e21007161001d5000c032202c0c2901105410607401030310310070700141590251040d003440c498070084400600b42c071198449100e1664034518001b9110306812040003e50801100840192034808050f141d16020003001e05003801c4009030007860900043c00b22134441c404d80541c18900010100409034409030380107040051968207046080300c4031131170090112440c1c80301d42e448143c81d40d00000701081604071011000910322040420082506001144c6401c0505203c0c1080744440440715404041d142024000301071000c00c90b490704100c081909000d5a41d550340c03e0228105980d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 729847508 1250 729846258 729846283
    0x507201305190216110102010903080f0403090f091406060405010e0909030c01091a0f0f0c0a0201110c0616090503100b011e020c132c07150206070306150c060e 70
    0xb0228039441e502204d20600d60140d07006800c10305940011800490036a120044081c0101c4c1d00e45d00483c511001c1e0980c071581c010300074680802e240340c9611030b40c1c5201040e580700a8041d511030402880c240c541400f0660004c40441d003440c03616103400c0010300308608000007140309510440000b01c0e581005e104440e071550040008008100c1c180c40e0202000c40301004180d0001d11400000d5600c08034000b090303000c0c24009030780c1d10b11a034560704c2c116541d40c04640c1c020115500e80d070b900384a4076030700030261141d1061100603200ca032924082c9940f2404d03410f1085030401c01014030401164401198141112802d0100490034030950070059034580d0800781c0c1030990809021414400d503902003411825850308803440c40403050995601c4041d11008000050400080981041d0440d441d04503520100c16940503100d00035900c9000d45031001f028900b07800981c2003c410080d18590520691000d40008a04c0260078400a00014010310010b10001d107034558400400800c0101040340c000c0071071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 729848758 1250 729847508 729847511
    0x60105070f050d051e09010c0b1008070305030301140901060909092a06080a0902010e040e1207030306050f060703230c070b0705060f1e0c040312050720130519 70
    0x14008004000382d0144503104017106000021076441707120703041101c0505005030355011a110041d210749020000c042c005000802c51408005403079001404150025801840615202e42c0340c813280d005c82003503018aa030700c41c408590042c0440d07074200301d6030000d0711004a4000f4440c0c04928140c100c16031000e00a0282c1c2040e050154501c40c1c095100a090751915500c03940d2540380c82040000396903907208000d01269507010000c0050405601c1f075042c00903550100c80300404050b00d4488154032604003500043d84400b0180240d04103800d1a01c040b05083c0c40e0280b800b4003d48004014100e101c04100040103222155184100108240d5940d05c1d0401d065841c42551000c00d00400c0d448417004403801e0040d0f400040184201c506a180301d418022440900c1d1034a40c000400807c2000b0318000c6201002c0c0008008207507010000c3c002000c0796218076584412900300942c9450458414480320140d501038030126894001602c00b96414061010405c1c0e260220403d18444441d03112a4225 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 729850008 1250 729848758 729848773
    0x12d020c0c060705030c010c0e15030603011112220b0a150f0b0d06090605030c0d082701120509071e0302030303040c0e090105090703080d0213080609010c0e09060105070f05 76
    0x13001c040b0040c0316804008000700800b00082d0001d40b1004840359805900540c514800c1528882000046500c00c00c02000041d403090743c2000640b581c1c0080070424090002802002441007011085d0007042c0c4e0149080708200c0915910000311a00c0101240410394503004820311415402c2404070203011510f140c044110749608031280d0350b40205034003041080c2040000101910030380704400990710f025001c0e000d101030b800709003c1c5009001d50100e402800030084007060404003e820801c2c0400ca86055060000800c0010a45941c25410701c21003031404091040242c0001072140444016012400c10b011078000d009100000c10703400650180400401c0204006030465041c00792080d02d25201180c3c1c0381d1144c2c1d00d00700c4800300c5100741c0740c1c1d1028800340f0206103640080d080041c517221001d442d14030554100c4202c1101603111804a5020030b003801036440080c018101030314030780d00d0a4490403550500080c0d9191002d840181400000a141c83c240011100c002e51030540000449540 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 729851258 1250 729850008 729850013
    0xf021f0203031024030b2e12180212030405040207080c1204080606090402040b030d021f0b0114090a0b120709050a0b031f1505030603012d020c0c0607 66
    0x201d5104880c0e14420345403a9001107400082c0300000160030f0080d51541c4500740d480e43c4150002c0076108807a0780e11200e0303090888000b00003100036290600c454080320007c04100903010b041001d10143c000200c50820440c803620140c000d04d48044140c0450700c40d0440c060035403020382184200d40200d0b400900000307c0e04203110ba924024840340c0c4a00040301c0015005103002c00345801980111042900108040b840c0f80c0b5000100c0d541080c001080007514420490001e46449064610000560070500d16694290785954180412441c0098248100e01e0041c0000344950030f807000071010410040ba001031140c07a60f1003080d0151447d0f490403a9900413000810400c02402ca4030140082c0ca0450301140ca0300700044001d007220030826030f813829a21441c0940c4080003214518282101b214000010300c080c141c16100e052052544540b0f540341840c80906081d01c40400c1c0030080e1a6071025020528a0701c4c3c9200c19203881c41610060b250f122030350900e403c0100801520b0780c070240214000e010f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 729852508 1250 729851258 729851263
    0x606040b0a090323030403030806040605040f0b040c050f04050d05030c0d080f01081609090f080409090b0a1b080a0902031b012303280c0503010509090105130f021f02 73
    0x19680104c1c501550f0008411001103205506012442a50028071042000901039138205030032030001003010030091b0f15200458121064890340d01c486035110300e0004142d09040c0705a001929451800c07901c1c014000d006400b2034402d5104450049421507000b1041c8131061060b2002016030005a404500700e5001c0280207001c1624544a000f101c4400001c000400080348408039640c1c8510f1900607184ca0501d000070941c0314400e55005d00013499580020ba5400001c201038070000c2000114010b4508059540090050a144040b480d0026074010000500e1340100100d000d86400403165950307840101c0501701c03c5500035098402c415a041c401065045610360703500081e03980301e104000310098012401c2460300c0c0d4540040c01000031903504c0300c03014200b6003203402007154040a000e240b056101100e030301581c004000340c00070005000c1850038580964002c0e04020081c0030505203001d0a1055181088008013191040d00c3c3c4c2d08115160850b0210300b0402c000440f144c590101503003c7d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 729853758 1250 729852508 729852527
    0x1805280918031409010206010923010b0301260307080714010504060209010e010203120610050403051006060f021605130b030f0114090a081c0b030a080d0b0a0605120606040b0a 77
    0x1c001c20007041030f034009024988140c4002400580c02800b00d079103000c0c41c0c440200190315480009000c041110f05014081d100d200c0d00801c00c1140741e59480d0700d031104680c81c40201034842c004004081130440c08184000090f507a816400070700381035482d4860301d00f04400000341d910900b419400d2208003c18031445a02401c00c0030001c0e00c40250110011004a84a00c940c40b02d0003d000d8010000c82c4481c105002c80f149100f9640c01c007245040d440391a840d21b042080029075890f2500c402042c40342907881422006c0c440450300080a080621030b40c007074090303d1140280c3e03008450842814014100e0b07600f003002561b070043d080e035140d030300c170886054060104048041601c0041c400403580002000504002c000d401c04c00d414103103104040d210510300ca000310901e01c003a03140c00c0c400c1c8150340e051146286c130350310031000700d40d8440701c058201080d266440182c0c1d1042000070320030400720b0741013001c0b40d0465505521a154a039500320014030f403405030b0741080e4040100402e401102680081214 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 729855008 1250 729853758 729853763
    0x51908040303140c03070305091212100b0703090b030c0f03040305031e090304090203060406050907020a0b1e13020301200d060f03051c0219121805280918 68
    0x10322243c2d000107103810761502c080d40c1c613048061080000403c0c1600c25030005400510107000d03202c050200810418558100e401d50348a0743c04442c0500c0b5080d40c4503c10400101308580d4800e041c428140c4016000c20301e1071080340c82a800000000b0741c00b810711800c8580e01c0c078948480c503807203052030304004000390403c031411030030a0310020039010f0f04172105941d64441d40d05540154a05420314040d440a50006480c440d005512981d001c211551202482480307040346034000c008100c3c0c0c5040c60108600043d0803074800343d08503405200d001422403200703580f0148144901c8030024042c40413900400306201403202042913007010a490320007503001801c07500710441090200d2911404841554115444010026440607041115510310840c6140866040d401529003250743c0489005111400c070500300c81c2200c04003034401c4031503081522031500440310802c03105103074141400f145000514440076038040380102140c0500034902d82d070100c050610071005009503900d0307441c0c0c290500101e0008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 729856115 1107 729855008 729855011
    0x2d080622050706080f15010905090c0705120415050309101d011a0a06020f100e01020f0408030d0b151602010903062901230a051908040303 61
    0x404154a0b154045d02e021080140e46070f84c0103210001e5284030356142480f60340c1c002520700030b450b001c3d01c0c2d409486d1541c18400c4510302a04100900a01c20690800c070110501030281040b00e1508000c016002d01200007a140350100701e400d02c40b5680142c41041152801d60040c6c030004802c90100b40130345400704038290031b4070520544d00f803210300c3c414045061400d14180c004002d28407403014211440c0b00c01813954540244151070250349071500c6c9461207018082d81158003040d110b4108503659507503001c903652a42c20045452070a45c3c5800400412414a114103500c401b0b0301103406880d0080b01007c910707c004241038168104003050501100240c001c0c03083d51130b0014100218400c42c050602550071411480201da4100580d8221400c0701c0c01481c821101c101d401455401c0d160913288000310360f00d0080348006480d00310328001ca61074550700010071b180140d019030740 = true := by decide +kernel

theorem cover : BRFrame.Cov 729676258 729856115 := by
  have h0 := BRFrame.cov_init 729676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 729676258 ≤ n) (h2 : n < 729856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
