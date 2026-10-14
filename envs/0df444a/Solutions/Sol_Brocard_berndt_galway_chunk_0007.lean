-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0007
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:19:28.133999+00:00
-- url     : https://prove2.me/submissions/47d71281-47d9-4bf2-b67f-cbb5b3921032

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 1079144 ≤ n < 1259000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 1080394 1250 1079144 1079147
    0x1080601050307030f0f0303060902030a05010302040b0303090d0f03090b0301030302070503070b0406020307030c0201050f04060306090506060702010c12030f0501090207020406080c0f040209030f0105040b0709080705010905060307030b090903070c080a03 111
    0x2e0601046d00211403041c030310309500d0105c001d031490341d101d80c0410740080188a544041a0704c001d04a91088a08101e164015828103489000320490f8540c0080c030a0801e40101d8140c00d50101c0b418030030b144c8401345907124a110b440070303007082e0420390069000080c11300203411304101300760260200c05501c0e8201803411030001c0d40c0e0301c1084070050404c040020b070344086901540c05e84c1c0600c0580004282c6454694030000d00034070841c40b0b10804242490f01050280c14108100c801c100c1c3c041e51150040b01d81c03901d44007480070007010035004040c0c6d075103100f54800e2500c0c8203490191100d404c4c003590b0360300e042c010081900d03a01c0d003006245400030080007400e076903064000a42284140c8025031283c240d07400181c00c0526407541c02d501542010100300030002c112070304a11605031034940c0b0300d4168482c8803040c1d4801c8135000d040e0101e1825030090140b890003002841e8464100e14010a0a42d0854003280c45003078191001c0741a64004a944001c1000c40481c2c200034041041c020407845500703840 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 1081644 1250 1080394 1080413
    0x1050603010b0a0318150e060c1206060711040507030c020606010f02030301051c0507030302010b0109090507051605010e01090503030115030203090303040303020703020304120f02090601110c0f0102070810050108060105030703 99
    0x142c01410380e6061412804c0540c030110445c141d8000d0b810b0b0351010f01c26032800c009000c2800781714645004500010300c04c1c0c1201d03415900142e03a1078000300c0d40c9642d060280803540c0e00c40c0310182c0c0d510104607403042c0c9580d280d0040500c590b549030b90102e2202100c981c00b03071a1440141415050140003c5016030055001080e21f044410849198800c0c0018103030356940c01785240c0340640140142c2070007006150301500f20040000003a07a078041203c0d0389400503000c440007680c000f0001b503820495503014000c800028071046d070103080006012868000d030503007122428002110745030001300c01001200d000c2041140040b5050800358a14504101001d440c0d00c0024002001c4c1540407a49905051007002914040c21104040e6200c00f0064109000303030f004242c10880c4130b10407480019000b544294040c0ca0b081c18250300400a107421a030403c0603444104017168110b114501d400075403030300e0410610444540c1c200001442d5410039000c58184413058008500035440450200000780d440305 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 1082894 1250 1081644 1081657
    0x4030209011d0a05280c08090703030504090b060904090302060103140102120c0a02070f0602010204090f02160f05010b060406030504020301060f030203120a0203120114010906030510030f050a020402030403080405010501050603010b 101
    0x400010719692220048108005c0305e40d005c890200c01a0017800c284403840c0d01801d0b000f0400d850360071700c0b5591801c860381d03540094040100010000d010030058801d15400c41042c0d010014041400c110795000400c2c103e400121080d00181c0c0400c004009221211814200b108802c90007907192070941c00d00c0d0b4101e020701500c003004403c00043c4502c2c0e041c2c070a20002c4003900081601701c43e1107030350b110024080d4200b400b51064180c07030404000341040440c400c03101d50322403d00800301c220b8403d40341c45a03000218075080c0e519540303404251010b507451030014800381509480c009444c1c10a40189402c4402c95001030707141550321035060000d03035000100540d01440b21080289c0d1030b11500c1c0128114003607034881c0700a01c0c0032040089003001521440e05850082aa19206581d5840d6070440c1642c0040d1802180c4031447c00092004c0b520803401507510602030360448030010540d43c04982288d000710b8050300051126000d000400c00d0a00031980180011142c190965050801e004441e10400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 1084144 1250 1082894 1082911
    0xa05070f0503040608040c09091101030905010609050a0204030309081204030b0403090f170105090606090c0a0c05060103060b09070302090609010302030601020f060f09010c081003030c020102070b030c04030209011d 94
    0x41a040200000c10a8900c0d010398080c042d29242c82d0380341e4014005107410780701201d5442c0da490000c107060b8450311070002c04030741004011510300c083e20019002000b01260550320340d521203001041403001030107000c0c0181088030300103a48502d54200107003a4011a00440161340124044031080c01c1035000303841c16030b600b0200c0025140c40358901076030490416440303210000060f01d0300054900804c094003000100b1400240001d588001a650700e481045587c2503000b01e502001c542a502131314050b1126083e1350510080f29132040d251240342440c264012140f40340c450003400140d04004c0300070394000d025414190304169034100081c1c03860180300c4030349042681c0400000c045038400c0080f00d002d1140b2206070b69103414294080038000c0c0c000c40308004550308044005588610503131704280702d44a60a0110030090031654100d9091406003010b03411442000408181d4410340d00007980141c4604800039625451031040c450509016072101300706441c4051601b01c03445c030b56915140c1c0301d80035 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 1085394 1250 1084144 1084147
    0x10506090a08010c050414180c090a030501020309010518030c03030403050310030206120a060f03030903080307050c06070c02040606050304020f0d0302190503030105040b030a0f03050c0a0204020f07030e01140a05 93
    0x10840441d0484038654000c036055070030b103001020899000002403095410282240c80c08040d41003d10001103030001500d013400d110400003445c9404c942c0090520781c54010107440038039650b40c031040c0c2660000d0306c0500d0343c5d96403a42481611460040c208141450755406541041c609682c0c25482c1d010080015090040c004005681105066222005540e0007845161074243d4401c9001090f03200310780ca001024686800403071110b021140c51821a641580c40e580c005003150346160f03c580001d03041d9028414240141c40703509505001d80d07885011255a038050a2005004010685040d684001c3c240300003041070001580311200880b40f03031642960155007154140c41d04a14105412860b0300104c02500794403810040040000c604030341d03040340d0601c1242c401c2010540c890300c200d01c00601c3c01050200d0f039800240100f01428949000a00f5100520301d05d4010805a0b40460040702d9480030015816003010303000344c03040742010303400c0c60300c104c0407646e201e00d8000500c586805002401750 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 1086644 1250 1085394 1085407
    0x7060f03020904020a0e010e030601080c0409050a0b010806040302060c03010b07020103021602030106090605030708010501080d081509070c0b0a05040302030f0702040b040207080910030207030c03080c120f0612070806010506 98
    0x9404030380d540b29000e0011076840d40020001082240740d41c40c85800203840c15084410351038001007980c1a6038a40b40600344024a03038041000900c80b41e481220b560080d05d440d0030100300032440e43d03030013082500060300152406150090030300300c0040c203280c40034ad000e00c0140000d030340e16419180350135030a0030016a144c0f101d01d5540c58034005400001d40c99801c003070010862a0840d00400100c41007a41104c4401e030b183e01d09242a070364240280e10300c2e03500c10001802d000b4403c881d46c60700f01c0c4140d001050003c11a10100f6564041114010b0101d01c0c124940c000b00080f540003981e106050b128104a1800d0a98000b9124400c03071002210070b410201d034560940d512948040098540280708540d14403991401c0903c40d0031086201d0700c11145540340300b040c180203008981c2e41e2070307040e03840b4035210304189d8003601c0c12500a010501c8582007030042c2e0300300c0c2e00d0220350240100e20b41000c2c0e42c0589003103820000e502d090a82c2041c115049628100a035076030028145041d200c0031220680c881c1d8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 1087894 1250 1086644 1086647
    0x20d0f02030c060901060603060501030e030306060f040305030d050f010e04050c010f020c03010905070905010b041404050a060504052406090604090f11040905011a0304020306040609021504090b0307090e07060f 92
    0x102c044081d40e900429081c4007000c030055014504460180d00d0510803965518015011038004012000081c0c008000103203803440c00c1e20090014031090368003241000d81341d480e05c6266401240402c6655a03640d4103000e41d1007546044035005000000e0807100500e40360790b55540703401551090700e05024015259101250090180c500000b4010b00200000061410082e41d900810303c6240b01803481c01c030000c6a4a940c9130110b41c152645a203c0c140c80505060500c070003010001c0601c4040341c4d40c1d0340d0102d06a60f0701e0149a00801404084031402c1d0902c907030b1755000c103120b14551032084404012511841d1542c109841c201e5944090000d0b160703241c06101c42c05400444268140c03440000f40100741050990b211034180d50100a071043c1c612080060b010030307444180c80180d855400100010002031803a00300e010303ca0300c003402c0e015290305001d401800a81040d08064030715600c0342088404c84c18108803104c01084002e40a100c940003440115440d01d04071301070305c41080114000d010116 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 1089144 1250 1087894 1087897
    0x30a030f0e0a0302061609060c03050901020a08071a0604020a0c030804020d080703080106080108010203040c050d0302070f090209010206060303070201081f080a03080601020c1801120f020405040507060212030403020d0f0203 98
    0x20350340407003601c2c8060382070b2400079200c0104807441031600800d09201d1072400d21a04c090410b4507210344034544141895102a1416000f04840904521030041c40704001007400028084180c41208072a5407128450540704070140014603203401240705200c02d800c041d074403107407900081e505401c02074850f49944c00460320508220001401e00080004c0c001c04141e0309c03a2010b0304907040795407101c0040e43ca9038030041c240d1200782c0b0083c1c61403695680c140100e15060b08906805403284c011107601954074240c001900070135620921200d0350214500b201940c045c4282988814118091407614103264006131500d00050328050b680f245540c510711400191744a024090505070702154010f00d40d910340240710200454201d4014050b5003072500e1142495955015088029000c610300c88c4e08020ba9101031858024040c0c030824031a282d0f040c0981ca541c85828011800348000d00074850030140068034113484c030003203071498480810030000401e501242c04078503000903142800c40b41c080900100c0c81d5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 1090394 1250 1089144 1089161
    0x11010603080304140f0f0309040c02010b040608010b010e012102030405120309010b0114070b1503121602030c0108040c0918060e07030308060301020f030a02070c1707140a0602030a030f 81
    0x1240001807100744200b00c2800e00a40c0000b50403070300071110340f100c0780c2d484106d0815180303000e6106216403152868640c005d07020511540c400060984408400941580c07029400010580d540391060692541e00001445a60400382040c0c6003000300054603c0507000c103c640c2d4100c4c9a07002c0041400c0140c2030147c40a5000208020f640f24241540e0460007001e500d40e029011500360400d100b0032805c1101030301c040716046584d08100d60384414849070f038107640f010383c1c130390501070102c090001e241d48802800c0054401c042e2044942c4070362042c140303404900200a8180241002000006a0101c0600e800d4508007038010511a03d1240c1000010803c114000c10a0381882d1400020002c002122400c690090350f518100780c5850050500700d203c0d454640100c1282000000c0b01420340ba0010a440c52150a55402d11a600d90318102072111015440e402600019020000d071040c1d9501a02025000c40d40d50340c1552070520040d41e20b04c12469000d0906417200c0e200400b42c2a240d000c0c018 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 1091644 1250 1090394 1090403
    0x301090c0309020a0303050409050a05010b0306100306080f01050103060501050a0515070201020102070209010e070206010501050918040203030705010207030906020705010504050603010302010e040b0604080705011202030106081b070804060c110d050601050111010603 116
    0x100c03180c45c0c0ca009405c94000313000d00083c1030328003070005030200c94a00800c2d0480d0102c45030180345072101c030180403280c00e0890000090688400d0000b691002c100b06607501c2c400d1080c0000741c19411407610304180c80060b40b00380e103d940001c1c003d202594134203203e2462001c0050340c3c4c55032408244010b0340a406064030280d4130160003c0001119400800264800c600c55801c0d100700e6a240c0c00152818051581415089071307a08420f880c1080a000d18590080d0008049a0a184903592031a0a80e4000b12080f80010f0384c4100c01c006541c0c0410a080c058807003400c119040a04100101e0054001448080e04118107800150344c1034946521440e1051000f4080c0b96a880c0c5500d10240d0381d500320b10840317001851030400e407040c642480c420750341130303c0d5543d55010031034440405840341030310040c0c0403081e181010005280001c06500c01400140b03916102e07050107001604000004d030303204141c41401910350161000000700c020a0301c906680090030010845400040010300402d040d420040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 1092894 1250 1091644 1091659
    0x4020304030c05010b0103090c0b0c010912050408070e04051518070305010509070b0301050306040206030c0c07060305060a090504050607050a02070b030108010902120d090b0f09030a030e010f0e060301090c030902 93
    0x1050580c400340002460b80681c1c02172081011800c0111708480a1000203802c5100303070a4240618030701c000041880b182907900202d4100f41ea900d42c0d5030209110b1034002c012034000507007000190000d03c01c542c010310041c22240c0c80361401da1105500e5030300441e540c1140c150010001020b20721603d61242200403c2e10032101c5413600d81c03404600170701713040c0c0f0070000314407840ba000910303102d000044a040c0c81d00680940303100e80b41c590a00a00350030192030703c0042c0c0c03018084022040020410312006010507a00810b03581450340602200b45141e800c4050b299042204100108400242c0d03203401c1010792a10b03541d900c1408400301d040012980200c1100c543c0080002514803054000d00e54141c02224403d241000130384000c0c1d42d4034803c0010783e0108006400400c003d9007464040e000712048000c080d0301d00b41a040010382002c00c40c4a045000ca00348503200151541e010b0380c2d1201c5110f032800e002d03003c4076040d0002081400144110354000d5250000140005d00caa00103500300c660182490 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 1094144 1250 1092894 1092901
    0xb030f0d0e0d0b07020601030b0105040b01050909060102010b060304080a0306090c02030711060c0102040305030909010602030901021507030906020301060c0317070903020909030d020a050403050c0303070b010b07020d0209010b090102010e0d05030106081005040203 115
    0x6c0d01c0700310a2000b920000c41000010030286401d1140001c101016143e107032501304014103010002c68010541415950307201c99491041d01c1e558002c0d44694426400c540c4e45241c0c44e030010301180e003035810500540d0700d8200503140e200d4001045070101c0750441c04d03507250350032900001041032241840507102d95002150000411800201070080000111601209607803200d60803681d0b401013200c16401a4803d903501c06540d1540b0501582100b0b01c5d1801140e400110348a107800c0e68800c1c0d001301d0008980c00d10700000c1c144d0010203c0d40351011101003070100e00f480040107101c2d0790750780030191140c1c000c403012504c105401c0045540006202d1000e545410510350040d01641041c4000c0c0d410303010b015402890f524000c400c07924044d512902800f2181d090000142d100e402c6440c00320b030000c160714501c9015941c0c805c2c07214001c10109070407940e11070070b15000a080d0340c104106855a5803012200c420056002400c0c2c0781528502d241c22a8a0b41da10304410710704810302e910180d002880081403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 1095394 1250 1094144 1094147
    0x203030c011a030c030d0f03020405030106120204150e0a020901020a0c08070303090801050705031305010b03010509070612050402030601060c02030a0f03050301030204060e0906040204020a03020f031003060b030f0d0e0d0b07 98
    0x10300b22001c00d00d407840c500c403100c40c014036071240c2c400c0340119850b401c01c42e000400180911001d840f24100da150050a154503180441c4c00c4034020380214004c41a00440b00c01189000d01540a1042082c075810f403806162004484c08128090002508542c012039281e036035074801c03c6103845c17464014160308142030ba1010019118070f2580416000501e5251001c52006014000d45028a04d039958042c038654400d19004180790706003400f1a034079500d43d800c040e900d45d8240142401102c83c000900034880c50a0005001d5100c1054422a11824034040001503074000c15200d04603a41401c05504007461840013906140210070000c000305003100c580001e00d41d202001d036041e00c1c807e40d4108021074581032140c49940c402c6800c0702c19a4004c800080c014200f40e0007506121000c0d00340075003041c100c5840c000854004551400e42010b041d0020018080d081c092030b46d4084050700a8800d80c0c0c000d400c1143c0360801007046200344240648880e07081d8036441e034103070207044c0c0040900c2101e0920280 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 1096644 1250 1095394 1095401
    0xb070c0609110405060d0b010302041104030204020d0c020c0307030506010b0a090b1809060d020904030e010909020d1505090106080c1804020301030605090105010e06030304030b0a14090f0106060305060d0602030a06030203030c01 100
    0x39805a807401000403606c0c204400030803c45908001d20440d240c2c40c550820000e0221700c000c580741c4401c2484000016280c50000c3c00040d140c065001c0340d4060388100c001d28048041088030300c2036000352001c2003c00c10204174241034a52003107140d80d4600c540981610641140d9000c4002605c000900d010300703102c0b00e840500640402c598640c0035072100c2e81040301c11000142d010350300440b038030041000240180f012072443c0700181403490000d07a8400a1000b203801c405445800b045d140d46d4440c8401031840220b0000d00310441d0010010b50402a0042c59040b00401003401c90000180d00320341203d071110b07054000c0704010030030b43d80c0e13684900d03050b005072009948c01c40302582007100218141d207107124401d1150348050011820189562140b07625800c1c0607100e00001d60b41c0301480d85c845407058041070300c071b000000c0081800d80311002c500c6003100e140e540142c040500e04401e00c80a540c9081e90a0040c43d008071000d45c5035162000340340000c0955620080d85403100142c05045041d040d003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 1097894 1250 1096644 1096673
    0x70303020106050405010f0b030414070603060f05030109030e15040302030a06090b0901090203100209040e010c020d0f08060307051002010e01050a0609060506040509060105031012060501030b01060507030c0b070c0609 95
    0x14020b0007031568403018801500c801303000f0079104805142c424000c01d10341c0303005594464010b1a0341503400003011410707070a220164106c4400a602c0740828408085c7c018460300003060160020040c08030180c500034846030110540c0c0744191f0414281e12188001d08081d280510340083c01c1c9c5100031000c0c03a0040040041c2d0300120340020702d1a0000301c10050603c02d11100e030f07030050058000303400002c110303000030350041700040d600c03580c0c0c0e040240109109104050340503096400909038803880007400b400c034560b080104810424000108211524007290010441300242d07104d40100008000c00da0245c0903000000a840d03291004021000f400c07038004008440c00c15008001d20364a40e418460a0311541c020340fa00f00c02c0741c0011131032651050004540c070a22844100c3c204980706c0003881058255a182500c9841e144c400500500500e031031810b006043d1428101c1c80c1c1641a6809480c222400700050701c0d001c501c0c400191024041c02100c542a80d0040c2c00300000d00041c50304801050142 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 1099144 1250 1097894 1097897
    0xc090203100902070308010b030a1508030735070609060219030b01090803090904050a1a040b010e01050306040213020903100e010507091206050405010212090606040c0212070311120705070303 84
    0x1c400c0010030350901e20855070041c3d0169200040c90b0708003001c8030071070307031019000710790740baa96460942c0e441c00320590301741c085c10406003e03642e10800ca0800c000900203003c004140c0e01245030140010000032000c07103913088a19401305489481c01e00f82100107002c00382004d01082d00010300e1851415001010006403181c54804201ea080b80c0c01c01151001042d00496040307510810480c11645080748415510610400444001d01e0155a54a41403010000c1d96660400010b040c0010000844030035400740c00b1844203034950398500b0700000e545010250000e4001d402c0380034010081000c0e50112031a81c1c002a0440e425201410b0105009041125074440781c1d5107844041140c99110b40d02400803103000303000a096180d0b254449100070034018104035103e43d402c01c400c1400c228101c0348d540c85a5000c0000c1d06242c50b101043c071080e203608214000444d006151a03407140412407058800568040c41c1200b0341c049110401c41c0740c0200c00304240010f49001c107100040000000d0100306480c802d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 1100394 1250 1099144 1099171
    0xa02010b1003020a021005040c030606030c0311040203060108040b04020d0605010602070612020c031e04080109030504030506070806010203030c090a080303010f0807060309020303040302010c020d06050108010b030d0507020a050906010c0c090203 107
    0x40100c02c0b400ca000d054003100042e001081c40360042c00c0c4540059030018000d00005244035900d54584045914a500486043e24001010020f200c02c0f1076120b48491025070b800c0d071442c030348078000030000b00d40100b0040840940c88040740c250744500307648000c42c55015100f00550758542d10040c0d81d40c2c03024410400002c4202c445613541c40954000d551039004818020340c282407035084400c541c5d00002280503206001400005003d0b034007400f810302102e001e42c03621562242141846414503200814540070700604000b0321001ba40e00200b101e034010202c00d0515251004000000c0c44076032158403001e000c0c0700c040000300e802d104c095940002c4401940885a007a90380744000c0e403e0315070700180654160001c1c842000036500a034004100075100805118201480e59644422603c080c0c1203440582e5441d4082c0105003400c2007582182070b05814264100581c5900050301102c990007118041c4080030003055803070340222100c41c80142c1c040120104903480301c10410080d08104d4401454007034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 1101644 1250 1100394 1100419
    0x8010b040b030a030503060d0602030112030e0301050601020706030b0409020604080f0c090907050d08090303030a2f0f0706060503030f03060102010c050703020d20010e060f0a050606070f02030a06020a02010b 91
    0x8292007200381104001d0007802040743c0320345040d1007a03040108410382001e41c1c9848000021035a2004601910b201440f40b45450000e042c0144070709031b00013100d8000c1e072414040c000140c0c0c000070307600b049400314900450780381d50036004130b03000e040d462000035084200890080340300070340420f900a160070a03104440001d4901c0c000c002c5100c44c2922507030b1041d08a00c00a00560030054042a901800707110031034548201d06022a1441e031040312500d03041c1da07542c0303003c04080034a00c0b1020283c031040491483c103444c0d0a01200c50314860008540c41a1400003144000c00250760040c40040c08018141ca4941d1102108962954801c4030b04034015481c000000b2492409070f001c0d14039440c0c040e070090000602151042d140d40403c051100f0301c140358107801840701082402007000480b0100d01401c058204100041103546014102204c21400c00b0f080120a458250a80e42303040d41000c61b8a8500e460b03400824203201a0307a50160005000103101e030346190f01500158100c010503500e4258010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 1102894 1250 1101644 1101649
    0x909010504020904030804051c0507020103060801050105032806020703050714010903050306010807021c020a03030b04060302030312070306030204020f03150312030703110409020301060809060a060e040b040303090512030108010b 100
    0x240e003220025030100d074040200e004030344682c480507030003485101110503c003100070600705403440880e444000902c00240103821564580104c200508905000780119410000026202c4012040d081c0c00741110303022002043d00d801c44201c6500342c022008640d00c800c10704009003503500405081d9a481c000b0160140141414030503190041d801d90343e03042c01c41d261200116041100527041d1000c41c07042c00d01812100a040300600b0440c1610b40007496068501d150103410781c2d56690000384202e19002c420005600c022048842e041c0384da0801008950b00e43c1001c0c0c006081d80d400194000340b0105200b0344901101d0005c40c0902441900140d12040c01420581e42e6080010484d206040a00204044a000c4d400200d5012400c1c480700d41000d0b11510403c0072a0401d0b80020000303040700060115040003842442c0c1c0141c840c9405012b40f40c2011980190704102a200078080307406140003405240c0f00c0d611040c1c81d26400401e44452450840034103490703400038090003400c2c0d403030100184c01c01d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 1104144 1250 1102894 1102901
    0xb0901090303030209130c0e010318050604020d0503041703090f06070c1e03020402030406020301090608070b040308030606210906010f0806010b0a0c050604060e0705040203070e0906060405040606020606090901 92
    0x1144140e451488103821550200c020750016540310780c11810382001e0550128490084039030071406503540045001c12840010291803018480c9210440310707206a07008900d010800680c41a010f4881080d112280d18205145104607400304800480207151040c00317a2020000382070510045481d00303036100e1a081080010310a42d100241040c8a8007001c20905100701c85410381105800d00841440da941d4001c20186c0e48102e604072100f65000005020079022807055201401c1707010b000b0003410741090300c01c01480c450f0b0301010b014280c012002800c1907840b04211000b4816005034441142030081c5007150108080d135040e541e5005d00e80011480c000d10350381b5482261866030062010740d1030180d075030b5100d5005420850400c00020055000f1030002c202e2640241c3c42800c00003600c0307240c0c0641d941044155040244603030300400510503000d50001030000d05440c11141030a4a448100028908c0c0c45154130007030b0481e0402000103001c0d0380105002d4030982e0259403039040c03aa14080d0080c00c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 1105394 1250 1104144 1104157
    0x8070f051602010203091302030f07020303040803040308101502010e07051906030209030705060c0a0501050703020306010801030201030c020a060501140307050f010c08030a060f090209030c01020a05060606070215030a02040305070b 101
    0x560900103181c01503001403091420030700600590340361020381c1000c81c4400220144003d60581c00000713000300c40d215500e42c0d0754007403118409542513042c150b485499900c0040c0c0f0240c100141207000c2124070382e80669600c0107081c00c2500005ca4140044003034060614070b6881078850185031000945414001692002011000340c400c140ca82411016002500700351189601407084007404105a00c401c4010300c000300b00380c001407448a030300b45846802d540303008200074101030062040c8a40d40c1d07000044541501d0342424049002054900101e10702800c0305c0b40608080d050000000d900080e054110601480581c140e07000540c60300309005140000c02c5429001810340306c20007000c19582e0001e90307041402644081a010350780c05000306444181d400c50b801d003035400104246689402c01a00d65184400e0024040f010303030f25243c007500d61a004102d2409a03a0000d480c1c400c640c2d07401054011080300b01c40c1c40b603c07403e00c3d61122001b5089400100c172039101c0c2039030105a860080041c0e802 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 1106644 1250 1105394 1105397
    0x108090c01030e0c030a060209090106030b0109030206030a0917030907060504030507030602090105040b040e010609140f011101090c030b04020306070c05030a0e011709010b04050105060403020102070302040b0105090306130308070f 101
    0x40e61015000440007030030086280362103401040c0c0c0b03207045030f5814083c0320061400b450000da126101001008401e01c4d040e8042020315250014003640c41c1d8114145034102c94045070021b8580d030303c00c0b007404c0140203000802401e010b07800810203040c11150010754001c0503844201e44015448140a84440c400c3d404007401a50129500f00001070340c2d03800400d000401032619904082e980e28180c1038540164010030611400b00006001003a80980b00d00b00400c05040c1a405480d0800003095941c0e405004c03460400800ca900040784000940001c00000c0d440101201d440c0ea0b6405c01981e505810b41d800c138443d010392000325442d607214a10700050503810401a40c034042d10703440c0a48040310003500c0d950612030504030303030281c40d20400e00e401e03c0f0709081400400c40b00300d50710030402180c01c16045544030344000c1c0018800340c2d030300241030300580c0d50540d0001802200c010050341d49004a8402a80c144a805c5c1000f00d0701c01c42c01784e41e41965200e601c4001e5981c9542c0d80580c5d02c0c04483c6207120 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 1107894 1250 1106644 1106653
    0x303020a060e010e060403020102030405060c0315011d0d05010501080d020604030504060e03070504060312030b01181a07020d0305180103090f020108060a03080a020706020709050f060105030a060504020307031a010809 95
    0x28007086180e030081220b049808000070b8044100d00324581001411602640980d40c080104428498140042c0742d004a0505034545185407891820446201e02c1c1505030401c040c1e01c010744072121041d190811601d00003418091040998500301c7e000e07200901501d10280240c0400c0c0340250300002e51940903580c507840e0942868213040044990061600102d503144c03150880024041c1c0b6284240d40146004480340078580244900117070a03030f00b007101c0d05810808003103010300811500580100c10b581a048458a00901c01d0015801600403000069807140881900da010503801a005100603400350b22004241d0401d10015030071a1016000030301b5904485030220300561280b4180c80e80000f0090181d8106510317521450f24581003c00b290b00568040c0405100841e01040240c00401c180c1d081400280303000e44015076107000240690341400004004034000d01c015801c9500a407602a10840d02e902c0c02480089c040d150740b60280501041200d00803126500c203289071403003000c01e04001c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 1109144 1250 1107894 1107913
    0x306060b040b03011203021c0c060b01020d0518010212160201080a05060303040302010503040302010e0f0705030c030102030108030f03060105040305030a020d0e0301020a080417040306060308030a05010b0a020a06090206040e0703061a04030302 106
    0x134116094017110840460040d1110780075400c0c407414004200540d41d079640b00301c03100c0d503281c000216142c02c5030042c10343d40000e104881d0564050200c4201012213400d22001c3e402ea4401030303103080e10060a40703010b04030210740c1840301c0c40c145100c1001e481c000d903507040291f00d42400840881d882540ca258050304108028805540078500554006100e440006410a88031400f01d040484134061030111b504000d01c2001140b900300712039004500110000c502d0b65141a80701541c074405c495035000802c0d404000540240e00a8041e10025500704041c1d0307983d107098040084d00d130440c01183c08003090340e043c0c8060260074148240c41c9001c1d0300c1d8980c007405844a8841034002100d014100001020822000c00012202d0041c40300643c4503a0070142c89042c100c1c0f0800039158142c00040e4100d5051020902180c2d00142140603107401c0040000c8040140c008a070b941d1003550401c1c0c0c456084401807107003140d4503502110441d01010344084024101303a1a001071440343e07100280042e4003c1403038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 1110394 1250 1109144 1109159
    0x30706020f0702090901050609010b0903150711030c0706080a090203030a120f0603030302030604050609040b01030b0606071e05070509010f090e01090209010602150a050103030c06020a090902030c040306060b040b0301 95
    0x1088290a0030300c007581000e206a0005481e60401c44100b4280d944a905002e994102041c00a01415540310b190341401141d5000c642c1d0b518421014245041a26012450a07400740040381f100704010410f0303a58807a1011502c5980e130016101e070310b00241e0b0200004005184d80e201d01080f481c1d00a02451603c008110101c45010381622101c0501c5c1e980c0341c000e19194103a206d00b9004501ca610050f803245070880410045600003012603004034240d0b010000083c0c109441c0303605603540f00e100c0e00d8441d128000481d469008982000b000314a101820040c2c03001501400b8441b0b910840444812070344078024003500745d800b032103030203a50a0b0a5905000b0400c8903080444d14109000001501c800389400003002494207920582c0540c01041c905282c000300c682d4016406409244203201e994550380d8010200d003024100504415808107070100510310515003000108883c0c4070540d100d080c29040c101940d80b091008440e0346150aa00042180210081c2c40441c1d80b005481c60031a0b10f003440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 1111644 1250 1110394 1110397
    0x703030506011e02070303020610030210050703020c0307090506031006030c060e03010b03010606031e02030705040306050403050702030106030506010501020d030b0a0902070c030f080403020f060c0d030b0102120301030501021306090803070602 106
    0x4002d050060340302807004031001084445803400c0003a0b0051000c1461342c2400b03401c05002800350741c005903500e81c0610246e2505280da02d4003100f2480d015940d4608e5003012403c01c5512121290300d03000d141c1c2d00141c00c0d00343e504242d006100440681c0c0124801010300382c112956484004d016140c0400104241c6001c0c001211341c1010180000c59440d07101400039007141c82035008440400e907102c81000c1468081d200e2840c0b04415404214698144014040c00074043c40c03000810f0303d81c5900c005420580306000baa000a60b002d0024020070351245000c6480303a02c01d0144500500c11040345140c010b11901802000000140042d0100313400d14100001a50000ea0240c9071422443c40000004100e10080c18600d40183c040c0d50f1103604500c104121a99266002ca00c02c0c1010310503243c003c00089640810040d0504002455604410040c0e043c101680e145001099000c0f0000082c0081900103104003108031410040e52502c900e010354044100d4015076000343d205001030000280d0590 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 1112894 1250 1111644 1111651
    0x30603060a050601140c0102031005010f050301030809060705010e0607030506010306030c03020d0303021b0c0301060504050103051009020f13020d0606020105010803070303020a050f0304060c020708060c0f0706140403080708070206040807030305 107
    0x5d0160454a5046090704040e4415041480d1130fa5000040007000414518040003030725003440c001300400144000103201d4001800042c081c0000002c90201542e110012101c10743e503c280244621203036507201070703220070007140d103d804681054009481584a8070400d03060fa6482040d800d8801c0c21078082c4100e15001e00d400b1000c3c07590811048101d003800041152407000c021008050b5002040c0900d0300391819640218043c1c1e040000601c0014800b1580c1f11045803c800d00285103040e600004031490400d00d00f058201d18225214a441e4409800a085280741f080c800d2080c0c59441c1c00c100e00300e540922030180103810500410300080d109400a2201d101e0901c0d00e00e041c1100100c403050164025242110140c1d561801d0042d80d64062111b1300040c450b140184ca00703440c0050900800f4404c502c4e0105ca4210006800310400103240c0c080000070a03091940282840e00d81b601400450007640c8400c0400c0c016000a41040d10000d80c4078411a0f000f4601c80c2032542c103135030581c007601d03019 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 1114144 1250 1112894 1112897
    0x10506040e03071115031807050103060b030a050402041506020307021906020303040b10030501110c0d090609060f030609050a050f09010b030c0609011e0207090b01020303040804061107030c080705040e03030603060a050601 97
    0x4a00404284401401b0b9405402e140b102c000d5505202c5451600e424640d0303011506160405c070007004118102400e40e40d014991000105241d5190301c0024000d24045543c80c5a04140b40c01c0421540d07030000140c00140d1090b02c16500e1401c00805138000c000b1036102c2c020040c1e000304000741c0000d0309130207865002000d01842c0c80b01c1a0710f0350f40d41800d4490096081c6100800400c809070b50490030414040031018904102d4981400c0039070041005015008241c2441001c0c1000c800540c881d0340803400070030a00004101f5810046404030141100380e51010540000c5008104001d80604c0307000e19000000b0010900a80120140611074010740421818040c8043e035200a02541c400039000f150b00c1030b405008001c2c10101d512080340c2c80071034403904560080c07042000103a5002d0848056458504041c3c0b4400760703200102e4a030540b55000108400c000450003d0110070014035441926000c4074284140428a01c090750b0301c1c041110240c0d810f89c420004903072100030310b0780200d07000a0306 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 1115394 1250 1114144 1114159
    0xe0105040909060b01030b010c02010e01050a091d0702070509070e0108060607020d03030b0108090705060409020315030a0501060602060a020313060507020309040908030402090c0a020d080a061701020705010506040e030711 97
    0x1c1c0c0e50240121050300d1001d4805a0700c40b070144465682c103204074415414242048211107949800003032603a141800c6050510000140d0030b000c1c0e0b0b00400382000280306c8030103000c050301c0c9500001c107802d1505840c0c50700584501d160100e65481c140001c00c0c40350007207641d2007d07000c14460046500c14009088240c00890802804016840704002e0494440c0261408101c0d0782c1400001450920300030003908003904554000d01c0282e4444080f13400725010018003503220b440d0000c4c03000c4c1c000c0c0304c00c11543c1c0c10300c41c0d0005801000701c190001c002300c0c0e6441e000e0305e00982e102ca43d01d4041cac0c80b00301d0342029a014a907000e600024550f9209641045041c070450741403400181c0414200c2d02da04105441c1c129020003000110302e4a084c4907980201c804074405e08000b6180700180d61014a0042c3c20180060140081c0c03552101350b1044000380010680280300c0c0c000e03c0c14107030003540601d005840d15402c06000403407134107040c01200c0a1917104801180b800180d41c942d0200d0303008000065900010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 1116644 1250 1115394 1115399
    0x103150c09030602030f040b010b03090c0409020406050406180c05040501080604020a0e03070b07050f0d08070c1a040317060306060a0b07020415080102040806090105090d0804030e0901030303050603010609020f0702010e010504 99
    0x2051004d14811b403a0300345541c0303d0f8101418010014641603209002500c0c080013040980880411702c40007402c1c0c20b03600403404102910014002d482d49400c099049460200c00044420355032182c1d9100444210b410410315444120031250780c0b00d64050b880c0031640c4100480c00c10306059004200024180c540348100007070b004c00007410000c075a4820429035001095600501c81c0a02030410f0810031a4010441008460350140001ea0020481c13400d0101000400c1e082c440c800e03483c004a1a0b12480140e405d1610f0301d00a080c0031a10940c1d030102d0010000001e80a040002d0704501421005160b042880e01c1e21591028070b500c50441240c1080d114950b904c03454150302c80000203441044005078071642085030403860900000c00000e060b0b811315060104800021601408901c151302e0212129541c80c101601d00d80070182005405c03100710350001081c076606522290080e2401c400074001c0a07030700c0141d40241c0c040d11340c4071500c1a604104480066004024080c554401070402c6400c065 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 1117894 1250 1116644 1116653
    0xc0203010906060605031501020106030c03020108060a0e010306021801020105060d02120c03010203040606031b06090e0601030b0303070302160b04081203060a0302060c01020304020a0611030d0902010e03010f061d0103150c0903 99
    0x2c81130b038004030110f007001c400d06c0000010f030f000a080d102000e04c005c2090524680390a5000c500c40d00c4082c2c14031411602141268690042060280000c917407002210359503490f010000358001d901d80241c84083c04081101507206000f014059000100182e55240c9a50200021403048801912041c41071026502c415282800514410b0703001d0100001c803180f460030003860890722107080e1450f4174200401442816000440d18094500440e03030502c180d501c04006030300816281255a6040c030002c12400201031780000c410f0540d045a030b003c1d00c809035403029440d28a001d0303806201c1e10b6401001d0344618040c0b444000d5640400002c0c110a40c0c40d580f07402040d0b456009202401090350008100025400c14043c0e5200508580c5004002c40d000e84c1403194aa000d82005c0640040d150311005040da0b100e001d540c948120010020000c1106d901d009800920051061903058600130f0803038100d10101014442c107c0390051884d0201e000c1d0054000010402c2e5201681405034010010000c074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 1119144 1250 1117894 1117901
    0x60e07031505180609070e0105041203090902030a05090c010201020307050901050702030c060703021b030c0f0f010212040b07021302090d0b040c0b0403060c03150803041401050705060a090b070201050103050a030c0203010906 98
    0x8080090f00711009003015024004d450100500c95014410041d039061070990f4410b044404403101c207038010098002c649401c8418000f10341c08201c0090000c801d2260b816195802b290049503c802194100720148e0700683c04d0340000c48503040452030521026150307500650082c01804d100409071070313502c0752503000100305803c0303600107a005a00030b01c2c41e102d0b020003000350345410307040c2140149804248071000803d01c042c242c41c400d000b83d581070000015a402003008a00c5050502070b0640c0707403925025034420070307000341070241d10440d0611507200c03600c01984204c40d00541d02800301d545040e1951201c44003240040c00071100080b0101000428029003005880510310030040880d08410000e402425608011041c2c124240e085104000c0520000200e8049a2058070440b001c0380070b120043c2c420303020300d16015105024036000c1041e284a80ea00c00d00701d5a00c6111181195210408203d0032102c090000411070382c440414a00842d000b0041e002a007480100007003540c8003d0303130320300301074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 1120394 1250 1119144 1119169
    0x90b0f03100b03070608010305060106031109040c0e010210060b03040b100915050111031204031101020405030715020d0503090703020d060209060a0e0102190c1703040f080a020a09060e07031505 85
    0x8850b40c44580c0e9095103030a0221100500441c80c084000b9411030700c90540f1508180714207401d0550f60a20100620001da0a864810400070704c100070b4900951405044440340c00c00c0c0714018007038042d1202c44030a040c4181702c25112801045070940e0b03115a210269400c0203440140011600c03403001a4484040c0035404050002004522070a842e180015103420036000600c42c03d42c00c00c2c003140d0140840b40a90691080d010320300b079950880c0c4a0340041c0213100b1500b0403a00b43c001c0600108094000340c11030015420385500b11000c808044000f02c2c5c040c001900d901d803080d04084000c06c0503150461a6000144c05014014a440108000101160700c1841804c020034000440d088080d0380521240c41ca010030b03801003507400c4480e9607500f00800b0440c0a5011034031081d520701d00e080001001a14041e09000381001c01180d1500010381d80c03144980d000724401c618180d40414000d11328041d410444070000040e40b101d484100c41600070f40581640302c2c00341c11035540d000074070b965408800d041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 1121644 1250 1120394 1120423
    0x40302090a0b040b1507020f1c030206041101020304060507080a02100204090509060105030d0215040510020703020303090c0402090a03030309060b06030a0204060201050c03010602060c070302010608030a0807020c01020106050102030301090b0f03 107
    0x10704044890a00c41a0f40b20322003454820607100c1e8011036041c500308100c0c0c4225034102c403180c23903c2c03409400180410070105040740b20301e101108210100f54001512074003441c026241140441090b00049a40740301c0c902540d030016106015080000342084d000e451030340c116005494400001032a0304040341c000350f0114002035218014841c400b2028041c4034050001a40901030740402d202e00699074a031000d099000d072806450024061290510154584561014040d5030b07a40c41410025a26001610400310750300030603141c1c03240c610b030510803216206e00c080c249040359465501d0a4008242d41e150540d80c00e45c58007501d090940e10040198032822031203e005803078500f400302c000e003102c50080c410103081c50708000501c40f1503000529150b100c400d01505607520100c0e490b0480c00340066038400310036072102040840140d60800c1010b0304c00c41c1190308550080186000490907501c0074800d250150300104014401c00800783c21a088480300034280c40742d0103200d0700100c0d1800d003440001f40c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 1122894 1250 1121644 1121651
    0x71502070c060f080f19020405090a09020a06020a0c06080a090213050709060302040b040902280201060302090717010b0901020109050601090906060e040314030411100e01020106290708040302090a 86
    0x1a19400420051880e220f92402c00c0c84d9151046000c00c603203801810007410744400500e1103446030110b40495011340030140c48003240d41404403900001d080700800883c8181c15024010074060300c0000c05461189c0c004840b050428038044054401800151454079007030b403201c4000c400751b101d08401c4184008070745000030f82440c2c00800107000002c0c54200f5000c050040008018400c101000d650a44e0a1490016680c41402c5d0044014206188402145489180f15a006644c0660202040324021303580c007200b954520104030380c4903051100c0040c1c0442004018030030703803581d43d010b0800100d040c0000104d086803a100c1c10b00c0c2039000d90181e0140c03515840c00f0b030200406805031200178007184161100901b86503501414102c400080c03d440204040002403e008000c2c0648400c080050000d043e402080d000007031281e04a0300c942070243d800c04400186411104c29030101d6100c911010a8050a10580002c040c0d84081020394141105000c04000340eaa0121101d0050741c0307020303001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 1124144 1250 1122894 1122899
    0x31903050603030a021005070e0a030605040606050402070203030d110f0f0301050a0503010b01080703050a02040b030406050703050702031305010c0204060905010b0406020c060a080601030b040f0c1106010e1b071502070c 96
    0x2416140010507140c082d41003845080301c01e5800003060b6480c1c0c5015a4007181660f078001d0f044608820708028182d2080c5222400001c0c44080d134040c5028070b00501d800c1c403a0607210001d00c420f80c42040c0c002500755100b007209000c121100c0e400076032103043e0001c00525000c1d004513607500b26042400140f100c442c000004102d00d243c407000c0c42005020540c02800010b4000001800040c00100040103160710340d4000350b21403916a0454000d0000b43c0505500d030304003418588001c0500b00c076140080b82c50100422561400041036a541582e007107212880c0d0303800c0500440b2509000142207030016140c900c0841d01c40d000d4041c950103042800070307040c0c03070758134160009245c4a4008030080c00f4550030452080030384e501c00040340c9d200742c0a007800301d2040e4246012030300130305888210b00c3e50f15250500300148140d100700492020640e51040700d0245e600c41400d42c0d4691007da5040e0752320140b40ea0710390303204140000a81100d078090010001c0302c01204000381d003030340d014480440340400b25803c00e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 1125394 1250 1124144 1124147
    0x606030506090108070303110c0310020403050c0108040206030606160c0602060403020706032901110109030203040f05040b0a06030b030304120302060a050a0b1e030102040317040801110703020c0108060a05030319 93
    0xc055011008407815481549045083c40d2030f81042d00018003040614120340700f00aa0070440a00f6110000c0c0403102d686a034014014000d41140c00200c42e0b138050f60810451a621900340703140030f41d80040c4260f103180c554108016255018410340000c0c80d5100042d0808500c08032400c0c4010541e03074015040078601868000d007008030b160401400d0610f0010a0940c050030103a4040420680944a006030304599005036607c030b44d5011407403e250b081501e40000c1650200142080350100c1c55a00c1c1440c0c0c03150100011f540c01521349580207444130a04001c164400c2c0c01030401c0190150036245040d407a000c1c1011000c2e030320a0f0aa01581c070640a111001449100d0719901030741481e0b00300159802080010008104040501c0d03405075040803042c017031703582903044030021030780a0000b000c000c030300641c40c074400d070054810003907554a0480d941404800c0c07101100c2400d50701d5400303000c1550800d00117450f00880030700703d2504070300360306804141a10304200030061801c01d010030140d5200705000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 1126644 1250 1125394 1125401
    0x50c010201060b0f090108040807020306090c010801090b0105030a0203040c030f0c03030e0405060f210d0c050114090a060504050102040e070c050607020d020c0d060b0d03090f090501050109050f0a03021201060603 93
    0x501c20f4208034001d01010300c5801d84003115001d1a150707003e40c4450034400328500401502950501076901840340c50140017a8083e5414400e807940f52881c0c3e6961401c900b201c00d212812740c08140104005400a0026401180d0007485601d54a1007140c81c0d0f161040d0030010070104846c10140c008081c014980c2042a0a80c108400c9030140201c1c6051030100304101d00100c2d42c98003803005181c103d61501e156141041437204810126844440b40c11001170003800145000d440c0d0794a4949400c030302c00c0c10203104078400c103004801070490709040d50385da4004202c010410f44144d542844007017041030300a2032080c0548203d94411080d034055044c40d83c240380d0040c1594040d5400703c071002c515150041496450040300b100c40c4410b901150610801810b019003259500a0003091b40c1ca08041d0401e03101c4027524604007581811540721404001114000e000c0c450110fa0b48070030401c0030b4903049080c00d03d0710201034030044070b0980e01c2c2d0102e2500405d094501c0156512500c0521490b50b0521 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 1127894 1250 1126644 1126649
    0x605120a050c04060c0203010e030d14090a0308060607080706020a03020703170403021002070501060504090506010303080907050603060607030507020d06050a0f060302090604090521040e01060203030412030506041404050c01020106 101
    0xc10400041c240401c480030944128443c82040c130558022140c00d41d0340a42c000024650180b0503690340c0c000703401c8100c004101c1288050301c160404000303e6001070000441100081d4140ca50441070740740d0300100581e580200340304075000320041011900040705400070b80359640081d2005a16542c0714600600025418a1004403085001c0200404240d00040c25964040190310040e55284a030130114054409500700c190054100003c0c0b00030840d0015103141228080c0e5180d003510b0f100c50410360b454004601ca1158010004d10100c1c00d68a007000091044510a040040ca081c04030340c00300701131000954055803041d031341d4000c200302c00300300740203080c1d00e544008810060a400c640c0012048107001d0000c0d030089503035410706020010208120420041c1130340300d4140300111042550150340c000c0c0a1441070700844000019102d00000681c0c3c043d95100c000081c4100301c82d10120014180100690351160300c0300929800d00710f400e110a07024501502c06001c0542160b8006401d440095 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 1129144 1250 1127894 1127911
    0xc0905030a030801031e0507030809010e01020303070801052101050f01030203010c030204030503030c0309010204030b0108030a02070603060302011709030f0705010b1206010302011202070302070e0a0504110108011a0313050106060512 102
    0x1c03420600103640103400d10b0541c0c2e0710150103005030400f4030030041400c03e20040100a4402d101c008005d01402102400003600b0990b00d5005800150004a03181e000650b01903000c166544014400743c58a00c0d48081550440350584c01d014400c02030311801d440c011b4030860700114038031005009504007800b40e006500500c1c14103501c0c0510795a900c0d0740d6880000c00d0300d4007008020020448100007901120010b54200c0074100c0d865845000035500d0b41e22041e03800380903201c0c0700c0c00014140d001e0f0080c441100c1e0141c644132910000f611001c0b5040f500240109800d0104010100c4903076036040240c0b1155004400000f003200e049814000950308100703159415501c513200420050f0703401590000c00e0490032030003503100c01e01e51070240c0c50301c1a1078100e0340034520031004204011403180c1c4640d00c1180a840c080810b405920015195810280610003820460040c508001c5000900650700f050103d001c83c0105800c0b6240c01c0d00b1242c2c580c01c0140011800036100c1c402d0740380804482d4104400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 1130394 1250 1129144 1129153
    0x10602031305040f02090303030403050307171e040309090c02030408060a0e03031b040e0103030305060f010c0305030606090307080a0c080d03050112020405060105090901030c05040c0c050a030c0f0c0602010c090503 94
    0x22aa042508007055205662095486988a070b841152030b80503110810b42c043c00b00c948a00f031502d005001ca40044034458005101c0103002c20442c90a540c00301d004240d44004140003140160700c0b0400c24400034025000c1c032003450340000d943c650038415a9003050302940910340365420075405500305180640040105824180000c0203100d010003241d811074030843c110540c0c07409800103c05140140e6020301c4068004800000034950540c00040c0300d61000c44a02c0c50300c00c2c1d1080192101c0e00300030800390000707000740005070310341c01d1000081070080c0e0010103c600746507458020500e022000c52003102d00904041040054003800c1041b040c90007410704041c81650f0419090f40c2121f0489140640718076101c0010800c140d0041045030344c01c1d6030240c2686842d68490620b2603203541076204080c003952804140111407031003001011400d1390b0000c054118200143c5048a4020010b40e055400040401c40d200c00960402d0446004003100d800202e201c0e003045101810103001a407005020742c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 1131644 1250 1130394 1130407
    0xc03090507061808030c0709060602060708010308090d050105010308120105030708030d050c0903010504050a02010e010c1509030201020405211204030201020a03120209040603080d050105010311030109110d020d0c0801060203 98
    0x30209005007580c1c00b51400f0369055000c441480c20311012540001903d000000d13030543c52941c08240b41055840d103030024002160f0352207040ba80c0344c2c2c080322504002540a0018000a0b84130b034000d000f0342000803e5150300070111741300c090840e4400e81c0100e840f83d800284102d0322515460203180102012800341c2130461070040d04030b40b039102d01c1000840c880d81d038200040c00e110390603042d90584103011b0300800603842c003881c20f15551110514268003007000543e5100c02580314042d15003515620090007029600c0c0156030704081c0081e004200c041d07540038000803881c1d4441045491414a8520924501c41802110641044010b8800114902e030400091016076000030310354503070700d92510342074880e0345280803014002e01645035165800303810098004107202e80076010b4240346900000c20841c5980c0d460041d0111070300a030040620354401e0004000c00c00140d4070081d229819000480d00d40114003804004913480464031403551552905001581640448400d01410490004618010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 1132894 1250 1131644 1131653
    0x4050d030813060903020f07090c09030303090203030c01020708030a0605040204060503040809030703051e0606040510050d0c0b120108100c021b03030c060108030901020f01060303090501030b06090306010605030a0c0309 96
    0x181001405010036840428065a116142d40080980220b4208400c03a158a802900c504009000c51010700c035803400442c1c038004603c980d840d0256aa29940d102c6032542e0f40640c0680400c68040e64140014000801089800e000601c46c040c802c0b105242c0d203103026106171040790341e03a03003001d80964030500080c0181c42c1c110701202c0d00300b07070040035072901c5010500029280440603000144907025565403500303802d02d45028000c04424810589450740c0e1000140812250304882c50203580300f00075010846420706556002c900340c041c07000c01c40c80c29250041c2c40103d510915214070045518070040240c00e00c01c3c04100d06491581f9824445940844402961a11000111041101c86200c0c10401d55000c0040b60004800030b4241d9a09607511800e0360344907003003a90014094040d46d0381c55031680e8418031408043c0c0c1c0c0d0644401c002a41071000442c020000d0b801c1d4150000350810000c1d0b130544d800c00140c0e00802c00303030791602e90382e01c0e00f0401e8006854040b40c43e08245403d100382d940006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 1134144 1250 1132894 1132909
    0x40503060103030c110406060203031509040206070b04030210020304030504050a061715030102090301050405010f060e0702070303030b01050424030b010c0807080c01020906040e01030302070501081e0903040b040602010204050a08030405 103
    0x490b091300d00304801c02e2460800c0c502c074004494601e80c0c02881c14000040b100d80200c051803060b0352042c402c0311b10a084000f0300c0608103044400a40c05039081041c000021030348030445030001c0c0070740304072200041a102c4140499105560640119002040400282c41c01a9109024010900c0c00481a2007419032400d04000080c02c0381402d07408007010388045480950580e940601c00070001c0c092030803d0304103640208068000c00100c10f08250010a000300d089000c80e001e0a81c6a008094592441d01e0442c0100118144581005010480010070840030034040802105d0460080840c0c002c0740d0703015044807400000701e418410b6481703505010919841c02e5070074103500200803985c1c508039041141d00a1090104044d8408d030003241c0424050f0b08a1117660603a03110340c0840b502c3e59110760040d58641412a02c00082c3c2481400e8400201007442003290000e00310012a0b040c03a481d20564000d903000f03500404010303036021404022314609024500300420320345000d50714081c24540460882c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 1135394 1250 1134144 1134149
    0x501080412020c0303120402090703020406080708060d02090405010203090114010501090605031003080c0303040b0a050c030619050303030903090f04020a020c01080c07080301060903030809060126010608060c030117030405030601 100
    0x20102041030340700d5018000d209000c1e15020050079240d54100c11540340c00203410560f0240d00910002000503803045c003d108940c19200140c907031020b03d6440368821a28850010720480d0000c5000d020080180c98641d41d9600070751141d0009a12482d088a503142122084500e01c0c006e041228010001e598011030300c02e054600c103107400b560700e50758419003008600541d0f000400c01c01c0e00196a43c00030309e0100146000724460a202642a26944120b0381500c406035040f030310400381000801c0c041c0c50b0091f51083c1950003600c45c0994a503842d0002401c1d60400c0b5001e200c00d17000001c0065003490807088054a01300107c604500b88044a80002e60350104403c0300d505110760721002c40c0000800e0425900c3c0035600c54106660303907841d000010f00781d034641e100c218045100c2d0340110f81c1208003c0388140c10303600b04841c180b00000c080008a0280d82c01d03480d0852880d56120008980b203035080c811135126071102c010b85961380d41340c200750a800c4a81d4048c0400319420070b1105104940d00072502504 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 1136644 1250 1135394 1135403
    0x5040207030203040803040605250308010510030902030a0309050109050619030203090a0f03090303030b01030207050615010e03060f01030506060306010303050306150d09060504021203070507030821090f07090605010804 96
    0x300d49249140a03451849181c0000101e44004600041c00c5584040141035a010b48400c42c0254203100805e4688003602c543d004020500c05801031203582025003886089441d50b00d0042a94080c0b500428140130502d94140e00280d0351150a109550300000b940c0001d21098a0192030200b80c1c4020004a219009074101010380000109100c02010810102d0700c94205c5868100b0502921b4040c00c11140b41c40224040790405820541960083c802da42020b6001400760015603a00e0018515010003524040d06020320340d0301d071803035603141041418800e01001b40c4101c45541103080c814504034004042c40d00c01d500c01001800040c0e40300c030a980d0440001d403806c0402c01840c00342d0081c103025103507a42ca482c500d00204141804929044240501e000b9540b4103200340c1080d200f103440e4803402ea0050015406201c00b080000c01600003000f0303404540d1456440109d0007040301d207070007005648015a0b036200403800158903c042c4800c500030b000801d400c0201030316160000e400c01000910140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 1137894 1250 1136644 1136647
    0x7030809040b010201060302150301030b070903050d0f0203040f08011508010209010c0b0c09060a021f0204080c09040807020a030c0602010b010e090c130b0301080106090609020a0e0d05010603021509040b01090f050402 95
    0x180b50364000d402510107554020090f1003d201c00c0741003402590824032003600c0d01f6440c01c000c13411080c050041081501c2c1c0080243c1441e0142c83d0301540c0380700e9040005004c41c07108220000e0142041e480760000b42070107400100c0c65808503140e10040941c9504003500e1a40304001011082ea0010491174540b9132180c440c0d0700d9039455441d100c026010b40004142c02890004219030902d602180b0003140940280d400311080c101022420200d0256000c2c145156100030401c113668070702000134962143c401e0105524110951b030128040c191150700450740c02c01084414800e4640a014280001781c0a103071402c0c0b0a14401c0010308440c130090702d000c04001000a0b03e0784503480100f42c1c074020303040004002e50f4035651260007600178101d910880e840640360903070208400c0990b000303d0b144440301d540c3d0584c003000002c0c03c10a9880e442001150307159a80c40300000141c0756222050700030389450000b43d441c2c0c04100d06120580d20345040c43c604000e41e1002c188001e900d1845030384107444007581c005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 1139144 1250 1137894 1137911
    0x60f031602010912030b090f04020105040603021309090807020901120803070305040206070b01030309050117010b04060e120d0305040201080108010b01022d120c0f060c0307050a030f02130e07020703080904 90
    0xa0b40103001200f40a030200c0041d059010125400d07070810040310909440e40625955010b8500c1038020703066030002c1c000b81003023008008251003030300a0201544031403446416550340e02c06500840d402030004894100b000700b041000e52900b2210280146559400380d41c0c01c2e0f246550300107191000034011000d055035140800c0c19074407070b40c041c2c403586584000c10a28650310b90802074040307c802c0c460740d40080c071003a400d4002460309025aa04070303180034000324145410501c080e961b0002c0303024100c0d080284295950365010b4100800c00221b0516200024503007018000141000d0050300b20b0426a0304055404540e0b9038000b410119002d507004801c0c00c80240c2e0f1030462000d01041c100e0059900c1134010007940f09039034000800150340d055003114034030141e004080d52523090854416580000500009941c07900801c002c0c480034001d03150000741400800b4620080344c1064010f4401d034024070318107000f40c2900c14a000c0d0405090700040280034610303560505c2611418101500403501c41121 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 1140394 1250 1139144 1139147
    0x50405040c03020409060b040b040c0207030f031103070303020309010531020f040f0203011403010501030c060e03010f0c020d02010617120708040504050108060405010513080703110c04060801020702030705060f0316 94
    0x58020b15030040043c0030480d03c90030b05001528a454070f06126502e09030f50360b1520f03c1c007445040c214020980190030b401d441c42d11420901c14599030103a003444655250341da940e440c00d2000b401d0f01d41c800d440040c0c607400e01c581c00500310740c0014400c88144017113a0101100b4161388030451042c51249141e1003203002640301294548030b154003000c1c3c110341024400c00c000912500a14141d4500031001080054054201400c1e200300b0b11000c0c00d2090042428030200d845002c0c0803a11a00160001c1071103070071902501c040392181d44c0d00d08010b80006d402600303819820300401c0018100540e008060100c2d0880f03150700c1e9a0224034500e09410001030240c104144102070f5401800001c104121075030b95201e00c1c60b00c905080398220b0b229460301c030014025906048604010503006554103007044c07459642035486070b1241140c0d44a03071081602001041d070340e60003200c001e407840800141e143c480f1841458544440e40d004a8801c0b14144010181100e1540c20390f54040524444607003184082d020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 1141644 1250 1140394 1140413
    0x90b1903060801110c010f050103080f0c030c030d0501030b0f010806010501030207050106030218100807030302030307030b03010207020904050304050a0801050f040204021608130e0606030601140904110301030c0314030c0705040504 101
    0x2051036a0f50070030300c03002e0103101048090728151802c003009000e0144001e201e5011036100740002000040c6c01e100c0100c014500e1000380c10070504810840780f030400074005540c6550080949207007915110401401000740106819401102c02d1700b05c00302e95414030340040d803503580c1406007a04040e07000c5007500034040250000001113801421081c01c40f090460f0740c00d201c50044601010f220411040081c440d40000341900450780c16901860171602d40003405c60181c600701d006168590b4080c089000983c1c0c0c1c840145025610440096035030750702e002c0501040600950125442c0d034034000820a420b020020300552203641102c005907241880c06d05c0d04071b81c4451840103002d40001150004810380b8200d011001e0783d01d400700c1102142d0710181003000301e10049034120300003044600d40004043e83c0c80098880c4020090000c10041c0381120740341c400341c00980c020380304501009406c03c184886440d208070950b02260142d850411542241c1c0d54414a41c42414001d40c0d950700054140300c0300c82e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 1142894 1250 1141644 1141649
    0x90603030409050906070206060a030302070b0f07080d0911030a020a050f01020a051504110d0201020a06050c0405030a030210050a05010e011707050901090207020f01020714040f020702060c061006090b190306 91
    0x2004000e14284541d43d641d903541c5c00c403484d0026202d40d00200b00d10746000030007a012a64140d006181142c20300301504a40e411501c50b2081405040c4481000a0a010007401c000741d81d001000645810605029280c1d03140382c01b510b4000d4101d2070000c1d0241c2c980e030801c84103990381034508680546450307004030300d4201c400d10301030801e000e02400c2c0701900d800800498040c502944861503020706900402c241c4400c00400240540d0204200307000040e940c2d0070141c2e101e1395299009084c981c5c4c8602003400e1803548502100141c0040111286541d29413003040e41100c1403482c108903d60600d641c0203544541070060030321994550b0703502070349250108a01c601402015181d180c880d656401c3d1a00a900115401c9104403810500d203101c9510018400c001ca5a18603482c246c44005842440300414100c11030740b0160390200140d80258449000403e0711060010050440340b80c0151040d1980c610f6401810070820340d29000c00841000030161401e01d25110501400f030a514941500100b40c01d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 1144144 1250 1142894 1142909
    0x50a05030301120b0a0c0906030c090302031903120b0604030212070f0b090907020c0906010507060b15030402120d080a0c031508010606090602030c0d03090f060501080102030402010e031501050906030304 89
    0x100f1089118031036154107900c42e903004803c43c3c0b1440410350139101e030f02521000045180c0700c2009480d1190304400c608481504001c0c2c0c1454880c3c0110742841c04500b030808c009545414070700c0030540c2c0050758500400540f1010402600541e00081c2d05214038800a40325092000307002410f20f03000c0c0201c0000f04089180c8401450341e42a5440032504101c2496101d400c02c400069002400861b54030700c69840144003c0c01c0d507969030010b641c0c82d00125011b856180e0341d0700b1101ca99880b01c903406134100b2004041c05880c0d00c2c10b441007140c1c0f00c03204211841960481511306110a03004450560040315448012807a280b1542d402c5004007400081203500d9080c4410020741e542042d40100c044e40c1d100c1c0d0b5105c51941d214081641d0b60300c10707190161001c0c1d000c1d000d03646640d4072030b40c01000f000c1d12075a05144070201c543c44800c203a60013270f0059079280c3d6001060004540c0c002c0710742024402e0039800f8059000c2c000038184840181442a54029086000054250f0b6000c1c42150701501c0301d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 1145394 1250 1144144 1144147
    0x6090910090903030501050f01020604020306061507050601080f01060b040308090112090506040b060406060201060501050f07140d090602010f050705070b0702070812040302040608030c06010b0903070b040305030d050601030506030a0609050a0503 107
    0xb14200140541400e1280da4052058a4000d0b00103500c086416846260003030018500746e25a0b001340007640600110034140c0b200c0602100e0001081440014024804c2c1e000415a5103c1d030b2408600b1240907a100c0801c020080004000155905045d60070707002090900084a00a20851101500006500406c1406000100b104008004003000d0103900155010015240c5815043e030882c0c0c9940905800716030180000d481e8a50780c0001003400c940310340d9044070281e50311340d0304501d030445001100d404030b1228582404165824130802c5509985060309108a00b0242c0e4042c02e0307403044100103002c6220043c0011001d07402000401c00429520089413520390b064038140505405c14042248182d091003000910b00701c3c000709880c0035152080141c07d251b40f0b8074201c18400e40c00600c810f030309402642c100003442283c82c03028000640c006c00155a48240440200c3c04550303004003038030705040c5030000303101d90780d1400100241c031907520240004d00403500b81886440c00381082e0f0001e03c0b6100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 1146644 1250 1145394 1145411
    0x2070203030904052806050a030204050a020d14010303080c0a080103080d091502131205120304060b030313080624010c0c03060e010204080d020109050a020f120105091b01020c0609091009 82
    0x1060342000030001701c3d003107010700d0000d904200400f0746101c0e104003a40118041c00500151515a2045800c08690344005103481c1d81c40884409545450016002403004000100285038100803c030390b000c007100c40c449250101d0400040d0042c0418040608918070100300702d500004585d01c28290aa003201c81d0003003c80080d45610b01a51140c0000b1910400c14800025000380312002c80411550003000392001d0340c24100224001d410003003081c2c0314280c0b9468042c626840500c024603030814000304444080c0d052401aa2400001810b0002c81400c0102d000e46001d5460000c021800424a8510307043c091a0404d030410840581000e04600e1801001d1120fa41c2c0550003881240c20010a0300c149004150050b401ca400d800400b4005410001e00d8a00501d05038480b018404401030011006443c3d030101d40e401c45a00700c034401080e81c040001c82c0a90100740a140c07903140000d200030501101004041a0b25009200116000b4a0070f90007041c0a1900550782202500303494000b00304045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 1147894 1250 1146644 1146661
    0x50306130509030417010b0d110a0b0301060e0f0108040b04020402031902041202030105070203040b040e06040f020c01090201020601080a020102070e070507020d0308040209060a0b07030807030f0204060804020307050102010203010305100207020303090405 111
    0xa0040c829400030102c240040707044c2e0b00c5e042c0a85107100000405801c2c1194454668074541c000c030b58041c86c0d01c940c0b00b50003c90907075982000741d4040d005035640c81141c004d9903c10301c0104020185114103015429040100151a960b15150f100741c1c190740240c0c480d16011207090b240046880c8603081c540c000320340440d1181a201c1c0c107580c0d00340220b000340025216040142c1e2070b03224501540404440c100400e20040317007403076004c6400940c0a44001440500751b0030140072070f0403452203200941d45070303030100381950780c100007440c00b4200781c201038030043c0c10542c0007079540d01c21845075500403c00c0100145500d40100709440c809a005004941e006c405858001c00f0190203c0e0124030411669000c070703416040840003a41901e0682e400580b90140c20f880a03140c80100401510070180c5034002d01030070402500181005249940b00e54009003424410542412513513007242d411a80306000420200d0300000780048d54000c0c00704010703903d03a114000700b401d6218030148960414205801d0040b0b81 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 1149144 1250 1147894 1147897
    0x10c0203030a230103080a05040504020304030804061506050901200604030503010806070302070809040b0310060b0703030612081905090a06080702010e01060f1503021c0605011404051005030613050903 88
    0x1a030b0324040400003100c1103441c030740c0d4103124589641400500c000051000800720002080e400c801c41c18003a09044ea00e00c00039050740c0c000c0f10106d0001d04600c05000810900b4040c046a8001800b181d402c49818a0001416030148042860401c40b412031040d000d80c154180c02c913030207038044060307482038541406d001d4511380c828481c2104038072600000440051103407007030301c12659102c4a82842c03c0f5540c41000058021104c000d640b40c02405090300010b000c03031080b00700402c1c4280c042501c4504900f00034040310096408042200c09160045000444050840c1c0d0042450b1007040184010084102d5540c0508a0130300d80000c400c107804102940c01c22041031103008039034001d00403804141056403c3e03030b81504c03850584d02c003001c90a201042071554119034020741c0d2320f0018140940c21140030207402d0400210b040569071110b051010b541c0c000094075006506c0c60505280170701d001d010880c406400b0b92613008000340800460815524001d800044500b080000d00c11414036640f29a05d9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 1150394 1250 1149144 1149151
    0xc010203040311060114041a03070602010606020c0405010b070b0405030d0212010302040e0c01020607030b0114070c03020a061805090a0209060304030306050a06030603050309060f0702030f060604110c0c0d0201030608010c020303 100
    0x210744420358210750b2030300000f801411ba0340b1441c03110880714901014040540216401030241c0c51440800f00066101040102d000f400b107580085901c600d0804080c1c1000c42104480780903138286001480101c008a086880880d840b01140c2d100e56924100507041d80070742c548240004e8000110603141051180d0241d058038003c482c10003405282c42161591000304120b206d000d6000003000076001780c044da124850707030b980c18103141c01d1b61200d80c80704100300d52101504581e240c010070310900540c105138840703801402c0c0504111882d80c51111000b25100e0349840741c0c0c1e21404805000901301a00c40e0140c8038244009800c243d201e00301860054040c00f01f0380220f902401c1e02c414001a81407181c0196002c0340c1c1c111001c0c51621030110203100203948603171a8910245001c01c00c01005841c02c1009089105001d005015141050300400080d61402d0485d503d04400a01200c10341540c0840d03cbd0000a20441c0d1156840240d4401600540b074558002e88a07541fa024503a0111034010004510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 1151644 1250 1150394 1150397
    0x60301060509040203060610091205010e010507020601050307030f03050708120403020606030c01050406030e0c0307030305030a11070804050603060f030102030705071403040303080103020607080706020301090b030c0907050306040b150c0102030403 108
    0xc81d803104180030152004540103981031b807012001c10b046040c45181d280700038069240409a03035072200803403407202020704011686da81d50740809400e66803080c030403590003000754400742100b03514010020765202000d01000d42003402e154810305c02c0601620440d1415135004404c03e4540e071314118003840f031040480c0c090340540605000240a8940841c5400b0201016100d55050030300f02642207004105807004030701d040c41350054248207980c040081000861090b56003603034070710b0032400c510142c40c64040b04004070030342482603800041c01c100030760b8140d4009541c5a07449550740303000140520004010146c1651000080c407c40c140d01c0700080110354001d4075140200d00c01a51190b03500d1042303100103070018510070300500051400c5c20080500600550740b0301d04020b8a078840400700c0e4001e17132040f8211a5a004044a40d0905112601095800310344880c003910b040c1d0703009408c034400103090314403032a41c40100c044140e03201c4816070720b05a040c04143d911042503d07240d034000c0d84103035001e50 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 1152894 1250 1151644 1151651
    0x513020a020d030c081503010905010203090d0f0507020303030103111f0203040824010b0304080c030a020d1b031403090102040e01030b0601031104030c030303090f0b0f0103061b0e0d03050408060708060301 90
    0x403618001d01810811207000c1c4c0d2200e03417550f28201030418200740c07211000da045d521400e40030041403090024502411001016107841e856071b10001e030060a80a1808060280500010000d41c1c0c01005803411640c024219040c024900c80018068020031044000c02da01ca113080303041c11076400400340c0103441d031b4401140c1a088a1b0b0f41d001448160325480320002000c2c2000601103450a64050b5420500c100c2e400341c241905906940c2c1190001013078040103a22900c4060b881c40e5000e60000c600e010a030060540400994074001d04280d032608c048a401203000011540c40d1200350304a400605100d0940840d0303513100d00c1d01c14000340040d00c016001900b80400c0200302410b240496080780d43c4403405d20701c0c02e0700d996015406046158019585400c8448000012442d1a58024464400602015100d60651820304201c03841422505d4a00c15040c59010a06030010202250380c1d0342182e256003044400e2400712071501c246d41054120380618014003007039a8001d2515405680b0480003072 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 1154144 1250 1152894 1152913
    0x70c0302070f03022202040302061603170f0a090213060b040503010b04110313020d02060406020a0b07030c020a02010806040e0d0903030e10050306010302070204060803030702030c07050d0503040b03070302040513020a02 96
    0x40b29012003e0001a42c0520a500306141c00ea100c0c1640b9603c03030a08000c0941401d42d40e40004000d600b0048141c11480001c1c05034070101540240030011141e02071035030110904250100ca07482d04401481c00d940a90303038003000800d5581c1c0f801050b000c64030b0314000b40803440c0c59804521064000c0c0c03089501960074490001da81e0325190046442a081044009065680d011252641c000c0401c0d07040c1e8000c50050242d00c05a00da06004102400c056002844082c20a2400042c6a24018080d1007010711b40b08510b000d055002c2024010701d9024604506942c4030200010700501403465008000e1007030106041d64640c224625400b101d000b0f4461960061410050141692001160b440000c10400004805600a5010f0700d18940081c00001d07880341c445212524540c000d60b22a40075034000b144481005a0412001001d00000d40d60411303c0d2585641d107659034000d90051480b5000e02000203a940e1740320781d0556005010082040e220261451a420003c1d8030082031807005010f0603840 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 1155394 1250 1154144 1154159
    0xe130204060306080c01021c03090f0804030506100509010b0a03020d05041101080708010b0a080702030c070e010f09090807081b0106030f0b010602010506010c02120309090a05100503070602060601030c0c02030303070c030207 98
    0x85844c2c030f0182c020380000120f20035100400d501a03023142d81455582c04103030003c61801625807500d5031160010994030340c110705050b440c10000500006d042d012000703003401251074a41000b0304545194041c2030710380da01c84400360080d010f00310169001602d460100414007000c401e81c1d071a05e110a80307030308189480703180e030842d50a00c0034012010014820005403105520074680340e03601c040385105903410078a105658070300b421a240c0c800e40c946a200d20040c0240d203a184042c000034001100e0421580d070300ca680b524030030301500a002e0f20000380800c008074081414110745140c4405c400c02044100d8591916204c40154031100f600c18600e86000855214014480d032409071505843c0c0c00c21203410740d420840c54501c032852024460105206030703d5a52aa01070341030240e1802e0358041400e00c0c0c0101c4a0392150203503031026200f648501d00070800543c001c280690403660a00e00400c422b414408252101289410029010b100c0013041141c0103034003503110200d0501c00e50a9440c02980e4594 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 1156644 1250 1155394 1155403
    0x501050913030203070b0c070602070b090d02010b01020a0809010c05030a0203030a05060901061707030f060605040311010201060302060a030203040503040302060301120204050603012c0c030102040f030b010501020102030c0414010e13020406030608 108
    0x28090780c000c000c1600420346c0c440c0126881138a50045a107440c0d51540c6402c140e8124480c101c4030180001e05020549000b8821719518135124030081150741003510000b582c8623030020000c1c0500d003000800306090b901c04c440000302184c01c002101d65880f80344074029540ea00854810003c42d1034140429107514280544904881181d91500102c026000340e11410820183c210b405040e80e0320b240009098190007030100a043d1521250b03100e40ca141000400d0200d82c402c2c141c116450302e6001e0005035904816503403100030b103113401a101c2d03403180f81092842c800c641020394040790200001035201c0d03131400540c444502c02e03507050169846110505003a01c0501e00e901305c100314040e40318500b5214105180007001210004c403886846a0000309003264440c0c0c00c440304e9801032100900500c425010103034014442031000f10301d54681a40d100109005600541e46800050b068600045e032041ea4201c4500d84001d0000380f04001040d01c0307600070760042c454600400d00780300002440d03101c0401c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 1157894 1250 1156644 1156681
    0x4080c0f0d02090601020114090106050109080105010e010e07030609060b09040e060114060c0a0606030308010303110708030304030507020301090204060e0a060b040302030a08030711070b0a110c010c02060309070902030a05010509 100
    0x20154104903001c2e03400c102d030700500101010304640d600d0001c0c40750f074000c9a514a01031000c9600004107a801c240004144002c42d402500590b8100001003110048100145d41111002c3c039036036075292201441140031342a60380c00400f80b1401c007400401c1c411f00034402080d410f0400c482c20480041040a059210a0244541c00141c1c0c03854400050700e007450350082a4201341d280583c0c1404446a840504461300c0f0382041d0001110b0785e0050003050303001603d81030004041070007000203e190401c150369038807006100601300140401c2c80021928250007080f80103900500500409480304070000d40308030111250410315040160000d071100180d000c4505403078003d40900002403c503228420030b584090288020000c502c074501481e4042404201c0160802c060b0036580d49001580081c4a031200b102080c8250f0042c1022008a0383c004802c0c1c440907606607002d54403951178041c0315040c4452070344a0b403c2c1034000020044040021760101e03060715401c44110705182c0740c13040003201300e80241c1c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 1159144 1250 1157894 1157899
    0x1050111070612020403050709020a03050708040f12030908030702010b0f0402070c030f02030a05070602010207030909050105031005040303020f04060306030b0a09030503040b0406020f0703050d0b0306100603110d020a0504080c0f 100
    0x14402d011080c030842c481144a0259040540b90582e40ea0b10f85160505a61013000480d6006c102c2011981d414020107070440072a1412180b01d0a00e074680365100345042034000c001d038441c110100340b410301030f4020107400760304a000e04c1c0c2c40786002e10000c0e0203440840f10840c81020080c280f080540f8091081d260500c4e0030102c1d0741225030a5a56040c2411210309080e13a040c4100c0c240c03140061010454580503052590000d42c0b034a8075813901406140c41030308100510f81c2040011300c85600c001652081000b80e22030003040c1c90b11030342403d400910480c0243d608a05001030701180b060341540018040364803072480e0840940d030f007030440c604aa05242006000170801c0010502180c54034003610f030064080d40c0c00600d0880c0100f04046554013112003203021903408202c00d03100244510070b200d1041403d402405013440c2c050300743d013480340c080e002d903800345035840540e81c15403010601500c2d95600d4800007199111030380300c8040d005400c1849200028800d00354040c1e502d0905292003c0d040001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 1160394 1250 1159144 1159153
    0x50102070803120402041104030305040e0c030103030e060307030609110a08010f060206040318050406060804050f010b01051c061701060810020703120504030e0d080903010c02061501110a0606080105010e01050111 93
    0x18181004041c0300050420390b8410748031f500800c07503100c0050043c8001e40c82a140c80740d90b2840e00c00032007032008000b0904002d448c0140700400119400611100095800f01c030810307680d540700c1c001076004007000c0d048420011300d0030800c80300b1440048003d000180c072544400b1011fa80e039280b404540b01c46801039800581194022800080c010256000a901c1c10f1420140103030710ba00c003140c1110302d19400703403000808c00b005000170b1240078444941030100a000a0044806040c0080e10300d10611540f003442143c5080c543e03c400340942c1c008406403810b10b030780880700b82c00141402e0103460540110030550045219030b2501c1c804500c21500c100758940c440c20710713848400600c1002020002d01c240c050241c0c8d40700c81d500c80c0d50344481500d81d0798440c08056884459020615084032030300b9001e4030540d8441e00900104d0f651646000c0e418520910701959004151034000e0304142420360700428076070801401217040c143c1900528141c591002e42654580c1e6508011240e0302e0000545900d503801 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 1161644 1250 1160394 1160407
    0x40c0605090109090e0102090406050102030309070302011101020d0e0607020c0a030b010303050711030a030c03030507090605030a0203060102030c06070804050d0e010c03120b10020c040b0a0e070806010c0c030506060307050102070803 102
    0x640140032030907414100702144039951151070060b05d00310350200d90b00d6580060b10b182d141c0341031311808020b03000a00c025825450303da030302c4075902e0006000203410701444400001074024250100c1d070004401020500440d01040c018585e00d01003554001e003d801240c4051945003459040481160381201144500341d04c0c60300c0694140d03014010540d0b007440300038004511a101084210a654420781d516860032a980c00e00030100c800c090003800c104807521038100303c0194400103680c0c02040740d4000682e0382c1c03a1b10300142e141d4456201803040501400040003402d07504031200d20721450181c020b0300c00b107000180b001c5134002e0810440601141c03001c0c01007404644141140f0414203082003000030342c42816800541c0c84480c0540d80301c0180d00c400e84030002401c0500a04207254000da070a5640b16007440468075114100805c0c260403c451200018926882458850080340e000780150440903141d060903905c0d4242100ca481c001d208594001850303502c000307203100449045030041c504259 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 1162894 1250 1161644 1161647
    0x402030403050a030209010504031707020909010506010909020903070905010b040305010606020102040b0304060504050f031603030b09090309010804050703020d200f030601060309030e0603150108011205030307030504021305070302041706040c06 107
    0x100204906c50420030188004000900c503030b80d29002075070044081544031381c6180304210001c03070020449010703641040248885a42c02c03030012419103004800c05a20340705284042803074a00d855105a0006007003400011b0780840d0000284141ea009000030710800340c41d414117a0903803056115581c0d0709001000000d000c075042d54445500240300b14141c54400c0300211100303245810800f03e0800b480d430b10981c0c440402d9018850501c003000c00307031100c05440c501103449a881703014107906641400303400400201080740c14403003200555802080d201184070f0904204150310180101e01d00e0704241441881c0480c5072a4020000c0c1c480b0080081009a0809004138040c09401c8011028407142d90500c0e0866582c0e10003852041c0190b00c0092a400701c140d000421850301039108c441c07100c042c502c03001e0104401008903940007945040108040d00c0300d10108200681804101c02c1192610062169440d8103400600807200f86150a840e0a950001c01c15142c02c0705480050500c1e000308410804c0c80d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 1164144 1250 1162894 1162897
    0x20306010324050703020c070e04020603010b0c1006030c0306050f040c03080901020106050904050105060108010b030c03040b070c0203030d050403200703020913050303090105070906050406020303060409050102040f030803040605060402030403050a0302 110
    0x40140d550300c070b07030084200001c12090b40c07402d07115200403e030003280740c040c1c4100030010140100b0308070794044554200754020594600c418052200308040c00600d04521210422501320000c580f04007c012456503400c00c00c00a1440380401c54800703041101090345181044200c501071a013111428082c01e15686c1c0300109075100e802464155520707800d001600342d8a8a07a45032103140540b00104803803030a01c0004004c06c038140c01000c0000b406105000071151404256640643c0c00700c04d0415644540109450700e42079040c0003541844009241d042c450f0340c54001a026070304c65101c0300040300f681c10301d035180365210204118031948003a0023040503207059003040707821110f0505d56001140d4961180c6083d5402140c00e890941e440d641401107442d80003003540018101460682e0405051030402502c1c0d200107801140b00340d480720000d005100086d4112402041030311075000d52503980b0300d0f00ac000794104503400d4a800b4030780000280181000e00803244a40e03803544d90350745000302c9280160001d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 1165394 1250 1164144 1164173
    0x9030d0b01090801020417010b0319030302030402010212040603090b0105060301061202030606070602130f050306060603040204150915090609060303050403020108070c0605040309090b0301060302150c0a12111002070203060103 99
    0x100007000c00005100034085c80100044c00c0c00640004016080c0701c4e40509540c225034031980250b01c59060310303d8088444d002e0329610799151402695a4886000403482c0c1036a0f40c0130350031084000580091513640650003105614480c1d041e811191b030340c0e102044070a0000740f08100c0425802180c80500007200c2d4021a4000f1000384528103200658681c0c80898115414401401c0c5100c3c10500c004094070b030700e040c000c0504a0040c0141c0c644103011402c4d9000241000340602d4a03002421011005410841d01801c00020200b205406412100c20340c000316104007003683d4a0080040340005e6140520002e81303816450b590f250a15550045403a203800904075010000c207074101e400010301d240282c60041d4000e0303587c82520303403c03d60180f08a50b2003c1409101360b140500c200b006031641080106040c030b541c082680c403000343c0c039000d5041102d201802004a141465048034003a044144005581410300444504580f00c2c14800c0403031050841c080d515601c590b004000045070b5a085041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 1166644 1250 1165394 1165397
    0x50d05070c0b04030309050102070801020a0507020d060e010504050c0f03060c190504031e0303050c030402030d0807030e0114010303020601050307080606060304020a05060d06050103050a0c0c1e021801091409030d0b01 95
    0x30b03941e40d1000c1c009400c036410440006074807400400041d81e0401440020340400b030000c40c503000c05401302071314510500200034011003420400d0b406105403640807081c1c0c0003004009100d0b516003071802d0794491041c0d1150303500c68500407003211140d0500260700341c8140c507502040c5140101e1704045203451244a6070750010400c08110100014040c8049002c143c0401032883c40c0604040c6805401e5440050820030f0710710003801000050790380000e2080410312541091401911402001c8019011011040440798240b1030500080c0c0300c0b00882c0ea04907800303603007500e4540e600c4408060b1228401e1141081e664026004071f6082d1038604021500644010a001c6402c1d54a80119210b13802c60b604101e08155146000c020650b018064290f201c000c080c3c0801022138061030140c031120040d600903000901180c3e848401c103401c4c14030001d0143d0000c01680100002c04124129440c00740a03072405d5508010b1460100c10142501d5406172034500091400c01812404100080805c140e02c5030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 1167894 1250 1166644 1166663
    0x90307050a080303010305010506040905100b01020102040b04030807050706030506060421020a030b06091005010906050702060d0504080301080d0507021c03090314010c09080309010c1502040503030a030b03100603050d0507 97
    0x400381c1c0c401e50010010407501c0c0c0590703282d40c03440c2021421264010a414056401c042d9450300050340803588000b4000385643c0016110120300040340280034507000030301100800140802807203038007005040464071880c111240036403104012415110103480710784d002a000d110510014043d004002c0b088443e01442c0d00001886400044400c1c000e40e1055400d9042d070f0052250506000c4052a80400101e4980d400c2c01c0c50400001c01090107846101d0800c44049054000c660300d200c102d81c05d0040104c41440f9a041508181395198002c1c4101400c41c41000c00e048200c500500c295113400e50000c0c002c01c0b8112200c2c0d070515001c04120341c101c08014801401000040c0c0c4a800d4284a6803c1000000c01c46540c0134007a200800b69040000107034010b21201456a03400761a140356198404080f1314070003042d1a00030b000c0c1c00b541d04895454080442c0785221258190711050707100c03008400301c841c004440d4003640c003101c0c0d281c0000b4204d608074203031540216000340c00900711288140c00e41d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 1169144 1250 1167894 1167899
    0x403030b0603190b0f0102030301060509060c0102040b09010906030501050a05090403030f05091b010503012108070b04030507061404020112020306010504091406010201051602070909141902040c030e0a08090307 92
    0x2165580308481004184240b944003a503c16464410780c1100b41c02561100101403040c40043c0d0760b40014882c074020003100080d00c03c40d6031108000d0307903040c00c03a400003591295162940005280c00041030540040d030740080c0000c05921a004507812a80082c00d482c1210f4140401e0160564005109400341502d54a1901d900c44c0d481c41564070614104d401340c400300c4910f000000c422440d1b40c407034a04120062005000c10348103109181c40d524843d01d0a103010f6080c5140c1071850f40203010001d800c814592041000f4143c100c001810703640c3c4101d004201d81e076045d203105501c001c416200603001818040b002c03880280700d40e00030340c0c1010781410110304169603090f10b603064130098a528143c1d072000c03170f0a110455809001c2c454101e01c100d2002d81c0b4405420100a545520318402c125807191904205014071003400c00880e0109220010b8503000c8072151486003044d03904071400c0f4041c0d850a0544c0400b14480d20070410b444c80d807403000e00401c1e00c550300c2d108034540124130115030500501100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 1170394 1250 1169144 1169149
    0xd050403140c06060a060311030a090c03050a030e010201060501090b030609040204022203020f0a03170904060b030106030e0d0203040b07030c0501020c15040b07020a020f01030509010608030307020f06060402041d0403030b 97
    0x240c200224a10b000304840c0c84c1c010f05001015034658007580a050070143c071814990a880c0a032941b00145030700000d0710580030304001c417581c5200c0c0e00103865400b54200031400c0c194807200c4001c4105080c8c00911489a46ea00119001e0b14a4401e2940c0140140003241071841d1183c02944c1013400200003604166908024402410351000c0350b02040805020400450174002601d444d10f0318100d0341204120300e036888043d001c1803040095005c400001030340100366500c80c2d0121000e0104c1f50040b50300d940c2c65600c064001c01c54400c09079294440c6401c000c0c0a1440002100c042d120180c4101e410211541d1781514007001c030607808c0f01c19540030f0040c00c0852404018000551031210603610860905052040000304040c01440440d0020404900503840324892041c0034403080c600015240d8039110024010001034002d050303c0e0000205025030300e0b074002400140c4410300b4066850340c1d25947c042104a1040d4407400ba5848031084120702050101e40402c1c1d8402d009040110319030303500100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 1171644 1250 1170394 1170397
    0xd0b0f040c02070905060904020a0303140706020a030b03190c091104030501050c0301051c05030301120204020903011a040c03151203020a0605040803010e0c030402010c0206030604110403050109050609030307050d05040314 97
    0x201e403001030780508420421103419000e03194106600356424201418913030080b40041e101d81c000601840f15455030030309040e40050031140070740d40184085460b42c3c00000020003800035a0300144c824845c07410210301c4410b40e500791402c0c03243e000c43c5441c1c0b000c3c030b03020200c400352040303400c00300b5003c03010720000001c210217004180c860700d03004201a80d03a41c103113002c000d4200c41900f0014080c0c0d80c1815201e0010301e0000480703041d602c40c8100340c0d0300d116061000030060320940d400d5940550030424000360001801c6c01c030707403100d02d4122414401207540c080c0841c112001e42e103440c0c5016a12000c200907104603642c00c0581240a44182c4102680390f441e610280e41013500c0813141c401000004100c0c1d544403088075600302e074588102500e0742c2800c1c2c0000348200042a0301a10503800080400c4880c3d82d04d41c05050901100c9060685407035690030041d000741814141a40d02d03004420010b01c2400d40401103911440342910780e81d003008034031407150f00145030050040b03050080c8540d0f81000102d0300c10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 1172894 1250 1171644 1171661
    0x20409050d110706020307030e120d02010504020127030f020102010e03030c030702070603020304080d0b06130306020c0d0e1012020d0603080901020106050405010501050d02031b0a05070501050603060c0d0b0f04 92
    0x40040c82104184007008022501d0b000b072074061500464024040070742d01004440c1d440f501494120001810b5000140300700f401e00f01055100c3c070074281c4110301950103400440c0700c0d074001d8a601c48200c85100703200000340c107803104040c10180361b10402c0c00046c81c00c6500c403055600620000900c8403200c0c4505103158400d40f0f883d004008007008100a00390b04124030f6028204a21b010750941c2010381c1c1c0c9060314080d284d404071140b51075820b00321480d01c4403403d6880300030030b88103c584042d6480c1400720007503112451101840c025140340070a158010030103a2803000c00500382c110f0aa40002c41142d00030f54031111240065020841c4c17003450f034414040d0b00b000d1401750f80071550300d00214002908407242d82d80320702c0c01141000c004005980e009402da83e521740e0151009a03036961030b051403a00d001010052070305c1004003c10410940b5038450040c0450302d100350001c00454032190201035880208031407042c0301d20801c03c503515044140e900104030300c40024144403000100c20002070152003111 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 1174144 1250 1172894 1172903
    0x1090b040b15030106030c090203130209010603020a11010e060601080408040f031127070c020102010e01050109050f090c030d03020c0c031509010b0a080c04050405030f030a15080f0604060b01020703020409 90
    0x38051002804280b0300782d950782e9104030700810582c1c1c039582c0d66501e100110310031502001e40c0400040e041c11285038644023401e6000749411000c1d1703151413000e0000d402110500c00045c90101d01e003180c60405101c0d001c17030741fa41711009180076503400d03004407a0200d004100701c80d00c000510002501d21000c1b00c045002c0c52051388412030011210742404198407800c07070000c041d00407180c1426440c011130524180c11000034904204129550f00042c0d000d090351518910340b40d86881c000207170070740e815480b03a40218500c40110758140c0703c2c21b00540c3d031a81207030790b1280d0540141ea5400004d900a0340100800040201070345c103110550b000080c104010a1010405034074420200401000e0a1182c2044804d045440b006030b6800c4c1405241d40307000607032010b4040c81d50750002c103040c00010010f8900e0b800070405456901d10340140044080d01036941c84000325656060301044006011a0800c0f4840115000306219540c1d91a0900902000c19882d415805205804005600d660281c100b01c107000c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 1175394 1250 1174144 1174163
    0x702060f0a02010209010809011b0f0504030c0e090c030a08040b03100504090f0209010f030803040210090e0405010603020a0603060b0304021504080109060b0906060405010504030605090c060d0b01030606030e03040605030901090b04 101
    0x4100007d8085039000300b440050381d150100d0490310300186210680e0488840c504641105410305098a84d03100703941015207510310051000400c5000c040341980320b13404440c155002c400703021040c15a110031410005040380c10500c07040c04030460103c0507607800350b40b91891000241d40e0f40086030458003405400e443c14001410341c2d40c01d42c10600c81d024014100c8506400403140707036031613140e0079020207000280714068001e0440b07151485041c42c10068841805220100e080604e002030003054148800c901516031040e002583e240a44100b908460130034601c0c2c1e00c0c0d55a95420048644050003510710000010b01c0040b030700070001d108482200748103613800210040164204140380030000c0c034880c0304050400090003166803100c140c40c1100c1d4425808111a00c80c074040c941800600951aa0803171004501c42e5000e0706642c109014030300d42030700c04202e015110041141036444906075618181c3c0308100402c002e504ca20002d690050001000040024560b56080100e6100707640c00e58030881c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 1176644 1250 1175394 1175407
    0x2040e010c03050c030105030d0c0204061707080607020303070503040f0f081308010f0207050d0503040c030b0a05010311040603020307060e060f0408060103030206010b0c070303030c020309040c02030d0605041406060702060f0a020102 102
    0xc241c403e09800c070702041403503415980b4140c00a9520b882e890351703690800030000d11403411520350341c000d440585840d0b035070460740190820150f82d8400c0c2c54418007070315100710750120320494004000c0320f00a10070790b80c4103840d59031a41c94070f000400384100c00f20b130301009200b100c6020981441c0644000e44419004c1d000e15458040c21a0940b4203038802903007c0d9204105450028100007070b88840c407441c6003492030310ba1351036040110000c2404d9002910040c0a58100f11440f00580c1c00941030341e00c1040066182a445014001165042c3c00006d4159108280900071a409440311004c0ca840003000d540c40c29031a001d025109402c00e41c000042c1da03108800600c10150180034150150540c12080d034104103507a20102e540700c16503c005014581d64003e1101101d1080c400c898150700301a00030310100040e510000c0d907a2b4000c0208140c590710300303100424980741c98000c141e1f408a920412070402d4039800c080010070b03804040100e074041020005003200c40710210180c0643c544075000142c0740c0c0c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 1177894 1250 1176644 1176647
    0x7030513080601090c02070815100306050103050303070807080708010302130b03010608030405040b030307030e061c14070f0203070206030a0506010203090d050307030f0504050d110102030d06090501150807020304060f0c02040e010c 101
    0x31280700d0817030f00355000510140130b0540000340c404c50150480065007841e40322219541c0c00a802e0380c0014110504080c00403082c030a0010081d0b00800c2d00d503541501a07990b82c0403c80d0304a40c1501e02c4c800041b0198010809460600c1002103907040d07210001400d01d4940c00040d08441e02c640c44021240c10129080109161510038900100400e40c00b4510f07008440d9030040042007100f100d244070310b001298113452094121403e2450400182003007050304105100c0a2030721104480c050002814400d05011052021064903c09640a092031b803c40e200c80c48600041c00d0020550350444c4000d01c00d541031580c3c1c50011110b81c0d0f010300c003d10f603505070300d040060050400c2c002c03c900703104003080200010340341c910380c021200b900180000b0320350b105140101d0442c400c120041c1d40b0b841c00c185011a1081c1c2550103d4120368407901c4040003092004006c2d81c0e10542255038801682042c001040031900618402c55012071074a011145c030cc0c110b500080c2124a03d401d440410781d5035008012586 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 1179144 1250 1177894 1177901
    0x507030b010b091f0e04090602030402030706030606051204050c031207050c0103020301050a050904050106091104060206130209070f0c0803010308190c02030c0103020703030204080303010905040506070905090103080703051308060109 102
    0x1454100a00e503e407000510200c1c03030060040c00c1801185540e6554940258401d0345210b0540c0d100410600c41201036041c8207000c1c1d04203a50583c82030003001d90005035940a0711400046900b107841d0b45040140401901005110040c000d46480c01448580e014994062102010700441082c9030340e2a140c180c200300b031501c50450206418544100018841a03580450800c100c039011a841030090355649061070250240340c0c40028160708041030007040c0c002160103001550382645c00c41c6c020b07a5820084542d84c03a89042d01a400c00005004680d08a00c560026040c1e51704909005003031048030342d07520180d070340309a0050702c04110100c2c1d0b41402481c07008001078003100703600e1b0500451000da00040e0720f03188406141030505a000540c501018000d4050303130010260681500d489603500c2511602800003250704a41600640001580d01c0b402000d401d010f8460284c111a066803c540c0c4900c01d0743e0050f401541840300c107000c8050440d250742041c42c00380c280000500041d51500c480385064 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 1180394 1250 1179144 1179149
    0x20706030504020913050c0d030201020918060904060203060303070807060204030209010501020607090b03090703020303041502070b03091c0e040213050306010801020a0e040c14030103050703021503010302010c020103090203010e0a0507030b01 106
    0x1010708040600001d0303a6403409207500072500030341d07241c200315083c50401d00d00003044259680124019104400381078040d030107494403220903031300b842e00707203010350b1004030300b024100c1d02c25a020010001080203d2080d034090350b40490007a088925194481d00e80d901c0f00e0f0480e076400c88500c2d03000902401182400b03100c00740105400c0c00284800c1c208a20080c15904c02405007900702e070004400100d0010041001500858026069907501d94981001d400fa906074114002e01501c240e642c0085d40c4c6039081f085911884006001d01040c54803825860714010002266600b00440c103004a01d00341d41e00e200914802450f401100c61051074541410304141e03059001d00084c2c3d20500648010f40c0e04480741c41e2940a048400090151070000143c80300f410709858131015400200000c01006000540003081e28000c40e40b0040d88000d01d0100765840c4003d02000380041c4044000d1070065000f07401c2140c088e0300c01400414881c40208030340740740c84d50041c000e44880e84140d90403c14090b400704898007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 1181644 1250 1180394 1180397
    0x109110708030f040501060b0406030e010509030c032704050108060601020d0e0303070609020613031202010608030a0504090203070309050102030702070302010e0402040e070c0302010608010f0207030314070e0105090607080f0a020706 102
    0x10409a900d41401c18000100b007106418249000103040010039403000d40071b032a10450b80b50b15142c940800030010440e6140c0c0c000c03a90b10780070119040e0b401c004140c88000840c072004601e888034600d0311a0f51426560116030031040011840c02c45599940a00d80c0a040741c000282128900b140c0024605007040540c8401e2040c2803070f030b40c41c1c0342d2000310855240030342040c0042145207440c40800d0b0144130b03103510b05485c401078503008010803039681e8502c40d040b5000d6009020094480b113080d80c4030b214078180d01c030215404100c01c101700b0b06560059684010380e8100015250815200c130741c00c0e40c0c070445100c1d005801c000018000c40d030701720a0045901206503170440c107007401d00150710844480a0309440520810062540c10180700350055000350200d50b00a0007840c000e004104060f40080c1c500310b02003424030700c204094000d50021070788a06211381d81c00c0c215a1100c4015502c0c2e900c0401c540da000b03a0100003d10115603240002c0c09140111221940e032a40d4043c40282021182d802090 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 1182894 1250 1181644 1181647
    0x30e010804020a0b0f0d02030702030901110303010501091809061104090609020408060105010305040503070f0302010515010201020c151b070506180f060402060a03060312020607020601141f020102040e01030b010911 94
    0x9a121420043c054940800da0a9a10503500011110358001d8803c91a05d0600020420201c03960202c003801000400381c03910100541c9031170303405449020074007403d070019110000c201b01a01c214100511a0703240040c001030902450703140c00064a0710180340d003030380031000103081003464540c1c4241c400620942ca0214107140c2050220364903288184911810192500b01003020f0100a10440b080c455010000320040c0503d860080c2c06448112214003108803caa1041000e50040c000c4499151030100a081129402c840b458480600070b010100142c40040c2c0d10070f00c0004200003040100d0240c40142018900071001c0c080ac0301d41414480c0c00c0d0f27000751360100222070340050411707080355040300c03410703221315400800300c00500b615403010b40942d200c504070305010380e00400c88070701406042e0300b030f2005683c0b01e100c52188241e02d00707481900001c0e015007aa440350f03481e4000502c04486840003501e420340c5d40311a01c0501c1000e070420f6400015600c01000042684c0c46149407400800310680e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 1184144 1250 1182894 1182901
    0x11010b030703020d05010204050612040302060604050402030a1211030c01060905010503070302030706052503050904050a02031b030a020c06010602061006021b010302030a0e01050109090201030509010905070b0c01020c070b07030e0108 102
    0xe52107503414030000b400350720a0065502046020b405075805000c2c060411901c0cac1c3c400c141c81c11400e507026941640580038050101c5c0701c6080500411740301e281c0140003810300300300c1e69a41040600343c4640100400804641050510200340000c002d403020080c0045180f6080140e43c204440042c1c0c42070f03202c0d5000f01b0041005031000715110044038070f94142617440b840034203603134018170284010b54031549100c0300d4803c041540210242c000960261002c00c001e0b55001c3d400c4040744000d0350420041e084249044180b071140000440d484a14040003508101a04540b24a401000c2e0007080150300b01604011101c1901c083c241300410461001308040e224000ca0111400f40d296005030405070004006a10380403180c20104408210100800c815039440c03141600800045000f02d0019040c000822403054050289003207040d0404042c002c51840c0550300800c42c2c0c000710301000b055400340010b0b03110319014440000145142c901a80d5107810030b03e801450075200b80c20481c103002d03010050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 1185394 1250 1184144 1184149
    0x20c030c120703030503090304050303040603141e0118020702030706031b020a030e01050703020a0506070e0114030c0405040518060405160b12010501050a090305010501030c030501060b0403030509060702040b0d0c0611010b 97
    0x61100b03c0790142040e550b0380d00c56400c4941140701c1c0d07400054241c4000100064419455402460120502d00e81c1c1b5040d6100c5900e0813155802d258549d191020801c0700500c680814800c0c2c204102d80c202000614101c85903001c00e0a011090348401c0120f69070b000d40d11407240c01000016481c83d5144007900c04050169000350010b2640c400103810000c002ca14282018000c00119100b180c0001c1110380c5440c0165000304078125028a076400541c40c0c111010345c0c06029170549001d110400e20582c1000c0c2010280802864001d00f04d4005055940c00c4925441003849002d020310b0013940640700d1400d481c0030b040c43e404a00c6e84081d40300302e02001504c2c00e50280b500128107490092034803540e982c0035020b007101d170a902608058595441d0000001c00c000c4035501d00310403a8411030003840002d588865001e040c0c0521310014003c510704010b69500b0f4034107040100103461006000003903210441010840d041d15101085894040340d038424003805420400342d503810841d140c003c1c0442d2048001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 1186644 1250 1185394 1185403
    0xa080d050c0408100b010e18010e04030c0b0106080f1005090712060b0a030203060a0602030301081002090d0b010b0702030606040c02030a0302130e070203040303030501060203070308060609040e0607020c030c12 92
    0x892106a490010814250301842254000c0500a08035901001040000b07401442d80845c07190104a1178201400c060401d1000040e030040c09a2188081e07070f00c0d061402281a1b4010001c408105a4001322000981c12030710886c060603043e90790f52010b140034030501e0609040640400304228952804112696441ca01c007580401d5070701c1c00c0001512414112400341403150000c813101301010420241c0b00da0701d5805140b0495088803aaa5056601c5000b070362684400e026208498203c0079000810200e1900108004440074111104d4881b20f80c5030020344684c01e03040840c407004001114400d40c50100710590300840115070402c5180c4c5c403594069541c1c41118420000c0c19008660b81c0e04a040c110340180c000d100402203042503183c4024000d480e076116010031070210b85000300209801d480041a1198650305407a00c50b4607803102c10401106422100c40356910a4035035581002e059414002c1c079000d8903554000b0070680c3c064004041c108a082001b049c06a03561a800a41640d00041c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 1187894 1250 1186644 1186657
    0x110301030b07050703020c0306010801140604090305030105010f090503120a0305060f01090504090c0503010c02070303020601090203010b04090b03030d060b04090c03020913020c07030b04050d031a1003020c0102090a0905011401020a08 102
    0x43c840d40d10200c03450f0590502040003000b55142c0140d01c0002002e042c190881e417501d00c0e01c60003120301540c40804000c225154044c0180004105000500180d4040d00c80c0340365010300c2d82001c15900d565000080d180c1401c09111801c625000b10705803030542e400d40180364000b40101e0f003540707003040304d080002c110340c07140c0c03103418469903d819a58003800211941140640304c00b40080c4040003550300065610401071200310300500c40c0300e00000344400d0900c2034034140d802c5003952a1400349000c96881c05401c80021403645408200558001c0072480d02c204001411080711300780c0c65600d0a1400740c00c41e0103034070b03602e400c1c1401000b1584140c1c0da064440360290710000d60040c0ca40401c282c105152681c50380000703010341c28040038402032140c00558403540e6002a50140144200b8620b14600c2030b41d82c030103103600003c140c0c003e07464160003500903201464521000500348521440022840b11507503010112a9079100010302106a41c00d460003006502800200305000455803041502e120f080d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 1189144 1250 1187894 1187897
    0x30a02090402040c0306080f01020c0607020607020d05030709150305011a090310020310050603040809030607030b01020c01080a1116020a060801031707020105040302060703020d090501080126010605040204060503010306110301030b07 102
    0x18403070b01061314043c1c0d010101805071030003110219221118041e000390321000003048903105850010b02d40354030001c0d4075442220300d6030150240c154621002d8a464201038220700910070f0303005010899082c040401c6456990303d0f0380101d0319501d058015180040060b003c10416038041111140d00e44002801030709000661100507a00d076982c1c00c0602070740e5401d1f080203920000020501042c070842c440030b001d00c81c10880580c0c03000d0321842801c1c0c0c1240d082818460150704a1110107440c1d41c007134090241d0000e50080041381090162441ca8413641c4801d1a90305c0d41440d0944030000e50401040c224080c0a49042c036000d6035040d41c0710990b002c0d0790701201c50a0418002001c10440e48034105450045d94081d14064449440b858065190030f020400c21002480c000d41c001420f40c4a203026904941c80c1102c0b4070300710580d805403044c042112005241c0b441d900c440d8000b400d500c1c0c6100030001865607561b0240c89504519200c81a110041540800890140014004200003081e100c0c0c2001c0380303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 1190394 1250 1189144 1189151
    0x602030a0906120b06120a0608010606120c0905031f05010b03060306061011070603020306040e06040803060d0201031104030f0b0106020102030403020c01050723010501081207080d0b030307060c031406030a0209040204 95
    0x10880c0f03000609402c0440a410038070106034039000c69110b10b1001e0042e40301d450244022503c80700b02508071103051040300000b540c13040e0100800c154903882040c01800c1480c01181880c3c48002003480c2100307031504451540d401e02440103200c1010b2088601514400c039076280385092000c00030707a0380c00002d82998822140c040000da44140181804015115030b2002ea40906560305005402908103c2e6120700940c203008500b0f070b03a5580468201c3c401c80d80002002d0a40c0c4401c01130080c821040741d403c9042c150348036210944c020245000d00700851040c0440780c6514550714010301008410b85c04441568010b105010000e60040b0302c004804400f880c00355211030160624400607010b8420484103010400c00344141e207141900024142d54030300701201d1144035007214904092041000182c40c200060101c0118035415800c0420300304002000c490401e03130310342c07107510440d0302c81c1c1c0322000880e60300ca546580a80034002c0165000e03008074047c0c00c1f00d181d942c0100343c408400420091080740d5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 1191644 1250 1190394 1190417
    0x606060c030c01050c0304020406050f090c09040b120a03030e060405030f0d060504020c07090605010203040501080f0603010e0f010209030606010c0b070305060109080a0503070209010e0c04030b0a0207140a020108010602030a0906 100
    0x604205598403105003800a2121703041903901102c1030b900c02d507016030290741005404103c038100881100200400508440159a6841c1c01e2000c590041b07003115902170303128000d03e1059903039690203448510045000d88681d800a1601800b21000620b0854542d04400c2c108030100e1400b000342c031500074243c15483e9647cac080c00c900340020196600050740c06440803c00003044400042e5120944090b901c0400c03a06032184016031742c0f4000c0d841213034001514440043c0c0150210300c1c1d99900900c0150003c41c410b0031280c82241000201800740c14a6075000ca58580d16140810880e5040f070f501f0700f48212988c006071109442000300804100031f01d83c03100003040041c2d200f03102e020020f00c0d0314003d42daa4a0b0f01450700f2601c0307510802c1c051303200d0260500003042c500950319080b03005003483c0741410304d401c5c036540d07480301c01d50b00040030004516400e22030240840c0d8207509401d402c1c1e031aa0080c00000d6081d100152074040103070004000c41d8810300c000030005170016404400c4d5020b504006071001d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 1192894 1250 1191644 1191667
    0x903030403020d0305030403030f0e1002090a030b18070504050105101107080d020304090b06040501051c020403060f02030106020105090105070905010c020f06070b06030d0302070c1a07060608060601030b04020408060606 96
    0x440c40d03000a40080c1255020300c20b0552140145005034032a642c24424107200129080a899084590380542d8014803140e850503480da03801030030011800342c15000c43c20341e00e4540c5c90507604112000c0c001e60303d00024040b80100d003885804050131007142d041080d941040d01146407103200048403402d003c0300b080140d5a000007001810700500d071000444a101200c100000c0d01c1c1d400510403240c0d2241010500002da18100e42654151001a0340d22400d10084a20000c0d0035407802d031040c01119405c001c0407020803d180202e0342000c607404401b43e075a5160000c001d003100da00a00d0041564908828400065403040340c20341280c101f40b9280304050403034000611480040540d9540c80b01000861404000950320040d01ca2441202034452901c400081601684107801000341a8009114188085ca17101418a0300ca6070301d60b0500d40c2400090364034031044641c2500030007204d902c07240c1006455a494081c0b60484501070390103508103031030100100d40e0fa400c0a03050078810403000c1244040710 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 1194144 1250 1192894 1192897
    0xc0801050f01031401021b1606030504020d02090408040e010b09010905010206130602030901020409020304050a051204030f03050a0c0501020705070806010f0f03060b0d021003090201020c0d050606090402060d0c05030a051501080705090303 104
    0x3c7d031001c00758001e00c90141c821503484007616100d202680d03002c940094507034080e1240e43d105035000713030589901101c19402c02040d68001841224281000c1c00046800820101c5103400307040a405c0d02035441325100c001403c2002c180d44214110350180e02040510b42071400002a601d074449000342c0c5035110400c5c101e003e406641c100800c0188044100014071000044004000703000300c068034040e0080c9002e0303143c40d100d9400042c2c5032408001c020313000031b40700c2c400504000d0704600d881c4070480300c0359541a0999011340f02c180d80c1c690240209115001303080c41800d0040516020700ea40c400d11b05040090301da2603d02c400b402031a07a4002c03109603a100c042d03030901d031b00e41d0040c800880d501d007410b0301800412400d041603005100381da00012260402d600640206504140140318668407030b010060502c3c0c00400c22a00600b00340107807140d40295000c0c510b40010562216502da02c0c01b0701d03000c01142e1000340711030307812035081000d403606980100d110783e0040b0040c82c00c5941c1f400741e20301003440c6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 1195394 1250 1194144 1194157
    0x30307020f04110d23070f050304030c02090108060702010f0c0e0103050c09040501120308010503030a050d0902010e0303030901020a0e0402040e0f04060e03030a020c0f07030209070c02030f010609090c0801050f0103140102 97
    0x2d40708001070406071030b00117078040120440404240444904002c80c031418902040307890300040b40c0341202d42d1040034012800b85501030311a15002104802940c00300c0c0b51040207a20a1b8106c1c3d01910500c4541c580a0068a42c0b500160000700104515040c00401000f400010903050507551004121004290350440e14000b0001c0c000b44402c0d41c0d00d410302141084180c000307a0000d1506000070035107181c08401c45102e89031540da0305061003110b81c0182c2c02400c102e0400c0341480002c01d51301006480903c051031141c02c1981c00141c6a041402c07003e4006209030900d641304074410003090141e15070000e00180c02000d4038402110070740c0c942c43c1060081400d0003220a00d44008420003080980540003800c081c15100b0544040000502002d940c440c0d140c00000d501044000c000f0b40c1d001d1180890394030180c001000c03541070f00700e050071480c212915508801000f903211102c64040c400b08400845c018840341000700308504c3c1090032030342c0907401800010200d4a251001d03014001094042d01d20 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 1196644 1250 1195394 1195421
    0x1050c0f0a0c0303021b010801030204050901140906011401050903070b0306011202040905071209020f0105090d020d060615050406050315060d02030f060405090106030506010302280803030601021506030307020f04 93
    0x11008071402c101e0944a00c0b0b2000318014411511031403015244441030800d42101038440582c40d908660800c80a004010000000e0b0340da038008240440d994034504600958134203000d030409504180c0741d09038a641d03a400e4107051020401c409085902c000079030001b21200304492903142d841703010040b240010340800380c1000e2800410301081f8102a80c1c8032601501407a202d084240608618540940e00030100203540520f030648600129406007005003034461004018014501040d4000344408803c1041501d00b983e4035101440f00020064102c11103112904103542003910b004001071a83c800242910882c0348107600c500380781d44464003600c17003285880c0015901c82c60300c0300c80001121801c4074140d20450400700030035000341042c80750801b543e03041000b5040030303801d5409002214000342c8141c8004a00b51100040c03607020128590301405440e00603550300e0600750f00092905c3c986000a40000000100b804401e5400004071400ca541c15101026094040c0d00098001c0c60f142c644e000c0e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 1197894 1250 1196644 1196653
    0x3060308030a1a01030b100804020f0618090601080c0316090f030308090c01090b04030201050f090402040303090905060102030307170403020f030409020406020106140a06080a090203010207030c021215010501050c0f 94
    0x3000000303421004990208100000307001c1603800044091b41c4007059025004242403e2156019204aa4450707101b80003408007244032044501041a95000307210726540820f5801c0b44007080d192281651b500018246054003c90401844103030040c840546042190395400e840700b00098042c03480240203084505025900940c0d908029100707000440e401c10450003504280500c4ad0b00030032808044e280380c01c4809050504581c010f417542d91000000e185404800d02125000386c2d2240010302c0174521a5465408191030800703107105883c0050310b480d0554005100300040c00368401d507c500c4149003d00c0090242d21a410241d0400310315001c104680c1c00300183c00b040114a640042c0200d13140b40e030003007140c150f0f1800c01200321442c80e60002e42c0000034450402c022071044102035003140980c40000b4150419034000703400c9a0180001300e01207844841044154a042c44401000620f45400782c41c5640c18002031804c43c05050003014180b00010607803120a500802040700e9203044c410803174 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 1199144 1250 1197894 1197901
    0x3080f0304030e0102070b0414010306030c0b0c0d050304020f0409150c0e0a050405040b06010c170705010f0609020703080402011101090b090303010e010609060806010f0309050a0b040203060106020a080d09030306030803 96
    0x251025441100c0a4000c07840b903400e03d880551000404808a58805003e03604117070a005030445001c081c00206810903480300c402002040c4010645801024121a507950342d84185450382d080001c42c0c030001c0c003441003c1c0300704405601c0b80000c035001900700300d4001a00034540c3c649014401c0d24021400f600380d184c03d003c18405500041c40212241040b03c18810481e40e900410003901d4007218003e000c4a09c0e030f4049611035008141440d01c5511503004c601540c1555143d00e00d2a8101001c00d46042e915003101c01d008894034495440504032600c0290314060280d140942400d0003e800207040000700840c2c40f00a02081d4401540950310400c040c400b8200541d1240d501c0c0c000f80034031400c410829000043d030310f0003585800100c0c6d0071038440c2d160998a02005640b5000d00308600402e15403a000c2e28000100305001c40d841c0310348030300d03207890300c605041c01030501c0e10405170441000e540c440140e14011035a80000e5404084101c0000700700c40455240c1140036200c3c6601c0100103031800b0090 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 1200394 1250 1199144 1199167
    0x30603140703030201050105040905031b0a15020406030b0f0d03081b04030c080c03070503070b03060307030606060518040605030307020f0301020c01020708030f0601080705030106030207030e06030106030b0a1a1b070308 96
    0x41d1811039010341e0003400184d88a80421003201e80ca103000501542c000c01c2101401041015808803104a65080d1100151203440300381400588000d03442c036280e80000e0501000e40c00d0700c13032001a2801a1800c14000c0740071004940b0100b50420094240b01c0031000250b59900c040c1845040043c421002c2c0e512143e50303140c001d0910050b4001c0d03c2c418082c17498001c3e054240040e16404a8070300a000740312843c900542ca0069a00103032403541c05008100011003c19100d0007000020502c5681d055601c42220351503494203005d085010b4402d40c1401010485c6582c008260751019070101c5405030301135000c0000900900c01d500c090340255002103038400900088801561040320310502149181c0d40b850011144528110761960200b003080c801804168403a070f014000d01071090410f824200d02600009201e034209a0107e80000d03102c0040520303030b00b8502545001001e070440c030018185001c421000e03182c059840100d51040100c144044012000c01c5000d004542060746141d0b2004c11483d0f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 1201644 1250 1200394 1200403
    0xa0302040216030210090804030b04050a020301060f1d160509010c0b070306060809060405060c03040305070606030803010801060f05030304060e0102070f030b01050a0e0613020306030f030d020c011b0905040c03060314 95
    0x1800c3c0c016029013450403a202c1214014001900d9025642c1c5150038203554030128035010152055a683c800c201c26000182c609100d03c070007521107150901455481d0010004000d50480601c101a40c807c0c01481801010889010204502d40c188280c450a2013401243d0b058412800a00a00443c00910544a415074041007e94900d0795401a556491456055960720141c40052540d84000b001030f0560369044055078100f8440c0c905146083d0440d11044241d48080d001500c0385040000100420b0300300340b003103000030311490780640c0b00342c1e103880c0000b43c49010302d1040c001400040d85c07150b80168402c4c0114000303060001c4d07901e0031030340e00c0e4100300100039424000d0502a00c24100c0108000d036180c1b070440d10841004044180700007802c4e60841c0650000381c40c064041c428114241074a440c280081c0c51410722a89005840d6a4141c2c031136030940703440c0c0d1100b92034149024a451a03140e4080310340e1055510948020402c4420700c03d04400920345940003900e00502510b0b004140d090115 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 1202894 1250 1201644 1201687
    0x100507020a1d07020304030305040303080402040e011a1c02010903110406150302070302010c050403120c0809040207050c0405060405010e040f03090b0409020703080601020304050f040b0a05120a050106080a031d0a03020402 97
    0x1d0302d1504a035281c81e0141da8a1180c2c0c04091701150341400200006481071201551052001c0e0000c0360b401c030711500817400d40d0140c8014002403010001504003c0c01c3c0134202529211400e408644d840c01e4a4002801d0040c0c2030102602d40d200d03494419615403a142c000074010065004030440a06c13903048018001c0d046058110300550a199042110318850419542580c0d00004410020000b401007503d82000c0d021049070090001e01000c500e50361188082c22000707004e440500f1034030246004000c110340c00104214840c9140070014840c010041c800103500c154494130b044006016070a0645400c419030740121820a00002d0200341e15005030050b00040f4800d80780c038081502c1e02401a03840f40130b00c1c041c0c603820110034160260940787c5031304000e2100c1d101030101030403d03403034030040ac01030001071101410652101c454078081103005d114140040071008083c11140186070790051851611043d2010345400086420038142e540054890003580d004004540d200640e0031814410007201 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 1204144 1250 1202894 1202939
    0xc06010806010b07031e0908100603020405010503060103030c0b07050405030106030809030114010b030a0b04020d05070c0c08030a02030703081e0108060115020a0f0204020309070905010b030a0c0518100507020a 92
    0x101c0006400d111010550303c55682c10344030b001200303002100c800b0300e880280c207010042000300c01000844001c14400000111075a01c004a0032500f917005120076224180d110038043e504c04801000440d510140798041c496115a088a803034840c0d031000c88071402a5003100c1d6165107000d01c0042006158401049500c105034000e0110405901c240480c0640902c980d40f05140d0400c001031120b00c040e84800590000100014240a102051300088840850f406404681c500c0507007010b0021b003982c020001d040440042d49407012070300c0c1c004c2d26805499001000c2c4245200400c3d80c0c64240501428500605050810150794812420365100c4081c411010a0991a115a0400351003c11003a0080e600166002d40700c10813542400029840100005260301401c003001ca1109010301403140206a04040b103500c0c1d0174903424010032501d0a810402c14032804100e40e03604011030300740389903890700220350403c3e505550410039a181e00c1201b80007540541406804101c403041c5203000802016031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 1205394 1250 1204144 1204153
    0x20406050d0c051317030f030a0614030712020108040204110a1706010f170405010612050d02011406090609060a080a0305070b1005060708030901020d06060e030d0e0a05040e0c060c060108 82
    0x2020001e43d0030b80f003044405245400b9011040c0044d02c0302d6a0b07501d003103420700b4007100d2510340d03011106603072500300f03694801540343c8410080009890b1000c0f00e101c910006c8015005413894051035080c0c1c00d03a0740380f0090500c078019000409559807544400c2000c049007554540d90303030414200502c1d501040500001044c070410100b0b51075445540030800d002c0761a00c3d0003d000c0c0c41401d0100800c41c000b042140d05640b12200032900e440b010300740c011064407035801006890505040a42502e000d070320403854294480c010448140d4543d030360f8641086080c1c81d1810591214804207860301d0301d0f500700b10400c0c803070398071500101a8003034018212140110480d81075a15134450800d05100d1910426501c0042031200e6804100740100642e00702d002000014540321000741400b00340d54840d440741300414448060440e0900b02030002c81c14002140c41c0040000386010300003042d040b414014540150303036840c501c4444010800c10400940320081100e6122008200c9040d907403802401a00042d005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 1206644 1250 1205394 1205411
    0x60306050405010504021509100302070507051009060306080d0804030c03030902060f07020f0307050603040206030a0915050103050d02070b0409020d090204180c14030307020907020307060603050304050109170304050105070c0801020406050d 105
    0x7d4400c152600207400070100804d4501604c42103000e500b107035000313558501130b6880003d01d075503e0301000c101313111198484444480ca032440c0a022111151300c9007059811803400d20142ca1750104503542c0c840d81c1350910070130300302203030804400a00109000a4203d44001800000a584c0b0b901070210b403031003201d500860b020f15000741078031a11a841980c1c0c21501c140045001803074004043c0da0312603004c100015101e29a40c0b252030808411210280310560340e100103005000c02441075038005003e9000424480c1e2401820003458816031103503009241d4041030502450741160060800b580c0c000744140001550007400c00d80c00d040c80c21040366202101000000d1303010f0a40c50851801d50010051030502030b041c1c0900141d4000240701c0801c5000c1004420f0001d2a07e219441c045e60081004644490a240c0090311314011900325420b0709060824000300c41500004640a0710300c00c1c0b80c101d48074a040e251501c00b200d001c2c0c02006d00c5500104010441c141d101015017411504c2d078406001010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 1207894 1250 1206644 1206679
    0x9020c0705030a152406030c030b09100b0c031e040504050615030105060708040806040606030201080c04050607061a060705010203070207120203030d0b0310240e070909050402010306030605040501050402 89
    0x460000c02054500c400c068244203540310b03031203032180c40c40401011001c005c0b0503401100800043e000030000c030390750382c2140261942c513202c1c08640c14029103001c0c0450618002550111603644548030000d100020030100158082c016500c2c04c000d0442a044c0e03a403070b1100042c861740c0140c0265400781d8a0200040d180d4030303040020316100200300728642e1441e402d0a00b80071044d400404140c4600b1820400003440b2942045514400d9005030400202c490442c030004007030050240103402501c0c0140400e0282c2e40e580320413113065942c0000d000030250185065410a9074101c40c546502c141c004c10404140503043d0000d5115416a03820f40c0c2000e0b4582028420301e2800c80743c082e400da8400c2c044091202c1c0075501070802044000d00700c03180342d04800868000e40b00755015140020144d0441c000e0020b1040400070090003022003002824500410001c0510101d4810703407207540d031100c000c241503900a0344840c010f1508540d090140f850207003031543c041c00f01038400f2405161500450041301 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 1209144 1250 1207894 1207903
    0x4050906060904030c02030a0c0605190801061b0507030506040803010612050c0904020703031e090204140717070c05030406080f13020109050d020109050a0609050907020c0a060c03020102120109020c070503 90
    0x5480080459180ea180d82d1030840d01c2c4c80c0c2c1741c0b00480e01f5100b0184030382c0c085001001100001e0803260b4450740d8408070702c0d60060b01c42d242d8035044c509102420006001540d04075950f02c500d101e02403404a504001c504009180c04c04a51004e006030140c80144400d02280c0070055043e52003d442e0107000d810761102c1841201c00450b80400340c0d45050203005642e150640080c500b05019180100302881c0408052802581c804408003400c0d81e80c110080450800d4010688150743d400045805031400000280c12060202c2c68030210203000c0001030a8240120b6282111a030051700701c1e611992a840013801c00e803804c0d100c040c7c3d14114200010b1040b00b990300c20072480d0b0740c1a5260145240ba00c000e0151a6124002c120f0602524040100d25616224284002094159103a01c0030500d0304080c001d1009001d008402103400c0409540310903107441c0500c034200d403440d14043c0c410100c1410201c0c02405021403915030412400e00008038400c954014000d040440700a403442c807680d900c1055a079 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 1210394 1250 1209144 1209151
    0x3020102030405091f0f0906090207080403060c020a050d080105010801080c030706081503030c060a05010e01030503090f01050d0c0801060f02030703090b0d020903030a0518060703050d0c03020409060305070504050906 95
    0x5a00c10842400f4a04107090042e0300081e054590600c0c440303940100c40b000007040d800185403030380d0743d200800200003070f40207a0740100341c0d001046190800c143c860288500c140c1c000504090784900e140303507005100300014a501ca41001c141c4601da586c0c5003004042c244288246c900140d42e500c0040741400c0041139035400400c0003401403901c1c3e442e2820548050310000c00185003690401d85080c020307242480203040b0200342e10050b15140ca0801020b004485042e0400a14011510014070004200104541050500300e0340340400420b0315004885a1082115004540d810320040014064101141c00d058546a446544070420942c2e802c0341d5a000e4a000600003410542c010000b41c03034014001d00c45040c03411070141c41c1590100110786903501c8594190005200000c14030144800c4040244050004454052500500e614024080d02910080c040c50a07514040701d81d007280613904540c0240105001071010741e50703d0a00c607844810701e204442c000c44c14003000a803400c4e00804d52520 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 1211644 1250 1210394 1210397
    0x102030904090201020f070303030e010606110a060207020415030b040b0109110a080402060d1b02010b010306060e060a09050306090307020102010e06060108010303050c030f032401030902061804090c0803090901060801030201 98
    0x1018002800c02002d080460390030707415030003840e00254207130a040c419000a14041e4a0108680490016841c2110280c4c0d0101c2d04020480d40281140c00020604450719900b143c00507880318030038000100240840c0b030300480c2040a28100004100c002201107100710f0140c0400072013a079941e100c40e0305a5502d03030201800d8000c20001004164003400c103250b00300780060710786170410a54100040489984d032040c0700d034003607500e0f41150655a09000342c40b100403082c40c0a201072031405401410140c050000507204010100d0b002c241c15104281460040078003d003212103601b41500178640ba90b00c104010b0380154202070350301489920004450b4000d0301c042e900c0c4130b03140c0e20b1903d0486181c1c015101003085800100001c1600c0304c0030300040c500520910b00040c0340310890400c034103140c0311150300441c141410605024090b07912102174a01d01e03228138403052580f18841c00060b000b8601f0720b00081a844109201092a010001c041c010803c0241c0300c0510603601c43c4400d41c3c410301d091200a0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 1212894 1250 1211644 1211647
    0x402010509060a020102040b03090303040210090503030703030b040e0115090f020f04030f020102030d020c060708060904050c040507030b0402070c0e01081504030c03030608190501050711030708070305040506030a020304020906060405010203 105
    0x680310300300308000700b0b0321078004d100050520b6101d02110445a0041e02e007a04154408000e100540c80c0c54840b40401e03810034103184800c0e42c50700c2e010076220f0161311405001e05a80b028003039000d840da80c012002c1000100c0007004000400034147c0040f00c441d0040c000f80d40c0c50810792041c0b1180340d04c201c41404000394409414545140d55051000b5281103040381140070500a500707020182e80007404000b0700c00c80c064a1a4901140000c1c0356200041c60203100d004600c007408081000842e00c91884001500c0c0071030b441d5a461402d030080c04090340469081440003a107a814451038080320030940e00c41c503105030216640c40c0c42503655061085241201f5a00d04008540041d000382942c0090354402d040c04100e5543d00c0c0100760600d1800885802c15a20713000c0d042080110078491123030303ca2003508181c0c8548202940d00d80d0ba0b0301550000401c031070b000203040c03024140210207503002854014001070350b0380b03000005031000e90000d88040b030159608402146072403a000054406440041c3d00a5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 1214144 1250 1212894 1212907
    0x409020307020a080f0408060f0f040204050402010509031002040e0a09020105030a18060203040501020a030507020607090611010609060618060509060d0f0603060e0c030f010504020a060503090304080303010609080f0604020105 99
    0x4000960010703000c0d00541c401c2c01c288070700189895003d0008140c03050360a80c2c030b440c034021400d403d04500410201c01c288094041207203229580d40c500ea0010b07010341c0c00003031075070380c074401601c3e03510880c1c451035498454051031105400c0fa5400a0041c0ca92541010358903171201480082601e01d1501d0082c045401440000c0516610343d111a002148141c04480314820719110390b0120f0307106035810303209a500018401e201070340502445d034201c0814401000c0e01e18004000401810890144034104003c040d241c0100d00070035008000074003100d50381001080d070380b624090444814051034485140411100180442c010310075921440000b038084e500d428071005410300140111024904419654540880030a1041c4540026100c404004207a40c0130050109484c104007030494542c940e040c079040200580720030541204991482c2007458803a142e825030701e42103008070b400c10f9a2501c004400062403c1e40318206504583c0b480041e19401d00304000407584444084801074040340301040803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 1215394 1250 1214144 1214159
    0x60705030c04050a090501080610050a060c0303020c06090a0210090612020304020105070507090c090b041a09030304090c020601030201080108030c07030311070f03060603060507020303040b070c110904060c08010b04030804 97
    0x15a400001c918115240c00d03116000101c04c9051500800d42d40f40d90b0700c0041c003640508000d00c0f038200e801001c40c00c1e0303018545030000304540d095000f007104000d5291840300c20103000740c05607440c9282190640c2c2c281d10b000303240241d4406070103030180d104c1d072010081401e0141c0105222020f88140340d5030801604524480b400203907001401c200d040040401040000c540107020031000760204000104071040000001044a92140c0101c0001a001c00007000002c0d00310355514160941c0d01d482d90788807085840004e086001d650700c60352504d4102600d0a003280d81c0412214140c0b0700c01d80341c100c1141d81301c7d0703881e56503401001a0360909a01c4154180b000c24002d13034a21565401050440d03518588032111a27440c020030380e1048401c00e40301c050610400450340501d5902501910055095290588503c5112180542102c050000005c50351003441002c1c116a0107009024001034160705283c5801c40040400300c1c14080020070307036000030400e400980f04460407a500a07030890f003054145003a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 1216644 1250 1215394 1215397
    0x60309061f080105040308010602070b090f04050406020c0304030b0105011e020c12120d020c07090209010c0b04022b020109090b030304061404050d0c080c030c01050301031202070810060501110303060102060705 92
    0x10301c00180c2500c40400540050b003401074600c0f8500c41c0d500d5031b0303803549441400317450080141c1048800030030600c032100080c0c440c29503d010740d1070304031808105502c45080440c0203101b0100c0c52001c5000c00a400720900c440001e1480c12601c0c203a940c141070552303a00c816900c80045401020058000e031080504603d0310720304a1603608201c8094900d0340040740c11000741d9078060102240750a4010a401801c6a400d11400d4001e2000c500e00f0b42c5000d5414000804007601d05600524003d802c002181c10f40d01c1c0c4404860342c4481d030442440d002650388041d0140d40848603c103d0026068004c00b0030a01d005010f0204914800b4000310700703250070090180c581e1040c1000c5c004665105000014066481100d60702d41c0c0d074080c028103003040c4c3c109003a2901f040c1c594104a4040e5102240c6060540d90200c2241d04481e000101c210604401303090032400d104c080e6010381810310408044c500d442d0fa06600c410103c4009032914005a0a032031545c903100c0c003040b50442c2c0983c0090002682c207a00800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 1217894 1250 1216644 1216681
    0x4030302070203100e0109021306030b06100203040306020f1c0c0206060d030201020c0a03050403150b06040302010e040e0703030806040c020105060303070206030403020a050304060507060506010c050c040209010309080403080702040b06030906 106
    0x1d043e901019030a0203140221250824030170303c81d80d1079a90301000e504015650700c4188140840c240044e40c1503488018a80c00b018044a004000e06c0024914492007841903401455000c00255501e1224440d41d0303800b50007108900380120841c031294080126a84542c201001c203540180c2030a5403104100b141485415400b075095540803c01325160b40414004010072501ca0b40f00d0740c2e1954154100b4030b00340b0f000e9000e40faa81a2801078400f48503075500c0c0984085a03424609040c140040c2e5000c50041c1030098946411441498030120425401001c400d100f8003044d1020808814030600803402d8481c15104150540c00401a40c005824030310011644180a40101c4c0d103000c80c983e903140e24641c0300c2c4d480280007410109410b010071495000c1c10360002d10910700078000c10b905842e0103840b0707051600240d00c110b600007090110340c1d0083d00701a4415400100711038981c2d50781e00b000c1405074400c4000724802e03441c06046180354942102072300d0080b150398004003810742c0c80e503003100071945594 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 1219144 1250 1217894 1217899
    0xf020c120f0903060109050a1d06011202040905010515030c04110403060b04020909040f02090708090606010c17070302030408060a0504081b030d02070303020d050105010906050d0510170d0e06070803040303020702 93
    0x80280b2520780d2000c110702802003515000000da6413030125154800c4910340c49044001c00e9103048c190300700c0e240014115040d126208405410b44000e440040e001b03003e8518010803550826003041103e0f8120029444044400da0540f40403801410406c02103070f0031103101c0c26111106000034008511a43d00c600c6540b240507100514201003540090001c1e41c08580172900304039407407400811820110303c1306401c42980d04004240f420010401d94440500411050412100180042c1130110011480c10b62620b00c460603603030f0318054140203480381d1040c015507020b48244004600440c1d150b1103001d10580e0465034140c02c0800d010f2425412900d0381010b24200c2c0310030300c0601c0c4400c1e6244018424180710b0b450040e0354a01c0c4015002c1910070590040307040c001e40110402c1069081401c50b0391907500030400040699074104c00c800c02e90841d410041c030440e14120540810b400000340c2d40102c206a445840c4502501f01c10856584955040240042c1042c000300300005d000750090104103100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 1220394 1250 1219144 1219147
    0x3011a0706090c0305030703091a03010512100c180b030f0601120e010203010906030209060103050105010203030a02070201020a050304060302070c0803030103020a03030f0e15030601030606020a0b061504030f0302010209040f020c120f 102
    0x2507403100600c83e030701504180c03455000015a10b04164001e10a00010700c50040c0304035103030319404511041404144101030048001c5d00690180120611948051101121080100c1000d00388001e00741510728414610b40149001e0109515004100342c81c031881c0c4400000c2001d641c1d000044458072a48101c07041c03000d03110b403035441d0903403001e00196000e41100300c40001e08500c0d500401002800240c026414107140500601003664080100c0f81d01c032454400242c2c0d14034880c0300403031402101480162482c0400320740811095416002019103d01405000000c03907242d05079691207101c00e10bc000d620011000341000028003800c1603812440036424034400b14080b000204c1c0c0720141c1810721940c050000410088250313050720444002c1d000910081000c8250352b6204008240081e00481c03140c5075000c21895110f1100b000c442c05103034052900b106466080c43e010f4040e401011810b0702ca40d0808482050f40c1409200b81ea480506400080c40710354911030b0000195406050105044d80c0c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 1221644 1250 1220394 1220411
    0x14040306050f04020f0103050403020a020f0303040308030f040203250513020408010c020d021006030804030209060a050d050106080d050703021b0307080102070302060907060306050a0303110c042a0503011a0706 92
    0x100e00c6098030030030101d4545811880d291041001001c0c1c55203c3c03505161501d02400046035000508030711280d070548503093b020781100002031850140f644000d111010001c2000304d9947c661050b140150701c260219038000304802c0700700c1c1c0e50a50801ea0a4241441840100141e02d46410010500034042c1401441c16071211540307401e40b00d00490100c05030b40008801040a41c3c10050011401e00803801003010754210b0703981030214880c0740300c040d01c2582031074007042c5503172b6544d61003600514000341503403200c44c024984540a0030440c40b8011040c0142002805414090800c9501c40744c0d05902403d030a00744d44011410341c2d403051210719010b128500020440b84001d100502e0010302940040040c0e00d4541c1c5c4041c5403500c1034110204141c10b00c0c1d000c20141c2ca0310b551407429657a140c1003410f40d11300400c541600c1c0c00d418610300e80e071003400c249810400002410085000314001051081c00510392803082c1e85601c000e1042201d034822101d00110003d1400c0003812265210785000701d550309 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 1222894 1250 1221644 1221653
    0x70609020a12030801090506060406030b03030c0601060804050f01020708030c070507030506130b01080a210e0402040306050105100806010e101103040605040810060b0a0516050f010509010c03050115140403 90
    0x400758011000d8024440c46080c02d2542110383c1c0d0f40145843d02043c80940f5102c004a20349010794130800d01030503210b01005655540900aa9854504120450b1242e694803d4014803962094a099905008000d015007035240f060080303951280ccc10100441c5180c60383c0040130095031001c00c0540b103034044e80c032003c8005001880311038083e11a0311a070003294115401c0c0f4505624060f4040401940880c20050014841c1c54640d011141c40720f20710440c48005007000d41e202a081d00481c2e80c0b02e880041e0100030004158042030507940159420710b4920b002500503181c0c0f190545040c0e01003881000031494915001908841c010320030f2030301c000b640f8241c1c10000c0c555045500f00c0000703d00003041c103110380d810810861101c40404072060000c43e10300324000070709200c0d107450354040080000c2d0240710800005a50a81c1c039a001040341c409519051a2500a10081e0fa208401e035081504840040703129001c2c480c103942d0344a201442c140b150080540e144600c020100d64203080034040000800c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 1224144 1250 1222894 1222909
    0x7050c0307080105060a050109030b011203050c0601090c09060203280203070209040f020102190f060209040608031201090605010509130c030b0306010e01080d030c0203090108060f0d0503090406050409050d0507060902 95
    0x7802c020002280c40d0030040f04000080403a60403050400010440c1000404c4480c2006411100420b0303400c109050281800c9070f0502ca00382203550240320b50b000024903001c00350700c4610102c0290f90348104280e10341c0000c0740c17a40728100003040301014480c0d1190010001a80d5206017007581d004072482d141d543ea01051b03a40d2800c50b4280c40310b00d004201e07501596014810604144500001800740f42d509a0b554000c04d80a03510140020f41d000c2441c5686448a5003d42d01030002002200d0f2114000240c4c00440c0c2002d0050003d120b04200c00040d141d4050420f889410000410800c0e0f03102c682071125006080803100341c000c06840702501c4a40d603d0500046000c2d001803800e1a14944c105000f440c40c0c00300355444c407030401d0310307050400a2256020040d510004000d190860894032580006048020b0343c0580550240151a80404003c2c002000304451107080c1c5007408095918401c1104990711030502401d00d422080a05841c18810741c001e00a01d071190000050351411500450100b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 1225394 1250 1224144 1224149
    0x1119060804060f02040803070b1302120d020c0102030301050102030403030315050904050307050c030a020109030201030e0715020c0f03010c0212130b160218010311010c05071505040f0603050105010903020607050c0307 95
    0x46100034040c0010301c0640c3c081c040314000d28160951a080c9481809070f507d10600030003034019106074010410500198240b0385080e50000d010780c0808000c010000d444d61580580d2002504c1019040c03c075550001c070030b5a04a820503005036080c24510349007540540218403540034801510940415907940f4080400c1c007482c040c05c015030b05c841302860150f191900c196440ca1290b8412102d000041c0ea00500c4c440030742e54281780100d140a000c03110300e80f9010315900803e41184101b40c81039101c81d8001609940c81204070ba29840c0e03840d0781d0701854200e07070505814a006800551000000c106000c0c0101a542818903035201c401d80d9603a1926525005207031440c8007030003d07001080561a1512101720120409503080b030643d4035580c0ca10210f499038070065810710100b10f030090f0501406000803402840d503103100c0c1180141c1d584000b070880d0b11600405607856408880420140d11911506041ea02c040c2c60300d03d1100d0840e000c220654203c0700d41240e2920507a481c04407d52024001e5400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 1226644 1250 1225394 1225397
    0x8010207060b03060108060c0405040e0109020405160f050c03030109050601020f030a0c020901051f03050702030705060f0601080907080304050105030402040b100f09050f01020a06020c03070b09060105010306090606050304111906 100
    0x280c1502c0786041505012040c0c6c044001e540c400070510440e0380d40e482c201c03411140c0c01c660001c2d9038040300340c01601400c0082030184d441460401085440310441c0b582111590580c0e4995990401101007510788e030003915036060b503d52051005014541c156405a41c001d181401240e00c40d10a0b0060549164092003a85002030341c40c4160000310308102a8003805400c0031500b540c400da04001c203d5042089941c0d80070101511040461100d07402401200e0656411400741d0f151403402e0007228040100a4460701c0c00510100c00042220070b01054010540d142d03a00558a030500d00700045443c1d800192003a42d1040c1e64883d002e4055640071150f40c0d10b142280c03a060b201c00802440034240c020103601840c02030303100e240f500d01c0320703030b40032820303280301c0f0f42c04100142c40b103207035405036481c5008080300201280e8507442401008500040d00340e0499a00740d070103205e41e1f85c5881d02001600c0d03c2c0d20030000840d0040c40440c00041e111012009003000140007906c0c00141041407a030701c00c489600440 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 1227894 1250 1226644 1226651
    0xc030706030c03050c030402100e19030501090c0506091c02060415030b030d030c0e0d0804030209010b030f1e040305030405010e0118031b0503091e040c0302030a05070201060302060d0e0102040801020706 89
    0x2c1e0940d003601545030b00c07070207010006055141607004903215a50410078841000110a02852a6900c00c201c240d040c0d13040c1440c8801141e123030301d070160080103912020390303018080c1e5400007018a000781c00c6440115000c0e03c0010b46074110200400380e50541d10040b64061418440402d10500d09610b02002c0d01030741e54045162610a0107050a0103070f21a422000c060800300f1211181d0f0700f0641c081540d072030a9030383c005240304500b0a04098025600001d5115001c58000102e40c80018007560165812103075210b9991078841207042070840d4006441c0c0a02415070014000c0790041c4040c581c0f10f40940000300709100001b580c2e90840781c58602d540e00b0102d0000b80c3d0380c14903902c2014103030901e10410041d480c61001d521426901e004014940c0d110300d04034200c004800e0300a5101e200e420001a00600070f4910714800503010f5002103502c1e689030303031410740000d00d0544140035460469802900c0c10385001d6038211640040c00c4407210511466408110000e0550400d1000f080351034080d00000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 1229144 1250 1227894 1227911
    0x3010213050405090a080318010e030c010501030309060801030b06040218030a0b1801060b030a0905070306020a0201020909060f0108060f010201090b090309030607020d020c0d030309020303070c050423040204090201020c03070603 100
    0x10080b41d030050040d0b15658800c034110070011b010304085a070012244682e0401d500d02114045025088a074110301003070001240c41c030102101500024144c0744240c845144690f2100c0e02103c5a03403003448054803002210000c5a501d09181d4001c1c030440c21200c1c50a485255408007103850310754000400c49152083c2010002c6078034040449140c103412204c003c0c810300307103020b508600318000646582e818030340d500050010080100036081c004c503484003040d074a400d500c8601034000c3d040040500e0107194000002105032500b030217a070005140584074210561500b00a108a001c2851041410341d0360f02c0358030f5000305120401e82449400814000c40c0e45201c3c1c1307014542014005070010003550301c13514101e107070150080341e509002c00c82600c4020a1300e126050450107004e91f264042c2d018003000882c401400050003a03082514020703517050211a0030a610f490440c16010200c12651080e000420010301d8150070003503004c1d005104841c5c280c140c00c0002030a02c00c90350302c101d021a9480020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 1230394 1250 1229144 1229149
    0x40e100506010201020901020303010905130b0403020c090601140a12021303050703060c08010e04030c02150a0c050f060606090d0807080a0809010f05010f030b040302150a02040503010b06030106090302060a0507020301021305 98
    0x2141d078046800c3c80294100040c40002035501e00040c09441c041685840006081118850404003210f800c001400c2190a040c2006929040c40382c40b02c9001d0421032000460650085208105000ba4203802d549810700c2410120341861502054560742ca4017040840300b281d00380a0410040c40c0100f005d49411031030352602030115a54a9101c60500c1013072001003080042e8002c2e0703580d00c66003500b421703030000c040c03440094000c04c10390686201d440b00c00b044140c1220ba10a1142c0c50031840b5200700c0700028101001503942d040101c648680c0306100700310b0582c0d44d0418000c02100790740300f261003d041054590f0b072260140c22a02c107940c00104080c081194004003401051502103090204100300d50400320061a900040d0002030000da2004001c1400c1510810107120715507005607440e4503034145246490060345c858400d451080d820962445994540f040c1200d048034110b0311015507062550342488101c2e000b10442c0e1041c8036007030200c200503031000e00003030500c40d0346100142e41041c00d01c803c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 1231644 1250 1230394 1230401
    0x209031009080405010c0311010c03060501020f01050c03010b09010903020301090305030708010b03010308030f06010e030109050601051201020f09040e030d05010311130b09040206130b0f03010f06080c0405040f0605040e10 97
    0x566034854144507031040801c1140c811a81a2002840d000b400020241002d0f2140b480318a400701c519860210b4800c01554154060340c20713a14264242c861248800c44001e003610000d65002000290400040061003260001070441d1101030520085241e03481d00001c1c01c595040200780c000c510000304100c58681c3c0401c0c940d000d0408076130014255410354958081c03500004003600742428a80300412a10381c000d86803202c52800060083c000c440c060302e041c0c0c1e05ea800a210f040c0c01020030b000030311405801070082d516804816012981820311101c10070000d071445c0949040c83c0c3c023040000e81084c5246029060185004100951032203881005200c8038542440c00c0403803203854201c2030f00071981e8499030150840d404645a41e02c5d50151001240c0043e89139202c040c01d1400018010403180d0f012024604075042941d144005554030201964011011141a0f10451081200707201c1c1e40303071a52000703425002c1c24000245403030303c0b0740201d402c41d0032400c00030800761300100c5c4543d001c1005c0d01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 1232894 1250 1231644 1231663
    0x20f031008070e0103060b04020d1a030c030c011403040f050d030219080408030703050402060c0106060e040b0d08030406090629030601210206030a091b0303020708060106050406030507020a06060603020903 90
    0x1005020b118641104100d9040c4103000041100342c4990f440c9002c2d950740e4040d03038185541803000300070300b041c150308420508000d0b43c0590701074080d100e0400e03e0313440e004c61100581d000c1a19680e030b02d1051003240e846158401003040300c156254000d003401180007000081540050f60704d0060b900d1050310318403d0b0038440e000c01c2004020242e401c020000b0301000070b50340c000290381800700b05510b6501c001039480c00307110000358003580782c043c0002e502a40100082c140f00030545041185003d050b0a00ca80c250403050040e012010801c003080000755154070a081d464007c03030300007072031034641d0314444100c0c1c8100703e0114107070340c44401c40d6406180a0000d02d005118240001a001c24288210b50180100c04800b92140c28080009416807050350001d8202551244403a855143c000c00141d803003100a010640c018400d0040118200c1000a0241d040c0e645130349031181494680002140038180080040c400c40c05120b454000203219809581c015041648004d0380350903945060515100616 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 1234144 1250 1232894 1232909
    0x316140708040510020705120109110a030804061223010801050f061c03030b04020403030504030c06020706020a110102010b1002010515030613020405100b0301120b07030209030d0e0a0801020f0310 86
    0x4101100c00900040201d07800c5900540381000e0108201c4001d03814081d5036071045400c040c1520f001c0701010810750050220a1044032011006400d80c1d0034440c0640c4036000c010045c090070441880014007400c80c1051540709044040b90100e404040800324080070340e4000e0b500b9901400622582d8800c0c061687c0c0580000100c0c0c20318a040c1002404011141240b940041d80c07514400041c5886030b0050100c001c0080c0c4155a695034a21b0300805642c4944415103034020411404207a841c408141c0200300c420640c001d0588011a466101c1004810341c0000e05640d42c1d04900b00454541c55880044042c20303130000541442c00e21001041e406550780081c0c07083c1c200c4020405000343c3c002015160310740580700000c0e10b946d4404e800201a400f03030070004c3c603075a010000203680c040030a11140b0740c0d4842d61522185031580b1600742c0503801211000b17907254101000c260001071103000d20f1a002c1d0001003203d808160b440b00850f08991020600008004001080014001800b200c00005008a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 1235394 1250 1234144 1234147
    0x806010e03070312030603080309060103021804030504050402031003050a0b07030f0b01081906080a050102090307050105040501050d09080f0f07050d0f0203030703180c0b0c0106060801080c1309050102031614 91
    0xe0380c00603031120403900006040441c1c1a8400c4000d5200f540500091513200d08030b2a0b030307400d251400b145e80e05001d110880c8940b41407000902058807680d0414012035041d161a8105804e001c00c010280d08001e01d903044004440a000012890801c03000b4456400b031600342805091055005050303840400c050b0b02428201904411580d0340720700010b602201c0c1d06040506e940da2240e8101c0541007a501c8403501740308030b00c00d940c20b101040d0f0003840314034001c4003214005560b41005460350b01880c81021b0108034140302c00382040d05650040c1800c10700c600c003a00d240016540c1c0342d0025030414616108082d0300071545008010b070810100f040c029890808403500030701000002c5d5a44002044401050346a0164203a129010403055030020b40c0071881d1065240c40d10980c02c80e540040b08a18460740c00c0650000e503d40c026221326050310310b081d01814141d1022801c2c0640d54801705140003106d80c0e50352200021440a1001d107000b00d4841c403900074003074142d0000418440300d40c03c40c204251f10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 1236644 1250 1235394 1235417
    0x110301080703060e0f060403050d05010609050a0b0717040605180a030209040f05012a021c090603020f07020a09020406110105070206010e1905100503011d0a020f1201020a02070501080601 82
    0x103000807000c0840c1e40c031402c0420b05200d03101100703050060207005024a4070400c018070041642007805407a041c200d002c0200700340da0b81c80b80100c0d00201140314064110b80084024412480b038140280034282c00744840052449644203041c105521030b40c06200003400c0419902c400c22500806400b94603022126481440d0940c1c00040800c0e00c003400c0184080d11000c0c030142085800e421401c0541145030709607607056078400500700445480b040d0392005009910200c0d072541101c842d20807941d500c80d03031041217083c10302340294000e5024a40172505040103004c01e0f001070f07480e88403032130103040301c0c403005038807545043c9015003400c503440010001641854100a407007940041c84604507500400071008136110b07103141008136400310f80111809400d0104000c0c914445982d520304541e019802040700300c44002818805000c562083c0d4081d4000c00c0301c080151400d034403520340002006103064500811001041e08a84c440f050344005a04407490800403580c0114a0702e50246003804c00c94040d45 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 1237894 1250 1236644 1236659
    0xd0201060504060b0a050702030703050f0a030906031e11040f09020a020601050306010303080f040807050307050714060702030a0b07020102040b07060605040f0608030304030309060b0a031a090d0f080403030209040203040305070204110301 104
    0x51768056030810901140440655608204510003150008203075031700d02c0c1d82e58200c1600d400d00ca940640c045070f43c6a40003d0003601c2803048145e06260f110125900c0b0744140d48a6018000c1101541c1101009000c04547e1440315104440100802d000041c0d6072120500060f0900f04d05030f10903482604548010000301e0f8004613410341c06002e5919481c010356461501d0101c5000342500176010f48400706144081103000200d040c16185e001359001c2031410b244040112620900304006d416403c03030b120180008100840c00303034102c022800094101034581d03440708066040759005440403070315010100b04604080c8503210840c03904813000d010082c103220780c4c03594907c000750009082650300d04d01c80040c000c02d0f600c81011039400030f0414551990302d080aa23542c1c07101051444072100c4640109441000c00500802e1010316030b201c1003000e060392003081d594504014415000d058081014038295505c41c8000d5201d20b100c5c0c1c5942e5201c1c0b21900500c0119904040040c5480400300010312041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 1239144 1250 1237894 1237897
    0xd03060e0c0903070b0d0905060105150d020304050f0a0503030a060902030105010e010c0302010b060d0b0117070206060910050603010306020c01051303050d09020118090204050114040509060108040609050f0d0201060504060b 98
    0x1502040c81940d0b1001080400d14008260b031100115107804210404100d1640d00480b107914081c10450725140d8031402000b50040e610100b40c448040100100303100c0644613006194050b005030103455460340c10780c0c2400c6c2482c200703480480e0107403c0001004000501ca100b694041c0407600411401c40d81882c0002e0031600403103260a040c80300101d00e2004141c401d4009410070f01003c2c00003034a810901e000030028007000003c81e40440d0503401c0c405031503506902070503c284400c2e402000580c44c2c100900c00b101201070284450901400c1c000701d50354580000940c002d601c915401682c0c0d00301a0062400c64170007400266040140861460203c0d5104080c2c0c3c07020440c00000290307070042031006942000c021f50b5100001150028000f4001d0389550240c004c8450a0b220740700205441000000248568004c456005556001158070745d4401d4803040e50041c4039910009400741d40d40c849600e400e45980c0f0460f00b503840341080a01c51503081c081c4900820f000d440034450b190400d2401c900a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 1240394 1250 1239144 1239151
    0x3030c021e0c04020c010e070611010c030506060403060b03070b0a050315060304020109030605090a020301060308130b070f06050601050f0d05090c060403050709090203030405090a0204030b0c090105030403030902040f060b0405030d03060e 104
    0x126008545c1c1c07008402d0039402820a1002c900444070411b550300c4c009842c51400b441c60842c0b9503c1d000c01c0e0300c00d05009024192003041e0007400300d468581140d4440c0002d103030070044641c141c0314401003c150400f92000420b0710720703802c2c1c071a03a480c0e140c03040c004d556680903460428040c580500600c40140d81107507100c01942da101001096940d641041700f13140134140303400a907040d82424000001d101e000f00003002240718a000f42c021031a215200c12500b48100b410042030103080c055103030042406907000d0b94001c80145081b52400320025580350007130308182541e10180e5030f54810b100c90100c081004980c400381c113480e81c40c05c15281d500c8007511764042e403246490658a46d10701008554051040760080d001c02010780c025420050301c1480290002c1c00100c41074140e43e0007083d034903030510003901c030045da05079202451070782c490380d0440180c155000100e8003e602d40c200407200503090b0180380d01a14200d40c0aa403200e01e4181090700e0201408a40014185090070510604800711080340e403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 1241644 1250 1240394 1240399
    0x150b09040c140403080301140108010303050a0507030203090402040902030a0f0b010203040314030c0601240302090a03030c02040603080d23010e0705070804030605010b040302040b010f08071803050a03030c021e0c 93
    0x18103542051060303038407040340b60307940d20041d00005000c010032800c00051360690300b041e09110005a01000191280b03403080c00054040f0f0301c24806040b0582c8540000c0808034070a02c166030920b810070f80030400766041038101c241c2a5030007008025103802c0b1031003410400c0144800c144500c0d00b0420010b91244220b00000e483c2c400072100300498480108100c4a4201718101217421948e9035134031410444011503125425424500311140702c0911900940742c1c0400020040400c0610f19030f010740700c602d0b0441e400c81c3c0107070f140d07500040864840c4000d4585207502000c0440e94600e090300326101c040603041c240c2e00d0000c0180041c0721080350516000d0b031080040c1403041e41c403d914200b2140d10302540e40000c0c4a0b40c2807500100742038841102a00c01c59200341d4003405009440801542c0c52311102869000041c0c4000c00101d526100c0c0c0300b100713090011081c5010f6000c0d166103441c1d08180da4410141d0200f40c0328500f0485072036041140b9841c03c6c2401c1c103080400d95080c20a161a250801c4260b031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 1242894 1250 1241644 1241651
    0x5030112020a050907020303040b0702030930010603030305101a07080f12010303020c0901060f0e090a0906020c01050601080f01060203040b03100e070804030305010602010e07051504030c09050901150b0904 90
    0x104549442000350b020b49402000a81e5510301020000d41d030741d1040310700321a02e94510340401c0c80c01e0f000100741c4908000092141c0c01e900c12101940081d0f031120080100c1111801c08680c0c400c0800b8071501d8043c5000e81d0300844c0510345201500f45040ca207a10881079100305605410f1202d006900750341007a54016056030391292a001c821019004022000300d840032440c0c000400c0540000304480303100001d440940301230303a860303400b951804418112240820404030780101146810009c107540620705000000d03060a4940300d66040340c00002c8604070340c1e075541062018542c4c01c042010391158803c1138011541d810008000d480c3d000b10b2099502145012011501a0460b000780c82c02130901440083c2c528940003200918240c42540e0580c0400d283c200042900d03841030141e040c6008040d8010480c01e45000c05110341d00c0300102908000c0c5070305000110008100503c45001010900c0b008145e6050441c201400c40c0d0200421302c0c1044401d820820110b1800070665104500494002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 1244144 1250 1242894 1242929
    0x7080702030115080c0102060105010309030e010305040203031303030908010b040207020312030c040909050a02040b0f0109060507060e0102031006030e01020702010903030e12011e0f06060503040209070228050606010906050301 99
    0x2a000d0086540c000f80550111400442c90040008103807020b5403007642101c05599880300150119040044040c0025018424215440d4000e41109030000d101038102c91802098806814107100709400807400112810020085450f00740200d941c00395048400b10700c0c1903140d6000990320b40d580d1030210711007076012001842c20040c40d0103460061018031018045203410f45041d90302d803144803504034030552410702d1201d071a04250341051422103060b151021901d01340501034906400c1010125005600c401038221803140a00145009099800000c50304508040003d02962a0701c03c0c64565070b0310500c00701000d42c0e40f100c03000c8100c981508042c402130962802041c0c03450301e8084032964641c01c084c005810b81100580da440e080100c0d10040042d03010400c4031905940040c803821000503414000305001d071034039040c2c0541200785401103032207986440032075000c1040020b4400480c40c0402c0d0031031041c084180003940d489502441e22480e8241403140280c100c4c0410f0045042d0206c891594 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 1245394 1250 1244144 1244149
    0x90f0e010e0a02090d0b191b050d02090a06080405060c0f090108040201110f06010f08030903060103080a09030606080706140901080103060c0c0501050a09020406060504030b04060902010c1407080106080f0307080702 94
    0x480d0008280079050005890b59401c18955014050b60b1782100d061898940240c0c03018144204080b503c4621804044400c8d00b82084480350461081c1c1410f0a81c2000078132030350780d0780d0005e10009044a40701c0c1019840c05050682c03d2490040c000c0c40c2d10442005100111540d001c100c6030148024200754003142c0f039500040700e440211030820701c0c0c01c4c8242070320101c00c2e210020b0440d04a1300740070300d1450340c40e844002e4162640980103da5405901083c01072000581c0c982c060540400145480d50f003a541e80d450762429140d0581c483d040315009008144030690b031020700d022903240da56001e80d1611010400003043d103001407101901181d9112203036540c031840740520301c40d155040380c000e20450600c901000002c1c5481501203105a203800e40000d221030140f4103850840340c00040d0800c4a40d40c685800b4003815508108034104083c4420210003c0d09d011214000c0c408400300074241c0c030341801f021600315a159080b0240542c040a25881400300020841e0fa10030703030001000e0b48641280c4007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 1246644 1250 1245394 1245397
    0xb04030c030e040f0501050306090304060206010504020306040902100504030201020105060402040303020a0b060102010e03040603270203060406020c0a1401050405070611030708070809040501060215010603050103110d0201020c10030b01090f0e010e0a02 110
    0x20b0280c3c03280c201210101c1112598001074182d4000f24140c40b42070b00c9509880d6a21301c034610070200541c001c440100800d00d01940034540c09080604040341c0c11111703600099480e21030002d040d000c250045010320541d6424890950301031000c2e2021854181503884c003030358030b001000005288a10000024209920030b401c180070003503654044a4a036030703d68401501070038001845c00404020711140982d000590359050f8485a000340103844181c517551a5003020f58040b903880001842000079000c0064132550280c00b8031038141c000090642483d1500c04c2c1044120381c0140100412004c05400399071002c0100d902242d031042c206542c41ca518a0901c1c44c501610490560161500c1d00000e1700580101d21160030340c2d003043c588101c5030388804054044405c02c0c00040d1100d6101c100c1041c881c1000c0c001c3d4079200f801401100c0641c0300c0e020000d4000c909114604000a03102e0072000040d580120040014094a64601c15881d09010340e6001c4268140f0408003844070b80c9000c507160355a90390 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 1247894 1250 1246644 1246667
    0x4020c0f060106030c0210020a0503010b13030f0605070305060405060303040b09040b0a0303090501080906150103020703030b030a060b0a060518010503060d050a0804061101090c060806060d0603150c05070b04030c03 94
    0x102038034030350b6a41c1d000c090010140c462070b1401501400283d401e00c81c003540708482c0303011107a8840d103065034200550340d2440c2e003000c0d03040b03600c0070a0403c010002c41c46008090300c940b441088081420b2800d458000d0a690029040a01550800041c801b06e80d9021059a042d600402080b42d1600030010008000d03103080c00d0015001054804e011041c075501011400580b4000e0326032568640f10740c40c0706a95914212014200e02280f0302c0030541c1988a5002807407014001d16000c520041e40c90700007428844000812124035076561400c000030b041603003030a4004e0015042c92030800000b1040b214140081c03000301410850004001111a0764a2428207651500701081f511201542d1900a0403036100b40a0603001c5641c0c43d800894440c014014012040da002418618040c0b42c4007050700c81c1c035000f80109904c04024440c4640d14041e0303105105c0250300940350f68031495442e940c914201d5401c0c610038020400c081000c0808590b1040c0001d400c1640340c903040340b91240a04080f034100d03aa40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 1249144 1250 1247894 1247923
    0x4050103060506040e030403030207030b06010c060c0c060605010507020a05090c1209030309010f0513020904050106050d050c09010b070308040f0201030204031a0906010506030105031510030501090b0109050601030203100504020c 100
    0x100a2080c1c0381d0100d403040c04103840420003851403c3c8800c0c0e0340d0255200007030040e80080c00c280000b82c0e4400d0b9468200c0410b040040a0500a079103050540394813084020001b0750301d454410500c03040c1e000c0c4a0003460f003803c2942c500819038008c1010607016003d054003841c40540820710300c5510b441216170300c00230010b80880038108031440984952064801551343e60a041050132240700c80c0c4075a40c010004450b144030810040c1d401d101c11560001d2056070503560310500040c590b00c5010b040880c151081000c2c2010980060400001d250180c0240160003c14400100041e0300101d02a4200d600041a28080310440c40124080d11850704010800280c10360001c040122500d8414000c1801009640f004da80391000d120050109100c0c4541c158000480318084050460000360080990308228481549988070942511140c0d101181c0303c0e04014010800c901e01c603c43d65400520910b425407850400800c148502040c501885d486a0381c0003401601d010010000c07046a080d54 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 1250394 1250 1249144 1249151
    0x3030c031903150608040f0311010606020c010311040602070611010603021c02090a0e06060103020901030615050301030311010506060706020309160e0604060501030216030804030c050109050601090e0d020d08070c0204 95
    0x148103440300c4240301c00407031004282020189203000b00f0010340300081d00c4180c0c0c4c44100641d1680c07180c03401d001e2512003c4e0240f01c480b41c07041924090a004450181c4801d400a111803a200c100050444144465002516030140801d1000590100d550002c90704980380984203807c0e1a6030180c01014186d0000350300142110500c1c01c1550607445c1414100e000b100d2900180d6180743c0d07401c1c1591550300d1601c015412a4000907802d60282c0e001d841210010b2400003806511540c001c8a15404080884041040031004004041c0c0c0b000c1103c2c640303502031000b03100505007680411011b00400200901c4582c0210005038240403c2108154040c00701120000030340d0b40c1c41030403220b80c0041c0c0d040c1d0f001d80c0c14000042800e500030700803a0880245031380c2e0a80301d8049510704846c50740000d841142007055200540011503024002d4003c200d00800113032150b13507d0800540c080702e142c80300320801900203d0b08c40c49015000b0231012980c5010341869040d80ea902e1104840c601110500298018034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 1251644 1250 1250394 1250407
    0x302030d02030a1d01020313020120010e0102092803030503070e060a1809021206040207060905030d0e0105010f05030319020c04090609020301050606120c0c0309090108150c03010605090405040203030c03 89
    0x1d0382080707100c840090001e212042c13082c3d140c1d03400d038402180d1031f403600604038106100551041c007900c284e20780402c03842030002c400c5018542c00e5506180c98000d0036900460034042c41d04d08000441d0b1902c9695040c1c80c1c861602c0d410000d0003405034030001d81400404000507048a015004014640400a108a540e01134101010740303601c00034450b52104440441c40466010381910032038903068203510403041c050713640204100196010340d204403101a10b91b42c0c0f4800184007040602b0300307020007207001b103900c80244078100c5c21680c050740082c000f6005c3d03450070400f41e1408011201350704005000340c0030080c1380c03100a83c586254000f590703400030310b091881000c0c02025030100b26680d200301c2c000d1005413602003c0140901410b28800c50302440c2502280003006a24000c01500601e80c0940b0304200040c1d0014110800990008425402130b941c2e1501401a001441c0d500035440a0701d18155414410001e20074020181d21602681c2d88001180a540d030400a8a0308101c50008403a912038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 1252894 1250 1251644 1251661
    0x70b0405030a020f0c01090b0d06050402030f09010b040b0f1c080c070603060504050402150706180804060e01030504030509040b0307030c030503040608130b040305070204020d0501060305070f0302160b040302030d0203 95
    0x2c1c4041e19080050081145030722100202003131002c40e0100c1655107007401070a00c0e00309101580007101c2802180d41c3c509000413941c8960016612071122001e60019a10346003503402d095905c25010326110703600c1c0c0818050a41d0383c50000361901c4409440364480130030584840786003151070382070103800000040b501c0d0b4801d01b4002408403d4443c65a01400321b95541c0c024070080c0d440c103a400a50140c442a04554402c032800003800585000f400007207004100101040c62010180714241d80310800007070b0600a413038104034103403148071080c070f420005850b060714010114040e40100030711454440e401480e885c1d80c01c0001ca800746411038445504c2e039a40b450421b54070361203445030708080346081c0000b031720303401458400c1c05010703400108242e1140c0d13a82da01283d6a500c0601c0803a070160742441440020b511600c200c0b80a80403035100001c880c1850107002e415100e01d001000f040500411801c2c1c0d403c0c1141040311011a400060800c4944551800307900303500a0385126000f141c804000c029405 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 1254144 1250 1252894 1252897
    0x70507090203070306050906090103020603040302070f0305010212010605120105040e0a0b0a020403030806031c030b04020f12010311040908120a020f0703021609050127020f0d0603020906060a02060703020c03070b040503 96
    0x46403c1d0f20f0400500e030fa100300340a81560212030309170307210381b4038001003015040c800700945c0d100c2d110b481564500750b1103540b2111490340d01e800a5901d03a44c04103002100c0003d034a032582c0900b0346403d01c8c40c100a40c070840c404c12507005004040c02151501300e84071fa0850104100440310b0350cc0b01041c561403402000b41002500541310941c002440b8201103921824081050304140c7c60000c4a001d5807103031a8016005010704410b1203400541c01c00c001d03c00040e030f0740b0290082031143c1c250340c1425451030800e8405581b1082c0d11503c980d03d40000940000d014400703d0780820051000da503850703a103000c03408000340101c080003100e40c04005504801c040d40412081c10403080040d030002a29201c03e949012104240903580142c5003280a24003011040d852610401403030340d07030251814403400c0410003150422000040c803291101002e100310301c1c007c1c4d0007503809003054a5107805e00b800004020755594015100d41e050617400036003103001c0d02042c8125115140c00400c0702415040910700260340c0d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 1255394 1250 1254144 1254151
    0x10c030e010c03020a02060403030b0a0302060d05070201060602030405030304030b06030705090408070606091104120c03050f010c0305060301150308030403050702030307080a02060601020a03090501110319020102130608040c0603050c070507090203 108
    0x141d482c0c1950b000c215402442519480041a0300400ca250303603560741640141050741d0908c1e4001c8a0002c00001a904e8100034044803c2804021807039061888000e42503800982160741076400070301050055880002c20740e000c590304006c564402d501c915001c241042c0183d0012900254000204028826010000e000c010310440081001f40e40d5294024122254001030740044d00d0b01f08410040c4885c5400050040e5003d9414080401d45d695a203a29000c9000c0304c0c41d1241c2d4580c0e1298030941c1d054800c2c070364000c3c0e09400900c94540011620404002c29000051071502c001c4085030502d4404c1040c2d810056000e412a030b910501400c0c140c41c0780d00b010410070b0045c419000040c205510100d20a8107e982c5622a201c0c0035040200542d200915940508442e1209201006010308a00001c4000ea000c58000507521041070065800c0e1001075001071052194180a02001420214001c000c9407900e1400041545030801c4858a5200392080a0224401c146010039200c8196005501 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 1256644 1250 1255394 1255421
    0x9020703030b130203070504030f05011b0e0a0b070203070b0c0a0c060c060b0402120615160b06030706020d02070504020703170708010905011401050d0e0304080609070504050c04050f150c010c03 85
    0x25505080707040f0300c284d100c200c071204001a03060000b0000140300000d416001c0d445407002181c40c401000c68050404103a022402c0001d1288441d0505810080d0309100640100b1f401a4500091900480e0343c1d10400d01c146e2030341c0000002c0d16207084005002d000b0441f0392000c0002070032991010018502001c211040c6d80080c9030090522442c5414801c1700c0b507105c04030000e042e565454600300300d81c410300018000e0701200104540c000c18560a1074000e00188201807813003860400c01c050500d069000e40100040d0751140888619040d000148081101c0701102c0c050380e00c2000c0c1c9400c481d402d9108400c58143c00e240d00500a4258101680d0350507075000403810005a80c1c0e074a0040d0a440c2581402408a5001c10031100300b101540c00408102004004580c900341c0c0d105044c0d031600701d04843c00d0b041b607005040240030914060141580002035110403d081500b0500041c242060841c6218400e60320f02d805000e052070b086041d10a48103a280081110000901028000d0460f10b00300c0c08 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 1257894 1250 1256644 1256659
    0x80601030b0a110405030c0114130e01030b011203120b01090302060d020903010e01020a0e06130e0403020307060e0102030103020a051210060807050102010b03010606020a021207080303040303020703020d08010302060a0c03050409020703030b 105
    0xc6000031040e036040745c0c0014005e00701140100019694010024100404103030b081002e040714440444000e802005c441c092102c0e2985981080d008601042c1c0281c64440e1541c2d20301d001003503100502da450000e110384001901d04100006a44016171540021740188000c41c501074880b40076400b5104015003a4000d1011018a01a4500b00d00c924000c0c140030900a913049801402c009018140092040c210301420948034810080d80c080100d50440040e4000210fa0040040700d0040301103071800c0500941c117550469000402d508054092180645041101c221603c0801c103d080c480181c0503034204984c6880c1c450250301c0741c15034046c4c140998201071502c2c0300383c20144100c104680c419406840e6031052542044204c0c0d11030b030b600101602c84c04002294001080c8011800345110303490041e0740d4a024134000e420280c00482040501403400300400250321540d003164002c03ea10701d0300b041c0d442c40ca03150584070380c041c50300882506417020640100301070b0181c1c07000501040446016 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 1259000 1106 1257894 1257911
    0x2040302060c0a030f03020c0706030c0509040c020105090f0303010e070302070201050d02040f0e0a0c0206010603050603010204030f0c0303090803030c0d0b0103020c01020304060501030c050105041406070606080601030b0a 97
    0x2020300e4001035606404c0540024241408000c5801e0030350402000c4e00700b060300c0e03103c7c52090b90b041c143c903006481d01842c0b05030111011050003c0c0308004407000020001d0080c481221a02071300d125241000740d0303040001055074121104d9040010380e660b140c1404801a4224040072414840e0600c4a1109078140f070000d4000343c81703120130502e14a441c00c20041e01011024211042c59860401c901e40625800f0401a0640b01c00b41070100d02915104082070092080fa030001d080c4066503078243c010403100503958400c40f4040c0d91150b510507160a11940c03244415505e40d28108810099418880c071590000c17080d4407414100103042c010300050003420780e80102c03400c40704a0358034001881045200311900025050a00c1c1031810982021040c0741007a03a4010000d2245d00085084410089039070000400342203a0425515a941d4a24001420702801c0d01d01c40c01d92402d02844 = true := by decide +kernel

theorem cover : BRFrame.Cov 1079144 1259000 := by
  have h0 := BRFrame.cov_init 1079144
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1079144 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 1079144 ≤ n) (h2 : n < 1259000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
