-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0104
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:52:02.43899+00:00
-- url     : https://prove2.me/submissions/59202c6b-215f-4f19-bc47-8769d46043fd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 18525186 ≤ n < 18705042 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 18526436 1250 18525186 18525203
    0xd08060306061002060c0f040506040e100611030403020603150d050c0a0e041101050a1101050106030914031303030e01110a0506010305010509030406020c011803060c031a0301060b071b12 82
    0x408009150030203800a19290294401c602c059014980c0041c8607070348034590b41041529554504010320719442140d21040d40094041004550010b900b42c40034083c284e55036800441d01e550300360a55582c1d1560344c0010712600f09010410150034842c0c01103610041d001d1a14100c0c01e0602c1c0003900e203c2019400b6911540560350b108076030708007914110003404040665860a140035650104280d01000e06941000004280481d10900417444a8511400640288055a1583c5000b00100f118102c190352700388a4840481c480384012084031982000c118103000340b82d05540302503a00091103054541000004507400c5040401804020380451191001c0c0440303501d035041072829900094100b03000e0781c008100c100201d40d000a00c54428650071300b84509090030072500480181d506a0014010741d00b40303001401443c2e49544400f5103c00000c0d0314030811004001410300703c40c42070140081d214000c000c0f890114002e00c4241c00960301c058540392aa6454001c45280510f800904964403403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 18527686 1250 18526436 18526441
    0xb030f06030c010e030303010510020a051b040f0908030402040b0f030a0c18050709031e06050a0e100606020d030b04020d020a0503070305060114071202010e0303070216050a050604150e030d08 84
    0x140610042c01040424a040e80c0325950030000680c481c407041c800c5900c0b0706e07080c1c0440c1c91010f00a01041342c045401c04140d80d0001e81990048401844403100c0c075100c0c600d06003c0070320f417001d02d00ca05064290041e201d681140e83d290300740001030a0b403603c0f080d4007007600600d4501555080240c85400b9100c0c45914449900e0850134034000c02006200e440c8042c100070400c0006d03940b03d000d98044940102c103401c8070a5034003400786103050f1500d001a10950a15040080b2542d06400502d6801413500444001e2540190030008030360050040300010f030098034001d00c0c3d8070700c02d4110f6040c40030010300041c9809151043c034401c0b039109600d11000b10303801000b00401c0a415200740d9038804002e0915000d8004401a41d006911071107034010700101d11044100c0e4100c2c802d600c000d58200d8880d00301c0e40e60b41801c48003e541c50400c6030301d0341c004501003100491241003000084080368006843d09040505003c0c5044150800381f5010041110038010303450207590401c01040700d0b0045450300c00890 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 18528936 1250 18527686 18527689
    0xb0d231002040e040b04290f07030903090b0d110a090302120706020304090c05070f0506191e0c110a03090e090f06220507031505011203020a020f0a0b030f06 69
    0x1140d18500c0d001014414841080120700103201d540d13000381e000caa003c0c001e076070740d280518079210190007015070100f0302c0c00014074284a000306a40180035410302040c41c1e65840c00f00303c082d00d0b600c440080018507900420040e8113410700c007030000782c1c01d5108041034a0307070744030030350080ea40190030f2400009245035010415428000c440310080820040640900760501b04042d40d01d204a105581c00c4907a141c418862a91103441612900b42c0c0c424078040114400c0d0900c269500015140100f940700200420383c83c0441034840c00402c60741c110300302401c011032180d07010b00500010031128203120040400303000c011810310050a030184079032100780300c282c00c000f140f448140d801001c480c070340e50180114212012000400c5580002c0352800b51241382d04540180103004154600207050b48210f03d804020403030240000090a13140e80e40405c9660b982c2e2000e906503900091010b40580c21125982c405810314250381c407038014014101540455844441d070b005a44102c0d49140700304100300034000203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 18530186 1250 18528936 18528943
    0x509030a0f170c1303020603070201050f060103090314090103020f0307080115050306010e0f06040510080a0b010804020d080f090901060c140606010e09060301090204020a020a0b06090106080a0b0d23 87
    0x5540c42c40d080b044640d05a007000400c280280400011070404030300408000000b0031140080c4d80d01902940e1242041c1c04042e01a003001d442d24040310841c0e03000100903500c68800d10503455015610031501505505001105a0190501c0b40c109030b002c06c108a9142d004800441c0100315030742e101245989080ca40c0001e4118015000c410840c040080c448180e900c041e41e044410811102602c2600c200c0c80080c075184580da00c0341d500944100c402c2503510341c00002492055030698014006220404d00440340b00c101110300a5210b0041981000803c1d090000742090202030304940d85030020680020b00d11000c00d0744903000060028511404010601810154110344000144014200440046c24200f16240f9460140301854009280f80ea02500559404c175005881150368561500c0025200d401400041d00d12246800101f1100d040c4110b00d141200d800e50b90b8110a91503400038940a09881d155a42e841303484110080080340c80c65000c0f45d01d094607007880201c16030f8540462802c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 18531436 1250 18530186 18530207
    0x120a0209240303030106090e060112060602030a0e060a020304060c08040e04080403060c0e0f0d0f0204020301090501030c08070b0702040e01090b100f06050712260a050601090503010504021806010203040302040509030a 95
    0x3d0f0000c0c40108501a00f004541c026111901c1c0030107107654038000100e4010004a0701100e03203030300307194000074207503008030040030b86040c9681e032640402c2140c0c050102c0c51240012400041c3d00400c41006103d10622072101c40c50710070451107141075078800c0c4a80701c5e00703804e98059441140018081013003144ca40300350100d00156003400d400c09011500000c1c0501110702c45103002d8921480380404100c2e00905513100d040c0e0040085480e942c66000e0200141002d010482d500043d180000c18400c10010700601140c1c0300060562820800d40d007440040e000d101c0f0015040d41d00c40c1c0141c030008107000041031245056000b04410fa510f4059001c042154540c03043c0180402000507a0224404256888078007a81e8180802810845000b250301e04400c0031041c3c3c0b00c20382107418089402d405802c241d000300001d90783c0074171158840081500f03c40051707a00a40c0306944400c444c4001c9140350101c1d60006050040d20304080e0b40b0b8000c00c007604c0d021201c000c40c582000070072802d520f400429680 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 18532686 1250 18531436 18531439
    0x3040617040b0c0a020708010515011b0816080412060507180308070204360203060703050705090f01030e030a03020903011a010c030513030c080f10020c0309120a020924 74
    0x944504194031015591007010389804210240001c480213030724002c220b075038001e101480082019140c18900720218100003100b40e400998401032080042c62803d90700d08000d40c00600041c0740c040030070865030000d55180011188681c00344000544c5040060808111038060400480d02d454101d8008004480762100540352440366541440410102c40c1a1028954141d5001503034401107082c00c0d241ba81c03042640c0c0382c00c041007005800210404e1203580c60407442541110515100c02509a0a5450855a282c0000c0c014402191541342002c1c0030080c4800605000901403083d505a0313080d0783c400000d044c0400d40011f01140181000d01c50424078083c4120481020760104c03000030310481c5540000f17001c212011803801505400c501d461801503500540c02054940e0340c800f120780310f21000131224014014000007091143c0075008540c044c4900c7e43c091031030605420b00304044846261022101c0d44984424230f00162140340c0020b0040c02e1130880c40c00075115000300354012040b80c0b0001c9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 18533936 1250 18532686 18532727
    0x30c060b1e1201060806070908061e2e0906030c050904020102150406060806040b1501020705010906030f0605090405010e1b031903020a0b150406090204030206040e0c0408010c02030406 81
    0x14842540c501d1000d5011001110a4202d2a0354010318902412054100581c0c80c003401b414001d429030410300c10000c50300e0782d4040e55002d503502c0303001c0c5584220010440d40c642c00c0c844001081040c0b062110820320382c0d05022101c103c5820070700001c580071540c0024140656a007018030502c0611107a2400a0200700c1d5420318915140d40000d40325080791091203403070760044021804114041d00000c01400c4a04115012440d25091130780401e0300179200c0000c0d100c0742c07858034401e0354404a14601528411b0319081a50f42c41d0110450080c60558200d0714055592003011685545032a4150302940c010030000c1003c08403070000c90304113081a861800c02d403012116021032a21301007804880760309417000030b8541d10001c0c1802d07810514400c40c0141801292001c2085ca14404009a1181903003a6410492182ca900c541d800700c0c030490201961040d0103100400040032064945907200d10907010803420160f5a031541350a44107043c42020140e040403505011050340240016031811110050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 18535186 1250 18533936 18533959
    0x50c040602160819020a03080703020a030e03060708012303010e0102070303060b12010b070305210106020c0d08071104020705030d0504030e0108010e070e03011b170601020d1d0307050904030c060b 86
    0x5241d0320725034445504c01142005044000b5581c2d105036a4000750341106c5243d0b61116a0700e8020345640412800b01c000c90407041e401070f0941800105180308031113946429a20740d0030181940c816203009070b90b1225884c0c0546401072940ca00380583d0b000402030f20009070700d8818524024090f00c940c2d4101c00146c00c000e00c4251001e4400030100f0781158084032025075266620b00b011907440c81406002c104180b0400e8080c82c801070354803001070484461740c0c00e95000c09805010012020200140a42030349000c0c001d41d00801c48201840e102c00900410040c54801240d40b21419500131004c95002d090340c038420403060541004154440003000d01e40071010b503040203045801c80c6400b80400003040414941c1c0070860310258854092082d003519110350310810b01e000100b00c41e001c421001111051480858450350001501d07851180c0c0c6610382c0b103003401c454401c0e0b079004201c800c0110340c10300c80e410b0b0016481c0c4401c0f62541c09036010383e8503124040440d051000c1a01c02e00e00120b40221902c150 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 18536436 1250 18535186 18535199
    0x20405010e070f0e0d060207080705010608011e0b0a080f060405010c210b0409021c0201020709020906030403080c0706050f01081b010801050f040b030d11100203070e0f03030706050c04060216 84
    0x2c080204103d9414010a40000440410200142d0420081c880381c8001010400d1043c901c002d0f00d95148143c0091100315151100142030390700c0d80c07070a00404ca10489140d15010800d8000c0d03903550602038003201e004d650310191140741c001c20016001c02a0050f42c248000d008007805482c04030291410f1003103408644c940e00e28468a040c1d02c0c1c415005541d1402079080350340d15000820070036002031100310040b0b1120001485100307060310032805031140000c00210785595000b5035580c804006c1c210384c11a591902c0c00d64440710024046000041e01b0800840050064071560740200c05c4820040361942c1014103651612a009031000040c4079685c82c2c101080e079100c00e007981581c0040c1d4411a980c004540441c02800302800000d5050007003420f0800c40581c060350390009081c142c0100c0e100c4500d5402818101c2c4410f032a050002480c8145612079810414201c40c90b80001900f00c91500195449c3d090072a003041d41c081c0c0b052800090100b00c4240c1c10040005500d42e0b50f0b00380c8401c1440c152 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 18537686 1250 18536436 18536447
    0x306050105030f07050904110c0106060801051f110303070203070303060b16062d0b0312070807060504022d01020c0114090d0204060503030a0203090108010b040e070e2407020405010e07 81
    0x10010314009403e18006400117215000341c1359040b10140062010015600307200700c503904139144210040d840c084000411520814006040b114050018502e00510300034009414070b2503240103007481a03207500051100c3d0104010340c0b00d10b006901550311800c0a1078010241c0e00305502101010780244284000840032922031010164031a00016014a0105401440d0042c82c1c05589240c10045c0b000700e025000c5030031100d505070084085e41c40308000c05070b41305800c0c021640060442c0d1024001c4100050180d800b0607040b600007020319045d0762032007000b640c44004c802442d200b080c0134840307036100780c0d60100b00c000f90068007400d0050a4410b41c2d0700c1d01d010341c060420090b04c03c4210186031425500d0301d601403809400c01409807a83c54480240282d034a500ca000703150b0014404000000300414140203a405070b44081d40614400d840780241201c0c040403080f14242e0040c0d02c50040407000707030945103482946142d0010a41c4030a0a40100011510140c1c01200310b60200401c001e51542c0c0701 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 18538936 1250 18537686 18537691
    0x8060603060f040e0f010f0606020303010303020307120306120f11010e0d110a030c061e021c2105100501020c09010602060631020304060e0a020102120c030c0105071707030605010503 80
    0x1d4a00b107901c1582000010090030402c40600940d0080c5103401e020f407074042d048030f0f0004c0301c480d80500c00c1640d03d5104070b070742c0d100174400900141c200b809a2000110003201001054005d841c01241c225111100e20010440e0040203d95140114198508200644e101600c0550b006d007010a406100701010884401035118000c0c07500c440d03403001e82103541d54050358130041c541242c1b010103195162000648010403a5014012341548418500070f120310000300700041c0d90a61140d640742c0900070f0b005441d400c14242e80300a01d00107590038a03c8000d07461042e584030b1810f24101014640c0307048006801c7c550740c42069402082010b00500a150300021440d802c1001610f1144043d0880540c0031840510902a049840e44051a022801a50b5000703140140d0140318108540d80304074440555407007a694009000d0707040503c00d0f0300c0310041000582070503100d0401b5a86091442c016807801c4031411a0307820046546011003001c130a0130190b4160f4811800e00381008010f007040000382090200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 18540186 1250 18538936 18538939
    0x1090504020a020f010203040305070b0f0c0f030a091b050418050705120f0703050a0312020a02120c03090a0b0a0908071d0618040302070302010216050a0b07050705030304091b0806060306 82
    0x6403440780e10f1007013102103600d05554000319101d0400b4a4000c015070700c001407c0d40c0704911100031130000b078141c40310309015994003d0035506d07003801040c0710480d540005009110203555103548002052a41e80116103008020038100c822500f000304210844008480e04064001c20040040014600050801c1540c1003110794500c8420080c101518040e4007600141050007410000810808001008681d15110303803244c1c1c509000441030a800ca0298961000050340b2a0f106201c803010140028654007203a03c003504c0c40e0a0503000420301248a6901c8203150303060015a0b000030951101c0c00303d0140c44d0603c00340c0400c0c0e00d4070300c902d80552600414001c0d5000c0f4030700400ca03103035034401513a200504040f071030040ea8070303080c03c019441d40140d20090780540580f014031101585445034800680b08000e04416145060554501c0f150300258001c0b030361317885214404225581c04001038001440044408a141803018444201d8010400300e807805101000d81800441d6070703280252031340304d00c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 18541436 1250 18540186 18540191
    0xc0a0807020301060b1207090506180103050709150503060307050d080f030a020409090f03080a0213030807020a0b130602070b091c06150909020102010501080d0203160311010606031a03070501090504 87
    0x306400060300410440d40803000c60351000a88130b204800b00948940304a041c4d0304c0381c1c2440782d0f603502400700768420046410750720748407507040e9115076000303500968020581d03181007c041916001c01c02c00d60302d1003c5491000c0b031004420402d0600c0c0402c108030143c0000e58507205544000d540c0c4030218051101030f1101c0d60000710018004c000580e054900800040704240540313a054202200086c00046007980001c0c0c803400085c3c3d829040380204c5448182c41440304542505d13549079199960480d1108036880107000c400080e01017035030805881010b05c005900300401e482c20002a00e0002c481c0c0c8806442034090081084e540c2e50401c0c511b107100c80207500808e00d8030807458208014081114002c00000d40d083c40411012240c2d400294064400e8000f003050340d80f039400c5540c0d1034040760704580044e0320421000d0039003540f004034034420070b11a041440388014412040d50a45656030401c90009039180e128141442d20b543c14100c82d02000d070054a5100d04060000340318078821b011351402240c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 18542686 1250 18541436 18541447
    0x6080103080c030f0a0905030d0305011802090303070602040806010501020d0c050d0c020102011e24080a0f020a08070e06040f150b310e07020d05070209060409080d05010905010b0c0a08 81
    0x82d040c42183c1a4400440d2440ea40700304004000e4051456401464043e00c205041246000e0081c480d076416269841d5812800440c48001000030794060020039415000078048880010760070b0010340042c040860113094198109800207141079049102c034010800b000910402041011940c41c59217545803400c0740c0611070720b00060340504017102190340008040c442031411203013141e000b620040451030405004408002c000c800303400f8503006500f0306400400c502c100050340494507d216a01c05407050b0381032980e890040f41840000e511424020b4603002c1002400c1c0f50a12a2300605c081410f402c101d0100031424403585050715000d070b140307151707400981c0c1c6010305100b43c6891150b520001c88820403180b03181c1c980111108600c1041010078180c004075041600100e0101d058840e2551250308000c0144c0030060100e03c09030205406c50b40d10716064011410040c010034040260300000b2400b540b510040c1d4044803c1644410307503241081c001c4150041c4046040912107401c43c0032240c460 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 18543936 1250 18542686 18542707
    0x5090601050c0a0303060806010602070f0b030402010c1505010302030c0604030b060f0a08070602010213150c080304080909070e01021c0504050111010f020a0c060b0301060f210b070302040e09070608010308 90
    0xe20072908022410f125103400c01c800c03d070741500113009580001c0280c4410f030740e0340c60f01070780d85801c1805040c14140400340140400440440a103612500514200c02d410759140ca03020302c0302c5140c65004500c991580010710550400304404410400b043e00ca5920700751030741d1188011100e000e0007040c81641c0c91752521003540d45104c81c140191a181065601c29a55204003a00070b6020b150358000c0c034030441d400040c000c44e80c60042c040140c820380320001c5460141d620b2225982c4000c1084a03031410502101e1510380380c1d031200620540c5e2940380c803c109001c0c000068034100380001e040000880d181035003041264048241c404403082030a108489240040b4002e0260186140c0803442510209184015907880943c200d03186010302010009a108902818240c42d083c2c00b404810003400340c8200982c5034203c5081100440c000e40b1009a0701eaa070b66150000300d4107450000000b6004242885844026010380d50011105d03802041170b80e240040240142105200207850b0f10301c003140c41e1044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 18545186 1250 18543936 18543947
    0xa0f02010b030f0d140408061f03170a030b0409111203091e09010e130210031401030305040810180816050609060406050901150512010609050c090f010f0905090601 72
    0x700c8008060310484600041d059540b9201d84482000259041001c2c03045038001604507402c0d20600c1d800340000d541c03074180000820f001a108021b0031041c091000001c1074480e41940030030440306070400d50702c0d01d194100401380d500e10003003548900e290840710000114030a10880038043e040d50f40b010b0100761948020b0450107000f0185070028801c4910703c03205154130340030444540080781d030004543d8035400079941c040d40032100c114100d2032000501c0e001d8500f03a420400e11407240d15012400003c07081801da0105000c3c0d1003240813590110b811f1041100a1042e015602040081002250a60742c1045d000c6065041c0c00f800681000903904096030406d4583c000958029003110141c0c2410442140c0e1010122400d558062905000c02e050b15070602039191200d24051050540a0505040010300c8074051f9001c0b000d99170302c1c1d000248142c00e9000d0540300300f40c0f115405c1c0d124806501070021403680c40313185a04205844690050b0340c0e03000294001a50001e890303800f12a695040146c96 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 18546436 1250 18545186 18545201
    0x20f0103150b0403031b03080402090a0603080c06091c05090603090c060a020f06070804030507030f02010b0a12060e06010302011d060d1803030c02030901052b090c0602011a060a0f0201 81
    0x507142102000032901ca07100800038002c413482561115100c6069041c440c5540c40880c500138005505240441c0c00340c6400000d6a800c00c5402c18000307a0140e03a42e68240c07240d40503504e0f400742504140b04220031000188850752541043d03404500000a148000401d58414a56182e11030680480803500c40c1c103040000c90780041c00680515540e00040b24065030301c50403020144118131941000801991048901c01d004940c1901d8140c140107072594240e03040c80c0d044d2989001c6658614030601c0e180da82c0004200240100500503039194400d00704042a15840b1030021680d0340082d00403c0140d03032101e54850807646c01404481c04505510004500d8800e02c0500042c66060104090035810320024926a09100762020044901e06d034405036142d0140c3d0000c580425410310110750000990007040c1c411071a10a0f03910140058028600120b480300f03001550b038140346040a109141d024816400829a46a2031010702c58032080001c40e60303c12484440d040180121074002518002d40083d03c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 18547686 1250 18546436 18546461
    0x106050a0f11030409020310090e070b0a0804052b080c040f0510020109020d030302091804150f0b1306030521040603090312050901020a0e04021603032a0201140105010201020c0a020f0103 82
    0x5569040007042c0e551110118054000300510340400c085c140c00e00099000300b100c00a424030dc0c14000b444100b6100b641006000b6251402851035490441c80d90410020304080780d84110420038140d0800103003008402000c907200b4040410041c40410011000d00701140c4003102c0c0c501e1149103c100c1203015242030b03540207410411060400040581607009456050390a981c4492550100b41c1401d200c84000e44010340082c0c91403800c1450352071190007a8030755107020500402c40425002c0890a942c0a0f100402d01c0180e5404042c401c00c203003800100710320300d10710509109a8045469003a4948101e01c035410905559400c08003c0500401d00540002c011140420143c039004803218043c0d8403098070100010f440402941b0a0700c1c0038402e9511940c000c50644010154640d0242c00a140e00a0540720f49000520745507000310030000c080e00b2544050b400400c4040b89190f00d2042d1080c1a0006c80c151390050200c0c110035600040e0f0841010f030111058600c07641d6480c01a40200300e400c81c0071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 18548936 1250 18547686 18547691
    0xa020313060c060b1c0605060a0308070503030a05060306090c130b030102030a0911030a0305070f0507180603020307212006130e0c090306010306020a170403030507080106050a0f11030409 82
    0x3407580e00440e00d22142401528203100310140c100412092101c00c0c10745480701c0c9480e08030180454602c1d80300f40c1c0c0c0940e002c1d04900c0400d071603803a4514213800c699000c48441e80b00204000030740c0018026203411403000e078010001d90801035401500e030f10528928602641c4946220f02900c003664200841280c00078000315aa400c00050f0710004d08000207058030860101c00c2100d03100c0c00e002a460902580654403182840a140d032007141030804480d0680e8517105201c0d0200b142121501c082143e65809039000400707918510526040030078035440b40c0543e0421001c80485d03102c0c6002c04601c100d62002482c40c196030171300100502c4440c200102a007000c008034485900c0e2404068600070780e050f0303540001c100d0391002e0181c625486195001501074100400401c00507800ba0080c1180b190720741040da05550341d0325640e0b08a940121410f400294458042c0039650b40c010b02c0d03660141030185407081c1380100700f40001d00745080c1c0c40e928004000c005240e4003103003401801903802070410540c6c00e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 18550186 1250 18548936 18548939
    0x4051005030a060605040602070611250806010e0403050706020c0a050601060c0b0604020a050906070501020403080f0406030c1814030c040203040b1f05150a1b12030f0603170a020313 80
    0x1000d41d0000c9604554452502c180468528041d40c02c0d41c00712a5294014410390741810021070b2004030030300c3c00f0301840c4603124610381c4d50500107080082c010703074001c0d4010702c0e586440080c03440c02c20103134882c4084081d07030410301c00800c1d480007c41c0c18640c0c20070b402582c1d980e41c04d2040351401c54003140240240c000d140c00825081d50103c02d5901c0c050040150b00c1e00d40e2903030010003049105642490300030690400c01d600745414508007400c0d8040c0210001401c0c15901c0e1240c580c0b50303000c80c94080f80350100040501442c2c0d010b101d2442102c20300d103001502954089010b09182e0080d009210b041c4001c06400f001542d0100407080310290050401d5480c0d04246c0742c48075030b803001680d250450411303400c003c2c15809001d44040d0100c3d14011b01e8440f01e800f501c1e41d1041c0c1070b03000d043c125080000c82d413070721140503030907400350140d040c8100307029a0007007100710004045a06525120040030704104042000c80c140020b0880320040b216222a0f0790882004160714511602c101040c0101e1300050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 18551436 1250 18550186 18550219
    0x80a03140901080a24081605030c0907031104080105161103090d02120c0316030201020c1008070806010e03010c02070302130603020603040209090a0218010608010e0903190203040503010e06041401050103020303030f0c0405 97
    0x81c1007850306d40441547e10050340f20410143c9840c1262080c43d040307016580065001c0e803090300890101d040c9a004245000e8899401500f500c008441c0c00740c0150100760b1074030b0364cda8400c41040e5800382403000355040c4503103c3d0004100080018001e441400c44003507034800d0b40424000c0810240c0b0040869444c0b050200303551004424600c4240c1c054010914444220709083d1154074145556686038a030a59030700c0e806460018000d4840d03410418029140d14440d00c0900c01c00602c900300e44c00802400c0d255104000200d03c1d214030103011310f41030060801c0180ca4480649810a90448003a03c403a662149510301d000384412000e91f2010007a02078032603080f501e04441d0705070381e100c0e07491064030381e280d411000d1103000645003220745900c100200307002c0c1441c0d41d5040440201c0c80c03041d2460140d551000900752490b410f08a0001c1e0450000d01c0b082140c000f00e00310303a2083c80c5000384070a600d560002906c1c0c0c0401003042e6084504080042c0d2030013016822100541300050a00c51040c100342c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 18552686 1250 18551436 18551443
    0x412050405130617010c0f030c02010b18180d3005010b030a05010806040b011211030f010c031802090105090403030902030109060608060a0608060112020103020d06080a03140901080a2408 82
    0x1c40c407110f146020300a0880004e042c0181711000d41c580e22907460080c40818110001c0c0380d455461f1045559810482c40d141d501c103082030304104c1d10705200c148a4181a0514019404412089903259200b00c024a0b002c44e0031491081483c150900074910b03030800e488103800d03042501602d00d001c1610700310011611003000400396006120602080003136a880d51102c43d940d45003510041c2c00b06920b500100000403101034220751880c4213200780c3c1c22160102000c2407a0105000500c812a5100c9481442c800da0500c0b40c1040c1100744441030400e8265600882c18260341070103050300400701c00c00000c05040c040d4200e041c89590103002000702c0710756414400001c00e8940035660460080340d012070903403049400340c0340540d20500082c00d156460902d0105150b501050f00309d05140d005d01080c01103003154401c5800070b1043c10040c0210f500980740c01030802c081c0450031400c014051103458a5030340e108045e00c0d48248042c0c1e0029145000d8070300b41465076085030301d908009014100c081180c544c0030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 18553936 1250 18552686 18552689
    0x50103030201140a020405011d0d060c030b0103150e04060203100b0a0f08060f10030513020d0b10060503010b030f0a0905010207110a230603040303062402060f0c0304120504051306 79
    0x1c0c180f0811920740806100c2644038a1040300e001403001c0390441804e200050034004064001041003244000c030356908815109108007000101380e0710300c04102254ac141c0109024440c859428098035800c0c6004aa221a0050310141c0159408000140d8414103044440040c0031030090480e00d92010300001020410600d4100d00001c04203000300b0814140442c6c0040c8a0324014071413041d0705601a4100d00410000b4402d0803034001080504001d0b823540314100380003500509009100d840c1c1041c2d0311004001039404101041400c2004000c90f654040507039402030380c141c440007941d4940070424400f40c0004031016205503c0001c28000b04a000014842c032a5015600032548c0c0343d84220414503581801c01e903141d1101c80c60682081c80c584100210f500071720a040000c0c0346903e41c0d03800d6991741e100c0c080e41c20030745100c0c040d9106440c0c1c0400c0b00350340c080e00c81d003c0c0d2070103860300d4000c0400a0201030001010000c8907141c4d0340c0785c240104103407006410090034001440544030b41d801c0180000c0e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 18555186 1250 18553936 18553961
    0x304020a0305161409010506070303050603010b0a09061a03040507030611070c060f090605090a060309140d05030108060903190509030f010f0603060e060403080f09010612080703030c0c0302061f050301050103030201 94
    0x8401c0300c12a2420040f500d14102c880c020040c0b8149158ad86081d0083d110003090300350b06541c1d500129130b0075594107d1000150048000010f9500c0c20f08002c002d80980100d0420321001c070500c208030000c1c038001052410703254409000704400368240e1100440b80102000100540b40e51200810203540c4845094240405a510030002c0d039a103602c16202840b9028a20b50071000e101000c0c00010300079040400c2561148102840b10112400d0290400400b040f01000085000004000c011020071003140c0041d40840079500d805103c0da17150701e00c80d81c40301e00310040c807401180300540c0d50b80910069040c0e4819400034844c0c0c03591214248008e203564002114144d03d42420030146280004207148500d07030503240c0340056281c107290340028980c01030580104e903407940804541094103a18418845109100003529009240b60203010b464440384400b04110302d80b13941d1000b0a50001d08a90800d11041c2e94030241004c80380444206012038100035059800c14000204141d81503224151403240b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 18556436 1250 18555186 18555209
    0xf0b0f090105130c1a040803040311010212090a060c14070f05010f05031608040c1a0a110105070801090209010507140708160e011404020909040f02040b03030f0f0304020a030516 78
    0x161081110f81518080c0b001a02d8a00743e1001405407129a05031044a0304c6480d4509060690302c240c454603541c41070b001255801d44105401c0915601000503191208061180508210702080400c0c3c0504e0310748078010411041048080c180041211158207180e00c80c000d5510498503496a03804104491044500103102e0000329581180304009407801411045002d0803404581001100d02c21006442500d80003603010340000c0d445d0707400c803800100c2c410050b5055128219803601400b00700c034107400005203904040030400b0b00d07a800308401e815101903000050700c405103000100c401e4011101e00030301394002d80140751401d480008543d0200c44000c0c1c11a051000c640c1c410640c450001e210b1041d501056000501c003104801c1601c0c2140c40000d440182011b00110002d00c110a0aa80658108500c440003009504280c041c144940500b07500461405000705210b01d124811140c02032403818011003c14115581c0e002000015030304a4102c510401281410040d101070510540e0031240 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 18557686 1250 18556436 18556441
    0x601080606070b060f061b0106090513020306040b0415090302070503010e0f06010b0a02010908030f071701060e0103050a020c010501032001090b030112050c0a060302090a0f210f0b0f090105 83
    0x80c0950840c2d1815a21219400c4251140800d026500010000301503000300280180b801280d5402c080024a881802c008a4100e00c1d04180b0000c690f009404007451030450096100961400103499420942c060b0a620442d901c50800c00114a40f00c09000100d5060500200606074005600c10548001701e0080107101020080140d690000100e0a01c4a4020710010018102d55a0180094150900000c141c0841c25500c90b1074a5100b140c500c00400014801c2c081d480d584001c503d9844491001d42159550601c03001030511000f030a0380e1810142c40740c0000c0c80b034149603015a0399100316600207001329612850405528581c528030b00c84100318803028005698401d0a9440c100c851140e196451a402c11031502d10710100d03c1310588191241281c041c41e1501d4070601c40c0010000d560300162a00e0000040003005000399104018800c40e102007403010483c003800c800380f00c80e1030019104440c0407501c4c0c10195501c04540141940301240c0401ca210b14000c900360b84904011340c000c000aa = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 18558936 1250 18557686 18557689
    0x6020105010509150108090a0606030303140a0e19030c050307030201090311060f060405060f0315090d0914010c1b0603060510050a08060f010c02060304150e060403050909070507020409050606010806 87
    0x3030b8111020082d203130740800c00c0b0342154082d02886403c0800300e000e0700c0405070b1517212002926040e510480001e0f0b5515000c4404e43c0b07aa000c8140c008024000500180d8160b00d03003a983c5a911020170301c01c00d0505843c0d40c0825004a03d422280e035445401d881d203030f05d802e00300039000707000c0504148e003c2071541c848520403440108540e4460b04460461490586a42007484000c040c02400f041d04a0301d44a04001940c0d0300304000c1494a0004030401d030249480c401c2c0030b00f89203084054900b40006c2290521021034103100c1d45031808028600800044014108134802550400400c088584c90703580204080b03500d40c01c1001903402c192285042c030b240d01e460440741c900c81e4408510000ea40307000414501d00c0c040c90b82c05601c040502d0140c3e262100c94000602c80c1d801610102c3e401d40301e0091181c1d611a6034082c043e440240b0034060b000c3c0d40346c02e490141181c850311100070b1256010400046115004034295514507030060010807003040315203010b0b0b544034002d0358481e02141007100040c145 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 18560186 1250 18558936 18558949
    0x31406071b20010306080609100b0102010209010c08090a0b04080c01032901030518121207020a05030a2106120c08030306060412060b091e070203040312120b03030c0304060201050105 80
    0x40c0d80d0b020885280700e02d80b0744034412640d0240c40e205030402d600c0c5c0300300203110f080402a0303502412040307001c1c00d61001c200b80784004413200b1401c2c82703055900501a40c02035070b811075840000f40b500210100d0752880040005510240d40d03400011410750040f4010625150002c0c40740d1042d242a02c0070840555100644030310b503908440003040c20300d5038103500345d1b04d075202c2e82103290449a540c001240b1104800c641c203062500080300341c0e600c82c0b804a465102c007154640d1080e0480f442d070000c0c00c040b589a1704c0303c1fa2244600c480e614280f01b4214149041619919100007903111a20002c1003c0d50300c0e0510344082c905503940c01c0e281890f056a0210301b0b50b5011003200d000d0100281918070b800c0c900350f6510601510500b05a91640d9150300003803040d00c0766033582e4410f09d80b6441c1c410141c0101c203520355440e43c002d000501194002e020900001791030300310688560010b41071450080c1070b4951010003812113000c0c9a50180030104000b4005032002028109445840d00248883d0381c80c2c0d010b1200c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 18561436 1250 18560186 18560237
    0x30c0d0b041e08040501030b21030721090e07020c030a0308041b0e0a090503070602070c03050601060504082d0a0303020a12050405070306020906210103020a050108100e1003140607 79
    0x1403c400b00030070096580650300c0a140a40c1c0640442400e481da0755160f5000b105c0c40c150701246410004030700c0c00300300300b084a000880c618015000514040b1040081c0b08070b40c40c3c058010200c1d40d180220f01c20038000c0280e1094241c00901722100310402d0b1400a000c844140c2d02190a540217660034054600318410701001d072844a440c542c0503550300c40a8001070070b03110f0819a0b403800304104400224405000070034020f8007070328500395280e1852134900e24120050f4401c40c00c00c0401e2006215400f4041a08003100c50311054000c0a40d42c10450340f6548990000c0c3c0c4080751062941d04403c050701500502006032090300c1b41d010541d0741c0341c41c1d44251642190300801e642c200c1003003480055a130341d01910045001070030060034541c560958641c281c0350070541d6801400e900c40100308520b4029040b02c00b81c8402e203010401410720b8003d00f66803c1d000d0243e0b82d0700d4040c4c100050460209105110300031904480f0044918490803c050348443d4141d0b20800040c0b03103580204164000c01c0e028a1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 18562686 1250 18561436 18561443
    0x30218030f0c090a110d091106041d040c05040e0a060605180a0905030912010b0f0103090f1101020309060d091b03020105070602030703150608060108070923030c0d0b041e 75
    0x15040064410003070310f100300900c0d8106055450420001018024001c1c14600000311070008201445040040d060080d1000d585e10420081106104980d050030b0b0b601da414046420401c00f9454514040b00f001603903400103600320307140c815405072881000070404e800500131002000015180c80c00e1107226907590030141504400314001c00e1081c0107681c0110b0b02d840c011402d9a080000d04000110464124005580c81d60344072041e2404a01d0804940e048985003400e0801c40c00416541c0d4604074480304501070700e400c4102c1c1c4404c00c2e40c1d0085c02102c806540083c480c0d551f8202d050182c80040910300415240c001c03105501d00c1041044407080c0003a241c05031906400c000b581d13a03400020390f000801d000101a2100d41403128003a180d0441c0c00540b089869500441c600000014100c100c014200310410101c0001040450844035040307a0494400f1000c80b1061a0400840c0c40c00c19016034858106e0ba40c000050b060101c0ca09801e0f00035889a00c040300c4c02d001461109100690032800138 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 18563936 1250 18562686 18562693
    0x40f1802011d091603050705040f0302060a11010501171002210a0905060106050a020d0306150c030207050d1202120307080a0504050f0a1209050409050319140a030218030f 75
    0x80550300941202107860048606201c000321200b02240d582c1030306944c000c44030b40f82001040e20860301030003031039403002c4140340c51814240341841030100034a8074440a80181c0c00041c1c500100c40c42503403039140c0d81003610028459541c1d503240031130800400d0003020b20036005032191200500c41d94008c031140740c1c0040784804140031502e03e200348030a034060b00c0030420540e80c0c0c03001d0f00021802d0140034001c0425865450301c130703000440301a05120050820b6000c2521f060ba0a2040010755401d58020102c0c5141a054501c4640b60a03031a10344550412544400c03695280404c10484428000888540740d084d1a00310084925400380d60105441e1040403414503000038104500b95400780b540a0b000e0022140d080007043c1c2e0460616031015001c0d41d0140f0a21030785801c0b1034024100100038003059404100324021a1240d030340ba80551100c00800e0b00e8410481000b8500c00c414501c5910550000260f0395001c03500064000d500800b8070407480000160080c0c031070724011824003001c00c3d104014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 18565186 1250 18563936 18563981
    0x7030c020c0a0e090f060406050601030b09040b0406050703060f0f08010623040b011b05060106030506030c0108010308090d02060a0305010510030207050a06050c0d020d050105030c03060702070b090f06030c09040f 93
    0x10b43e6644000034155003885c403c50142820340d01d4200f00b0507000f5402000f001a8a00380403000400b0340d0030120a843c0a42d00e103005200c0002c00703c18003154010782101000a0030380320703404100d0180c6620341c0100590410850040b0701d80924103044001c07a4107560081002c02d82d2006000c074081c40401800c1205030243e2081d18460619410503a00290140f5100c0c00042a44c1024402c2804003042030740d681c0d00060061201f182c051154a803c00c2c400c0700203010900c55800024652901404018003108021895110a40361180034140c2c4690061180e6200e40390100002c00509091182510451032003603c2d201c15030191080b980c20f10382040180000f4201915a10058a4054034079012003904012141c600440c920103041d01003040080820f0395450034040610b46103140b001a4401d400180502c40074a0300040c1ca0812580c040e0742007070300c8400703d00000d00d011b20100011a0420000400c21a5040e28035000f400f40c441e08a40401191060000190481c0d160500000781030741020030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 18566436 1250 18565186 18565199
    0x1020c162d0306090203100507050705010f05010819020312030c130605070804030209060109030206040b04050a05030c030d08090a08130503010515060405010c060e150403020d050a09030b0910050c0307030c020c0a 93
    0x80b1303185800601292540c07440c8288400803944125423142c0002c1020030100d080003000c1c0240702c44030034840d1090145504111744592503c0649006868250340384490500b15141072061f4100320032000d00881e20b1303103003440b003a5083c5e600c1030788080c841c5400144041405070042094039807068104800500b030a0841d400c0c0080b40c00042d16140c148019450004010303a00c0e0f00062000d404c0b0000f04e1b40e1107074604800c1c030000c811250440c920175049aa050809903c0008004c40b00c41e18030f142040c0c40c2d032240d0302e046052500c9160054100040080c005020700d12641501c1c00b221400d0f0001c02282c0c0e5400010810200710301c0c2400d40c403032000c000801880d8812503052070000c3c0140c00016114001030102071600030258100900310350000100802c0c560140250030349800d00d410720501d8500460310080c40041103000041c03209000001050103168204a03603100110a081c040155040844094102d42c1081f581d0500081c00c2c0311982c05000d101085003140000701a000e2006903003890b8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 18567686 1250 18566436 18566441
    0x106020303011520010e010c030603080906090111010f14090a02011e02120d050f0c0c03071502120403020703150603110d030c0507060512060609030d1101020c162d0306 74
    0x75040c1041000d040c1e03104504a555a0880b604456100c1c00002c6c0c185560480c10300355222030f24000c09140c98054200046005013048400b000310440e5003595071402140107880c801e0300d00340c00c0c3c0b1480d864001c4450103104103a1090602100790001c4641715941c400b4807590715035512030b00a000a0b0f81e16403a07001ca203100d10100100301e40c140140d800741913650444103003940215a0300c20f80152100144054a01d128811079003010454105510340a91140c12036507238400d805004004101c2038890074444203843d4140c41c15103540304402c09048c102410000e58900303450101b982c0201c0d001b100801183c107a4800e640403203030302c8842100c3c043c98542c01c010380000382ea1000d40500940e0040c99001a80034003000300503007000d072100c6841d101141c410706c0111a006200700d0240c0000c00403850aa0b0700000c0b000580c00322494560400714400c01501e003e400340314407106040c841c404078813050038020084075090340d034809000b0340340e02d1004000c400907000c0400501c2200a20540c14004100c0a8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 18568936 1250 18567686 18567719
    0x10b09030a11031e030d05070207031703130204140601120506010c11030a02030109030f0207050a0b03040b060d0204050c09030606041505010c1b0f05130903020303010b090418030e0a06020105010602030301 90
    0x1000d86624808003000180d4141c0c60f134540740420b401c0011031445504a62243c160492414402403181504580e144c1e0308129a0224078140740d18003000143c5690914000300030869405402444510300c05a00e546c107820307080d5001804644007440c07080075600507204003403082405070f5600300040880e44a00c0d0500c03424a07060340e050700a078408680917031001d00403070202c90711940c0c1c0e18040d0a801800281030101c41d400c2235104560301e11042000b940c007001900d81250704150030028036118400001e81610184100a40060030102008010011780d400703000301020607800d0752203030f507590020442243c00e00345040d5108442200244059482003a140525920550454103046600740f80e50040700516800703804400c3c0411424802c504000300c6404503007910903000d0081c940190360107901c9000501609209280203d0b00310700940c3e407a00180d0007810600c240240550260800070031180c609100d05000321462080000c500e441445554126031007a800b441c00c5908110300f110546002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 18570186 1250 18568936 18568939
    0x50306071d100512040807030807090305030a0e010c050d02100f1b08130602030f06010e0d05150907090906020d06080f03040b0702010e091303020f0c01020705060a02010e10060e010b09030a11 84
    0x900209500c00001d13003402c2d000d2401030004d02e40380c2c2e03001d20300108541c40091003002000500d031010400030700000282d0b103143d061803c0c29410001100700480e404102ca9901504501c80e90f0180100070f5000f10b544200300d101c9040521000c00c91980c0c030b02c15924101c000020500c0070041000680f0b01c10002d860b04032094003c6194154015100c460507030b001078403074210301e860f40310501281d580c2008000000c140160740360005d0039800d84415480d0b50602c3c072903800940c1d401000900d40c40042c08410041c000305c0304100505901402c0c1000250807000411507914034098010650341000904054005000c0c2c00945c9058149a003402c401d4114810890520a125010745c0181e913a03a10101d11070007284549181a03d42403c00a10b010307005401c00059400015441140d039a0125205050f0342c0241d5001755543c43d617520480c01003400035110b07a80350142c0000c96050f980c2c2d64200c10120340c15000c0349144c6da43c0314007101119101d40120b26038160312080520b00041c81202c40780c2e02140b030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 18571436 1250 18570186 18570197
    0x90105120703090c090b01120507080a0e1603030201020301050f060702100302070c030804030809010206070f0c030c051e031803030901080a050a0b03030301060e030708070f06080a0605040c09050306071d10 90
    0x40725614072001c1226070300917280e81a161100c401c0c19590201034080c10190800080c0040c0c1816038001c3d0002c400038203045c215540750100706203208400c214001c00500e454a02c846e00503901c6c04d009000f07400070302800d48105407a529400c07840c641001583c0070b20750002c041c148503048200040d80207600200080310113009444c0000f010074403042c06440118040c0600640c1c400008000908110340249038600b1f0010300d1000184540e0320048a0700041c1d0f241c10084480c0c8564200f0900d4940c1070400d03032b00c0b1541d11400114983c1c04c040054030518007419180c01440c040313070082644078040c000560b8000b402c40c100044c4070700d009801c40340d0030005c00d0000007081007030315011034110b40c0240c0040380402c60420300280141010403003000146441030252101c1030415405600c1c400c0395224050402070120081020a00c1c6a80400010140140200044c0c8071101c80544104584d20415129000300000110098000d4840c2c0f81010480d84880c0951009801000071104440b40207108120 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 18572686 1250 18571436 18571451
    0x150903060c05120609090d0309020402090904030f090608041511130801020414040501031502090303210a0608030a08040318030f0b060907020d0e040f09151401060203090105120703 79
    0x12141d00c070340c030103030340040d030316140e46901c42e50800603250b4020b05150b01a24040d0b003000000d500204d40c0e1103907042d1902d00070814500794000030b07002e03005000103698400c190509000c205a00842c2074084c1007885d031580b901c0940eaa420581d43c0308811940074240c4080b030004952244600e50042000d0882d0245803030506070444118031008410384c000c4a43c583d03001500f8405030410400504a225003242d050040d07604680d508510509641c40c00303085250081103d42e03280d9028000e54440040036200003404950f184600c2c0d004038401c3e100000c40625010300401c0d81040801111400d0140d9114160b03e51501c1d94129203507003030790390b45e03550f1440d80c0040880000c02d000c0901355001e000b00c1189455061a804020701101d024086000351340c083d400010480343c01c03094041c0c102e03001300c400052002119010001a00340c1c0c0400500c044058031581403000e402d40d000c60036412051900300c6c200c2e80c1760001aa5244111042d085c0440e10a01000c111807404009140e070010710f0b850041070720f4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 18573936 1250 18572686 18572693
    0x9060606171f03080c070e0c0a0c060203070509120703020f040203150f03030c0102120406060608010509041403040e04050a1a0105060f18040c02030406021c080a0504060603080a020f010b0306040309150903 90
    0x790003286405c0d2094111810421102c414020942e8208030320040007403408020042c00380a1700b0084400401d8503030007000241004e03008909841c4002c0001e007100e07140075a807801ca9a00c804941c04100d120700c80c02c45169056050603c261ba102c1c01c00950b8018503528070400f0007034240c181e40c2001c4d605200c200b0000e030052100380090070380903600310307000b4449007801e01d4440240e4029030403030320412054000402540e602d8001850b006038200c4d00481c04a145005d40d40e00750321450308002a440641800c1c441044000900c00c0c2500d4003c41442ea901228040c07200e00042080c451240c0c845014081a5103401c0b45000400e2081d001d1030041c0b042a04403408038007510480034000c005600302140801c42c8030340601c03200302d0921038641e602c440000d50040c0030703048610141887c082c16582d1400078003000403d600c40c80103550092010303038441100c3c5500a55030f00184422840703d5007440c0741c0300d4850500003500d50003aa0300da11000c141508080200301444180703d4281c007003022080000011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 18575186 1250 18573936 18573953
    0xd060b151305030601080f0d08130c03030509120601080303160210060608010312030204080304060c050a05150604060f0302100c05120d0c080f0402010e0907090308030a09060606171f03 81
    0x48401c00c1d644103803103454901010704184050780209502d820003540d01410034408510000301d00e00310f007080c14a94441c0c81c50181003da940a00803d80a200400401490f0704840a000358401c00c448510030003600715140e036141c1c00f081c440ca00c1958003c3c00410701101802ea081302602082d0301c1100c01d0901c039080900c0965100354003a10109055800500078018818103106c200d40c807d0a045d40b0306840e04480360780d01e01c030720b11a90341003200d89502c0404010051190340340a03030300141210948070366112a000d0005081d10002c3c42139190a030f0014641c07046015020840703800900c1c41c1400511880256407500c0101d42c212084c1c040c04441010500b104400390070f400e554003c0000e01c80a042e103001c1c080341d801030210302450625400f0400140e92064803007400401c103a035058150703140c0fa10156900c50140e080140308460100801c42c1d4440e03207a00501034a8000e6105201090380d52400740c2e002d1412510450754001440d00080200c4c0341c050310403022102d610441c0c503525680b512400310 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 18576436 1250 18575186 18575197
    0x10315090903030b06031003080a111c1806050403060209030106051302030708060906030c0d060e030c1005010f0303051e070204110306030f070803040e10030501110a170103020d060b15 81
    0x41155a180000c080c503038036100e00504c2200907100146036050120308007514840512008110040004403410014407800021490302140745c121055200e003c2d15003000081c1c603030909000100c0c100344c55905100c08e4100c07601140d4480d00c0da24901811a00c6600195020f07034803071078141d9251b9800280c291100340c29400d0142d00d0400050316400c007510018400d1001070300b07940c07296218000344082a5000728500035120002c5075151509807140c0307424400741c11000d003004650700005c10707a5070882601084080c6a0344240e90100606c2c1e0708c0e80484442d0f40110301024001a205008591090f5070100f2810681ca812410340c40c10001154001019605510910500f24801100b40301c50f40c05c040100c4000000100040c280f000d050402c402d64901852164400c03500221011400030446540f810b406550880002d00c255903012100940613400b0b08041000514406402210b21081a0943d07045c2c0f94000c03d10321202400d81c45140140041d00c220b43d522046c001840d0085880d408028007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 18577686 1250 18576436 18576449
    0x120f020405030a24020a12020703020a020306011806080303070806060f04080a2a06050f0702040603020319120824210601081b03060105090c0403120302090405060102010213060e010315 81
    0x80e28505803001d04d00d00e1815806140201c07030300501c00b0324082a00108806904a840040143c5034801c03800c00705c0c54021a448007030f402d0b01400740041141098140780c86401c024801081c0502c907990000c49950b4031089803841c00240c0c0c404089a80d03840e182004155a02e00445440d007090b8a135036106003881c01c101c004640c201c040401085194a000304040d0004007405c0f51326040e1031603d50080d0151042c0300350310f4040300e40000d19204641d503644c0024003440d005021181240b901d050b558000066900f01581c2242403001080348040c410041a445103040c0b442404409840e40041401005500340003a800440075085941d914100b10350282c3c166001c500805565140120382c03401d0a0300d10310021145a0000b50880c0c45460004110741100c0082d030b000e003d1a6600d03840c1100c2802a904002c100f02c0101200ca070000354160068052a00e0031101040340380c80d80c0d00164200d1146c82c94005075050001d4040203900d01a603100c200108040c100071030b0444150002c00158185074001c0d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 18578936 1250 18577686 18577703
    0xa0c06080628180209090411060f07080d0e0a03020a0605070311070c030b100e040803060105040e072c031b010201020906070614100b070b060d02090103051c03020a120f020405030a 79
    0x2c210a44921001000b80ea4603c1c81c1140750017220404100480001000170b0189007200340300e460b00f80c85103000c5401841031801c01c40d864042d00e00d00b0940a034010910310900909040711011501c0b401309628010540c035400800c44414242c0e1580040c14000b0102400e140d52a04c40061208040000341402840b51818440c031074158580f00c07552540103000f1001498031140148840820080015003090b0030005079520707656070000403203691240d1781003080d1f642d041c02c051040715070300a0500360702c80c3c208041da44107840c04000c1411508040360800c5915520050a030b05a0005001e01d41011000601c00503240490a10102e090b40c0d102c0da40071210f01d60382c0d460070703040700c6080d10286801000d08002d8540c001d00d06000c1c600396000d101400b500c0b0310f8101000c20540e680d005640140c046c1d02500207170196949041407621103c084100c0c4010741003035a4400030040c403030310031120395190725210b5140781561046d1400c02400c0c0b240c1c620f0001d60382084082410768040240d11409031180210 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 18580186 1250 18578936 18578939
    0x601051612020708060106051b031303030c0b010b160803070c0203060c0406030f0b01050406050a030209040908121501080a091a0103060b0a0b0a0e06220305010e0f0a0c06080628 78
    0x240b910f201c070741c4600d441d9048000144030f8203921504980051140f41c041c035803810544400c86040d482012002405810144000400c054000088100a0b4000c01c0100000c1c0e9803484146244c0c840c54a24441c40c060380028900010041c0000c3d41e0000954581101051060b901182c607007a01680e400384215004501000055070500030107501241d1840309015803448000081e119005902900082c81320206174840300f0f0b072083c0d05682042d00014018005c44405003080c4259902842000a8000400c4009441038880c6104100c40c030308d040e036031511a5683c0f00f00d118001d100d00324040702d040900c480c00c02d920f9030b00711081c18080c50003080c0c0021030f420500100f002c032100990103560036140501000e00920340041654241c2c100a50b0310f2a0b882030b801c00303100d42e00d280c000700a805056031910003100b88081507000c0d2101c00c00b00c80403503d19640c101c0c2c0c020340e240148007008005c00b600301828403200344a00300b6160031440103083c0188004c0d0415001c11030714055103090040350080c0e50b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 18581436 1250 18580186 18580223
    0x4060f0504030201020c0c030705030309040c120507180501082707030f15050f010b0304170f070f020901060306050906060d0b0307080d0801050604030506060d021f0903060e0102040f0303030506010516 88
    0x1a039810007c03c0300201691450302000c29200d00403411300910441c1e84030343c00700841d130160600070004005404200000d1809480292419114400c0765103801c8644002144a501614800d4021514140b00c0b01c1000d81d141000016040580500345c03403800ba880c80080082c031980611342210348210419805810303008069011180000c00c035130b00d111400001000034031096005c60790031035000004403c904c0c507a030802036001d00c1541d070442c9107400001209001d016005200c206054401c039860030381640c0c0c038003040b07007074600380e0043e980e00030300b0718001c51410b1500c1c000500c074250048001060022010740001c0c2003400541c00f4401581004150b02c06080c0d109150502600007211410f00f81400c0d80c840076544ea00060245004844035070070213040d0b540d155450900c4800c03104481128403503000c0e000b8140450f80c4001c035496814194481420001030090304d040e14400303545004241e18581f011005800c01601d00d6051200800c070b03003814a001d1021000c02035004002d150501c0a0100c07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 18582686 1250 18581436 18581443
    0x1002180906030a0b0408030709030b090a11010503090c04050a110c0a030809121912050a0e1011030f0a090803041a0f0103120e0303040f0806091006030201020a0b04060f0504030201020c 81
    0x180681c2c801e4004021030f01c0010f00e0b2902c42c9400c141c01507040d6480c1d0740c441c801541d440c1002e810140c614070032001000400c11000070140c02d01c0e841190440c10a0200b480190380b103020940d1680e04076040740380902039506043c0c7c03100e0740c01031070550041140101071030741d07081c00d90008143d0040358120303c01c648103064100e0601c0d500480e24000a0600115919600e1340318003580d02c4402100000c410070b03200d201e21441c070700001d076403c615080015007080d10710031000b00503c3c100d0f403503070780500441c4c0500340c015441401814480c590700f440c80c5544885805d00171010080a907180ba680e41c00e1000040b54141c0b000e1132003584145415541a040800d00707403c1364a0080000044203000b100500004400302e01c614031656a9051002c5071030070010000f411402550004403100b1041040040c801900103000c40c0200c2040d02036030f0880140e09001000c0d61103600000e03015a206c0c800000000d107100c481c55502600071040090b00014801040f4103688068805900503034000c903490b100c00303a00f032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 18583936 1250 18582686 18582691
    0x304080c060f0606040e0406020904051006090b090904030f0507080c0105010603050a09050c0105030a0209031506121c050904060b0c010b0a08030406080a02160b07050409140118090510021809 84
    0x1610328020b80c504080021340302c1c1301d18011014449400f00104c1c0410902e501683d0b40d40500601c10311a6181811124544881610412002030343c540030000791094018211200c941c0042d01d009403560326030700d090703d036000303c103405030100501005540c01064082d8081c0904114140000ca45545800001800d84901402c615207081c0b901d00c1840c0007420000c1c0c075000542c001c5c07c0031a101e41d5040d511800a005d02484260107019182c0c1c4d01d2806c074800406240701c0c1404403620305141602a0b10305540c3c2c81c1101c6403035011000504c101c09224021006407104400c01007001c90341c0c80d1503224203031880c0c000c0700328060141e440382c040d4540d6140005840c4094002d1500a604241c030780b40e402407101d10042c02440c0e409030f00240480f01410500c2001098a0b04240b8441090600440040c0f9a034050303c030f0340070340d44d19000540c040c40200d04001c60407240491104400741440790502c030010200b020085a40b4132440d40035450091940c0003505450400e490403a00809141c014000b004800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 18585186 1250 18583936 18583951
    0x507090905071706150d02090a09050402010507061119120c0e030c04050a020705010204030503030f06010c2001021510060e0604030210051602040204090504060b03010504050309010c0303020d020304080c06 90
    0x240310030010b203181d11040318002c1c08802c041420058407104046100210010100d070218000015500c00f8140d1580040070a0202903562510060f07a0300315413401c441050320024002082000044046050b40e04202001018503100503d4001c7c030020802301503880e440140042207030b00d0a1015010068800d40e902049036080590485020500194640e0318108260f48115031350701c0490807046269069406240d4024021907880d500ca041003583c0ea00201c54248441f01c2d143c0010702103501c00d6080e8003100f035015080a42540c14450030b05000401e2035071040c11403017801b45224014260b010514068000406025001420550000c00b8880d2103130485000381020441040180c90b13000d82d00000c28450b2a0258580001c40321a103c501100d11020303501c10f00100c0d01003098640c5034881c90117a842034201f04400d4030303080140750aa0b01c00711b0b80503211f9001800307481019401500f03003140081c403034500146820810b071001c401302e800640341580c0e02c40010801810b010000c006c1c0b41d400c10342 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 18586436 1250 18585186 18585191
    0x60c020c090402060a0516060c050403020a0f0305030702090402010203190f020c010215070c08070c3f020609010903050106030506040b07140414010302040503030a1d0109060203070219030b0a05070909 88
    0x8080d004550780c0d205c0e0b030603d6000c120000400303c0c1095030040d0358022055005030140294800030000401d25001800140d103c0c5004240000c2c071000d05610340d408499001024504040041d0204003508100820070f80c15400200100003440201c0c4886440240d466105d08143c2c02c400c0100034605600f100c98541036503c00050310100b20707000e8064550084042ca040343c040c1400d89080c030020700841c10000c1183c113201c04041001ca03c00c40c00c0e1645081c0507052000700d04510f039180403602241c00ba0485c1aa0181c490303840242c10700c0c200400c07214806050054030a80e0303c6e55170302e085038000d6005a4484c0c000304240420040248803050300070300b442c41c0006002080002d01c0c042e43c891441039603440c1080003406e90350307640030390160740c01032030020300740c80d140c541030a001b5020000c0c3c001c1032601c40800f117251a00d07a60045031050706444003a4010350030005070750300348a40209034282410100000c980000001140f02654030b11070007001e0804034140c240700d040503102d0391903034012910f080d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 18587686 1250 18586436 18586441
    0x120f09010c05030a05060607021503090c04110313030306050a031406060603011d0405070b04090b010f020115030204020c0106030204020712080108060114131104080309010905061e2104060c020c09 86
    0x2a0b010007540c0d000125100c0005407074452400050042c402c01c00700039003102c03074844500d0715101c40f14042d5100c4c400b90025104400210810481211030b00155541b4141080c00031441510a012030000c0561181c1000610103481d400094a110480e610403204000500e0804880e084203100d41608540183c2d4942e00f554140003628500740b180e410000001c62600300020244001007085000909640304491755403612124004050503c101035540400c00100841032a644140b041041340106905151240c6065508100203503000c031441682540d21244084056a6148010302c0c82911580c1c2d0054084092040500400710581c0f003e01c00d41c00640042208c91038001e90742070021001c603012100c03080484d500d000249030149d06040c54041c04140031810480001c01040d101200341c803003107117056481040103034a104551500c0303060310845000d51848621000a040c0000a00d52035a443c20208a0444845482141e069031510b4480500c8241c41d5014840c110308003c0c1a1100c04503403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 18588936 1250 18587686 18587711
    0xb060315060705030d02070308250203030606090301060317030601091502060103060f0e060106050903011119030207050304030501090b01030c120209060f0a1a0301031e050a0303090206070206120f0901 88
    0x10003405160300d02600001441c2001c0002c14801c83e180c0e089901001c64030b641c818100140984e00807144203000f8015000c101401518186007400b84074a9640103500e5580c030b4001b0300449070082c500441d010341d04c4180c00701c000f54a0030490310151010406480c0c59140c00030005111180d130340d0104100413003148100d501140d002ca04141900d402c4a404030f8250381c0c0b030350000001c105c00150480140140360010400c10380c884010040400210020b0048480c014220f13140e51003070380c1007182c10a00501e16220198001e4001d40ba00070302840c00d40c0e003015a2902c3d401d00359408003000311803024104005204000300c0089860241c10b00c5440103888121660224180d81c001a0049106145840c20503207260341c0c0350075540151145800344c08254400c1000d850142d00280022a4103001c5000442c09820541c55100810354122000300140691900d00360b00900310540140d070070440800010006d611501c00410b042100c544000304246041d00000300c21107400780c09890740364181800e44004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 18590186 1250 18588936 18588961
    0x207170613020f09040302010501060e030d090e070504180207020a0b070812060a0f03050c120109020a0b0f09040501031407050118050f06071704030507080606090106030c0c050f0a060b0603 83
    0x11141a645001c401500c600005110082c081c0c11290300030303401801c010406a06404c01c1d0b04035244ca84406010340c20b1a401c054441b0700021010340025a4201c00b0001031001d0741c5540e0b0007042608105103883c7c0c032000040e1400400c5054101501c0d0000b400c0011410b10542c000b00901d41000c1d0035003440f00f26a11017900340b0440810310040300007000414403e0303860030140c400402000440200d1960f880c41d0840d103034403183c40c0d0b0510481a0850031aa40c000600408402a50060070140c0d00e034185001807000c0d0704414034260202000707210b81603660300c0741c1c0b295502940c0508501809000d103440c0d00c6190400c00e8002038101300124900a460080c1803450300140d03002240c4034690440003c0c08524503000d114000303482600201c01c0c80740c01e5840d290041080d0781c000c809407451176455051060380c0b0300e4151103580d0844800ea00401100f071081d40800300c5e0144516052550380c009881d80340c503000c11103c02d211160000190142044094814140d103103006441c1c041c2142340482c6030000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 18591436 1250 18590186 18590191
    0x80a0905070806010f080d0531060c03110a020109051002030702040515090a1a2101020a0c020312040e040b0405011b08160e060901030c020712080a03050106020606030a021002031b0105060102071706 87
    0x87c1c42d840c427240103400d240f840f1040150112040798a001641d9501c8004005481170001680880c1800d5008880003001180310b50304d9a406071144600ea900d00320500001880110320901140018800c14006030f17100c0c0030341c07800303200000d002c0091441c1350030030041e11280203000d4002c20340c54905185441000c581f50b454501a0440301f10100d0046c0711012282d0000c900d2982480d5440000d20070076150300280e00303521180c003d8045820301c4161008000552103a401803020445860300000c0014010840d2150320610074000440e10000c1c02030580c03541a0310001c04004102c01c001008441000e1100c02d18070700242d4540101080010b6010a1851240b916402d04258955000c1000c040c02000448000c090070380d800718166645041540f41608603200c0c910000b0304103000050003d100069050040b840140500000000f031360801180200c07070180c2c20151b0105020b40481c40c0100c2c28004400041000041810b18000340028288140c80c3c01c03600a01c0c0c005228100e039004002240c55 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 18592686 1250 18591436 18591457
    0xc0c0315020403061d0c09150405060f0301020a03050906070207030209040b04031403090a0203060a02030609060d1104020a09090b1504060305150a0605090a0906080d080a0905070806010f080d05 85
    0x30080c015145a48080c1c411070f007024205904002005503e414a03603150b03010b0000c0300c0f00780d80070340303880d1020014500e03400d9400b03041c0075044034100c0c6850700d1f042d0b00540c2c100360010700203003400700c1007008242079030042101c4001180d610390800545900a10420383d1140c91031004d48401801c5d036000800000d00a08040c0680720764000040805000714001200038410500f519243d141068000f035558050f00d108a00a020740030108000500500960340100c10081c01c4007a9a42c4500078070604440040041d145c0b40b0207587c2d800001d4980703200034480c0c81d03c07980d184240d5a003131007054419590b0b426000703400788092160070740440e20104180c1d0b0550307240d4039001c00d003500c030031401105024001e402c8640c80710700450001001500800103108044040d40c0701200103556403690070480e80f041c440c1d4000c0d034004c5c0301404034640c46401c81590012154400080c5075196443e45c1c2d26081050b0091009640a540144040039486244400900d18030f0000c1280011080d00204503000703841c0001c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 18593936 1250 18592686 18592703
    0x3030717040203010212010b0316020712060209031c1215060507120e060a09030308060109030c0b0702010216080606011205130b040f15060603110403020a0b090a0b0f030402100c0c03 80
    0x1400c43d078003901203e0300c0b881d40011500385561502041070300741e80165401c0005110b2044219099400410720908417506400c074801150720703a4403590040c0d4044951558103004074203889104402c11103410718030600c1503031425040d00b2604500d50807036444a02280031403043c2401049443c0c3d100c01100c0b07000d90310121007440184e620005a07804c011400c401d0754805000300384071146a6219080e50200c038080d55030008aa00c1e000010346688545001c0908840344400062082120850040000900c1071040300c0c1d44100041d0042800400c0d0f40000e000380d003002c01031000d10346e84210700448180d4422010440b42c203054020040c1241c100d10010010714580002805000700ca401c0d40703400307540000e05034510052140b0000018402801000046443c1100901d5003080c5171040e02d054035030190034540d495081003003803c0b6070741107100401d82c8541c5003d00441e403100b4200c050284003450100141c0c91341454030400c18188600c40d180c00030402c4c1d0301e071003501003910060072008403500030344503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 18595186 1250 18593936 18593941
    0x5030a0f140f0105010b0310060c020901030311030f031305010501060807050405100c06020a020d030c0207030b0a0e0f030406020f122701051306020c030c01020616030c030f06030b0f060303030717 86
    0x1c01c0c0c189611810340110079440c02c0000107207521030000451040030860744c480d80c15901e0f40c00a41c0d40c6880340c40003940000302c007070040c000a401420603030b00020391103040301d0a2803401c0701421841c0c2d1045603000c6a41114040320700400c1002d0280b01e01504250510103058940001d00504034000c0703120f010b10410f6141d584d2244a4060a0b041c014540c0000c029507a0b0240e40d034000c3e5840e0464000040001c2c039004020300f5440c400b051142c00d072135021100c48040d486110562020303000d204010841c0707001c0d8002481c400d0070104024002810b0715009000d59518000600c1e040140b10044010840c00401040c050305605276a158400100c0800b09021800c03400012603150117400000c034080e481c0d2040105040c1d40015a20000e0300040f02280c40c0a001c1000481c0c4501d010b80c1ca220780c0403151400300b900355010340c0101c075400e6400e01d000141800700c0d00c1c864059603030b44d41c8140c3d8105008020700c031030f135031070300002640c0300109500440c6181048000201000c51804c1c070404001e216401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 18596436 1250 18595186 18595223
    0x3130807080610051e01030221090d020708030a0305100e01030302070305010b09010609051003060b0409060e090312010302012102030109050f07020c060d02091c050606030f0a02030606060d0207060e06090705030a0f 94
    0x19a0182d840c6000d14270700c420010990100b0190058500e41c94034070501c12900000e40c40040d042c020358440d80007a5003000304800007500030b4040500000e503071000c9034101046e4640544040c03402180030768000c0035810f2071414827508440c10003807001c2c02800102c0c01807040d9500b01109c40211101074903d03608a13502e80c3c20440041a81c0c0c1c10083d2018000500001c202c2c0a507040002598032a103035408140c0c480c008081d90768414420316089003c1a200100003660182c0c40f040b480c0c0c840e81500e44c420600b404190000c0340d0098025524103607550080c07000848100d494642d0000e00b40c00101021002040000c403d40143e40074055004d1f00080c1401c85904d4001d900403181500300c0701113603130725600d1070119201c4104035069800b910882056442514000455445040e009005041542c0301d4005104184d440720380c0e2600010340802c4250000b40c00c1c0e1145020190040300a01a5410700d15031180c144292640003034403c0d4400d48881000c41d0b101c8048110443e0300440c500d14050703e240 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 18597686 1250 18596436 18596441
    0x4050a0212031216030c03150b030903120a09110303210901090204060306020301030501110f0a0c030309020303070b010608100608010e040c030f050304030b132303130807080610051e0103 82
    0x42c400201c240b440c107201d001502403240e400b504d01c25481c2030000e620001030460071555100d60484a0621204040245984120055800403c50740980b450080201e180d148052808ea54019215546200c840c0500c07a015800c5414100300320055498424803100c4c1a48c1c40d40c0210070042d8140d42500890003013042580010840b075070241084c84415543e0800e840250401d200c1515a075003007160703081499a08400321200400a1401d4034140540100e04032a0400704000845c28950f64045060150f90100b0207450702a10a211002d02036041420080c488507024196440682905405004440c1c001140c2c074192501640070025994a50501200d02c040c0c070303840540702541846a0005101e8044000c1081e80e016914502440e11200030008040300f00f02000b0307140544405450206041e00d04541c1e00000700b80048030b0070108070820209000d03001e80d0140c07495500600040140301014080c180d803209503071100100d0304d85402e002c17400c00d001c10380d120580441808014501ca07802503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 18598936 1250 18597686 18597697
    0x108180c030a14120403020612041e080304020f040506030a02010c080f03010608090106060e06030a1814010207020f030705030a1502071209060e04110f09030705060a030504020a060804050a021203 86
    0x101100d001d1051400c180109a00f410340e880d00600070070300e90094210fa081d08031021242c0c05824a490308810718401d054122015104070361140c030b6400301e800c103018801050074020b4020035400742d0301d007000d00c10865030007038183c4c540380034030b05010402c907413664042140c400298081c01c1c40500440d5600c1c00d00d20301d107c0c00e16008106840030002090b140d5014100c4c0b8410a0144c0003000806c1e02c0c0c00050391b107030300c001100f50741c007140420015021440c3d94000100c4400a107001c10010203140da82d40038008074062030180281e40c045040000d40c9040360220712006400e40242c10b585080c040403a0f04e940c0041c102070902c0700000c094902da507241c0d5040395110740d000003c1100b18040d41000902081c11072092000151100010b0542d6240510130400f203095520406882c10000c1c84100e17410f50009440f8036498002c0c00400226911410000e00c0e844909031b0300040c8a190620403c022500540c1055041100140402001900000318150050380480e4903190b054607507615036180d441740 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 18600186 1250 18598936 18598939
    0xb150703030507021204080d20010903021605090f072a0308041719030b030102040806090d03051f0605070618050a0201021018061d0723040b0108180c 66
    0x112901030550691202d8091162542941d411088110000886020b10f00441145420114030451000d01403021aa488400c0d510480340d0490303040d00b80c0b800c440c4010010b40160b00310102900603e820040400c0151004986001e03880c1480e28036166040d0f00105020103000e0307081b011481c12420001c10004410150f001000001014903008007210020780e011946410340860004650501c1401c2e1252480b40030404806074140107822030250410002080e0195401c000101c1d5520040c010035210740103090080011014842c4018102c60b002400100481012003a004042c2001021003007100d480b8500380c0c3d10b41240307082c0302006045844264a480804594050400502007400400b4a00076020358030103c01181c031075010355034030811006030425400303203800004402d80c7c0005501c1031100a0886003100d1800002d14100060b00b20000041c040d1826910104580750781d407912190079141400704061400c0041c040304000391000c085221725001c0d0004000081114a100c1c080 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 18601436 1250 18600186 18600229
    0x102010b0a030501062c040605041b091a03070b04060f1202030411040b0a12030507050102070c06091806050607060e0f010c03020a080109090506010e04050c040f06080d030606120b 79
    0x41c1d07464044d00808462180d0308041c24801100003c04403520214203c81841007000d42d61580d0700ea440000900004104442040605014041da1b18800040c1c50103064805030008440040c80c00304a80318180c115130798440d500c1158207001c01c030050030945003210880c0c10038218100d45448292440300d0700041d064441ea202004100505c800c003142c10408903004d035810008440010180550300c1003a004020703051300e0005070000004d100b42e00900c1c9a5020b03a00050508c0820743d69622010f1041d8480000510072420500114051550052044d40710400070880d0b1403405000c182c2900402e50301170040c1360390ba0791224100d0418802040c6191001c002000420540d43c0050025080004500d0008692030004203600e629481650b46090b0004003c0c502a841c1407803010300094002c100b100d4038001e00c5058409612603024090043c0c04c1c0c4400410001d0400022500d0691103a800108060425a08010a58018120005100ea607540214603441e041c40031440303141c0310450314000c912 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 18602686 1250 18601436 18601439
    0xf0b13051002030106030c080402030c01050a1e0f0207080303091203060f0301060b030106090e0103080702041107211e0f0e040b060708090a080601030512210a0f0e030a02030d0207020102010b0a 85
    0x80c0c50b94000d60603168507450822076124289021100c104040324001d40640c0110503481c4150300540c00303403204034050310749481100002903200e0440d1040301d02081c0407400c4020107861307090701400100054004070300198118a0b03c400301950b075403071510038080e281c14000f0101d1641c0e190200401403084001d0000d000c140e50325907111500781d009128250002e0341050f40032640380540001541220f40108009081007400c1e001c100003000300a4040300041e5040004030001042058815460b4042e0704040181100c60b15001c1d20520010000a10401544c920000c0b190780026000d400c4580c240380c048803000c12040410f00a100030b1080640c05000481c414040003201d0008040d0031200741d0f440340b605a5543d61103070f61400d003808002d080c0d401290055480010710320240821703400014044541075a0004004a2482d003036803078840c001c0d00c801c203c21510140380150410542030b600214908030041c90001e4680c025241403841c6079800092043c1968801d410202d01000000c040382d600c103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 18603936 1250 18602686 18602713
    0xb060409050f150d050307021513080604060f021603080c0c0f031305040902030d0513120501020702040605010806010f050705011407020f070b040e04020607020a2409050d0f0b1305 79
    0x80b075040b200004080780c104002103060030042285103045620200031428a01158200240e50403000207074080035038107001ca004542d00d85650300c4014145d0f40b0240c121814903050902c00c0d945102900035510b03004100b032080071a544010421900e8140c504108075480e4000300402a12442c2e03d000e80b0f520500e001c5203014600403000f0104081840c180c506407603a6030051005480445001a500d40c0200c04070300c00d4a40550010302c0103941c1182d030048015224800d07208440051401920b8a0303602140c098110308003482060040c0a09080c07440300c43c07500d0b000080c12125201002c2c030400c24049a0041000302c2500400400c0710440f94816082c0341c41d1000a540e5040818020a648902c0e40c3c00140041590202c42c2920000d080031559651181c00b441881c3c0d0000c402260410b072074401c0010402d00103014086d03040d80f02800210120942900107041c902141c2150f889002d001c0326420004032690307110040540d20a0f08141950381d5960b07448212903600300d02504c64002c440409149 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 18605186 1250 18603936 18603961
    0x2040801060f050301051b03040303180b0403120902060405040b03030409090803040302070603020f0d0e0c030a06020c0c03071d060111030706060e0c03070909050907030f050303010302010809030a020c040b06040905 94
    0x1911010300000b248a03607100200343c2614010355810291b04440040c101c26540220015980140207044c0481c494030091b43c1c0b082c00d140c81d2101a11002c8600c0d09100030542d010a0001e000d01e4490018014818a0303000680035104d2031145a03c25a80c0385c0d2481280c2d14180240d8000305100b00c8100007808240c1028091070340204c60803001070241260119496000380309480c4020000300406013030400c42820703480100000c007002499445541c00205076070b9410060341c20ba141c8154809a1181c0303078926050720b41181400c030a8840d0b00315841c10f0191024030024500c001020352104d803038540310340c00140d503071000300c4074007440034080003d84500b4041903401c000101d4468100541855079102c282107a5800300352119000904c040e2000c1003035000642040ea040440101965040e42d620b0b9901c00c000154100c040b20160008001002550b030415820755100d080300e4099844e0606415009407200da0f0500030f148101e0751006c28000c103485031030603500640380e080020040b50509800c9941c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 18606436 1250 18605186 18605189
    0xa0e120c01021504050615040e060907080717060f10030f050d020c010306030302030304030f030204081f0c020a080d021606020309150619061b021503010806060904020f06030405010905010204080106 87
    0x2500c280340c0720324010154810014072854010700900312079200c150058603c4a182d030701c002c8c1d0054496000c45c04444052040c0c0d80150810002429094502018a410801b0561000103910b440e00b602100b80d09000c038056502080d0920218a20340c0d03260035444108600d40c202500b000b030105002e10800400244ca40040d58480d0222070390342d00018011026a28039020003401a002840803900090150902000f4241617040140c10310307880d000c0c01c80c58041c00e40c48040381860509900304996140e03104541d1452418800b0b060071f0455600d440c80c080c41007441d465850703036001a824503820450124500e586a2009066607a41030000300c0c1d55130b80112903613001d060032805022400b03074589019000b801240901050002a2401300b058605540c2e415184070841c0c12008010016030f0740d01c0075040d03640300601c265900c135410002c801e85000d000900c03050050440101340005683c908000001c1c0641c02c480090780c1c2c0d40c0e9450b109014050b040e100400e2580082008188994103400060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 18607686 1250 18606436 18606439
    0x4030908010501030309170c041b14190518090a050402040b012d090803030a060e090105010b1204050a0b2401030203040804060e030f0307110901060c05060105060a0e120c 75
    0x4a1544a6149a08840c8207101c000c0c0880d41603802000100804d807055491030944401755845840300802160642c0c0082c076507907500c800a1851000269044031000140038062407030142000200600403000e0204c0c2c0d10748205104000c03d003401c070110308041204040070084c0100c03a490a000001e00080e00064500302d210320b0820001c0c0030103500c144000705801c03c41841103800090b00501501703091030001ca1071001c0001d5190b000c640094104011405400040c40c001882860a00c1010702e601002e0516610f50b41020010000900079230705070b505014100482c185940c45a160480c90032441040040030440207a040204083c003d1816101842481480542c805e40040044049100480340140355005c280420b11541d80300b4105841220006011251011000b602c05845c680000008070b6110180b0b141d14880c60504410440c010507072800d0198044440c0da89040d00c80b08140121402810302007440007c1c14459918480f00c1c040207000c0c0e401c0d4140d02c102a603140d01007100b0b1385 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 18608936 1250 18607686 18607697
    0x13080c0703061109090a0e070902070f0b01062d0519030e0c010509150309030f0714010c090b0a080c090a0e0402030c1f03020c01020904020c010b030708060705040b13080a0b0403 78
    0x18581181c0e181c3c1180c107140b60081c03035181a42c6d01c544213407005204041100360355210b4038001180190325031005065940c01808041901f07406864101030002d4142c1040d001c21469020304100300342000032a00720762000c801c2409901079a83d9040f00d0314040c00010794181c4040c1d14031541950b415520440e204146070080d580401c0c4402c0041d10b942c070070010420340012a0003510240d03452580c01958120280300250f80c60055000050b00c4513400c40c0200b079864071030314407519030002400d1040c0c4d10640d54908001503001c0c40d100090745140a0480c10805001c002c1c000076100503840001c84c0c00640000b031110b504141c070f8400c41503000a04032400ca01038031074003410711010f00d001d0080f407448004441340c0c80c81c14240940300b100650411881d084c582c1d90203000c1181c05aa40340041c1c400c8844181c00002c40500402c00c252510542d0381c4880e1440c2c00c04403e024076244d000c02214103840c91000e4007a940c21a402c601440350005a1000c5018040c26805004000c900c56a16025134066500c6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 18610186 1250 18608936 18608951
    0x806040e011803050706060504050c03090f15040219031506140306010311011112070b0a05060405070206060d0807020301050a02040e24040b040209030f0d1d030c010813080c070306 79
    0x306007200c441d000348001003416100d210000901c608000c049241c0301c1c540109a0903035400c0883c05840050326a40d040743d20110401c440d0000810207058401c0d8400000c040350b018840b0000010070001d08044d0083c1d0f01c0c40c10003104400d03107011400c011a07003c00c2900c3c2402c06002d0f1176004060a018400358280301800000141c5000501d080c10780340c100c1c001204107452074005540ca803980c10180503450056086c04d401ea05840c41c0681442405020013060f43e1070312000d0282121001008288102c2c50700041c003000030390004459a104000341c0d41c0b100c08001034105540140507104d00254150308000070800c003021190041d0044501c003800d403070b400391501f00c5c090701385020507580c1d818682e0012035500c001349020307004401e24500c003900051402c920712000c2400e00312440c2a01c01550f0020100c030000070341c4518113551303110725071032003c0300e00288100094a410b600c1d082c1d1810400d0880c045a40c1072a00c040c40910310b41d0021405540b002c5115500b512210700b40f0007525903a180444 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 18611436 1250 18610186 18610211
    0x20a0b0d06050a05090a0921050702010e01020607090521060405011a010207081203060409020d030c03090b07020904020411120a060302090105010f0806150f070b01090b060405150309010b0a06080604 87
    0xf5806890004052409540e00d03050b80340000c15515034155110920b41c14540e60000c110031140340c2000203540d44a6441c48140000341681003400e0000d0f0465003c02c081028855012403c039064440c1101d01e0320a80c00200c6d0846041005251021524000c400c00d01041200550122106034a54400c07515034103940380040e40c6501c418403607a6410b0f0044038484031a1022031000310380c80070008100103043d18950300410310100f0700080440100307621041c00410706400414010007008c441214516008041c0d010450080c40500028003c9031200c04c40b00d680385082c010384230a070070302d47c0da6054140713010010140617041070f1006034040d0300d4200001c5401d500c1101e04090303a1859407180c44560b2100780600c50100c0b410076050010100a1080404003001078004000c80c501a900f01c0c0010350400070721108882d006080e240c0b003180200000c2010341c4603030b6041210000301d01e50441c0c91740d079284411405000340e0700d50241d100c5108017010a0080e08000710320b0003003409540c20003a4012400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 18612686 1250 18611436 18611449
    0xd020a09031101020f1902031c08070206060f15070c0306090f0b160c03081b030907080106050d05070510030f0504080304120c021c02060c01050703050103120c030806011407020a0b0d0605 82
    0xe803400310303030401c001c0001c00c86c1c80d01c401711452510103022941a00000b407003032001d440d0020034040010756100309110072280e0420403550880d200312141e02d6083c14280c00a0501d512600c4000006d080104803c4103004501c00c40000441d0000001d1000d80c0c031301d01e8030890200304464229042820301d004200c5c0306036148001c00c10a001b61719034061000c965103058030640c000421642280d80170407200d6480b01c5030f400256000746400402801c0c0301e4103102280303094501c7d9400040c000d1112458890115000141100c00c8600941d0140c4c404c00301c8a030224003a0014181d00d050345410300081c04100020070380154400c50251124002c1c039140031204480e9580d0408001c1d51004c3d07411a10040d080001040c104c2d0a440204150325210414100034203440341218a8008170350390300010010b000480c550348500c441c0d58503003600100400d91b405842220080c060ba41003000301001c10814003868400c80704103c1c0c00804d0781c4415550b505403044c0d5580a0018046018100b40d8001194204003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 18613936 1250 18612686 18612703
    0xc0b0a0c08030a0219020105060a060203090a030803060109080d080601080a0e0a02040f09020409050a11060a050a03020d0905010203100311060a050d0c0903021203040603060f050603060f03030d020a0903110102 92
    0x40e500c51140c140c850311908140c0e0070140c5015400e41e8200200c0e091040d11601e1118a44450340000c01c1c40d18000017080469940c96000400b90b400070040d44042d0396480c80d8040540303602908160f00c075150a00104e900d80f00c5a0400400f9120b0240403007401c0b508007440d1071150000741d807074424070394414403a101a102904480321455100746500c800514160700710b400300c0c003c1080d00282c40c10054001805583c1428401c1d50789800500c848014080c8445280b00c4144094600320718218038990014401e225100c0890105903021480400c8039940350450841030b5000402036440c4e0610150005c0e41e02c0151100702c880e000510b10004180c1003520a44601d20042c0d1942da003488034040c0c40c0005020402001d000708046243c002c80165aa200400c010818040003035032500e04110001d0201c40e040e80000b03410b5501580c0410141d600e060407242d01060640d0b0040042028034082460f50041400a100302c50005c140701c2d417401d510401460849006038040c03010b0303c5240006a845403c1c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 18615186 1250 18613936 18613957
    0x605060910030905030d090803010f091107060509070b07080c0d0201060609030b2d0406050903030402100507050a0803090f10090206030f100e011214010b010e13061703070c0b 77
    0x70484007800e24040e90140010310700803c241d0349804084281101140d00003902100c261401000600195601001500280010b40b00c01c200c000c02040c40c1c40482c1c0614140100f40e9070302e950014020341d0040c0300742030003000840c81954513100c03940b90044050f00018603000e81ca200750020203011500c14007511044941940311401c4060568403041520300d0000c00010361402c640c0c03a904907010a90b100c15100d81544111441d56007070519013401911405004441c95900c140140f102503a9090300f03030702c141e48490529540e998070b580b522906140b000c00000e0940040801045005840850414254a1644c09481208200018500c2114a0800003940081c2c040c400170b500e1001700b610039a0012000d141e50f501544e9502d940043c0508260880880303125160000d5082000c003011507244031040b10f00070b1100c018031100003405107819007916072164211100382c0700c0c210705c0382d44404003400c6d1880a04104a04041e5443d640b0f42c4900e00455802844040000304505004107a4806a92 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 18616436 1250 18615186 18615199
    0x30b01090e0c0d06050a09021e0301030206191b0302010617011b05070201140304080901030501050f031005060402130e04020102060c030712020a050c010f0603060501050607082a0601060c0606050609 87
    0x1a80b0451101c1608030440080840b55030340d0740030a2580d9500034000091041420150383c40c0c80013203294603100302240c8540c1c00807030309000500050380d8200940c4c3d0181d04004030301301e2034040d4200031640c00750f1040c0c40e2a01503020620000a066044d001a41030303039844030b07240c000c42007542245400c903540d52012666403281c009000070003a22a4006295860051401000303110b034803003800e00603620584017183c1219000511900d156018040c903030040c48219843c2c5441034400c8040307030f01c0f8031341e002010110030750b1500003d416680c1c903030640b01c1c01c21040c444114225102c50b4114030811094809a015224190010700c801d000d8101b101e00c2071080b5680c1c0c1140c1080b559440010750404250380d000c3c444140b0460528580c02d205070104e40a6521020604500d903050103811100d060300210f0043d0303801c1140d03c0c00300c0c100030101ea011081c406010141e0328002241101d007403003c091610968000c520000420951152000d483c0b1401900b0400c612a903950070080d407449042035203a006003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 18617686 1250 18616436 18616441
    0x1020309090601021606090801200715020c010c091a090a170a06020d050406150605071509020616120e01080601050c070902040609030b09060601050f0a030e0319030b01090e 76
    0x40c141d03070640e0080c0c0e0600446004a41c510020305492801d074000d100081c1031400100a001024002c82c0350405844d80401e0a9012201041d0814072030090061704114403294040d1f019145a8101c0300c414003404020032103e40c050750002c0c00901d003445505d00c25403c03003184516160700b500844048404c0100205460381c988003800c0d2000000700714981040c0100e40469001c0b507090b0000f015820110355000501d80340a140c0101182c130111600c50840401100500070603820900701c4a1040d001508405520802c0541d0700240c440702070025004a00824080c5980c9181d5540181c0030384142d254103009260640e08484840b4000c4020340001d0034000416007030350295004044041c0c954041d103541d140c0f105000700aaa02c2640490000390303140c5010018400588072060b0000366006c003070701c064207104c00020814000d90064800c8840009010000c5038085e5100e02c0105045100b0f4075101c02c0c0880810034101c80340c60302d8601007801c008140082e9842030009005903481825004d03401d8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 18618936 1250 18617686 18617689
    0x6091005010c170703170f090c01030b030f0a0f0b090d080a09140a110a0801020c0a080c0f0d030605040b10021005060409021f020c010504030507030b0601050409021204050d0e01020309 81
    0x41d0300b5004242c0c0c0d0103a10710550010320700c0c03901c020883d550007138540c6021802080994220000018160000001c003841805110700f80420550200e0000746008208860328600003420442c00781604150392041040b9a0100600001c51204c1e07035000d80a107960f0341d550b01240c2a01c5d110056400340c00210041c0014130b003211164030a65119005410362150b0003a0803410a107049124070040d02c241409001c02141c030324080f1055005004013078025420b0265010509907107005015000302900e902140781406a0000c0104400e01181c140031940c1540305000040c1c000c1c15180103042c002c074200300c941212800c09010303030602040b003680240900e148001641000313001c081c01c0c0c41d500035181e540d44009a560741515207240600529090107846441401902c1c1007003210003a418071505000404c04140c0104e1a01d04803a08041011066034034000101e07294491908009401c5102041e1407200341c04031f04e002c82c4201d20801c100d40401000b480c0c181c44034241c003102d26005134000c1180054a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 18620186 1250 18618936 18618947
    0x504150315050409050105061302090901030f02180c040303200a020904140102070503090a06110a0303090c0504020d0218010504230f0d03120b0d0b0403051b03210609100501 76
    0x1e0728003241808251611030b4005000d440440c5003d5525070b4482c0180070081c43c05442044202000c10750452501e0824008100784400520026000c0b01e5203140c03040554071782e03081c0c8450031400240d80400c6407500300e031034080503009400103800041141030780050303c00d480500e00c4d4494103020014824052582c0c208680080020011103109008060803044100240094607401d44100d02564482c1448014002d80c510258013910400030700070b200540c0d19101143d8040e0040e010329011441c806541880490404180d10203038000e4400030b8120b04800440d809010740031714103c40c1441a91030800110392901a50250a000402c640f0486030088a00400140c062401034900c0010039041ca000801500e0380e10340950214405814800311000e851040c0c0b40312440c12581f1342c1c1c080b441c94685a40c100002003004060150024407440310810a201d100403519620044a0b0707280009481402d140d4400081036980380107002c041405898100c404520540780300d9649904980780100445030b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 18621436 1250 18620186 18620201
    0x212030105060a02011d031206030604020904080a030605190302180105100c0201020705030109081e070f0201080601020f0601080d020705010e03030f0708130e1006020a0b070f110102041502070605041503 89
    0x4d5658400c0d2600f002601100c526010b080a00040c0d5101c0c20207400c5079440800051101f4440d40260080000503030307421001d990001c1e0040b00f42902c3e482c2448041d8001c14a6400c07190b445220303d00e8920b6081080d2141da8103803442981e8591042001c8000341400c00c400303010b21a448405c492403d04032910450050140070b00501c1200c140716a5074010a0071120b00d031070152035400c0002010340d80c0207001c030a503010841414514501e8103215845510300d1944003c80207040202c0000410040ea2023005020780c1f2039101d200b030300c80c0c030350750307009101d5640d0034180700e2401601a1141c00256503010b0240d800e00703d000940558a0241a22851413203544580000c071a205002e0021603c0c080c0b1244282d40500303062a0481010300345090252100c40d22540300c2000c641c0b0891a80002509a4501c1500140207060036000307440319410598075050680390000c0a580b002c100007804620310002c1e041040401e800352034005444010840d05072141c0e0007100100884401d0400100340f081c3d00121 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 18622686 1250 18621436 18621457
    0x140a17060303071e0c05011107060305040c05030607020105040b0709050a15050c030f070b161b02011b06090605090303010e010b0c03040911180604081005060613080601060e01021203010506 83
    0xd1900e0341c599101c1d513a13001d00340d101000380e005030003500d420031028812200290509007840c20300c8200c04030285a0b52000780c01101d0400d51104007140c208040403050101802000742961041e18050307000900034030702128152401d003000c90120f0109802a6400381c1a42c0010b402984441c0c00e19501c0c14581c08160080b60030084204a0f401d440c0c00c0500241644601610441d9a90041804c1281c440040541900000c99581544000d00d0740c112400007082440d500301b10810107050f000598507182c2c18032144a070408d00303408135010408a40e10141c4207510a03079007000a41c66140c2071a0b82d03408240a00c041d6031031008018040881c61401030000f020000044078609a15050b040c403d844440d041988640c50114840803100421242211002c0080d55910304040ca002002c641c2c587c64005800e60640e42c840101d0080d803284800c0320390340c9001401c46a03846a682e030460b179481d0401d00c03c010001e0242c2c0840b5105600c04120f1401070050100380c80d00f180d00f02810000c0755884441c458 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 18623936 1250 18622686 18622693
    0x120221010602070603050a0203060108040f030905040203011e0e0402060901050d0e070e0a0b0409080d0902030304120506071101020f040e0c0702030d0302040f140a030b1308031303140a170603 84
    0x510201020500060103001c0907405855000c0c1384c03003005000c1e9200503052105150061042112a990080d1625406904000c044204842600341a52908175581100d0340042c0004008070350300c8803e4000b8511001000c646040003513640b44030251080056030020f50203030301045072a101e503214030041d009103c044940040d07968003110341c25141114a03400400b0b886520020803180b40340078030ad0015217800985090090400030303a0f5071074082c804c80c1300302d030ba1690f076818681065440030420340340030384030b003003542d15461001d401c005540e41001c0b1142c000042d4500d05c020082203040c02030700d4006200c1140d02d800c1c5400d00c410300760841802003020700000d90034400c140259504000c0305880544ada00d005a4860510412401c08010740e0000c2542c0070340056815060345485010004594101da0780348082d8845180d80012041c1204000c1d02039003000c82440b501e548285060410f0a00c6030700d030000310910560600c1124007a065512011030240c10181d0041011415055403018009056 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 18625186 1250 18623936 18623977
    0x405040203062110060518040308090f030f0408071208030103020402030c160f0b010b0406050304060c090f0b0301050108101d04021c030305150904210c0f0303050403090f061202 78
    0x2000100070107081c5581c0c3c01e83c050446a103c8010341c0c807940c406008160764080f01030031000c0440201c448040c00040030000302e0000079840d18420702c103550b81d4011200035665198031283e900c3d80c26401c01d0240e0400d602980d1230004407070314038805183c0d00d03582c0840d100e0300390703031039902004001d40000300380740d51903102006a400100f14405050b05424880d000c108512051424200c0c000725058101e001d07008000c010501c0000c6d003010035a507000f61311031400306210b0a0320504440f081100d40c80300c01d0314034608401182400f6002c0145060f60700070390700c0307402d65550100c00810068140c4600310315105040800c1c05070180c90b48c0c0e03c581c45800038104002c19038a64185032101000c4d8141600000e5803803080c064411112040700c1400d03101101c03040c4907401c10345ca561002c05813094400444e4100c03001591030703040c010112079041e0b81d04000a0102d8100c03600b4007030041c0008650440010b100c020010600d2406a03981a06603a815550300200d03030401e066040007944107103400d440c3d0f410606070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 18626436 1250 18625186 18625219
    0x3110111030f040b010605180402070c030503040e0103060f0506060d09170c07060305060d0309050d110d080c06090109120302090a03020a080c100504080a0209040201050712020601080d02070803040504020306 91
    0x81d406803a180a00d00c07550300d00f6060030001c0d660103130003480070004100300504a42886103400701c000e003411100141c1d07a40c11850944078016460b4802441804041000070301318400c0e40401d8108ca016034010720409800140c007030100c80080b610968408ae0500c00312a030005a80c0c05550001e109040d60840c103c0c80c1d1040300a246c1180d4a480400d030701000080c460190f05000701600aa8161603220f54001281d5000d000f00d00c1d07a00070302e800740440765240c0040c0f2094071003105400a004d010240c01b5041400c109002d030348154808036251080c60041400d500e014032802966a030400c0342152502c5005c90101c01a40c000600b07668400440c05010007d40d5540152030000c0c00b50034001d007803105440040c401e490b2500c0303140c2018050144001c20501d07601207020704400c1d41c11a81d609880da5144010303503250003403020191545261100580d2002c0d000200c9a05a40c1840c080b03400c104404201280d4481c0c1900401a95410034082000b21b030030310707401031901b1040c004c00d40303100d80104a2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 18627686 1250 18626436 18626471
    0x5040b1b01060902041d04080d270b0105010e03030703080a0b0d020a121101090b0a0c03030e060709030309050604062304150e090a05090607080604020c0d090f0b0301050a03031101 79
    0x10040c0f00000c0d8001410000c00031600180021b0303040400604440d40340c0764558003000d004150400d9605e6444214446550921024005010301c8800c0d54041c42d500c54146604a40e10034000c0c00e022a4002000091501e0000300355901c650385070340c840e80d0960b00d0a86513009030801c007040c5500078040034408001660f844652002810901d450881c400c403040c20030302c0d07080c5034038042181801640241403040080c000100c42c0e901000782058600c5004519048008000c40a503456850243c030080c00405030b445501c4804407400383c1da40080603a1141c04001071485a48a40800b050781d0094102116602c0015080e100841082c8075090a0781c03400c801200010520503107001507112011401c092802c00300c800d400110300d660030895850200c040c29512000030b09230740140702c07400000668654031501120741d842c0c1c80740159800015806405055017040c1d01a1241d0303001d0b0810040b0366030a030003081d0303412520010204d10300d0f1440c58500750b982c04102d850340c0c0480d5490b103054920502180 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 18628936 1250 18627686 18627689
    0x3021c030e010c0504030f1403070f08070201020f01020c03181903050304180603020a05010c0204090c06050403051b01080403050c03070b0708180105010305071404061701090506090105060105040b1b0106 89
    0x903100400e400360105041400c40303010031510070610006101c140003268058071000000c540c44541042000c0e41740c00101d1840c024404000e0000410f08149401c000041015104070b0703100307030222181030001e24602402d078003500d01d118543d40d00038409080c00b00d221901443d1202805000d01141c0c00c915140c40e40c001c1c1080c0c0040e10b096100040820520032501011290035200030410404281182e0000d51150814403c490411000710703600015540c6d19409050b20300d52103843c0c6107425030343d010040c0c2032b5042444181c69078040d0541211150503070070407080c40401c05954100c1c4540d1503941c1070b1000e4010070b80814036444148810400180750314086401001951280c14081c908201c0b0f20700c0000d10b17400f0310009641071000400002d403001601e441950fa40c0c003501031501004a010030000c000b103034041c080030000c80e45001d6602a040d0300c038802c0e50780100c040d1502560751400183c01d807041070f1036582c0003c404002c200807040398200508880380500015591003c1840d0645094880c1c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 18630186 1250 18628936 18628993
    0x30b091506040b18180105010f0503060105130303020d0905040509030306061c06090b100c0c060f02030c070306140c03010810050a02070b161805090a0c0207080a080d0c110a02010c0302 81
    0x16140c06119510341030b1070880389124141080c5c1210f41c18003000920685102103040148100880851b110ba0300a60a4407845119000078990150b540c3c14000c4d910815110020b0101c0c0141c0408030b85802c083c090304c2d11030080320000794034503220304c070600040ba40003d00042e43d01c2000c1080304e080ba4464020300f0000c0c80e214401080901c0c1c1c03030040144030043c0c03940b82030034025050a03200c0010514455502103480d0341c104900e5036a1842d4069040d4454065450003c1c06400d00100401110b03501568446d0240d5200c5240c0e60b40340200101107101c28000d0710150380c00038041c000b0300052504200d0344400e06103405400c1c51007640d1034189040050301d10029000c002c0c0050070405a10a0514002035400000003d80903c0c1001080a180001e40001c12003074503080c100055600070000180240070400480e0340190040c28020380c40c0d0081854002d0890805041403c918404d4100c0120400b210014288500080d03005441440700240104d081d0700a001030103d544018041e03030207802d0003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 18631436 1250 18630186 18630217
    0x60d0f050105060307050103090b0a0b130e010510060f0909050c07020402030114030f0106120201080c07050708070603060e0c090d02180112140604080417071a090907030b091506040b 80
    0x100701c8101410040f540c1c06c40e50415290220740b0001c40c0c0114200364100568440c0084c50110203004517001da007802141c800410304016045521030030560005104d075128040140c0b0386a1a20021106110f03002d0400e0b00254404005000d820b05903030020b508071401c1d522031840c010b11907001c1400e0303820076440401c41d6035108140a10360700303084c002512544000d00c020050a03007803603900d4a210007440d9000e070400440e040010500d02800044911040e00302084601c420340c3c443c60310f44d88401e607000d40c03c001381c2010000a1401d11044100c0d0242020319102800c10003002c00344403d8101e80712084c1d0340f00100c405900c402850f0211203601134281c0d121030b4545414031741032040303080000c9500b1002c03951201d000c00000c65503100c02ea4060342e01c103500e100c4541d08205e110724503004813030700a110f07890088000f181c440301508005220f0b200013518001016511280268101c1d004000d49580084000000400c041c0241c5040b0420700720080107a070410361501c0070700c0510340003010804c1000c003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 18632686 1250 18631436 18631441
    0xb0106080a060b0301090e0a06090c05120105011809050c0d0c1a120c09030708010c020313090507021209010908070b030402041107050309040903031103070906030e0c18060d0f050105 80
    0xa6104202035480792840409101c2c01d8902080500540f00500c9030000255584030b0f0191603050510290300c469401c17020500c04103d036414842d55106880c8682c5120f40c0901130007540c4502c040c01441e04075081c0c041404400501003444070081c00c10024221094000c81d10b101d40690790f24400c040c00507001e601104146420074400031041032200d0700c0a103541c2418810300611188620101e5030000300e8140845d00c0e0910b40011038a03004158001d05465401c04481e19425503000000e015440000382c0700c0408140e407070009500300c0b001036680d2401a006140050001090704009040e000340600d01051620713500e02106082031126000017440000000c00c8c0425413802d4026a82d0344444e400071a46804101d03650203a40e0300ca030803021401135032602c8049003894081e900c01c08101a140d13007801da0f646411100100784a04500820740441e240c080100d180c0d000c005030130100200058502c107181400090100b084d440001c010300da020113142040800900280d0a070070f1800c1c4030760004202070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 18633936 1250 18632686 18632699
    0x5011b1e0f1208010501020a0b010b0a0525050d0e01020a12092303010b09091009050109060c05030718050102030409020c010f060305030403060e160b030601031b0c0209010b07030f05030a060f030b01 87
    0x21045c2c0c031450441d80100c0e080008243d519a0301030444200204641c4e40e9044e00c0b400303862602070040c804002c074000c4c12014400340b507000c1c01454450b1090040c2e40c100ea6100d5425500c0b6801c1e03254941c010383c401024440010010801c140c80e014423410417015142d03590340d400c9070301842c001d0740020b1466040c004d1243c50401340105130407408100d40c1c894a629028003056542c0000d60300d289a01501c6400101c28400c0a6002c1e1000903080341c1d09010750304c03411002801c0d640c015687d50300010001c0c01000d05202264240c103066500590143d03190614094490001c2e400070003540394036560398454400401c5407442480001c52080028640381c43c03460a10300100c0e5a0003044440d26084002ca02d20300208403040c0e901590003002840d40c5a1702d0309401200284000000c8821345906002d180181c2a0808002c00c020351084400c0c0c102ca80c1c81e020140154060f105004000c40c0050406201c1c0c41c0c01500510307401203140e0300005082c0c3da980301a054060142e8010340700400e80c5801131224 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 18635186 1250 18633936 18633947
    0x902030d020f0f03120601081b0a080708090f0601090207020a0905070c020a080610050409030e03011e15050f04180506010905070f02010b0f0111070b0c06010e0105011b1e0f12 77
    0xf440b00c0c5201650074103400d9604a41c541e10700911441c1001001c400169010f024450b00c80c5007035104d094100c0e282e404005014140c410300303540d59400324203660001030030a280041e1200921842c0c502429107a441c041c0310402a400c0300e541280d02c109400300120380d0411a2140600c91500c0b80d903413190f41c50b403d005002c0120701030b40280031650072500400c00480c41404c26002128419600090424101d0030102c4900d2030035050b181d40341d42400b02001d82c10803182c00c04a00340c030080c281001220482c8501340c6413030f20a48640c540125801d200300038607280c02c0e40821101da00c80078030034a50004a90798142030200c260004155183c0d075805104070039a011040d001d1841d824002001203482407030000b0103200100d00560304005d150400404249070a005e0500180101d5102684601c1c41038442e0b6110642400b0700f0014000d40740c00000d5030b6204996038141d0016200d503580114002c1d4039400312611070800000c070040324202001002403207102110f9a410301940d801d41e03207a06511001442c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 18636436 1250 18635186 18635203
    0x60103050603060f0c09010c080d0b0f030109051b0303040e070f030f0501060804020d1e0f140102070c15030908030405010902030f0c100503061203040b0c01050a02120105040504060902030d020f 85
    0x2d9003c182000200b00b148411303281c000c401a00001d80300c015520049440c0c981003c4000d080410200d1061003640140d0840354400c00b00311a07204c080150001850300301c030001d07030001e00340340d000300c1190001000c0403042c0d419541c0090152403519840d110882c10640c000d40e070481c0050b41d0f0903041c0f107050754148074000058036004424001e55243c101c005001030000380000e48a540d02c0724001d0204003036000e00d250549111014007660351a54204050400210981915019002030165203030710010701c2204c1220f030b400b40f03490640340c0c188034500d2291451a41d2501c1419070340e080580104004102962103035101300d0004c01c2c95141441403500f03041050708070340c28540c81244206902d40d10034a40c0e40d00350400c0e103842c0352241d4414000460300014600c0e449040d020005008c6030307810780782d0003e00700050100300a02c069115142144101c0c40342204c1d16416507032080c0140f100c0c3c0b070550409030304503002d1030000c2810051034001a0400c412001e200b00541c4c06910f05070f03a9010709004411 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 18637686 1250 18636436 18636439
    0xf0f09060103020a03020108071106090a0204150e01030f050a05030301090204080c0909030a03090501140a0608120a0903021c15020408010c0c0206072402180405150102071404020708120601030506 86
    0x80d1a501d15800700310b1924041c040203040c4904030300092080361007800541e007854110400c032001410302c10b03291f40c1c48140528081c2e00460401c00e08501e01082c281012017180c1301e03001c41000c168a151107002c808411080700712024041c1040400106000300065400f9003008140103035968034019003035244c11169800240291100403c11004034004015038140107020708020032034440e1442d0241c01002c2100a003810040b140c82070040d20002580001c09403007203201111150325000b0040c0c81c1600801c0702c210000b0b9004081440181801800402603941890350460003200c659103840030105011403000b00c1d1b0f9030207c0c00304003d24090141d04082c42440c100303000b03c2d80854000c11010f114056025219130b0800741a0766a4a2141e1000700024201070f00464865080d031151807140c448081702103115a041034003160024505c1d921148070440141c0040c20070500d0b0541c40c00c2452060a44241d00c103500303018004c00310300c50300020030b80543c141c11f03504403030f141c01c00001d001c550025040070b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 18638936 1250 18637686 18637693
    0x1707050f0111060601110c030601080c040606080f0402011d0607030201091b05151b10091205030105030d080c040504020406170a05060904110d020604090506090a0e19020406030501050f0f09 83
    0x20010b01c0108a40d03400540038030b0620100d8607170b40101d80c9405c8a601c5401c0d003610504000003604403012840d822030300b90032032f002c0c802165192011100e070b41d03040d610018580c011101107001507024440c00c1c52a60241c035200c1400c84250000242d42d50800740c810350142c3d44030404030003045008803159420005220b1115030050900c0e0100b114481c10906070784030381e040050120008000403030704446088004080b510341751b00180c10300c2c020f052003070401c403080c0030489070b40440d2600880940e4181c2c0c40150080500f480c050000300c0742c040000c5c0444443c1c400c208030101d480c2e03c84d800104060289901c48207003915400e00112070703000b030080c41c0c10035151901082c4405641c50310030380d50b04560401c0500300006d60340310000d45c1c5214a041f000350b003c08001400116585c0a40019200d5501220150120343e030384102d070425a5404022054141c106402c140503500b100c00703000354158006000058016200e81c2d40508440c4240d036080f828541a00801020641810b5400e80c007500a0020303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 18640186 1250 18638936 18638957
    0xc0a06080406450501020403030c050106050405010302060306130b03100204170318011d0d0b0105130507080a090503040509090601080601060c03080105040c0309060603081804050402090417041707050f01 89
    0x10b461034241c0202c40391001031543c030460240c050502d40154101a0800000c55a4594078503000d0000858614200c500d542056000034080c40d2600c02c85040340d4015000c2840c40e82d8000c100400300c203aa280c036251103552000c14134241c0c0c40402500440b641180360040c0d83d203040c15400c4500c070131110007441c25a1f00402003954010405020ba500407003082c01e050050704100c842403d00a440c4414503a00039804490b95002d11042c40044c504a4000752034102c40481c401700e5580661300304680007408651150040ba003040d07055800342c2d044501407015241016140c1d00040d01000c1d040d03030030080740d83c0305078018004004c0c1808207900400450800800c00881070f540504070680520030701c0e21079655451344001c4a8043e8011030946980200100300d2262030386019000e60f0048901e1905645000b0710010301401c00b8420140141e4000b84100001e642c0d076650b600b201110f108003064a8641400001081d60749281008907603168a00540070f01c9040409000d10702010803a81c0307040010100c0d6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 18641436 1250 18640186 18640241
    0xe010b030a021009090c0906172a07060504060606090605040e0c0a090909050a030f030e1203060102010e0f060601020c091e0601030e03040f090b04060302180402030c0a06080406 78
    0xd034590301d2a810740304403203515a141020341304002c05501006209051100d0300b106903034028222815550300d80c9550044100751040c03020000d100300c407034104070892006145054603100c0d00c440208400e800016140c10700541d41c807000d13107c0c150b80c2200e0054031901c0038000150880d9950010f01203a1402c1c034140751808000c600b18840107002d6503079211000031480c008a10401000c0007a010b88107050180c201c603403030308039910088544290002104040c80d42011032081c025054003820440042c2990300503880c0c91050b42c0c0c0040c101c1d038190743d41c5a040100c4c6850600c0348900ca611444060001460407800181c1030034080d20956115184000030490700f48040c0641b440f118202c03d0b4582c605a03a503500581c0104030044290a0a12000c503002803251001d40c80c40701a25a200818030540c4aa0410710045e2201404000d500011641101b401901c10000140d88117000074110b0b0000b131102004904c0104607500f2007000030b0052420071013071000d00e01400c0700201d10f814480511800c5181d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 18642686 1250 18641436 18641443
    0xe04060f06050c060610021c03090b0702160b04080c0112021209030406020706031515020c03030301080f0c0301200a0905040207080304050c030f120706060b1206031e0c01031e060305060a0e010b03 86
    0x30304108c651a00e8004154185110f540400a206c0d0700c0707108003070304d070810000203540d540001000302100302c0c2000000c604400d1100650341241d4840c0c4c0200402c1a696005440055000142d4122151b09103c290000c1c41071000240c0a0303405a00a507030755034188075000342482c00076002003003854140300150f50007005e154004c104640c1d0424000e0000c0c120100100d08110050700c13a1541031101000200303070004003142d515256080c0408442c080d4500c0c409140c02c0e603420703001103040c80d02c00072040505050310200074404411180380401c501612000020102e03000901e042d80d18260120400c030801108001d80c6000c850100c0c000d2400a10345c0410f80d81e5194410022107952001040460800800d8cc22800140016035000354445181d00706800e00c1e40c4003141c07001e109100701400040490031060150402100301005050032072018030041d009888141d0425005509412016804d6503c0d8803414005d9803140c0c002d0071050a000c80b00f8015120544450721480e49840481c0d561a40c000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 18643936 1250 18642686 18642703
    0xa1503020f040b030609030301060207081908030601140406020304051302130911070212010504120c03081b0910020a03140906030f040c050901060c0201080a18030e04060f06050c06061002 82
    0x49562000e1115500c002c1005007501056030b58061003030f181407101e446004005113060700e505600b15440a40e5074110384d9540d00384000e030501160813030205100400c00040065510907418106540000c007000030600295100e540144016040442c1c10700681c40c107001108030b14200010254100004c3d10b480c50381049a511812100a40e10410b11019900c00f8064035140c0e50005e00000d095420344404074003030082254102c5e43c81c2202000480600d01480519001c2d03a0507507501e04561381d0b4440000b92801d540e0303016000d14181801461199070380d50881c2a800c15603a40907000c46a010f14002c0d0001c81e064201a0612905100c90301d03164850384252035002c1102e085070300f103d480c1d508008014407001d401c055040107005002140c1e035904044202503403071007a600d2201d969904098142205e2007542d0b084c0b6850120480400440c1c8124200160711000030400503c003555107486a100414944c0700c080410004958403000080502c507103640700c10240c41c59913071004407201c001d41b1203261 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 18645186 1250 18643936 18643939
    0x10b0a0210050a0b04020c0601050a060f0507030c021302030a0c0305060f030c0d0807050d050408060a050f060607050f01150503012703050d021201090506030f010b03211612080a150302 81
    0x201c10000f142c8009a401050030160081c004650b00c41404400540701c1c6024091503010360201d00c400544c06104102d00b0b030031160309603030329410300903a9601110300e240c000c0c07800c0c1d9100ca903c58401140c90650701c020341c001d81c3c030700c400003803044160100501a9080181124820301c20174540f410300307480c041000b03c0c0300d1904484116014000345082c1000340100d080140c081d105540b412808160401c0040042d5000d50040f60304565803508180149e80c0c00301ca24074040c080d05408507105040c0800600350203481001500c00400d0303400049400c54281c0401a80c003202494401c00050500388900d0030050450342d80000d0740340d002a0004005244858003c00300302000900310f4034011958107a402401c0085007410103965100c0280380600300640701d5a08c80e0103000c1003d40704006c14440d000c00c121003c1d019104801c04400c2c90722100194000c4100f6400c010440b9242d02e040d620501c0403402d10406842c034152090000042075800b0081c00c00668510f000384541d0348114901042d01182d03030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 18646436 1250 18645186 18645191
    0x20108070f020307080a030902011812020402030a0209120106051903170c100207060c110105040b150109030501050f0f01080f070513020d0203070c11010302040513050a0b060313030305010b0a0210 86
    0x21103508a01c3d510038600d016110880c04a0403501072a4947c0016104a000366078801074102d040101000074220b500c1641c05642042c400c02006017440d801550b840f103541c800c01420415402c1c00304d09591a040c00031003069548000030b005178a0322034a0302c28003800a1459090346802c551344c170201c0c900254494015124040348200011504001c0c24501501c100403d54a8120f2460203001800302d101c450310109405107802e8a0100052144078861504040702e06c0d07042d280e4480501c032440091302d040b81041207a403400300c007203442400703400d0049584441000300c40c40d2115248000d55010b0308101210b8002030100c40001c080042c980041c0e5004540303040340416000000d200a00c034482c84a44158000b00400c454941c0040040c4007071402004000300f01d4100000440407481b0341e000b07080c1e000324401300d403110781c80035544481d84c05488100c0004005034400c00141464204507408020250b0b41e200790300405a0600915004080f0184a1820401d54510294840c11541d0a1702c1e0b0195 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 18647686 1250 18646436 18646457
    0x6080a02011205150d03030c120209030a060507140c030c010b010512010b03090a06110a02010e0705010504030807020406030f0803040c0504060f03030503101802040306050603070b04030209090a1203050103021c02010807 96
    0x611141303030041030f204000e000e0000c000c02c0d854040c4c044c0000b02c0451010600c5400040300c1d0504034002c81d69901002000342c003034200660f0b03c0708001d00f0007400010800c00c071400150b4504c04084003c0c189804420300460311500c0c111200c03420340c1d004001450410030203001903d600100d0818090644140038441900c950760300f04010b1428100b04d00c0580b0460400000d028024081002000e8030703030866009002c0b0030400350384907035140801c3c8641800940108030810100b00c0710340182000034801800894940d6594503007620311048400256030b40c0100200f8881005110000d400041c2026642071203042d1815072000b000040342c0c440902805000070020300031a00641c811005414801c0300f0400c41c0d6041c04410000b50887d000071905140b900e804900540b0b4005124003c039851141c40c2440c050542d03003400501607014006a0680c4104c1d4080000503011580ca100d680c0350070341e00000d40398914010405140d040b120402c0d2084a2410101e006d40d0f802915207030f1080f058200040c020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 18648936 1250 18647686 18647701
    0x60907030e0610030308060d0305030a0e120705071d010302030c040902040b04110301090f0e0a1103190b0609060909060708060109030b01170f030f0d1505130902010306080a02011205 80
    0x20041d0300406401d07801000d04020f1032101c080c3c00c000641e8069940c0400994801040c0320401036030703210250200d074040c0f00250031907200b604a044e02d8031900303050b15011550700403080155042602c08440e25084001e0034089001e540303009000c40c01e9802a01303121035240d500881d48942141000c0e60103241c840748048255100c9400071030b40c040010f0002c0002c0c003007a4868401c2d070340003800703a48a024105042ca06e4020114020a214581030001408800c501640d4850000554125264146c09041400d125800800c0c01100c0002d020f441c00d050f903440d0a608111142c0401013945110301184400d012800700c6c0010480d40c016070030705007a800398507a00010b07201d58a80e40d00c01019a403000c000400c2010303440c0303508480352002404840200450003005030712170241c03950510b450710b0140450307500404180c00003801e1090008010700110b840c5c0d0003280000389402c40d60300c40e1395210881842156414400e240c01010558060b03c2d2a00706075000904041c0c400091841d2503490707801003440d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 18650186 1250 18648936 18648941
    0xa1202040908091009030605070c03081f03120302030601021c0e0f04020c03070303020909060a03030c0303020d0f022107050301050d08030405010f091202150408030103150b0406060207050f040b060306090703 91
    0x3d80c0000b030803d540481c03071800050031130a032400121001401c1c1404203a4070390040d00c9441c0341036411707207410442c0d5444181c0d00041e00e80c0b060400805144a10001000c507840e02c071503108094281d9001740c0d0f04c0c03500100191030700c4120340d45d01484894140c080c0c1c1c482035014002509a030004c440e501c044100398000640a401384000c1702c070480c00006070240070150554010503212400340c6258010350707586010080340c00d02c00d00c809008503901c42d0488000a110b0740c010050743c104074400040075522000300204903084105108862082c0d9201000400720360b200469014100b86009840d541c144004039a59041c4510010700c40030380800882c0130494290014030407e943c1d000704101c2240d80342080e2013210318610401c4050301404c46000d01a0307008040740d902c5680c00c0035800d80b551740707140e031008010001c2c80c850181490741c8011900307490f5164051035005004070b078000c10003503040c642044445403c6e441c20510452600102c0c000640310031058a502035000c6030720414a544094081c0d01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 18651436 1250 18650186 18650197
    0x705041d04021908010c03050c0705060f0903040305010501060c0201030e010b06090d020103020906070819050901020d080a0e0601080102040f0503070f1202061b0a1202030c060a0e03090a03050d0e0a1202040908 92
    0x140b03549142c000c9000c51301580314542100c40c0341e40900c110745032007444200a110340072000c0c046401003000580780b07460b00c40550390003114074000c82c2e2406540b612210708580f8280c001d90f00107282c0c4401c1c0c80541d0f030306008181c12254424001c10181410781e0002c0d080e0300c56404164054010034680307000b0340e07021794161000f0307a10291503180e6170802d500c2d04e019158048400118034100c040c551410180c820000e9030248001a0010f211445040b1403c1c0e0708035200170702490300f0360b40b501c046444801c41880704034000d14204002503210350409082c00f00800741074115600903031003905d0400400007001415400c031000a000e5929144507030002c61100c0c0310f030503002c00b080d40c83c80303800c90741b00180050384a640b00d008118241e048145003204a840c1d21400740719210a50010003ca46000700e2030b0311654030072480d441264038080d04400403072a030030010f90059038650404c0c0303660444c1d00d420407103c42034424119514500c02e414103203440c250310824480640242d84d05c0c50004e0401801c01d04451 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 18652686 1250 18651436 18651469
    0x20c011b02010608060108030409020706091208060109080127141b010f050906031807051008040b0c0702010804030e0103020d0e03070c05120c04091a0412080705041d0402 75
    0x40840e0004156061505048890800540ca007001c002134546021034885d05841c2d020000e07502c1c2a00c0c0284031030103904400c0055444030b640d001d00400040c080c1e0441000d02c0070b217451b603200b20320300382001402902440c0d10090340d50341000c0c441c0c03020042203e680140100c88001c4c0c24652074503070410a902c1c50030902a0303545403142a1680c83c00c24142146150646000d0360313111030024101c2412182e50146034056500018240081741504aa4030030034400a0381000c1110403240d92070002030410569898100e011908180500050010741c844c401e6018039407441641c43c1128950000700340203001070024040040da0500c1d5a2543e200b0b4044a05000d903450382440300c40d107a0300020b0b4a03544100d10031540950762180c0010903040142d0b58103a0040408041c0c11554080c00c144006803001d050b040b9911040803680d01c0003580150000e50040e40108001305c2612600f80000c0c0c600b180c054081c006011003808208000c602c03c140904c0c5140000110034241e44861000c50701850741c003078003c1c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 18653936 1250 18652686 18652691
    0x20f1c020118031406160203040608010b0c0a0206030c0705010f0b0d03110a05060106080106020d0804110f061201030f1e020a030f02010c060504030503070306090605030a0201081009020304031d31020c01 89
    0x31046400000342050049102c0c1048091b5914070001c180d94130320031840b8041c086080c5100402084440310050580d81c0d01901c00d03294040429800034640c1d0380100d58034030608a000c1140400c1c00001d00c0b45100a94042904000d07487c030340000105c0040d240e4400a003000103a14084011410620400c10300f9039100b81251242e5031903240103070500c2024080c0400602c50711040a01041c400c480003400307036401c001c015503140b030306005100301c90401024054121104000da10480130351640400c2c0214000c40b685000e9800900d05565028000e5040d181b01003260342d00c40c800751340d960081104480d4460208180543c0c64801660466044a4040c0035075151a0402c001e1541041c021841040c43d80c0d01040030b141c40e04107040c2103440d5401840c1d003661204c000e00005500680101341c008561000c101c051960385c81040c2c040c0d0340700700e408600141e44070364032043c0b42d0305079100440d030a00101c454400384419580c10400d11142c000c582122138130580700e01f45149940e80e045031404040d40000307 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 18655186 1250 18653936 18653963
    0x408070803092809150f030615080a0b010902030a0b040c0f0905010207030507090e0c12010606091d070807180f030b0606030408040e070203090406060804020f1c02011803 75
    0x10a4aa8018a6802d8041c04419980080e404403205404a2a20f064480e408980d420080c602c40205009075540d4181c00396030b200440c00940614180c0002c40c4251030220301c00d2440d1892143d88030301580040d8580e80300941034400902120403060544602d0b501c0103031a0368034007171060050b0010004880c1c1003490049915019648401d002c0c0300300c3d041d615081581c56542004a960362010311001e0601e81044405101104150b0030031000c15004404950300c0c43d100700f000500349480304000340c480da95144801c00105810400c10030090640424410b0701c00d1040440100c5904018912020030a0440018002a0064640c01c4e0349440b07131803a154090fa19a031410100c80b10500040c1d4500380010009501403400c80d040b01c0c03003281d0043c0114106842d184030200d444c2c4002d4181000e5000602c440b080039160307441100028566070742c401d802c50400b4018401d002010100302c40c002c00d640700c250002ca50402d0640741c541d56080c42c01510200800910841007900341c2c00080c00300f0f280400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 18656436 1250 18655186 18655199
    0x3190b0a14040c020c0d02091003050d09061403060604060c0c1e0302010305010509060f010c03020309061305040b03010c0e060a0504050303040f06080c03060a03030f020f1c03060501020304030b0a0203040503040807 94
    0xc5000c8040507142006101000c01090760f640320215907480c1e1000460300c41e01b0060070540b03452a00102c400100001581d02d0340c0d681824406040313031290014101c5039040050603402190449001c0d808144035255007016408034204e0b1080307000e002c0c280003404001c01d040144246060703008000c02c0070100e0412004501036680034000e84800d900090420740040f6180c9007024407140200c000900301c41d080f402d03000065035178204500e015010340c0030502034098580c64002c0184100c49009515908450070134040100f201c841140e0a0b00036072410007901407c0303801260290420604440d2030b522444006001c464912854001c513805010115002440d8126410004141d5120340c44100c0e0b05e58402d049400d250008540c5107500c001c0c1d00b5000c00101c0c0c000c80212413000b400388151450300314500070051520700d96880f0b90905484041c03141d48803d41c10b101c0c241c05404240b0113580b81600c0c58075104540000500061011039001001c070f02040030030000c45000303b0600050302d0485940702c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 18657686 1250 18656436 18656459
    0x3070807050f01181a1b0106170f06040303020c070b0706090c05150306040c050c0102070c06020705010306060203030a0b0a05030a0305031012120f180803090307061403190b0a 77
    0x401c1c80d004070500344041c0069801034480c0c0950400300d0b03035403401d40f80c9820005685030304100340a80710914201b02c0705403128041c1da000c2641080314000410020320301540d40d08132501c8500442001d0308081d000450f5100045031045c0c0054143c940540c6a00062411509000b42a4041109035000091500c2001843d400034440700d4090716503940c1196885003031041040c080761204402110400000b1598605548820505e03801441c0290620082d810241c1c220391000c0015242422490003c009003a030400540002d0034003803070284a41441d1143c040c1d501d000c0a8041c902d11511064a440913880c4d08004c0b100429000341224000407103030801030825401075414001001c009180880c810004a0b03000e40426030003407000c507802c1c000000c00c0307803580b110f01c856408010117070380c070940200c5c1e03580f507188050040d41c40a503031b95002400406240203001e50002003072000d504c05241c801020380c801d8940c4040c2c640c1c103811002e580350024000400c0c3c903440745075002031180c034042043e80605 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 18658936 1250 18657686 18657689
    0x70b07050f0607020105040210081302090a0f05011505070303091a07090e010b160305030a06050303040902040504050a05100b0706020c0d05030402040b0d3c0311070e011401050309030903070807 85
    0xb40e950588440e003040b401d840c0b0449010f504080d40e0f0550800c902c1c40b8500305580640b0300307080d0400e11541640003540c44501610824801038660080c5980020548101401044003400240e042000000058494041c0b244090181a9103040703074021300c85480c25540346040c51a1144500746041000074003014954000d1034a4226010000b1401c4400e8800302c692846030f01500349184001690300b155a54002040e0980e001c0c0c9411001031a03403001c001600c003803e010007025841d01d0070f002c188000c03180010450103840f400c0c40180700900c00f01244850640f5505141250f4482c41c500f805d00c064468081c40b01d00c280f00340094156a03079804009940220300c00c0724180304280b810700402030603111454000c0c007810b2550820001186618180f055021000b1888007034104880744000001d1041d4401076000c10210040b0343c0350311034140030340805040310301921034455050003400490b122801030040d0500c40b0000100c1c1c0003042c01c00c1913a000200007412074a0f16501e6004003516155113 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 18660186 1250 18658936 18658963
    0x5010602070b0c070e091903031a0612060409080f030a09020a06031506031a040204080c040e03030108060c07140a1208090102040b180109030506010608090616170702070b0705 77
    0x100040403418000c0302c001c6420300885680107041407400c00110820310394020f40f00c07664500c1500180060349064145100c00c0c50701a4030005501c5c2c1d6002107482e26801c1c0d61400728031801040005c5150303c4080207095812030b0381514002542d045600c0e0120051280208080b00f001011003044001511034001c50321151083d03a100202941d65030b030540c26541480400d0308403410200d024000e4510a070b000f4549a403608030b140102b02d041d00082407c992140c3c11a1503240c01400030850141401c0c001c11442c2c265a400031883e640c50145031589400d009040350007003c1000850380c081c8041c9409965030741c82c10f042030760302901e10392400c141d91444102c0b10034041120040002d05c44501807081d20b08540301820154039041418580e84e58084002c60414180105d5101c007001041d02040f02501034842c0e500d801000d42800d0210f94580303000102000c12a01150320402e10180c0d00941c00143c08102c0a10300000e40c88500080c1d0404240e03821061071040081801800e1100008101e112a0038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 18661436 1250 18660186 18660193
    0x313080106060e060f090f030313060306080d0c030f0c020f04060b071119030b0a06031205030a060f050a03080306030703140a140c060403080c030c0d120c080708010b0a02010b040c0305010602 84
    0x10310f2090240d5070003013008400c10402c0c203109030143e50510004402c0214002000c4d0b07850701d0144100c0070980441c50f048440000d503030b06010b0200300000c204d802030001c2182488005c0c00d940340e9000741403ca4450ba139004100d0b00d80c20540464640c895404e030b5081000b481441700c283c43d80b8101c603080d04200d00c2907a00c0e11180a9200c000c1c02d02e0705a955043d0220030b1070859150540d12103030381c5402d02411408560750f603200b001010512880b20344001c0c1c0c4035070f80c905990341130031072200090300c00341c0c5c012481c4104401403c04c8560f40e26510441101e42c0144a65140da0307640f8002401c2c0006544060000c0304a120464081040401d40b071b100b1921403408211804922200c00b030b520007004001039046401004240042150b030f0700504003404e04d143c01ca910740b0035407250311400e2454040321800494180d44112282e4081c41c0294640002e1500d070020b0585000c000080c40400184540308001c000040c000391031034801c0d0415500c0b01c802810601c01d51100c554010f0040c002445990010302 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 18662686 1250 18661436 18661457
    0x309041b030c080609010501030c02100c0f0909060b04090e0a050a050c01030e0606030d050702030723090708070f030e0a0c0e0609010806010308120a061502060405010b030d0210020309031308010606 87
    0x43c040c8150070f000e2100601405596030034203005500600346038141c007003580b261890512407060b180c002e007010094195a00c051030001e14002410400c503542001ea04036042210600c0b0301113260f410f5900315034101d000880c0d00c2181e411054100300c2c03180d2028005005034418441480740c00a41c40e241550282e0302008214a0051250346800003a030700241d168000381c1d074589245100d0005890b010380014141d809140c2c5d02c804060401c44064114002e00d01342d0540540a442e00d80b5000e039102000b0304101c200c1e4608490300a2100e88800b0504040c907641d9840807030340c01401c00914000340d512101043c98140c440801c8121010304907266881280030400206030100f001c10101e04032680901900d0500b410b00911206543c0c0003040b204941d41e136120000391410880c020501254420b801410160500c0e00f040c90070340d003e039669140030303521410b0050f03e040c0d800154040704484607000103840b0340b12094401d096200c3e00c1002d016981d4a0100820481c106500c8003089600d0340e2141018070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 18663936 1250 18662686 18662711
    0xc21060501020703110103060b0304030801091109010c0b0a2304050d02070e0a11091c03030608070501020d0c0809090103030203120105032a0102070305010203090307140a0b010b0c0309041b03 84
    0x1188603008580c0182c0043c2001c100013a100a4501482d000505000c11011344424600100c0d0b0002c032009e5001030258030040110110304d21031800d1204ca00c0141a04d0503201c0e070006400c0400318a8004d0102c0700003400a0f1011160341d116058220142810f4000c403129a03101e5000d5010584080c0d41078050240e20b41541800000c03290112040441c154503184d8450b841240244034000021502c000c040009034150fa44d1900f0480070303841c101d0300a142e41c07a864100201124060f800241c03140e4810340b028080faa0b000922000030090618200704d03400d84514004145020b05a82a5000300d51540080101034006c40030300503c01700c00040c22410781c0d807001050350761054008a5001c5103c0101020f0b410914641c921040440600490f48030942c0da81d0344a00b2a4000c07504280960400b11303048041107180340908850212070302c000c007242d007866240c00780380f9039040c030030024007000004180040c2002401510b030451001081042100e594628404986000e00305103000a45030200c03030000d5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 18665186 1250 18663936 18663941
    0x3270c08031801050a03020f03100303030b030610120c05030f06010509070f050904090f0b010b1801030509150919080316020f070b030907030c0f080d0228020609040c21 74
    0x812548000e4100b07500c0c0d40d080151840d5200d03542d11420150204400020300750404c00940c09088000e24001a003451420010b049440300071032144642c024505005076a0041c1c50032070240e5a8001d840501c48046103050076684265a0009401d805584241140b0304004107030a4100c50040d24050340d1580d45034030440314003404103441400b05200744003190050500342d03c100c00300b07403150ad0501d0840c5a00d80341ca00074507000f40d20640020200044d0f41414046070485844144070030f080901076807c3c8060b00c3c07a06c5580d0740b03203085125840440010940101040000f1200e14091035003a0100a03601f0110000e610848031042c000b1b03165145800038910002d014014850014050000141080c81e0a0311a078805040511a0711070f140d800300100740c0003d81100140a080b0351070620361304d00001c1d075040040040c841d80c1903402864149041124030040e00e1a8401720342c1d01c030752800f0202d10008005020388071002e40c20605e0301d1503034580703160002c0702e06264100c004425044007840d20020000d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 18666436 1250 18665186 18665197
    0x20108070c0c030f0f080309060405010e01090b041401020f03070f02010b010c0f060f0b040c03090209010602070e010e04050717010902040605030c0612130218010e0a02070206040e040303270c0803 86
    0x101c4030303100ca010401304010007480f0108520659101190f040079442d100c030303c1d400986010559402001c140800c0100903c150810840c400e0001d11918041e6101d0b440c04080003040680600c031403400ca0301036a102941190903101c3e5612202d501d0f07041c1548024000c82c40c044404002d50328100c1844d103c3e60007244118499948440c4403e0010803035980c0802401010a21914040e1a450002e1440e41c86004d0100703640d100d0703503000070681c20305d0040102015041e8410415900b0a00080c84203c1604a015043da04092508071542c1c80c1c91070704c54078007106076200c1e40c07500c6429050880740080c190440740300c090007250203010082d1a41c0c2003640319103203001050341c403040401102602d483c00304820350340080120750041030440d054000c2080c14480b4a420b8000d1080c0000500c004900d00c224143c00a14540003181800d203541d0100e40d240c4120b00418224540303540c0000c0c10184a80c1028486c3c3c1c0e002070644280891016044207401003e400071617000120b050046401a4000188ca4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 18667686 1250 18666436 18666443
    0x409050702160806100b0702010e0901270b09060d08040513020d05090c060a0c0303060509040303050417030705070b060607150b010e04020f04091508010e0c010f050a08041e0b0405060103020108070c 87
    0x800080c51b0043c6695550302900089050041844100089130b850703410490003402c40340d1110380031380d411100e12620030600d01c00035000140341c82511229912a10b110660010054661411180c03aa04005205004644c0301c1613000e00d080b41c880b0310340c3c40d40381c0292084585000c07090000d40c1781c03000619103032404030b0030040d0400341c02d010340d00c0140e10501075048254002c0c14005001074032200030030580001190107802281d110014041000500501402d8400e81040598210b05010400900c02c0c810000c0140070ac0c81020049503559a840d03040350703219648440c2a1480d209400840c1d00a070046206590100d0058044c2c00003038140b900850740c2c9003640000151038541410a02c10040404020030035041004050225059409110f8010503401800007402c180d90f5800005062808a100707510421001b441030102254005801c02e8006d9480908001d202c010510041210b00c40c0d2180a0b110b00c5804060000384000410290b042e00d000783d0361141c03143e80d070341d206484481e08028000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 18668936 1250 18667686 18667711
    0x9061d0f041e020c0606010810031a040317150103050c04120803040302010207020607050609010606090303020a03030b0319030302091c020a0b0903030706050f090f070b04060509060409050702160806 87
    0x50146107090390124a040e00e12600700c851982c0040c6255003207800c01d0f4140a075a07840501406103540e0003000c501e83c00090a03194400d0541142c1e10000c041c81c0f02035400b00c1400c20040071408050080d40b9210820684051003102458030100c0403140008111a00d40803d1908001c500c0c0e51503182d048406586a550940a02c0302c103d5884145070b0f8402041030b402c5540c24480f000c01070b6a4100209507580c0124020702e058209200003d003100d009038400028019154800c200003078001c16a01501c58141c10002051b03120b06000c03d05112050000348a01510800704004243c0c1540c041c140f0500240c80c1680c240c203541c12510001c0c4941e6a003e94040860b00b010000e404c4684c006003000c0502400b50390a24900e50356280994005607170720b19040000c0002c01040682c2003287d96400701460000b030400a1414070307552024400c0d801500100680003c8282d00754507140e04a40050a62000822441c0381100d8020348400141c00b41310581e1401001c0080d01590000e01d090203295011b422 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 18670186 1250 18668936 18668959
    0xe060a051b0102030f01030605010602060402010e01030e12041706010509010b04030f03030902040f091a04020604050f0a0f170f07060203120403262211010804050f0102030709061d 79
    0x1580c1541103815000050300c6180e4004402100c280003660161703c2c01104081c86504502d454415540140c00460465108004000240c0e80c0700b031003244102401c0c24006901e0110f0400c3e1030600104200d9500d018100050001e03288601c1086940301d01d05610581d88543d80303500030000808028410580390f401c040c0000c0c00850004001003112318464100002e00311242e9022500307603816002500344061ba00c40ca01c400788052541c5841082180c1c20a1355500d1810781c0c0068030343d0107580502030054005040c004103c4c1c840e0843e05011f004801c0102a2450b583c0c0c5c1402110000010321b02c009010f2503070071340b40f030031000140c0c0380607500300790003944c20015141145007900600030030537400c01822400e0310744501d1008000041603205000d0003547ca05d42280d0302148a6400c10060340001651280f100c081001d001d00c80880c15002d280181061721641881440c084100c0c038956250352002081c0300c2e410b6000358100084440644492a4040300301d0741a04001807412a05900006c42c41d01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 18671436 1250 18670186 18670207
    0x2030606150c0109050d0906020114010b0d1806050a140c1210030f06050601090f03020303030c030612030309011a01030c1704020619051e040602070b0a05070b0405060a06060e06 78
    0x741d0000c000004002400e05070301c1c0b0107050030355080b941e058407180c02050801300700c507501000000161403031707000030710030b40f81c600000060360070051140d03100003140400c180d00804065080900305009040b444500300c100781c00d018000384820394080701c4c030a292110144501c0148020140b01d0200019000d04281c0030f4a00350998440050105130b00c3c0301110300100c001400b101000c2205030085900140503c0d054001512100098021708ae042281e6481000141d03030000840e540080301c401c2c0300d501ca8483c0004108a404494038200f070710b00000c0104044200150f100400075a00241850001d20b61200150100c450030060400010128110424016140c10010345c00c1440981058588078444401c010b1020749582070000046002680ea200c00015a244006c0d260055583c6845d0030314000c1c000e5aa0074880c81580c82c0c040000c100200740c28012001c0d1a4500e4110b10000007e203400d20f056611b9100445483c00c00500c0d01c440440c54504c2800400f80801c0044d16084c5441001803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 18672686 1250 18671436 18671449
    0x6030a0513080307080709050301050c0906070615030803090106050906130c0210111b010209011b1e06021209070305060117100c05040501020f03030903070201260c0a0909060302030606 81
    0x810241e15802809002000550000b00035886030701995140341c090700b001580104040102c1d4000780c440c0c2c1c1000244407604c5052401c449003a0700c11503240307a4804191524034050b003500c1c090080c0d28060840000107001004000b1846001c0f5500200301d00c5444104001e001101610100d82103052211040000c412980c061400c20360b05004a81d440b40c02101900d09480ea140c0c880180000c01041302d01c200c400c00d444006003a56081d0095051444440000300003018240c0700d00088029031030400c0511610807240c0300000540c007110902c6101c80d0034160007a500c40485000544003600000706080808240c0070107403035101c5e002d0103042e4600111075540d0307001c0c0110b01c0064021100202014030440c46004030440ba5504c0d2140c6907490840060b05120740c401148015030010000c0125330380020040700d400e1582400c0c07110f884201076503512030b04076400341100a035001c000c0c01e01940080d26005090740f25602cbe42c1e55288251a5920f0340e080d01c410b0f100080d007650268001c02c1a610303001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 18673936 1250 18672686 18672691
    0x14070e18030915040501020f030f07110d0507030501090b06040207170a020c0306011d070203040f050904080705060906010911040503071203020a050d050901021b010804201905130b06030a05 83
    0x11421282031002c400001100400e01200070480340c24001020455540c060040780c0512640c070000e1804c02141241034040e9228000e00201000720300f10407000702d9039400c410100c0064120342181c0c00035440e80b929500a1846103000e84818022030b001032602e06e000e0084580c596440071031604c0c0140c0c452154542034100040d03600560080401e020026101085024001e00b4060030b0202e0b04604456076103040d0602038007800c00c54000300014412100601102400c0380c4096540f012150344a06100c41c031402031480041407401184148405034500003002030680d00c41000030000a040703d010f10314a03204a110703c0e50180c002000412421052401703903084280a40155a4640000e43c0c65a003401e0310348a1440104d20081140401541d0410203c0c00616421000f18030b0040e030311001a000100080004100c07500d6501c44c1034000060441301058080040d040041518040b0301c002e0f03404006001d03180c0903d006840841080e003003400341d01e05594010300301900d1521a40c0a450240400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 18675186 1250 18673936 18673981
    0x40e031806090d1a13210210060e10060f0905040203040809060f0408010506010f200a080d0609110403080301060c050c0303040308090f0a0308030109020d0605040f0914070e 76
    0x500c50b02e6035640310110082000c2c3e1080c41d804103009041d560803611000007803d14401704004405210028464240c00183c41c1d00684c2d9041c00c0c030010003402c07807400d018056905c42c0d50f420404009040c045c00480c460040d9600d120323203205943c56100481d0b2103003440034004001a0b40070300400403402c1c40d40c021a08240980c0400340740c43d00304800b107220756000c41da0146207040006410001d2100030302c16283c0008003440c0018000e040000d000f4450b240801440003141b9520168a041031410001070f452158405030150f104e030002145030b80107100510541c0d80180c1800e005501c0b08003c0c10468040e640c0c49035249046900b003030003c0320088620401110540301c1c4405004180d6800c00c00350000f948034905c0302c0d039100e0010082c480407001920380a40611016282800040c040000b0382e130540d01000801a1102c401c10f001b0400743c9503d07413010350801d1030003600c40200304158000d040b03442c0c050169600001503648000380d56401a00c146044241e01c0d50103c0e500d201c4030b01c2042640d030007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 18676436 1250 18675186 18675199
    0x60a0b0a0f0e06090a020705120d020706052401030204080d05091305010e04020a0b0c0c040b01050d110301031a0709090f0605031917040b090402070c030c03080703030b040e0318 78
    0x4039404042201e80a80d00b06842d18851030301009000d1421001880e400800c3c03100c150b0034810160b4440b41e88002c00e00c40c0c1c010f003d01c08600345060031101e9055036820781d00904d0070302560400c0909102c010307040075100c0781c102c0c0700d0700070a01c400d500900072074086400801c014405869081c0046480d0780041c01c003294041c0c1013140307100e030400307640c01400d0180480b0400c2d030080d400c0900c10442c1da0b4183d580210003071074050104001aa03004a020080203c05a501248849010004940501c65018001906868040000e00c4052803030041c43c10703030b4840e0741c6102c8000c0006103003800c02d090461ba00c40003e075143c030085c4041400b03900610281032044002003811502c4800180c103144501c0720462500202c0c00030700003800b090b02d609180c010707820455985800c0c240706040d4114400d4000b041c0c051600060309008006940c00036100039900018200c041945078546100e080d800f01206030000782c104003040303c0500c5c1c98070520103031921040c0211700e0004d40501c02c610407051000155031062 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 18677686 1250 18676436 18676439
    0x20a1b021206010f0816060509090714041205010c030501080d0c0302100204090906110c030406030b0a091d010c02062205010621020a120803010b0706060305120705011b02060a0b0a 79
    0x90030084140684080c01ea41e2104c1070600c44014a804a01c903a4414000b940c440100540c0d034102c1708aa401e0b58060751a40f8103a55012419202040d0740710542040401c00540054841e840c0c0b60603000f524802e200030300c88104444012410ba0f0300a016440c00c41d0007101e041c14000e80039004131a921403082c0140ca81c04400820b170042280c20682c0075104080e145c584410030494540314041c21810401a80c500b052200c0c4a296038030301450007200c2c24195118240b111a51303ea110310401401000c10500c42d946100600741015040f05d600d500302503007440c0400c80301b5800802d100b44a402c1640c0b00c0c42d0b980f160a8049050100d07220020f17109550b07500070214000e201840c00e215581c1c450924403112080f00d105200000410394030004122800b17600c40b2000840c6074046a044880c1410440c5d00d502e050304086004000c039520042c2036116101c012091300f074145025164090180008014074680d9043c5044144010039840c801070f0044000148240b480c0c2c0d000d40551000506000d542c02d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 18678936 1250 18677686 18677719
    0x9100215070e12060702030901030b0303070606030609140703080702010e010302070605010605031801150b0c1203010303030603020406060302070b0403050a090e090622030509061e07060902090604020a1b02 90
    0x100d0a8405800040300014080d616040200300001070320000c1005201614141c01c1c002d4481c083c80d81c1c0181059120020f1502d1617504100380d410580e048103080002ca50317646060002000d1803842207982d21554480384048200218010046941209843d03181a586038011a0303060102c4c410141419400d01225010070224450140a0075090300c5165690808280c9840140c0018810840a07030410242007000741c100c480e400c04072601107154039160700030702020307a0400810f000e01342441c460100c000021705600d6000001142e000342e4007080341c10345400f011802d80c414500d0190800c2c041601060020744160010b107003030304c01c1346800c41d04c071501d803104254103150541e81700d01c0c00d07400103060111100710124500220061040c04814588040e03601800034029562050b10440300460751030349004503404501054423070064410350b20102031603d0401045100016406541e03980001981800c0600c221100c003417060310350400e480200f40b4140d0440030302074802ca070080000e110445d500c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 18680186 1250 18678936 18678973
    0x30306090c0905040e01020c1207030c05030a0305060a050d050613060b0a140906030f070308030406181407080d0c08031812030906090c0a0b030a1e0b030709050c091002 74
    0x140102c0e5900710025190200b0401942c01482d4182c026903c10044400c013850700081c800d46000742803910a490b1000c504042d2040d00caa010040c00364000040d2100741d80d036055000301d1084008540c201c0c0f01c0c41e01c1e0824481c41c1c1200600050051340400c0200d80001c8502000c080e04501c500d10104100d0f58420225402c1c1c01207a111a407010001c4c94000b044c0d280207101c56074041300950052040b082000b96003507440c456840702070401c400010118061002942100720488602c48244003541d56500d0080115100140c40b04d810380690324000c54075050104600b861103880c1d683d03010b020a4a87c6880c060390f8030240c4899070001d00d0103002d20007000103004100c03440b800400350035101d19003c260141020402013041d0055005508403101c5660307851145400d0701c401251041e1241d41d0b0202e603000a041c0f03e010f03140518070000c07010300410760325000741c00309100645c2500c1c01b080d66848480103079201500c11b480002c80134421040d00d070a0100744c8221100c02881124800441040b90190 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 18681436 1250 18680186 18680201
    0xc1c0e101d010b030601030b070e0a060c030f0e2b0b010f051e010807030f1d030a0905040603020a060e13020408160b09031e07030501110c010e031602090403030609 72
    0x840e15200e0452960800c009041c4500310030724940244801403141000a448400500000308008426404a644580f06540c0150740000150604043e16202c0c0780c05407000d9580764046002072454249440d0441c41414403207400c09014004081180d000894500b101142e1041044a806241c010b513000c6070407400c419008003543d46071458024240780c144101c03c5004850790b101080c003004820034590384480c851b0b91044041c50000741c040d001400300303809440c010660750321001039900c410902423004401070401c080e05850310102aa07440d03040c001610b00d2444060752024407440304004060180550043d0100f00818402019112400c002c1c100d800c25049072000342d10170004280c65081036a0b000000c4e01a05858608004629000076500e41c070740801c03200c1d024400035081d100e450041040d01c01540d403110003400210303200071403204150801001c402c5203600f010441300c8844008001c440c20780c3e4500c004440070b80802e409000120700080c00407010103550310030003e41c1c012507219540 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 18682686 1250 18681436 18681463
    0x1906140705010f02040303031401060f2604030806130b01020c040905010b0a0b0a030501050a1212030204090e0f0c0a0b031b0412030201091203110414060d050403020f12030c1c0e 78
    0x507183d501b1402c004044031a8074024003400d038645001031110b039800ca80030208038031207490856041c84d03d40c06890512200e004902c0c2c0003884040c00e1004150300104401d102d900d00f55100d10250707505078442015140c070b640345030740542c00c042a9920076040c07540220078040e000d0720001c00c940c11070001050000c0708c1584038044228012814140c101c1d41805070500602d0200d60f4035032844e041541850805600c030300e0007010210b100c0c1a00040d50b000c1c2e0140d90040c54003440400c4038480700f400641e1241070145407071803103005040748000301e454044001010389081780d1003141141d44050400310a800f0044a00700e641d903081c800010700c111403140c40c0b14034600c20760003c02d95861a00c0c0150f401c400e03a000788001c0c18200300031050408512429581220060b00c0e090f00c0003102c8a0202d07180e845401c80c8000141d0428080000380360f0009200c5008001440c100c440a071004a040d45060100360742104980700108052402c00c000d1040d00705400b956200c00081300c0780c001a0481c41c0c184540f2265 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 18683936 1250 18682686 18682691
    0xb0117090a02030f060a0e12030a090201020708030a0903210503040b1e07090905070e0102100b01091206022502010905010305040201112b020a0c06080403051306031a1906140705010f 80
    0x2250319641c1f4003d01942840da1801010446800d040a1110f40001403400c42e041e40d54064010541e8400c126800c010010070301529074039180d901000704808101c7c08140c40d800c0800c0745a40c2c0c03640c01c4840b00703050000300760b54440c2951107a5031128203005000e44404805c01c0081c49107801c2084000c400c2e030083703500786c6860755428941303400002507c200500210512140010f074800598001c188800d070214481070000792880c1000c01031f04da08620340c00515016080c80380c503004008681e4000e0180f0003040011781403049840c2c0361501c007900b180000a0020f01031900400295000b074008582251050408140c440b001c41c07155490007a01c1c82d1072702c4100006e1010701c464000c4440104481020038030180c0704041d480e459a5000014030300c00c010400a40c0340004003454030600c00d0b1401212002e41044400707955110080c003501c0c05458085540e0000790601d0254a00075854401d01ca203c1108003184520703021090710031510010307920b81000c10800201c00050420300c6070b5204607040b601c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 18685186 1250 18683936 18683941
    0x1503090d03181106030709170a020a05030d05120406060503011803030b0109081c1e0203070203070509090a02120c0a081b030105010807090209060409050a140a0b0117090a02030f06 79
    0x800b6140701002d556442c61140380784101040503a45a8010780c40d05a866640d45d8a49000407160302040e41d00049501a107485d49107002d28001c80e0050859000711003040e20507445e030b41003507182d074050480c0c03001280701001790440c441041e640e12035109018010001d0142d54410100303095520402110f200107503015003405c00c06030103201d8500000070038a000030003141800105990381d040324800603880710703141c0b1040d0320300c81c8100d220455003104803541c0381078032444100180da260000391003244280503140001c00c00c0d040104100c0c1c410840c0f8401030403040c1e07890302485640301c040c44040c00e41d40160035640000744c841c806071200620a4900504141c140441070741d13a401e05038561580300c1e07410240104450400000c130304003a03c1e1100c00c016500d0107040e00280061040754001c4103460b0820b810001c580311507034400c15040e03082c0300064950342c0e6403010b203400302e40c1908412404641003100c1501c0508001605541c403140300c0c0304070340305042a5000285400a10b480740106940315108 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 18686436 1250 18685186 18685213
    0x60b090f0604050c0f0a270b07060e1f021602150d050a05040201052b06031a0901060303050406051605060f010302100201050103020f060319050108060615030c040303030b150309 78
    0xd0541d04c0b8218504403800c0000d48803c83d40d0900c5050541c000b04002c0840544841c0c403640a0501c0c41102425100041d0b032380e400c1e01c08002d4008020a484842c50030301403040b0320a021469076210703807030040145010301801030000c00a402c000043c2481000b05001000143c84402c1d03001030350540010029107805180a941041d240700501002445052109120040c0d8016043c0c40f98024000900d010407a201c14603400c16105040405000e1030401c50000306002525000300d101101903916424180e40b2000c01900382c41032444024000740b81007004010f9548110081d1101c055410740903400310706607880c1c1500d04001030310100000082d40c4010811450003108020039556140003e111645c034540014441c0d8a8044000d8010b6100100081103408405655807041d0401c030030820855860b04201030303449208444442c01142052000c030500080756055030b1240ea8400155441c00c0d0456500320068100c2a03101e0b6048007850301010011034a00001e07600c120840303002018041308888 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 18687686 1250 18686436 18686441
    0x9070513020a1e034814030703020307030509030c0d0305060316091532060913090b0a0908040506090103021201120c0b03010605090d02131e05070905010903030c060b090f0604 77
    0xa41001a01001141e1180340012845200d1203071440d8178801004038001c410503682c84003410301d0060318150002c108500c3c6034056001d5400b403001907904004a40c3c4886c40a0742d0391103035600015841c0e2110081155991003600a01da025070042e0a540030b40c048000724841d5022036070003100708140c4500350603808005040c00c950003024803040484002c1d0307600d410403880000502a0810f10f0203070040d21070303094883c042103540401d0302529030600194998082e1000701003800c0100c0c0c82d40760b0710000c00e90f000c0845c01a042d865070000d6500340713060700c1c007420040258028044981415000d115150b008850741d035500d8000c09440318800041c070400d103060455070565401c4081d00010900050010b0342e4001e059681000041d075002c0d12034041c50000500c015460000010a45d08001c100100c1d000441c1c2141c080c0745082800b4041c2d501c40d0b10301501c007181c00e0f0103050f00042003101c2c2000828421700381c841955010f03000000c1e2030340200c0c001c900c0b0311008840683d003001c1d5100610125007000e1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 18688936 1250 18687686 18687731
    0x5010501180209060d02090a0302090f061305160c020a030807030206090c22020702040902030111041703070b061309050d0918050108030307200102030906070809070513020a1e03 78
    0x780811883c0080c000c0008080303028407920425a0703a404141c412603074840300404006503400615201c0a072406011260340ba440c1166020b000e0002c42141c08801d640702d002c1d0720301513542054080000c40c000703e0211040e9050321021f136401b00c1400c0c03002011507101c03001480920b0003540a04421300c1c2140c20249030000300c804481c083d14000665400551403211160301c2c0d000c01407005607485c4581d0001030050020040042c0d815444c0c000340e01d40c0d00c0325080092003203d225101d10142002040041758880c000c1840150080c001b10300054618940050031100c040c21042001406003481c2d00c4440c50440b181410101240b900201800080c0b09224008039415802c1b10138006907043c803002c2c548a000c00340050003803107104903010444001c2181d8000056000500842d100d00e030090420703075100d00030740d03c080118442e10046060360401288810540700050b0401c02c507805c04103001e40007540032441c040208814028440302c1c480d0b030a10b5280301190155004912640c0340e050017504c41004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 18690186 1250 18688936 18688979
    0x2090907050a0206131709010513060201020301050f0d0206030c0a0203070c0609030c091a0f1206040503031b0f040509190504050a02030d0302040810020d0207050307080301080c0913060b040e0a05010501 89
    0x800e05c6950004d1031500101c0c80d04420341d4001d64039409a000141c4840c0182c150f00b05648030b10050204000b581540918100e40c412140c041003605081c09000c1b502680e550040e4020200304001400805800002d088074601481281e00c3c1100380c0d00c42070409192600f1100c0000c80d40c0700e00b04144142604200c020703213455202040310480143c85070701e8192003280340360b01a02603e003100b8815070741e18070030000c4002400107483d1503281a2400c00e48a82c000c27a40c2e020096011011040c50031488803d0720b441a40c3d4141141c030f4241400200241d11031700038690464000301c4c0640380b50b400040e004480c0105e1081c0d000382005140d510426081c40420009802018030500040107081000255603c070361944200050384d800480031828040e2084a0001d0031a120002c0c80f0000c112400d0000c2d0304a0340f6210940b02c80c8a2140204020b1340c101f42c1e1029800c0e0f0030482e080340420350f958042d03403840400502c00210740703e0001020742485c07034421095416035510401005070001117044491003914 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 18691436 1250 18690186 18690211
    0x9011707020d031a0a0b03090f01090503030106030b04090f060e151e0a0204090203070906110303071d03070e09010f0f05060a030b04031103040f06030c0807120c0302090907050a0206 80
    0x10319000c02540c8120948001c2c0c101a151801042c05503502c0c402d0a035440009855079242a488504401d00d99100313843d031007980d105030b40340460a684103114410100c2c0c0d000c40554039591030000c1c114050030465050541c01a501d400f004001071584500c441120710504020031007400000c1d015040030790310940d0221455090080003401ca0b0104c0401c501c16030050301c1d03c0c00d151110b07070f01d19009010305c0c0c0000310444d100009225500390441160760072610340e0b03519a035600e1540c5811039142d00017924150003041d080300c01c00746280c207a2036281c070482101404685c2065991005a910308200380e41d00450760359a41d0b12520340d000c0354081e1460343c9001040a01a40c24460041484540ba0b4800030309646840070208003014866018015101050030483e0344130303622889200341c002d40500c1407030b010901c0c02e044800140d0240d030b6910311912142d00e40d0482c0299200960300900072542030042015400c001000c400d584110005000343c6495650366240e00c002000a0b1070058080c01c081504035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 18692686 1250 18691436 18691441
    0x3190e0409020a090c030e01020a080115090b090904080712080612060f011509030507060509010f0e131805010f02090a08150604020703090e0f09070b07051005040206070c030602090117 81
    0x840f105582c8040741e00c50b010001d1032240c042003c034001d003c6510081c905500001c5c0c41420184d101080505880702010380c89802c507082c1070169000051407103400c603a18000d221300792640c900090a10f40c0580545a07280c1b40406c0b075698000805109000c0d100420f43c401c0510989e41402100c3c050a0841038000704001d08001320f5842500c0d40c1407141c1c0a02d00501e40300803032018841c3d0200d00c0116404022600075689600024103650044010240028405c801c208a602d00c640009050350101800100d040141458614003800c000741c00c86101c0b101880070240010402d200c0d403407000140620040c1c83c1c0200100300003115034540e00102c01c1d980010003140d640c064003500603420000460380180d84003080d01c2d00b620200a180d00808455a0720030421407101c002043c00351084010350255840161210150000c03400342c550040c0051f031061403010002c200d15809190420f0008108030f0910085030342c0d00d2040d5003d074204440b10380d00421800038650b046400e40b50400c682065005151 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 18693936 1250 18692686 18692689
    0xe0a1a0a030302100203060406050a0b030105010311040e06011101020c030c030301080f010b060a081506071415070f14130803040602060c0405060304110f1002030a020c0a06090303050307090803190e040902 90
    0x4c4440c031000d815080d5000002c603240341e4075644210010309014040504403651a5403103170858100b40304a41c0483d050078407c80f00c245800007213900350740343d403d02075007540c81340b9004442c5407180c2d00c850419503508000c01d40d41c0ca2400c2002e45121000750008559940c1805270705400c6c505034048600f02d0383e041034a040200e55a82060b00e401010302d280000040d661034507015482425910035941001c80000d100052251480741000d021804204507400341c0f680035580c84c1e480000321840400181c9940104440e60322810200382a6030400f803c460a2018034041c0c1d032450302c840c1c4e000c414641e00001e01000190707010b00901e81d05c07500d800d8840c1d044c640b0b44804078050f0303c001000148400c500d003041d01a95620466160400701024103c5440350008071001b95403a400010203070098410101e0310022440d00403c04410f8401c1c2d546d80d4078a03d031440c1d400395240e4001401c80d909101c030402c2c010402c80d60070401303403401001c12881282c8020307020001a191365100c0751400e014a0400302c502c80503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 18695186 1250 18693936 18693943
    0x1c0302060f0c04050a0e0a0b030d050d020d020403020301110408060702030a020601060c06090624090e030a0f0c0f0602040303030501050f03070315090b160306170a030804020a0e0a1a0a030302 84
    0x161140062140998a40b400c0c03001901c10b0741c001c29030000d000340340456034851080c10715119050442c800c001921950302090f170b880800381040f000103074040202c2065400036401030b120948051b04050b0a20780c0b2640024250342084440355000e000124007005602020401e554004030107001561400d07403d100000d442e42c10501a00c01803004207480c5d04d0402034694071601680c0e80000c070420170031200b441c513050441c215a180400c010f0700360070085818401442400f601011000045150084203c02070350303521804101e80081c002500100c1d00455200070740101c41910810005907940c0c25032402900311181a0041e074023403005050429040e40f0005124030070b880d0400c03403050304d05081411080181100d0303c0020f04562540c400d211001e800c1c0c400c654000d0216840a0002c552035109404403c200001c41e0043c1e54800d18400c000319000f40c0c0b4040c0c02600241c400d084a13078030784481d1240000196902e5030381d5561000f20904600030302c1c041c04c10550085810b40041440c58400079507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 18696436 1250 18695186 18695191
    0x80c0111040812030c0403050d1107050a060804020409060204030203120d060f03020d0303110c1e19030504030f02041404110f060f0414060c0a0b090d0309020a0905070309020402030907051c030206 86
    0x14101002000c10381000d81001620007d562003c121802840052401081c0840c10400d0410603c260342021550345001c0c0302c800309540c600d68403100a41c0d83c6808103c080c4c100c1e0001520265030800c408030158605100c03c9880e080321003052581c0300c0034145110100c130507d030300c0012900f09401040c401a52619007514510b0f03003500d4081000c800004902c0c4044c80303904901c284610803403003001e48114028118040c00701480c401d48180400c59142c1700980c60b602000240040c40400c0144001030005517000e01e01c0d07001510000380e080c446a00012010000d03141614044140c142c1500f19181490350f02c1c801032802e5a415040c00c01e907050800e49805140203047e09100045c44030044d54840714240d6030b0744a001c4d4100d44141516007000403248600307a99044a6000300340744481d800c0e010f4083d015809601400024816143c004188001c0c000a04000105a02d5a02250160b50f843c000f5500a41041015180c103500e08020028154202411a0700248680001602282d00403a0059 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 18697686 1250 18696436 18696463
    0x3070c030c02040605030d09030204060f05060f0a02010212040309080c030a0b0c071103060403050a0929030405100911010e0102060f07081905040303060e24060d090807080c01110408 80
    0x652041c40740c40050060089900301c0b60f054481c00340c0c1d90308195481511417003100c1c000e036020841a81c640307d1540d641c4407103002e01c80c1c01a00410080306880080d50060040034100d10006007000821040b9041260003902c040e000140010f0042c8441003090000304440b48080b401000001020b580720f549100000700301034851032000c07580009001150a001d6240d840040543e00680f50074074011307109800c4118420002110340c0800b081c1603500d44817410301c0d0100580398640e194056105506194001002240d883c0500410750700e440d10305000e00c04000d480b4400f862529a0300d81d000400c4080401c214604642c000c0e01807000c880705910b44950804c0051070000e8095481c551610501d40381c6100c2024128274240c10441490b500da48100f05551000400d6402502c401e100c0070741075198074810381c41d01d141c00340d46030b26a032402d0b600409280c1d034080404200c91026850b9880143c001a00540e00010005503910001000303210344180700d800103480b24200b90501100a58031411200d160 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 18698936 1250 18697686 18697697
    0x10305090705042a0807080604020d06050301020711011b0803060f03030903060a060e060105032509080d02030c060c0708030c09010e04020301061e030615031a0d0506070e030303070c03 81
    0x160208409201c08000703040060800e000c40d1038000b00860016941c9001034400001d48091040014400c0f02c000b4090300316035581c110251035480c1040001c1d071007003100300c005941c0c433840007030b05071401c0c00500701080c020100b690040d0032540c0090a4024062900700380e51289245090004030000b090701d4115a042d140c07201d084000c9404649907100b08001c0a502d031149004200e20100c1e0342d008041900c52554448105032602c00041d24240003d81d85100c484c80161001c400c08400d4815001c010755040c43c02c051040c0c0d035400c4103424a00c1d0703105030704016080000e800400c0d10381006607540100801c0e02c45880c04445480b540c5442c04064800e0908500010b08000160310450607000100002001103640e540d403030101500280195000407192418a51050f50b298040d02c0303004110b50000382100e04010103040e00301d000b0000300075040c589141040c0e00540540700d0300b60a02c2410720802c000d20081c01e100001900581000380a140305e603108004001d1f009901500b03001c00b45901d030500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 18700186 1250 18698936 18698941
    0x20d030b030a170705070602010b06070303020c0a2108010f05030a080d0b090f041208040b06011b06050c1312020a060806010c05011a01110a21110d050306040b03150105010305 77
    0x10b41040c034010806400b24401d101103000d0254a8001400e6036489034080368000781d42d850003603080c0d40ca0f0700c1707245a1090003030000902083c001c3c1c0041800c04504000d694143ca1a070759030401c1d01050b855540305551591000d0200705030031a0040380949642c503188042945001c00007540c90f00301000c02005698040356810041e4582d4220800c603a500500038405071425101c0103182400498080e42d11205600881d4202802003000740d020319081049a00c0c9540c4440055408600c0340c08082c04440c020960400410040c1c495075025403900100c10b90340d502500411481010710340c10000f40d00280381680001a911214080304480b510b051190b0281d0700c0000589848054040181c06542810aa01a5942c1303109071610002c03400d803107141c0d000f000b01c0c2c6030310b5480c9a20140200314080101082492051130340c0d500d00607001c1c51030441900712190107040e0a1022110610303002c502e01009201c09480c3c24050710289460640c02030910702d108100c000f11070401807080506041da28400b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 18701436 1250 18700186 18700189
    0xc020118081b07150305160c0b07110604230f150c0405040e07030302010606090e01140d020d050109051002030415090303061208030105040615090e09070314060a0c080601020d030b 79
    0x1920800742100030030f0351010356842c08030540c64281081004002483d210010f842c0594000d100500803038166150300b0002140e0703480d000742c060090080c20074030230490100d810820042056600c114416282e8013152403080c00f81c03070641c90050452001e150080741000c0740c0c0300400112250307081d00040c1d001c80c5944030341d2080046031045402440d040b90400305601110413000035840100c134481e031b0081254554070902115641d0040c0a030301070321110080104025400e051180702e803202d0040000207110310341e90008112141040781129140d44559405091040034801d0031011001400d0641c81d43c642959840095000240c000112507610301c80c8505151095200c2c0010303010b40600e4407100d4059081c07e921581091148520440c1040f001045050103041044440d0806464000200d420710021210a0380c00610341c03142c5110b02d200000201d000038451a0560f64807102030081800c048101c501651300041800d010b000d682014046a40d90018091440035034074030b0000f944444510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 18702686 1250 18701436 18701467
    0x913060b0d03020f1c021009081303050a0b06030c010e120a05060a0218040902090c0a14040e0403080f04050c0f060f120105100908060c0714010501080c040c02011808 73
    0x54040e049140c214507502010740000e80c036640d0400d00803c5404140c0008800c2400c001c5260b00100160881003410360038034695000319240901c100d10085c14030b841038003850f0890b07500f0351040e1241da2050354a1350500017021b030201c0d0015000da014001604013000040c20402070644498040c0e07440001c40142c081c6c003441002c000503807100590300b45007030003041c03200070703420500400151034290051210185810312400c10296800743ca6600160f0b14840d9070040c0350400c03ea41d03400c1c02001c440142d600c401c09002000584040282802c00707040a0800a00e5881c00411282c0800f24441c24400400c100184801481c1e0303086802c188854038040204040380a0841190b092181c08034000481d0443d40b90110f060322020785c0c3d908142c5000a20485140803140b00715a250703048800030503102c0e404040282901806558034051a200500072942101c1c8240e00a03c03454000980c0244076250a0050a4200005100922480100144410f0040c00e9000003c0c20142c0025240c02d003041d410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 18703936 1250 18702686 18702701
    0x3241201110a0e0a1206021e04030501021e070b01030b0712051e0708070509060a05040e24060c07050603070e0904050d03050c0307050306010e0102070906030f1401050402091306 78
    0x2100901c2440d0201d0044500d641050ba40c2e50080f845950a08282e801c00c1c3c2e501d8411034503c1d40441081c0306803a1030390700003135214460303c01c5440000381450110154190080001750b20440c00182d03218503900c1c05079158165402001c018810400c5918003140b844070650b4150ba81102e118080b0b620703030b942c09594111801005500560a000800250800038404d4880c064080c60700d9210a41d1414011911085c048920201060052100e06c00600308040501015030b206d0524610f01078503031034541c0d14a01e00b140c00b02640c100b4114002040b441e07480305c4118400c03050340d071142002c0b069800140c903945240a81c6004900200000312001d00c58207418410a0000d0f10f00591420320303042c80b40d01da8118040000110341050017083c0358800c580216842030865030b9599043d610b884004480e4030600c81e0f078040c1148a0200c0125400d2000e11903038000350706c1603407003950180c07042c54800300c00b514001294805900d02010003015880b00c0070041c1c3c3c85104007070883c200e03d99070300c0e21500403e1031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 18705042 1106 18703936 18703969
    0x30c080f0d020a0b04020f1e01030e031305010e1503040c030b0f04020109030308040201140a0207030c0b0301060206040b040609050706200703150e01110a03150801020324 75
    0xb510750381d40d0440c6c40104018010982c0400003a0a81ca00110b00c01103d480b200300303010b82d036030148114441080d0050207182007200044820100e014240b10b55070501041065441f2160b6968940c50040c041d101d0450780c481c102410300074000025030004440040c0504003041c02c1200ca848074034412507050795161401c5045a408664103000584105d06010300070082035042007540b0080c001c80d002e02d50090880034514100180c28021682c0003075080780c02080144002507000c0780e1203510030f4001c8406095902c8515002000340b5006401806a01603600041642507109245042e69001d00b01c035151702149043e4401e1300c4801c148401401004201c0b240d004500080d081100504159000020f5480143c00e0303030f01035584003030055000039503201d0010007084481030108020344800e074002c42c1940b400740910707000c20b5190740e56a50202d8028002e07020740d55a05200c1c00c0e110340c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 18525186 18705042 := by
  have h0 := BRFrame.cov_init 18525186
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18525186 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 18525186 ≤ n) (h2 : n < 18705042) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
