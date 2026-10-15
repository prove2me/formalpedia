-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4155
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:44:02.686521+00:00
-- url     : https://prove2.me/submissions/a76171f4-557a-4d62-aecf-8df3a5959907

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 747122302 ≤ n < 747302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 747123552 1250 747122302 747122309
    0x100e0d050c091006030e07030215130503012a09080705303403030804082512020d121d0708030405030c030d1e05070203010203072a030c140f07 63
    0xb810a000a00404e507160103004c2d00c18480000500d0564203540000b02d045445918481847e0300003d0030310904195020a80001c0100400170001011600d0013503440071840814100200c032005075900c0c0310f9000d04c81401c01e44030110002e10107613082030144541c0014104c03d43e00e18413007141019800711700070415a04002c0b03644014144048a0b420b8184501d1000d1618100c0c1c1c48441c00c1841522428590440483e5018646400f041d1560700b0004c10034440c2ea0f180c0511140500c854034011554028071850040c41400138100e40c52074000101e0300c50300503c0481000801400b006401e005081d0442d1070040d246600c54142d00d140007201502d4580154840029604041000c000c00d180034000000c0310341c01074018196010900100400200c60640090300040c8031800311041103200c1c4080d28a1950f02074021940e070306041c10090310300581c01d011450010a8400c2602c0120200011111760070343c1504d030200300025690743d100203621000000c0321103110321102d030140003204000c143c005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 747124802 1250 747123552 747123571
    0x3060121181401090302061f0503030a0203040513060e060d030201023108060c071401020403021804020301290909010b1801030b13030c080d2a030b100e0d050c09 71
    0x1545010301e0807000d20500140400d5003641351030010300119801056455104811200d1080c840241c5c4401030f81901c8031740c00c280e4140c07102003042d0354003913000002070055a20803200e04010302c1204015505503003842c00340e1721141400f040030441c1810040e00c003411261282c0005801c0010014003040d01c080201000c445034501415188600c0e810b420807080a4028480505164900f601c0c42c0e540500ca60a0000c017554a044d100524066081d819031b0003459000741006400413005034005c640c04000d4609900c694684030f18280900800c00340255205080400241e038501c0050411500c1c0720020030704065552501240c284c1aa620072000080901c40700c0c0c07891480d41181816a03a281c002804040341501342076070800820b4000c40c000211a0340000c0469030f590103103240d5009000d02c41c2d20074486800411700b021801c540b100303d6100300207299400f04403850860003003081c001d51100c050404030b91440780d18203542c10001c81d9019050300881c02c036092490048041182401d044518288 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 747126052 1250 747124802 747124841
    0x21f17090709050c39100e0d0e0f1e0904060c08090c060306101709010b19050a09090309030b0f01030c150f030b0a03022e080c03060121 60
    0x10b118041e03c2056001000950b0142c10090000440c0300304010104039102810300c0f40002c400244121384900300418181c00917a0345800c0d16010700005003018151b0381504d07000e09121180c00620681c0200080b140c005d00c0050928032040c180002c8140c7e501c1c0317400010303240b40c501010b242c688030b40b00d40c015449250009140840040000d06a40001c0c1040840c4d0300302d9002e0302082d5440e0000d80f82c000000701c40c114074800d60b41009a5000c519010780c10303405a100c2d401c1040c0c81c1c8040d030041c403082c0c00945012100184030350800c50f4041c0940207a55000b00384810501103801c4a60004440512a0400d2900f89403240c450040c80300c4221003440100c4050030045c020081000c3c00340b0000c1182000520b00d0950592002e801540c1780c00f020381c01c165682c03c40d01e4030741d5601c840c0d803001141c0152002005511142c1c940c00244144800f0441346240044580c1c0c0c1c00381300304003180c03040c0c0d010012503003180c541030011100504120303056442c16203842c6e501c1c49a00440d01ca4510031aa42110144 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 747127302 1250 747126052 747126059
    0x16050901140715110a020c2106130201090f0501050414030316110f150306090720010212090609120c100f050403110f1e030f04030b180a021f170907 65
    0x2c06a60400b90710001d144005e01240c840709400040c10849044102c0d003521041c030410307485140e002c08104009450b4801d40d42803000f03c1c441a8030600049000380e0b070f56400b1135111815a00d05400500c62607001400c2000f0800c0403047c80003403e040c1c484002c090f2487d040e40e42c0e40300310404007441030507541e801010b180001d6900d041114048070201c1034032040c104000c2440c64100b140002022640030341b28500c00210101d124204201030680024500341c041c510200c0c407d0b0003900320100340c045440c04d01c4080b442c18070000660030320440003140100043c040b0340605200540010119003440c0c80750a8541403154006e00440381f00885001001506240904005080507180da000401d9508120904d00348810701140c400554a1210801e141c0480c0e40c1350341030310703500ca0143c83c003a180901113404020010510581030207440d00304036601c44245c0c400300c00c54440084500080d8441190840000c000d200c0c0c00c0303c040712021504161220726102803080040c2c0e0b40440310325103140c200303100c2070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 747128552 1250 747127302 747127343
    0x30b031b1c1a0a0b030a0b07030e07050303220504111902011b0309030201290f03030403080706091a0601050a08090115090608010f0203040206040909170d050f060306160509011407 79
    0x500c1244d804030001e0103007800716100d20900000243c8002d007055200d084003680340d04100300c0c0100809014003265a1100840e04a810104124440c650010007181002407249050b004013002c0a003194952881d080b02d400d031200601034840c0b200000c0d952201203183d0f02070f015405103141c1810ba91030210308103155140c001e003100c0e04502c00d003c006400c0c08603508846036030840e4010084050322601d0460240c200068590b00072980b0044c9100b0000881d80c00704202c0d50820141e4500c18141050700c0f00040d15048a05082255500d0001d0003e1095040c80c070300c0f44001ca508118204000150318200c1580701c10724510b03039041000d00a46a080804c0184070921a50101c031014907000c50850a0035030000e00301d0300c101e200b04d040f81c0351205c0b02d920900075140028001d2600c06082c0503501e004000d50075002d80011981c40441450341000100c09040c0452194420304041c40854058015050241c0e000c1d00000c8074030341000511030b10000f9a00c0b004c4018001c56001c0d0400b00240c0c540401c94 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 747129802 1250 747128552 747128561
    0x912020f0415091a21060a0e0a0b04141c02030a0f09030203060a1509021614071809020f0603070206042409150f09020105040e1504050103030c03030b031b1c1a0a 71
    0x5c2c026540a803051010304100850841d42003602a180811012103040036249020328801001d0080301c002024030080106849003040a00c9684090b5900250440000d40040b0031980130030015130000c004003000c1c144541c0300c0c1507050703140d4100100e51907100c1e00484d1500da002c031070000100307541d07041c218004505e108400004150900b025440c20464951031f580400c2c50400041c040f0761020740c80c100c9000141705041c0900940701420300e850004049507000b800054000780d0080d0101c0501b0718180c01d00b0710483e407003008140c0040440e615541e83d000116916558418100c00071042d003400c040010b030260000050285001114070014162600c00300e0b15400d055800045c035100d42c040042c0d82200546c0d0481c1e41088070a912a940c50044a17202c4544428156010f17103060000310030035400607450307121940a40e404103e031002d1002455680d004c00f4032110302c21403040fa80c610851402e060340320904545903030940c1030018150384880c95407040c0609051a400c2880030060040018442d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 747131052 1250 747129802 747129829
    0x20d1212140108150a0f11040e090601050d1101140a0e0f0604050a0e090c060703033c1d060901231b09041b09060912020f0415091a 58
    0x3520445940b52140255a40803110f883c03104c405950300005641c0311942d030203c2054146610140206643c0c0980c00405034414041c0b8641151450081000d01400040082c142d03540a0300311303460344445440b05d80b01150b014024904102044040100400100003e01245019a100c0307003c60200c00d02002040108180c044e400b0310403e0208106a60741d940c2041c0032606000c001c400d17180c540c040c0303880c209a20000d91540020f030024000c410941e165221382d103070b01e09007240c4800f01c260b2068825041001034107410f10480207141d41400113540c0d5400b01c4064140c20200d40441080b041c16503083c04812210556141d5541c0c02004034903083c0d00c2c060940c0c1c040050350304400d02d800c41014440380c001ca8100300c056000800c60b00b2194841d603010030a003414031400e0908500b05075900902828450007600c000800d10400003034440c02c664062106598010b095005010140c03041c03000900f07251032075103400400d504002511001e1840790682d01c90103a000700c18900c452405110000e02c901c41d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 747132302 1250 747131052 747131081
    0x4060f050a0501030506030a02040b0d24290f0415081c0f05041e05090a0c1d030604061109060301032f091915060206040203211204020d1212 62
    0x2006c010a990700803e00315607103a8111380c00945241c4070740100f4000105a0340c02402d450b5080900303100001e03044a442c10341580184140700004032001c8400561495000703c2038240000d50200889150500310003420384c401038400a8003408648010029240741d91200c003154100c50000d04c00b03560924581c400a40003414010480c03081e482005105101703920400241400000b00e400703440703511800460003400010201501424400c51500051101080318800710b542c1e40221104491403a0301c42041c3c40000f00506080c2c4e465803100c00c050f191038040c51441c050704000104c2181e407070301c0142d406103000d0940340000b54a5074600c103400f010f5414036069a902e00141d5150982e0b1844149544565444412902080c2e40e42c1c4032800f62041103104003102c48070240c0424602c0d4009409407150b4000c130308403030040300d140c00c1c0300000586514031400c4004003004107030205564421600e0308548040c0c5244100f61642d103a2942c802055602840001c0c4100595451080703c0d003d03a05a594540 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 747133552 1250 747132302 747132311
    0x60109060308120c070b04030206070905012c040b0a032019060c1103010c1718060105120a0807030c021305010e0a0c031b0503040302100e0c1c0204060f050a050103 72
    0x180c031030502c240500409206541c2c1c0207000208002001300980d40000da0001c107102c52810589000703525034804445a2001441c004000a9190b1007030342c0c0d03d68801141d6004845500070103071001141e41d80c41c41c2c0117400c5900e40b03801c0340f803985035040712034000c5018a8234000314400319840d000d000d40103918200d100c0d00703882240101c16005051540102c4507982017124100b034162500004c0d020809098035415440d00c101c4801e0b1a401002d00c007080c1200d420100c250b1307503801103070030b008040e41e201450b403030343c082c2c1d0042c040b41c1898000400104100302c111060103800ea0340b0450b2a90149c0400c60004a00900800031801c00360030010388511f40880034000346d81001c840d40c90782c21000300098a40350f191031202c400140030340d00a4030f00c417015010380d440700140c10324050709a51081e5003c0b801481880071401c10322060784640600d5082c41e034003801c2c0c880704c56820464101e01c240d41080303e080c2407640000059903544200e10041100c2c007900c00c2994076180c10071100c4500340e48102d05041c04d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 747134802 1250 747133552 747133559
    0xf0f0e0109120b01030312022b15090f060503060907060f02070f060513080c010f031a0904081b0304150f03060803160c0602010905150408120f0a0510120f2409020306010906 76
    0x1c0c0350b1a00d18840613009040c075427540c010070b4000606201d03600b03401e07211030b642004645440380750810380c2c81d02001041400466a240305055444908581c02c0c49030350810b4005100c0f5620400c2c140049004a104891070503417113200d403002c420800c2c0e01450100303d00051a00254030a050444010314442010700100403c980c0040c00004c00d18a80b202007580e02e00c012580c00d000010404031690018006214074501860001c00c0c0354002d20880103042c101014405561600100b1a01078900320ba0340c050380580e0b01075058079955440005001415115000400c500b1010809012803511030010700110801c24280221010f640d50000411a410a000c1c100400c1000444210301031918414481507521410140980d014403401200a00d0b00b00c0140040e1200c00d4580600400005404020586416540130204540744c80742c59240b00803429403902141c14154202c2003180160404070f810b100c03442d034141d501e0660b24414446155a070b076680041d42810012240074040c002c0003049051305 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 747136052 1250 747134802 747134827
    0x9020109060f022d0102040b090a0902070503070b0a0f0e010504141216020a17100e030a12090f1205040303020f16050d050c060a0c020f010f0f0e0109120b0103031202 73
    0x340300107261044d1060440d141d015190740c103000382003910400021501d807034950654500c141e010f4200e040c450f090b070500100c0c43d80e005100303d500081e4040000c500e0010650b070340d4215030f00001c0094014035a5400103c901303032402d00541e1070704558900006554a0145841380301c081d900b981450442c1d00100281c00a0a00b000444030740109145011754007109600c0080d488403d41e80184c07032042d010200c8250707207000001e04d0f0008005000d20600500b13075000580f51740d0b40908003080000450f01c1034076980c450325a03400300541c58024050541c840d02c1700d0f15840c0c02c1c0c0468035410400150005001c100b81035042c000f15141c05e0801000e00035410300c1002940030847c06015884c81084502c1e9010201301301004101a918005420b090700c40d4901c810103881083c114000ba0f00480440399548425845800034502c800000c3d00c54690011032054215002c90045618a051140c280700114902c0c4035980d9074040503116455544a56040d4600280420901c41000c0c44050042c00b84021445 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 747137302 1250 747136052 747136063
    0xf111e010f03150b07050325050d0509130e1c0c020f0f1f230702090708090c0306011715011202060a092303010c020c01050d02090402040e070309020109060f02 70
    0x400d1450301084694030583c00c1e50200100368489074040c0000501c0704100200440503148154001c6c550004092056400300d901e6054150001d101d0b0300100013814080d4010b6014001c0c28034045c01d44600d80c036056490204403000400e004149501050f080c0003507400b5400c070081e0340800b51421014058103903020a04c510510391b001d601c100e407040f04000d103130340b5401901d0400d25448049a20103074410b01025000076400c44604c100b120301d991000d000c0c1d4480f102101c4480f40c1c0a021000550365201c0215036841c0040c000815a00881c40c00901941c4c007004070602034048804017540307421a2203020b52400c41d07004406644190100700402c151641c070720420310015010f80d5190750b10040d181e0111081116504007214000401b101501e0406ea0700c07940907003032a81940200300c03440d18048141d83d01d1410b11a020b00165080000750a548580e4000d806c600c580034101604041d29000c044c0d01c141e10880f0b001c00001d640b034076040c055690241300d80c0000c180f242000d031580300035018002d4030365 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 747138552 1250 747137302 747137327
    0x81218040c210e0a1e0c030b090d03091a22080310120804120204060906031101020f0309031009060f061206050f0421020c060c010606020f0d020d08070c0f111e01 71
    0xc4107040342c01c5c00750b11030303c40b01d0619140e016440c54a05070316440d154020803010742d5401214443c204989041078000c1c40341002c070715000803080220b42034201d018072141c07000a0070070b04142c1244007207100382c14490500000c42d40c4102451a01c0c2c1c502900182061941584a00742040b40c11900d030010460510464050360100055811700300840d00108001d4005584080b045501d003190000c10310a004002c51003014099007943e0f2040006041150f0780d00070030015a606400c8141e07203501d011041e43c01510454800c00300442c1580c9a00411812034031079502400d18038402005500070480907120f040d07440320900c00400341e1030500d034940481010301d207400801a901e10450549025000b0000d00700c40da4002130105644a00510071180a003030544604400341c4541541b02814150210b1507018199865004003441840240b044441100240422041c070003080324010104112103035410000f03000310112804000380006000500480524a85004000402001940e0b038801c0d00101d80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 747139802 1250 747138552 747138563
    0xe04050c1809070c020603040303060602010b1801051306030501050903131a030402040207050f0a08090406050a1404230705070c060503100338150901081218040c210e0a 74
    0x40f070360f410106445400a103640a94000004420007003059031680104007650301550081c40a03018800510082003150100310080c03078003101c010301407420984418a21501c11900c0850119920303111282118000d0310801d103d40c000103280c000d960fa9900007080140340b020081d42e010a020014941c040c000600000d115603000104a004d00c00c00700450b6030600d40001c1a01c0c41ca41b417910b0400019403000790014081d07418a800050a85442d081c0d1074101c411074900541146019400c202c014890b501002052040d01180c1144041400100511940181c1ca400740e40740c0381420401e140d0201a400403080020801c10005070000c03901c0e07140e080301d0340038031041c030a071781500c9415140e502d030790701c404c5192580803140c07120002d52640c0c41350007100c03256002c4a540c0444400c0c420701c4942405808890307405078000c0e09111401c7c800512011342034107810030210115030001829186203214510010341c184185a28050320152405207a4001c5602005100d40e0003080580350001c02002600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 747141052 1250 747139802 747139819
    0x70e1008030904230702070501120c0e2803050a0b0a0c055e0506070b060301063c0812160c0f08150c040e06150a0e04050c18 55
    0x1501c100c0c0b4a2121071403404c0300803a2a01d25000034006d650f5a0184a00c46c0001c002054102c0140440d101304496040a6030300d07482c42201050a00025032054110b00c4144009204030a140c91140b0354807034003662240c000b5080407555402c2509920f000a07101c058464038102400400035042021140110440c6494010010145241f514440d00490031038841c0d40365144040c1d0002c00341300304480f0408003402c003072000406800020100a080c0c1c0203150f00060108018004900300b007003070a81c0000c0c003e0010038141d445200364000700380400100014010b214210381121f1280c15103040900242241400450b490300e0b000076a00c0240d545e00c0001c2c001d001905100041c03410a651001c04d800480c4070041c159a040c486191071120700c1559824020b5080091200d210113070494055503065003024201814003c0c008020b040c00740c4900d074044044220041c000300004090240d8500603100d00c1d0032a06924184025100000c3c81c445064400f00715132440c2c8188655100701c1940f00b60361016 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 747142302 1250 747141052 747141071
    0x8040201090905070c0303060e0f04170903070306050a0e060c0f0a110a030e120d0c06020903031c0204090c090e07050f1b0d12050f0610030f0e070e1008030904 70
    0x807a00400d9400412101d07060104010340c540e04041c2501030342d4400e90742080741507594545501319500a6565107100000c1c80003140c0030031441d450200121034001d044030300d0700c0e10308400240780ca600c03540304803906074581d0104228206d0134810404900030000150603240b8100e05a03000701d02c01c44443c0755820f2008101400c5282c4030710085541380141800b250039a4120341805030283c00c0c9403084921424840c0441e000100000c41c0c0f02c012000d10b40c03504686003000350b55103400b94000e81c100c2901352006224403004076139011051407a0b0f060700c04c00113035503a00b4660080140d9140300c0c0c4c0503040c03003081c020820601030800301c01503204000c0d10b030007516298140310280003403280b0018051071101003181403022a1010030b00303848444042c0c40d0010f50107100219401998012103115035620170b036a0000d0101e082c440b0600401c6460391178001a5240910820707002c9801c02610014690700145003844400c0209410315001174107000440f20f418a407160300c40d90b07441003c040c41d0103103448100c02d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 747143552 1250 747142302 747142307
    0x20a0207080d0917010b28030b1f0f0e01050607080706020a031506230a02010605060a0203031909020609010c0203120f0403020901050d0816020307051017070f120b13020f0c150f040308040201 84
    0x41b402355a01401640460403c1c4580341c007040e402c1c015030380c404403d1140004200350b0040d000b4046848000d9076100c0360303182c401001460380042c04140c60551003080f204001070380600c020700044072103450010f0340142d0320009d605004500d420000138400750411451003420405c1e001c06203101500500c0c0d40d1a002c1540c200e000d040301d64402c0d03401800c08130301c0c01c99890f000300107580714201502214800b524050515401eaa41d04e52000c1e4001d40100014425540301d025800324140c0050202c802c510300007418944258000c03130b40c05444000114042c002c42c03070101143d81c01844200d61040040200c2c0e02e0340c1140d84076445002c07079500340c42d60008045481c01c0c08403900804c070040041c221608420000380c032840e42e00b03c12074904410301001820081c02103041e03102c0c0100d161b540b00340e000c10003001d0130010300407000b6040d8040d101c0c00341c50604409600081492100403065981c4425002c3c03a072a1070003007c40d09600b001408641040311040400d008294840e405240c010078503101c50005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 747144802 1250 747143552 747143629
    0x908070503160b06030607090909050f16080606030105060604050d21030902122d01021902160e2203120603110312031603020a0207080d0917010b 64
    0x20498000400e04019a050b040d07603041009000b107005154641c0d4038803c0645410f030880704140862207801c01440003214035448003c0d01407140c02140e04002c040c02c861440c100c0c004000b0030790070003112010b0040c0c0d1720601100307811200586c02403015090103400a4118025401607070300403140f2048401c1804034800c0030003010f90124400e00f54a1914a4008001d040c0c00c0c6003c3c3e004e94072a600f03080701c103603000139400801c40d441c695603507004c6201c0d8650300401d0a4030309034076183c1d034080c4040d006104c510b403443c01224646400500d0325003640548503c1903180c1c0d5010f4460040c14030200709907007110301a842521402e40030703030342203002040c541134600700b40392040020749a03e07045c0040100270100c080c03409130078401c034101d406141504041507450320003191560b8074800d1404000910500a0f0060300d40d0300007034015206519250510325242421282006001482c000420404402450030390300e03108140000900c00407800074007140c00e00c0302955098084074110444088105c840810 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 747146052 1250 747144802 747144817
    0x415231c0525090606020303090a06051b131d071b08070f050606152106270f01092f13030b0103020f01020705150d110a03022106010c02040908 63
    0x2510600c889014603102e000040034080d44a4aa00d45800804c003580000300341c0b80308221031401000d598400e81da4100c050300020780f000b68000303a00f1101c1d800d4021000701500c04040c90304040a40345261030742500d91614143c106804c10b186500902c4422940300722061514540c1400300400200d6030b282801040c4900c1c00040c000310141c080c5601080008962a0700550003100c1d41c1c040403000c8401402548504220114090102c060510f0310032807103409603500050007400c042d001e10aa102d41c80040102c0b0002c00341c00d04821042048480c0261011405041d61440802c030040d10308203032002152208451b2140e4a8480d81452288101a802c58050702e201410a00340107507a8940301d4003c3c0c0d82070204a200e130111319401c514039440081e00384120f600040c1030700084204554100c01036400380900000803034a881000100c10314200003003542145550300165100c07000a0078220a01c192100030072107038000018042d0b16a48469014002901102c00041d160124036155401c0c3c82001c9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 747147302 1250 747146052 747146083
    0x60f030e15070302091923030a0b070c0c0f1a130f0b1e03090303011a13031406070804050c0609010504050d0807031107120f02010c020415231c05 64
    0x80c10004042d60580150242c03c0c4142c031349068502c41d10100f901b03061040e00800c140d4003142d05d4860701400f0b034103c248603403407400b5042c0d0314500d5094451003100c1c46c0407550301e00400c060504100070040310641c100b00621812030801e18440c10700208607841c06071164011580f240100359440c00e40900c1c24110014000c0c41000e08000d5510095040b458210b40c00f0540d000784c001545902c0500740504483c4220316000103149540c0c280006031854a075a066450540d6000348940d058404084005002440c01400c0295401a04108892415000070014400c05c0404014000094000101d003035a1103000c0f10000e0322001c1440040301d29000d90b03844a030744003c0c100c4004c4107105c03455005022070740c000e6403800c248084407805199145124402c4000440c00c0f0200c0801240c01c0d050300c0450f41e07105140199400906800140c03d4680d84c07003500300022103c42c0b00700051040c2581019550313010966811000c4e0280001411501c1a514007036401260100c001c000c1150a000c00c441e0000c591 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 747148552 1250 747147302 747147343
    0x51f030b0702120306100c08041707170a050d080601020c0a0b0307110d020c010503041a04030801090e0c180c0403080406030b180c07030e0f1c1a01060f030e 69
    0x381001809050180c4585016004000c441c2c503a000c503410459118200280c642000d5441240c4110f807180e0780c822050300d0207201480041103181d0002c0c041c201c050380d81c400600d102800c1c0314491b0000d40c3c00e44030301000c51f403003e410b0000054002c40d450f5100c159a09106809950307060060703007411034005020ba030000d40d0001c042a54032900c1c000c0e6026600650300c082003034166286480d81c0e8214103105001503031021481c6c1407558401c4004661142c42919070859882c900301c0036603c6908295000c07004602c0510040c814640184102201001c003900200503010803500800d440302900012440092040c50008649000d00030480d07000310307441a17446a540d81e503404018028010080c00030f1240703002480c001d03200ba600d080c186024040105035039241c000c550741c0590b0443c0746861001d13000540410491b83d103694452100101c000351403802c0046c004d8610b011210b160040904040b08500c3c3c1b0010300400798003140324161108203090000316214440304840c6424103500e0960300ca003042 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 747149802 1250 747148552 747148559
    0x10c03020d050c0a08390d0506060f090103090f230d090612020904061701090326040f0503120103030507140606060a0c2a0e1303080703051f 62
    0x154000d200100c00c0740c41c108040d4540d030301c0d168418426010a9000103019001084c803d40900741c008081000001440b0016142400e0490b50200051101c0403900e40118885060503000e005480d4810b40842c3c0740c134030300b0b0240e4407083c6c0f46020f584640d5040590382c4a50b00d0420620010a561083d00b200040e1408842006004919a40d0782c60046280c00b5400800220301d000f18201815102c0c41c2e21024107400c1d009040030000c3d0408404e035640161035010002c0d00210303185503030000301b0100c8004140700180e410301421901030301c1144141c400b540000d400c00b00e803558410f2500305600800c0030340121118204540b450040c9071f6000120903000303000100700340d0804002c11b1401c2c8600c208040700682c0e880b051781c031003038100c1d1080e400079020001e0061181c401c0400301c59052003101d046614071480ca451207094203412110035220303c60000203101000c180703080302d42d005011080200d0a06882d036402090300d680600340d10300741501c4034049506002c59081450050041100702540b0694 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 747151052 1250 747149802 747149807
    0x712020f07150306093b03030a0b01050706090506070f050c0c060721020d03051303090509130803011509050a030c0603180f050a23060c070507170706080a02070b1306060503010c 78
    0x2400289011035502c40800350001100c05d1b100c426441340090051811640d9550402010b40010701c18641046410068803000462904c188205240180006c0042c0d24040c400600b0031024200a142031000c01d102c2c5010216000411401d0a002503da40740c8841d05417504e241c4201500740030065101c076070326143c03517002d40c0000e140d2401042d0303581c09d001c0d0b512514002040c03032904540c080c0020f0046441442142407459401d504201002d8400c444a46031b5121031845400a030042d1007100d03400140218029801a50b1802405044030030b8441103180d0b684941a0290305c0c4103440a05864429091203014440b46488200340c0110001050360200d2800c0c54442c040b50304c04955012041c0070203440e8000030313264990b40381c1860b8000e0040e900c0f000c0c10130003241c01c4403604a441c2e00c20540c001c24211080c0c00d1041401e507241004000c1c4c1e60030702c0c9019100d0074005003001c801d24814401c220108038501009508281007560b5400c901c0740e14249040a040d480c0c1015070191709280808141d2039 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 747152302 1250 747151052 747151091
    0x12040915080d0314060108040b040b2d1f0b1b0703020a0311280b0c030c011e0c03021207030e0c15040323060402100c05120712020f0715030609 63
    0x80600300588403540e1703c41c010b5942c1c000640b005032861184000041c0068520701110b60000180c5180c10741c10780f000200d0310070084140703080b440c110320800d05120f48014518440301e4110004090780c0c40c42401e01000448a0207920210381204c0d00455840003618400e000b404003464000e46200305058980c100340100d03030500301169001c0c6016180c040b944032800110b910044003003c403490340d050701e868107555664106250a243c02c2c0000c1000e8040b540c024400c90040f4200d0b118103c6460022907007610846005184020030705004210b90043d001011100da80d111380b45040c005000001408050318021000c07020a0300000300c5070030080f0ba40700b0080603008491041525000920028221444e24100c0501c0c035041644103801207401494900d031161013405080c036040e04e5207010341e10740c1407034000c000c25884040d1000152070010300c40301c10b2009000441c10300007003840c05196040c8a03038032500c504c54208031080c074001048980e03101c2d401410080003100d80038010180e405040c002c440c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 747153552 1250 747152302 747152321
    0xa021c080d06060813021c020f130c1202040f05090a090b0a051006030204030b1524070605090c0907030c11030c1c02060403050702040213051309021212040915080d03 73
    0x40d0011001500c000c240217800c0c003007598058002c81440c07101c00408032094800d24801c83e4440c00c002c0300702d001902e40c000644091912440c002c130f041c0e03c0e10003019240403003103001090250b0040100307018007200403c0e200201d40382503034000c3c036075901e1584200c01054822402490524004240400d000f141e0f00024041d05404ae00c0d0f1b020759958103425402c904c100c0c40010003c01003040003c10745603503002c1e00e49182c0809448541410040c10345511101011004c040001d040401c032442408154816250710404007002088084083c40008101342c0c4c00400c2da8080680b6801c1c0c40341107612a942d40c102803400202140d8841015030342844d20380141a9051100044500c02d0070540b502c001420344c0100d8050315a40d14001c80e40d024000a54480140078010079401035001030a0380303030180020000f10701e207171001039642858410031031000010038010b08550302191750480301800360300859080325044000020341d1410b0b44480404026594400d980600511161440d041c2c1c064001c030141c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 747154802 1250 747153552 747153557
    0x10c06020a080924060904031b0c091109010c120e0409080c0d02010501050904030e030c0d060e010e01020a02250f0303020307050f0a0c0905190e07050405090a050a021c080d0606 78
    0x1110003000c5142200103900410310342c10b48200340410103a0811b60642d542150007454842e0500c1c5000410700b03000226000e04864030586110204000b030030310b1084107250769000101a10301724030280000d04e0b8028416025100b9820958240004c0307010302019a02141e01403c14441c45403a418821110f42242c0c03880f140501902c2150200e0500c10f2081e81d051310070003440c10170561269107084801c00d203580c10302905031040510310403855035034030b460301a550301c00c032030110799a8a044000750a60f0b81030b806103950b6a005014107a540c03500031031441c0c00d10031410500380940d0903406001d149c21400b5446127015050403600481810b0b40031005000103400b41003110000e902d0701c14010341d07a407240da0b00a030602055490a001841480d000650420140d00d2100c00c1030004401e10022261402d500025070340c8080d900f0401d84c00c0c60300855070300404240103494940c2550312000d8880d9030b940ea00034070030001e60307060240154213070341a030b0b020b00d4002e680b442c1c90f48002d00300c8100400590184002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 747156052 1250 747154802 747154813
    0x204060b0711030a1211100f0e011b0e0103021c0e0f1606080a05041b060f0207082a012001060302011103090d060e0a1403030105010810030803040b06010c06020a0809 73
    0x114140051030007151355109025030f80501242004a4040545108031305180c052600c07100c5040710a405540700701005c40c41c001401401800c551400c607a1651042040120082402031560303802c0340340c6807440d44083c00e0250b0b0b00c20f224800f001d8460a20ba040301481031409015030003d65002030500d4490b88400d04860000510800240c88003410f13121b42000501344030000f03500440c868100c25003040c0b1503a99592005e0491914044008541e003003d800116040c3d03504103a154100b04543c01456604054241e004070141f6030001d81c03124003107404008421a0f004584d503485078032001c0702d106408084101c0d0100c004012406003071103100590001d40c4849401c080da15000c011544501401000c6a20b00215503a90101414810301200018040c0b507080c5d0340030030946052600d5004502000d19600d60400c0009000c1706000340c4807941284800000380006142c01d8120783d0440e401084800840d601c03400101e4545d01e5111000745241c1c0003040c030020050300700c448940940d08441c1070f1407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 747157302 1250 747156052 747156083
    0x90c0d150e07030f08070309080105041212020406080103020d080708030a060305060a05060f040504050c1203030118230411150d060b1303061a06031014010e28030204060b07 76
    0x2d50710a02800040c010021031030020300042c41c0c0034028100c8511905103503036059942d1899a00b107440c11201611071030440c01207251502c0d80425420306401410504508060400d03200400f0000d05010007401000d40d08179100c184000d1006640086520512481d684d00e04040a0b9000d4000303403008803001c2c8604004221040701d24051070b1f2042e940505448600d520400800c0091b02c00600207842e50701030358010103e182c030340f00000072a500c5442e00950341c83d49801600c069891642c44e00c0c0c000107203050400587c45800c41c00c0c809000d1004003d41846442e18286218030240303403455154030810510b101900c00d54098003501c503d1429520070000c0c84e542e403880152911a600090030304016184007400021402d80c40090348a11410b034415078814640702103030041e0300c180c1d00041226000001002807182200d00000740300c0d8280307001d84a0700e400a0110700840007040382c03c164044a01d003041041e076880c1e1408401141c00070700c240045513642c05400c00c0d5070310000058600d100d10400c0301 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 747158552 1250 747157302 747157331
    0x5040602010621110a080106060c1e030903030c0516060c02030c190506130801020a0e150f041404090507030b100b070b01030f080c0105100612140c03090c0d15 70
    0x12407038500c3c44900c0000c0340c01c0741c0d41d41c2180302c00c1e8210f10f41d4402a103890200d8219000d100d6003000d4061038603900f1039100941008010b20101780d03c072010300d1760980b003003800103079200c1c2101085960508241040000d203142c03050820500f101144141c001e685400501182d120780610380880c0254243c0d41c151404401740078045c1001340116203810b0083c0e02c1040542000c00c01031542035581500c0615080e12500c03c282603a00c00703d01c400000d62000c642545a2500000d40c1d000155802486460104404a02d418501036131140000c0c50484140c28030098455420480c0e8981e80201682d40b02c81d202d1404c520380b1142502c804460480325440811150482c00807030b02110341080380d00c14560700e56501c40303401c0c440d4610202c511200901c0102032181c024001e280c010502005204013581c10110000c00912880400c900561b0501e8101601c2c1c1156403281c9030800c5a40d501d043d600d948030003006203030a1948118980102002903100c040c841d0940304021b110200c2441488200e0442c40d02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 747159802 1250 747158552 747158579
    0x60105091f1404060308040905041a070e010507060b0d060e010b030309030a0b090c0a03060204090f05160e010e15040f0914130f0c030b09061f14060712050406020106 73
    0x2600100450000280800000c0b401003407001d050003080403e03065229030f01c1020503009548500c1c1d403141c4030010f1008020302d0100740200d910b800954040c00b4030340114000c02004414803010f052110025415043c01103070341000c000a0f402418000382100d1030329040e0700404c240c40c0041c01a51030503001c14124900401101c0540e01c0c024001c100601c4a0b031108a072901001c0c00c2060648282d51107110fa44d1a480c0e001d10045000308001a2643c0c60404181c2c01c0ea80b004013030311500c915040802007a40c0c0c400c41c0640050981e882c0c1809850904001642c007488210a07250f8000041100040103511120041090f40d03880102012180d545400c00b90680d8280281c1d000404007080016180c50a542514050360340240d10110341001191100b841030f03805904241d81030b01804003040342d9008100441500300700d080050784403030640081080100c3d80e8034010380b0039444039002c1025040e03491380183c4428680000d06d1444441100350050038507401480380d00095424100002818904080c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 747161052 1250 747159802 747159841
    0x10207051005091e0405010f0e01090c12090201030b090c0403170a050f1e12070e150306100e030d09030c080a0b061012050903090a050a0f060503060303190206010509 73
    0xb07030349040980303d20811809000000000081500390b0000000964030360007043c2c001c204010360751614500b000d00158210030140c2229810a0401d040380d40082c2d400340b002c2c0448503059100084401072440100d0207441010120786d802204182400450a4003400401c21203105100161070310103e8132540340c490142060398004200188094001704034020001c100c52030040c4000d02254580340901c2d80550022224a0300d08148001042401d51b000a10300200e0702c001c4070903600d007601441d0640d400c3e1000501060041401d52000c03043d150149000703401d0603000500381c3e41c27181e42e0800e00a101c008244000d83e0040406100000c031030101047c0407900300c2d003000c40d8100990744d11080c4103c0d2854800c031a01001000b00c015200c00c00180f2466000d0100b18015541c0d9260f418100b080341c0d61507030015485100b40880400010f00b140e60948200e4495051840c0c40c1e540d8000000c5c05c5000b18080740e086505c500b80380c3d01c8030316400310b44070b416075004481c2d09069440c0e4500e4440742e003902c41c0303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 747162302 1250 747161052 747161057
    0xd06020921030a1812030917011e20031312080405060103021509040213080706050a05030a05060d0c0f080613230f0d08180607050715020f0c0c0102070510 68
    0x80403089061041382c65059002442e81241c0080741c1d03e9440540760740b0301410550004040e0b40f020b10844c051380410340c14841d116002805040d9461000303079900c1941e80c09181e100c5a841c9110f4080c00d074810340b020300c0b285c803c400701d076201e15081004488514454904442c000010400450080d015220b8180940c1e0803000a003441d81c2142d090005607000e002c0855210b50051010403c6592940010049484a84805808a490071403103070314185150300400107106051154190b010b078080140c0782d1040c0003a074003050a4447d18082144886500005000681c415502080c01072030040d02000301c5070210116107003a540e04100e49246082600300400d010309a1548603103895203010300c0d4402e11143d000703036011900103103000c40c03030700051349203400c0850048010012004000d000c4002e06d03c08a8001e8a803502d0300ca0b800400a220310303180205420089100d0900041c280c1c4e05841403401503079100b40d521461828090b50391121a0f24a0740107204040c03001c241030500030b140c1c00701104180c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 747163552 1250 747162302 747162307
    0x10c03060515280e060d14070206072703050d0801030c0f140103020c01110316020c1e060f1306050405240d1a0307062303150d08090d0602092103 64
    0x942030340740031000c0082d0700108960144810501c5c0d69003401483d41001009001170003011b641c80035100783e080201070201b03540000d01003000142d0400c642400c2c0e82c1e5165441c4800c841c0200384072000011542010b0460312441072110007440e00800740505807401407500d591002d565500202400ca518014044600c410f004169413a5000fa0041e20719900218000f0415107000c06001090350021100c01100203441303680007503a150107000c00010305006450116412010359103000c441c4064608c854007400e40003c103a110304d030000302500d4183c903030800e51319800c55a03003000801c20f41050103998410382048040060002404461160004191b0400c609203250b100c400300c01084080980c0ca405401c00044881550701400400040c1c81140c54801c2e00081c082d0300c070200003900101c5400d44500400c244121402042030030000c0c5002141ca01c0134280030740c030b0001010f0107225011900b200c0c0280c1c04030b04101c940d4000d0990100c00f518180403204a503481e007410989200b00307418084c2c004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 747164802 1250 747163552 747163597
    0x618081b060709150c170d0b120303011e031b090f181b05131a0102061324150602190b060d020301180302030304020f010903051507020708010c03060515 67
    0xd1100816007441581800c200518a0b078035001521720004016036103c04001444441501f11440340041420080d0343c0c1446007083c01d5030a6540b480107008000202d104401c9109443c1d04801d401006503078081c01a120444d610038000070300040c607000d07c0f02400c1c1000503013000c080c0c40b442046d040c1401c0070050500030005488450304807018081d124514440300102040c00d440717401c2400341003c2080310000e0803c5009400440050104100b0b80c11504850140151a005466402c07480d5800c0800c0c01d40d620243c40341415525802041c2c81d41d6a4209168681c226800000031000c60720b054007605c840005810b4548040700000c20f00904110a100200e81e42d420315030180c4007098030180c00060742d0800040340d0400a101540d04074010307030001041004604042007010504203013820508259400c2d55582d984034044200541c100c080311000049020703200300070300401010410001c00180703042c240024090500340c025103024607250390b07910701d070211180200c682050702c0c0303107010340080785 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 747166052 1250 747164802 747164819
    0xf030603071a18030313080705270c090409020a08011509020a0909050604020706111b070302010f110106170a020306011406040312030b090c0912011103130618081b060709 75
    0xf5086000c070740600c014400143c001103e000c6c04c10181075401c0003003207003038035000410454544e070305aa001c100c0c2d15602038004800b503040340c860b00801e14001c016202e500741c001040080c04080750282d40038000040004070400c06502c41006040e071051864031050300c40311035800782d10900560340c0c0025400a01003106407460f03030200d90000001000549000c9080c0c84440546950b03806484070b4410002e059001d2480c0c0c0e100f4910b40490000140c80e41502c5e54001a0480c1507005c00d15050210510260901690a6100c50050f100d440c2110700b48694800c01296a002d500b80200d0080c4940e074008140441c5640d80241c460740000e00e13140c606415a5250451116003103120b106041d194100b0410300e5030761200c4c15100e03650001a4540f01c00380001044043c0d04680301c00e007407513450061038042c0048901e0450740c0c00f0322410098200d510359850540010104441050031800c0b80e00007070707020031004070000c001c80c03d2945c1e0010601c40ca510034468550b0800d40350007010031071025040245c040c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 747167302 1250 747166052 747166087
    0x603122203080304120207080f19030c12030c0e010e0a05060901020a0b010b0307120b01021b210c0a0501081006080403030e0d0c03080c040e0c1b030f030603071a 71
    0x4000c000550560325600c02500760000d560480d5410304a0040914450741089117100031b10b00100100500c000c0c04d101c0c6a00c81041420344080ca005813001402450b0042c800407020950099203540c040a800c600100284500800326001039184c2d042c0180e60b41c81514030f075402c1c2c41d00503c1d81e162076151108210741680400505415401500c0a050106855801c01d42c0248a15505035649181041001b0f0464590041c2c4580d000e1a1850a0f100c80c2d900190800a104440b0407005003040791030002030740b1400c0002e540502507480c1519035455680410140c244020540b0040751998882006640018040b81d58200c1403003514030420410b4400e00c095604107000381000034002d019500000e06140040041801140030741e9030b0201059840289203034040140301c0c0590800381810784104203d440a040b144110002060004246191101080112000c241225620b0200c082c1c036880542048030060f210740a00100090200204802c9040d0110714100c428079003801103c4041c10724 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 747168552 1250 747167302 747167347
    0xf07050c09070e09010e0915070306080304180e010e25090608060f09060112022710031101081501031d1024030321180b0f060312 57
    0x144103180e408001911081038150080d2095034030182c848162400303100350b8a906038412020222800308001c1c0040012648078507490307511122969907180e07010128083d250315000402940000280012103070100041140043c100380c03002e11848810b1b16440d800c8851051030031016030480c1341d103207418240340e8024160208d0340f09400302d101c0740c5412a0070100c44440d000317800d20754001da0900c03090304410801594030542c900000e00040d81085140b1001c2400c10308001d0045004242150944015821800101002c003160038007a1405100c0348c02001310320300c81900c140001e008032513540e5100d02a454442c200544555100003040e0700114001c00d8024048100c1e40c11034101420241307014040c41c00c00d0301c1861800306081e804074003042c4040c410b0303112040c054a4203020400000760040c02484030241e511a69500110000034007101510307052100070350300d030f490448020800c03183c01c000c1c40c0510682c4c030000040750383d01c4050680e40c01507560b4002c480d01062001d0060908006c0440190 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 747169802 1250 747168552 747168563
    0x50703050a09031e140601061b031101110301150f0e090604140114010f091401030203090f06071d22110f07080403051603030c12200c130209060f07 65
    0x10b05689031a010039250408039111004003c1103840404d0015a40404002c01d4151001d17241c254505034001e41515550392052061120110010040c1400360b0048900d25000f90002e22550003c13182e5050b00d50700902403420040341c042c1e8507619251042c89000d480e0382c1c99464a000d40c51301c070340402c20145001804d2980c41a00e904610a941c1d1504a285000b819807071f1140c0305011f2940005860981410048020005161010000c00d0f910100700c030445903003824010395035102c00c4201800c020b1501c80900b003030321401040c040711561110b00b6a138445c0c11511000385441214042140d2501802030807c0101001d001045200000344e0240144003c0705400c945003034a4220000420b030884441514046000708041050040900c03801c201006412040c1c228a4116940600b0307a00f4514000740c14601d4841940011602401410b800030742c6650780031600e42d50131003c0d00e54071410364440314010051020318000d914190700980356001c800605040c20682c3c01c1c0803c02c0d90f03800c442800c1d0748 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 747171052 1250 747169802 747169817
    0x100f150f031e021804111e280f203a0e040515031b010309020d061d030c0312151203030702071509090c2c0f030a0201050703050a 57
    0x19503140340c80200244c0c50341c50010303903004d000007040100325502c0c10a1011010410001d80c180018106540303400b040341c10b0701d030766102e44120200407001400b0076404a62520084151403415800030001a104500c075a504507400b080d0340101c008003625030750750070234075070001c12220b94618a2f00401c030814466608d602003444848580700c0d13a692560105080820000d00084409003841d000710780d440300034420030050030b0840300b003c00d6907182c4070300f0000e0b04c01003550912403060b8840c0d040703480c0c9030303030000e10b02d81d6843d1450520782c0007088070400c0003800d001240c9070030380000d10103c280e03103621568030061814140000354020010344010f16211000c541e1820b07042569480c4040e00d010030302003000841e124030f0a8000640b400c091904a00d14145582c00600ca41a034001d100d40180c034501a00811a04d9510b0815a5510208050309480c0b00d0000d18280310300d80b0b1022280000b00303007250403807887c10346001499203d800d90000a800034004110110200c0d00840082c0707804007203441c0220 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 747172302 1250 747171052 747171101
    0x30308070311130504060e0702120705070b0703030209091003030813081207090510030b220b0d030f030b151e04080a050102030703050606090a03031202090306100f150f03 75
    0x2c4160320044060303a543d20000d0301402942454819040a06000b0280ea2500c0c01e007814042d686e00e142036030b4407080f000005040001c00c00300380103450007003172580c018a4071a619864041e01a41010341c3c0075005481d01c600240859800340c1c1c006044a4154682702865103032805400140e070381c1e0602c150f800301410801c07201c0c0004c06002c9144212041c1d80c0e000b0840c0e040008020300e001855450100b05030410390a00b2099942e20b4111540500805460340703001519440180a81130034000c01c1c3c5c1c0800122188024180c008100004035001c40e076040000500f0343c030801c60701080c0156a00c010701024040c0c1c42c0d02c4d0810b02c0b000b244111084904500741a0740d21122443d100c042c103c01c0f00c00e070750007100b80404990140144c41c0c00110444002e410041c0c1100440c20644403403001408105001c070318440311501c10390403a4401040a000e9030418a00728040381c0700c00d0300902c5041c918608a25000800c501024130366500804665518200040e40c0c1d04100c01900300f2079160070041440e0342001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 747173552 1250 747172302 747172331
    0xf0d0b04050a020102060c040605160f05100f05090109030e0d02030f0a06090302060c0406050702091017030712020d0c060e10090b150a0b160f050a0506040512130303080703 76
    0x110300ca00d109200500c07110510307100083c2001400340130404030b910f0500003800000d81080540d0510443c5034010740c0030210500303041c0e21081130340300c02801f5400340074030800c02c42d4030a400c4802d11090500f070070700c03841e00c81070a001e00b00c959015000d4005101d01c0c10a100d90b2030090400d4801c070b030000707027101c1000e00d0fa40d40c1d46050050f81242141e440d641c2c0c0481e0b208264051005552100302c0041060821f4540312000d4107034461048000d2007946450300047c44010200100320180c240c10041c810a10100008281c1c1c3c2d5000c10740644540c40b814000d032050910005001100b20441c2d6100d25a014150361640e0140040d0410007809014a0010752a003400302e1241d80c0581e03002e070010302d0070707800d100854064a0303807150140c0e130040c10b010704180034501c1c0c483c0c211610600b06108040a1100c00d0a00010b08a00048000c146010b008190402d1100001d03040e80100d0144007940c844641440304221280300d9030b0108202d900d100c071000c0000c20700460b00c89900c1242802d010a0360132104108 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 747174802 1250 747173552 747173573
    0x7060905030a1d0d020a0e0a1b020106090e0604020a0b0a0203090303180108070f05180a03080c01090203120c0d12020d1d0d05180d02120106030b07140a08060f0d 71
    0x2031000110b9183d1100f61107120695000325000007034031105289002600401c0001002e4020850b11800d044045502030a03141e02500c40b0041e0078040100000320504024044d22a621a041c1c0c45030500c007e451040e4030204219004030380c0202401c410520300031080c0040d410400b10482540000d1280d514941c07020300081213905c210140034204102c00388009030050384054540000c01480c00d40302943c507078002e0100e03184030300c21010520407141c05200203007268900d500000c18548000c203c04120800c150028804540b088054459284a501102109014001d082c010642c0111220142a4042e9500c19986504c5900141c5082003010b1103100f030740e801c40302a4038000031484a03e1110b02052096030b15042c40d91500034500451488802c80c5000d03c120410310901400c3c421004544c0c501001881445c2404028491660f99003000f00c0581003c442c100085060405901409841380040343e030016aa91111856901c81a007803008a14801c0200307a0808000710f0004003003401c0818 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 747176052 1250 747174802 747174817
    0x509190201050d091a0a020c15130804030803010905180c011b0b0f070e030316062a110c0f031009140118050c09091b010306210c05090c0901050706090503 68
    0x40c0110110798820244040040003042d801342030b481030094901c1e2460100310400390909c0002000c4098039070b00c03000703a102d13201250020458003000600004010612000d14105c0b928003804208659596414075030304030000226040d02d4005210204866014410504580d03ca40c07181c607002d119582e03a81c45042d102550083d41012a010803c4500d6900102c030190b021030036000745040400c40d84a06c4c0d0b241c0e00c2d45200900e002c1d211100c1c0082049824180880e00c0c0d04028040c00c039110881018180096075450000f403400b658201d41400d040608060342c82c007001030000c1c030712114500000001400c10740011a2002d107080090300208009000e581c00a820150010b401a42c162a190b440c02e400980070901503400b0310100401d00c034021030003480c003542c081c8111072070007248030049000308030981014031403a0320424100d6a400550040710307001840b46030030306112902c4004001c0511011034103000259002c0000c480d082d40b040c0007902c50513100300700c041161011a9605403c50b0003801 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 747177302 1250 747176052 747176063
    0x409020328150b25082808010e07090308090d05031902160807030b0c0c06040b0720061b040317031b070c03082224030509190201050d09 60
    0x482e0102081825842000915072030200618000c0307052007107a01c214840d00641d0342c40c01031111803810b105240080740c2c16106070340c43d02d12400e40f40d80d0380118010300540500000500100c0041440200300e11a98000c0d200f9071124061a40303180c0d503004441e0706c84034015802c1410b400400c00005c408101400154409440020078944403020003450000c0360a41a48120043e110410a0711404a0824183e03a0041d410040580d2211168045403045c1410311869208400412040c00130382000c1900031310040c0e54181c1900a40d072181e00012040c98208030b05d40c0c1003140800c841180d0f8000c551241d0030407444d80d6003010745e07a4a8100341c4202001c55000f10200000c2003001c145000c051110032804444841410488962508030803201c0358000246041c41c0090080d5a5141d450801c2000079045103040b80540e40f05c4022012014190542d1003d04039103503061201d560203070144904c901d207410010503105e4099074001c6455598414240d0500200b00150400099140240070303189000d007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 747178552 1250 747177302 747177311
    0x50a02180114010e0a06030b01020a0804120b0105030309030d0327080408010e0a0f0609020105040e1003020102011109220207050d020a0210080f0a0f06091a10030905030409020328 79
    0x702c40e00750002d182d0080904100b605624134050341c3c2d8107032280c41990103c1c5000101003005c0401070f860841d0010000c0d00800021500003040c1103099040c151040c0f00c0c002c0c84209990b98024141e8a0150308080e0382d141d00702006460206210380c2c803051442c450104c00c02c001354013090a105c0c00015244050b10182c10005081c04400720900847c007411000e04024050321200303407a250030751200c00000610311501d6002d8981568460300c29a000303030045440740d9030b10b414880d000c01a9401c0603c000c034059401e090110070503105907010380c1d034003903c05010409001003540e803503400d5800e0001030405544d828031812001c10710801010403040c805400a00d04011140100a07406102002020070803481030200001204990011034005240e85408141d00c100c0c2501c0b84042c107201d404c042c0c8100d1500c060b0640c00b0392081002c0ca4000f400b03a4400341f4003180b1000441c19241450000341284d4400c00042080c43d0300e580c01140e0040c2e07240c014010120304ca4140c0c0749550b04005240a106848 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 747179802 1250 747178552 747178559
    0xd0309031d01033b07030206071104060512060417040b12041b0e0108060c0304031d041b0c0c050a0e012304090b09150912070302030d051e070201020a120207050a021801 74
    0x65013141c00c0c080440d1303001018080e1139640015002d110f9942c00504101c10b00c1c2c840c0341c01e6125500b080d005040000d14000024010b24030259452750f049606135070462107c104c84414804150413075003940d00350018249016400c0b90a210810f001800c1183d144c11800302d41c400d9044417901482c090030003504050019450000700c5890030502030030160030388508000740700000c0d4106003080100c207903410030900090115400240100142d0942d00b0f110120704410200a40c1d000005d0034280e489014441241500c41c018001804c2c1d141c06020b040e02c5110005100502c0b68003421803800401070a42d00b12252008089400c1c2c95254034100c030400b041c0428030010b2007040c402d1040510404130900b00a182c1751850641d20710308403152004040c4d000410340240b41c070a104a4003001d0300e0300304c03d000c1418800c000240a901e046240703800b241c034280c0442e4449106000b01c4e91042c8141d5078502e9044e00a94041000390720004048074107120f200490401031f08da85c02c00c150f01003081402e072007182d0325 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 747181052 1250 747179802 747179891
    0x21305090109020c07060201051005011d130b0a08190f1407060c02010e0402090f01080c0f0c030d0606020312041113050f0601260f0c2206020d0309031d0103 69
    0x41c1758000a0a40e41441d0404c403030f401a090030b070411208240b8161680070401d928050f44040315003001c3c1d0f00a440c410820702082c40640080c2c807031310307001d0f10744540e01c41e41e03111500e031101a0149501c80510300c5100715804646115402c052950103110794015400c00088450300d442e01540c404030104010800940035503800a112400c0401e0655080d454a1642030001e000640001e840c40d042c4919140412050300742c6809840001003c0001641d40e606404812543d9410500d2440460f5080130b0b0302050007071003c01030703c2080d0a0042d20341256225039480c81d0341c24841070615a013001026103400c0302003d450180d103008070340030f08820400d4100200010500c2051b040686142405620003003100c000c079410700c80d0f004042e860782c0314081d15120103000d00c030702c03400d6070841500558485041e10850006490421110a6003c64654081c0c028058080d030f0900880a03011468401036a22076090361800480c20920501d00004d5815104450540424403c0c40c00d160341c4000080f081011072 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 747182302 1250 747181052 747181063
    0x6040e0709060e03100c0e18040c0f030818060f0d02070b09030306030a03200114090607091802090103060e0a0e060a2d0b0a15021915021305090109020c 67
    0x4000d10f0030b103500080c2d0001013542d07a24051004801e80382e5401143d54880d2213240c040f92040002030891009009a20490885040541d82511130325190a0002001491401d9010882e64003a020074100702c03d51003080005640d15900d06d070040b000b08182c0103488901c03001484104010a80140c90b10300c18101309605d602e00401c1449258010414000540e4000a05408903545498650070034080c8940340000f540c3d09814085080d820a42e45800c80b415a201c0d252080c400b0303400701c410031b40c2c41c80c10403200486103124900500202190307448082e0210340080220100604000c12051390316190300c1d080d0304003110107909090750ba2203030812104050004a800c41d101c3c140510180700c0d040c400c2c4003503100800c07003032400440120035481c0c030303112a402c00356074110010308560307540d55902c0201c0034411040c0d00700401409085564610003810300c600f1040c10303800c41c04a41c0000d0000851400951200000002d903c81c046000102c5590342820503018180340e071170150b102c0c1c0d1070484039484d00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 747183552 1250 747182302 747182309
    0x7060c0809160b030a11070606030507031a0105092706010b0d110c03040522090803071e0c0312151805062b0305040302040c020c010e030705090a020c01060506040e0709 74
    0x12910100659503c0c5419241c000161900001d000b0403003421001d40c51154020050040781482000800c6c800081000307000c0380d0140e030b04c2044590310691102d0301da02090107031540c081400c902054a00d102d03c2d00004080c1d55440200ca9001e405542d11803520a0903071084404500c001440ca6003004030380680008181c00758116030619824804503502c0340264002d0fa4003621180d100c0005141c20303109040090300f06c1190400c41c040c1a8100118a41d00032502e40001c83d00c002000c0a062035910441481d100407035035420504c115a50313080341c07074004038042c3c14045600e80c006c4222120450250800800d007200c100454400107039182c1040c0e440050510703120766207218480148201903009602c40b0513248503805086051498103840368040d1fa040650068640050303062140d0300000c01c040d000c6426200c04644a07000420981d0301d0160380510b0f600020013001040302c5050741e8026100c81083c81001141441d281c03808590715800550040001045460500401c580c04c0000000038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 747184802 1250 747183552 747183583
    0x41d0a021311120402040b1903110f01120c091a0408060705190c1703010e04050c03120d05060301092a0602031303120e0a08012007030e09090307060c0809 68
    0x10b09035804000c0b515000308402075151045540005045655952204d1b020a030020100c0515003541c0200252080d1113000468190803800080e03030891401640d54050904142d4030700341d00c44000c1586001819a924012040c44109032001c100002000e400c022148440c40301c1075103a52030300f41894905a8040d0200040c0b143c200101903030b1036480c10705405184241e003010740c034500080c6021741030ba0003080300d0a907030850044008a05011900b8030103000b5802030b0b04035000210200c00305070701c9007540c0d401c0e800c3c400e00c1001405c055401e541c00c070503405200100002801c40543e2944910342c1404034140b038002c48051780340c0401d032041d00c0110010380080d100550a0038544a80c940782003246010251039103079400b80c5140345c0e5100d003010303900d0b804010b4000543c0550f500c0e4101c0c080c201c031000800400d900e0002001c0142e00d644241d450494041d07440e00240b0b441242030104012000d80b2642c2240000c129210110b461030148514a00c032a50340c2c0042407814040c1035041046240c114003a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 747186052 1250 747184802 747184811
    0x50c0d0f02090f060c030d0203101403010509031c0f06030605070f03050105010c031d1513060e0f09060105270a06170403110a0611090117010b0d020306041d0a0213 72
    0x2e460303c403601c003005140020340b0425943d902101c030540c654040e06000c000200e000104100b2403010044480017244c04084c2c4000c1300b242008209401d841048908800c15841400110610311a040c40c1342090241820b00091095004a481040e699550800d4030784a448106100136164407000701d00d5108107500c0e081049504040000303100c0c03401000301600b0000c603507401d203031000e40329070042c180c085008100c0a40c0c1d540c0200d940c4420340014012000c1c7d41000c7c0800940c240c000e01684207a00720013403a040907058401308000000c2d502511442c100300f010312000c1090f03400040c12101c0d0808100c103061f41d000f8503000300580007085030010401c0000741d250003003110000d030400c0c64020b541402c0680002c800c00313210364a4504404000361049040004102000991400070201d030f00e000e903104042c4090302c01391481c13065001e110303000703c3c1641003200b02780350800d03a405035401240c024000318080c84003000c4004040c08018880c429504041268800c6241c190000851480b42400c18030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 747187302 1250 747186052 747186067
    0x51309330f0612140907051002010c0507061d100501030c0f140108250504080c04020301082e14060901081b0120150a05060307051e13050c0d0f02 64
    0x246403200301d22800b020700055030b800211141154002130710011603032000201da86400c28116a0f0717401030384181805158001c9000101d02d106008204091a19403240c0785440001c1d03443e00014200031a5003014004901e00c691090304080c00340c1005411740320b001050030b504509202030070f0401580101e84440e84408201f144959814035000c1240c400d0034000c0e0070780e450200314032a602d8400b500005c04154036900e03441150300301e00940300351001c040880d10110a940f003400201d120a01840f10719502014038505480030101075424891a80d1102a001c3d04050300740406527100e05000880710020036040081030308000500398010a4500d00038441e00000c1592814901e0074104024104181000628101c1c00ca0440b91080743e2605000c44040d2604401a022129410b0f29041400c034113010101c2c08038a00099401d042d540000c16050300918003035140801203202e14005604a50b07401e0340303503400301c0c060f03c902445002110307142e9644810b1503400300d0440750b00a41c00c0502030f10612520 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 747188552 1250 747187302 747187319
    0x812160311130306050a0b060d0e06060f0d0f050309040f0f0c02010903050d02091503040f0b0c07050d0807020c030d050d060504091a13050f011406010807080705130933 74
    0xb030031250800d000180d55192029807402810042d0085038006000148140005070580e001c1780700c0d1403151040c0c034801c3c0c82e04401c000c02a0b0a000701d43c3c0c0d1000452620501103501d004440d00c5892251044900c0c05441c0c501040941d403c070302e0890380065491000d180c1c0d40070f041c054401082e8191000304104001c50758090454010003801d201d941c1e40c0800d0100b0b491300d550360354014509581e0391a076100c0c80c040c903110b113011411030300407211489900c01103014030040c0707015100040c1c0d00201410707144000c00c0d0201c8100c3d0006103200110300c070b207a8182d0490b072001c2c03106a540004681c0d410303070380b040202604019035155501c1580140c1c0313002c090101103040c07032800440030703145c8103004026034582d070ba100ba40215940d10083c0c118001e2462124500d01d0544c0450448039444c906140c3c599520300040d07074032040855000e40400d8181d00001c0c40688180000c1805560041354402d1084d201c1e55803071f00b240d925542d1100e24207110504071003c4081003890b40302111075040071048050404402 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 747189802 1250 747188552 747188587
    0x809130e0615010302070c030602040510080408090907032307030605100212030606090a0b0d0c0f08060d1401020a021e0703050d0309110909010902041a0307050d0812160311 76
    0x100e0201040b070080070010382c3c0c442e8048410050700981e45a500740d84a050620007980903200784c43c824800c080d0203042c034500500304184100c1d000b0040600b0141a0010f008991000800f41402c05980380903a00e4080100c0e040d4035240b8a4000b07029000f8548080c0c050112020342c0c0199105829006401a200e40e001402c001030b503540f0a071207502c0c1c0d11101c0100307945002c0c1154695201c0402400401e00c0e0070708102801c2c848480b0902401015450541595900c0d031001c010000110000b0009205040009010002d10b220700200c00e02440720010b41400c90300250391b040d0040c0c022554560728110351100f251075000403c1d01814509145543e20b9527034030103920403141410b45235113904062042d081400705103048050401d0b080340c9801000e0600030a20504101e00c198035100500b000d401d00f6011191146202400400009041200704141c4202d00d00e4211503000703082240440418408080074081d400401d418100303541c5030440581035560402c030a911904091181c100603546c046035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 747191052 1250 747189802 747189811
    0x201060f0302040e0709110a0212160204020c0a29090c011707180303171e0a020f070510140106081603240806180303060f012007030809130e06 63
    0x400046100503131180701d0400c0032541c81105481d20b0302000e8502d21800e0703001006182541c1d8265004d05c86904070304096805944071821000191040000c0107007003035402442c0c140308500480b80018501d9480c02c01900c01820840c0c0d40801610308146203100a818007504820801c2c0540046050079000805500f160f00703440081e544c0103800300314154026006402c1086042c075500c1600354403030401811600c9014440c4009104150014255410201448942600009640d000743d11052140030184d04002903103104035001b0400000014001c000a11b05003940c0302001c00d180445000354008081d05a004005000c006410880d074008100c506d800d0200f094100010240068010341c8111500d0180c81d01031002007400200c3c03024070000d004e9101e030808071250142c0e40481040e0940300c5c0019914150041031036001030705103601900c210500c0046030960015001c56400001e8a0a0780036842690300b000f00158500c100d0601c03070b1040c503200e1140501805000b81ca220341e2680c8000040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 747192302 1250 747191052 747191059
    0x1b05030402120d02241e0a0b1906020706021203010303080c0c1e010c051804020901140a0e030c06120609040212012c060118050604061a0a0306060201060f0302 70
    0x1002a0840d42c0701c2c1e00240070110603104450340c2c402c24400c00395031803192258a180d03045035500d124000041008039203128840d0405202c0c2e1000000d20110150140a03042050312511102d035a0b5440c1c699200c2001d601801c4411070001d58a041c601904025081d000401150130086210001b52003032401c0301d0449074146800e1440e41d0703070f04035035964600444084009034000d00d005164a404c0011a031520020210b00800401c150600252118865220710000780604a002c070307082840d06034090a604101810b002c058001e1407149082c140d881000075170042900403642114900f801c01501081201c1075070054030b41141d0301003071002c2c4c000c024001881a039000c00000d085413112102c3d08c00d640e00c140002e0005242071249101c52850302d024003c41042d0281d05043c550f54006621030480b01641c1d5001c03401000e030204030010700b80090240f6041500c0d1034001581030b5039146d0108a0032018a903080d110f90691a00400f42ca0740c9a202c0d00c00c580c14502d041c003200d040c4d11115022a0341c100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 747193552 1250 747192302 747192307
    0x30f06030106170d08090c0102070e061f02060702070e040b0a0c0c0b0721020a050a0507050a05070312120603030503070f0c290702060709120614100503010606031b05 73
    0x190000e40503001c15000040d103501010281c451064000610501d844c80d15210b0b21170a964400006a4440021044500680c4260020890585182c030810b40200b000b4100e445c0390700c401f005a0320182021144100181d102008000c0007546c1400b50201a01e00e5140018a034209921100b40c5640040e0901c2d203855a1f03031481202041c0680704216040380d004020079084e00c1c4c1b4902c0604640c100c40c20350350385020b031441c403107240d880f8610880f054101d803500c1d941e00700350b03592400301c480e5082583c049a5521641d000360700031401c10400c01c00150b10660302d000c070301e140c000720084c810845003480e00c44060512200380002508101074a80c020301c20300c2c00a2080f41c440c1d038200c9803605105005041241c6080d10104c03210420062504508a0024042c9542c1c44244049a8400c000c480c1d400008000c90300600080e031140305810070890003a0008280d04840e00200d01d0440c0741603e4008800c01c10060801c2541000c3c0a002d00401c22410b042003403031410f1074011070022560401a007040b400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 747194802 1250 747193552 747193561
    0x20d1a0c0301630908030f041b15030b030d02060a0203060402070614150612070509060705010f0b0a0906050a030611040f0e0f0f070509040f0e0a080d0f11030f 70
    0x10500880440c0700d240910009104240380f0b0500d03100991440d02ca00000d807455400c0719460f80c01142a0340d5030000516143d60b0b05e8500c0d40c454114090012161070a099440c0e02c1c4400c10400410007410307a441507107001440012000d41180d40e9401c01a009800568400710010340204e01264492203819002da96942c480300003400a102c0c80800610203482e042009043c03403006455244902c0143d0100d4034290300308010440c0b5805291a000081d80b05280043d000340e00c940e000d00340c000c0300a044103084c40017941e100c03825145101d100c8990981d54815400e014a05044010003c02b800d150402c40d41d82454082440c010380c601000e09800c4d10f0f50500e84003ca46202128014140002881c1d1059114050801045010f50b00b441341174000c0408170707040d040d081110f00d0081c01141c482526100d9050f0910024090000b00d12414941d12808802068000e1009210b454401d090461755a080355018204841c5444103440e607841c0b07040121340690001c13800701c980082c10325000050a41d10b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 747196052 1250 747194802 747194879
    0x62a0f061305030d0f0209120f011508070b07031b050a02190807290712140a050d05040f050d11010e030901050901180b0a08180f12070f020d1a0c0301 66
    0x7007044060700107506180f0704a608002141d464089c1c080440203104080450304414a02c00e010300650035160401c4100f003010200c2c000080c00c4091003418291000200c0f0805640301c0b282c4581306445540100c90002c0444c50150042c03584880248005040395050100300d9a907070405020b80a01c00d0107108030030f40c8810502100030043e5488211160f920f1841d45011011101410040c0c40450b01110302d44d00041e660b031060b00c0d040540703a0303140c50400f000300b4000b070060017018009642181c850042d500200b101400030340c41c50f60043d01e800c0516811031600c10300b110004001109541c00034810031480b80e90010440740120000d20f0040c5048024541704100c074081588000c0940400203406c1350310680124206200d070074102c0c19882c0700b10604c0d82d0151100800d9002c00d1280c0c1241d40903e05030341940001e0311000e4000c000ba1080c454050307000c250303000300852044e1041c001815021641007180f10140c0e40c045000c500c9141554901104e1aa24500e105d081501d02e030251071741d1141219 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 747197302 1250 747196052 747196057
    0x30e1018080312100302060901300209011103040e0f04080c030406020a02010e040203040c090f090c080a140706080705030a020c0327010914062a0f061305030d0f02 72
    0x61004091040c1240d4803058240d580e404400440405840900000c0e50111545000c00485e40c02070651340c548650000110ba10090300c00c1602c441d40340c0044101241c0d818107901402111000000584d542c00d40000945001000402c1d11842c0d07108020500500e00801c44150300f080c1035040300d4030b4503195490032609901414540b0100d0f80701c0070030001102030340001c80e0380b0414000e803030b6596185800e2050105900c000c56024001c44c0141c3c4080100b95030641c0950075207940c15070700196028090340e400801e04560fa010031829448005e400050000c1c1841882c403600e141c80040c114036180c00c82c09410201c00404120030301c40081f00082e0b2407201a0125030700c1c005203209803030351200100803141c02c144180f5441c280f00100307400d142c40ca079400f0b02c4442d402c0d911500801e2a20300c09500030401035030b106112000300480d140c1c0b07002c148a000011340030390251100000c0c0c400903042114442c504000201040d0101e488030f50a400415404022620000e86207000419901281c0740c101d4040d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 747198552 1250 747197302 747197327
    0x703110f0c150304031e02010b0d0813050415030f050c150703080a290a0f060c1415060105030601090b0301080a0b0a05040201020d0c0302010f02030f22030e10 70
    0x34003602540d4030444502181e001440700c030031038000301c00740e420b1020496640822a00100494520280c440c1c0c162400080c9407510101d03440040780304000c15000c2102c0c00311901049a0110f0040780b0700300c010381c0e02c042403405054203880812803840300c10b101c2e5035461043d10000e411808008800350a00c0801d011400c41103a014048040e40700603902d08042d00c0d44046c0054001603418000b040b0441d0440c0281c15a00102400110403440304600080c9903600d01c0c1000c40d0700000001e0000380512000c894400189095200e402c07010400c0c1c2072142c0e80c1c40c044101c0b05040c0d0022426401100940c0e454650016800e18000b500e03030f9202ca00603607903889150042c4803030a4020000003019540014161a981c2c0320b1310380c0f0100d5484d410030032403e4890a4800a016070030006d480001030b807060017403c2040e4041d02c0080b5084100c500103000705d034815280101329070070b04000c0000d40c0e00c3e420907600e190080d041ca80224502079071001450440c182e444d03244200340503143c00c807500d4410190092030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 747199802 1250 747198552 747198587
    0x19030903051603050c0901050121020d0e070816080a20030f0f251a040b030702011d0628060b03150405010e0c040e10080f06040605010b090a0b0703 65
    0x3511452400a01091143d1008075458811031540003018242031030010304952040e1100321108010750404071140901c440c41b0f1040560911403070b0104400c3c0e0082d001c211000b0400350036001d041040035400d06441401d13181d9026090042045403090004244403240e8208a0700345c2c0542501c40d0030001c041076514419858480c642860424150218011182010307010840c4d5408901828600c02c0c01400030400f03603c4072003000c0c10461105244d54100980c20314460b614a0700d03459050080c0c00d80c200390b03007007c0140e44da514442c0000b000c944104035403a0004001740b059160100f104082540c0b910a1400c1801c280e09049900c200b181d04408050044201c529859151090aa85400508417800c0e8071403800c1100010716130b03c10850035800b4040c03002d810b518041c10188024031445000d00380381403400c50740200141c024030a20001d01c0094009010307107014140340c20420156141a00400007120003041540c2855842e03440e14002c5615038060346032100340905066840c08400d141403000e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 747201052 1250 747199802 747199813
    0xf02030607031a0a050a0e0c130b040905010b040b27060a05090a0923130b0f16090b090111030d050c0423090411030c06040f24021903090305 62
    0x780540540001603914510074041014507040420029116160302c95207410405c0400d080c048180b0041719198080303401c80d1b600e0310701140c180440c0354070f052980c0501c09400000c1381c2440100c0690103807500401e0a9007081e170038181401401d80141c032070303208528142032015060501c0003141c0074250140c40e00040c407550700c0d4503003020b000d8802d42c41aa130f12442030700d42c0c1d1000320f03680003e8407400384441148411107840d018141003404469001400c07011510080c840716000007003404002c0f80c0300d840550306215003401c1800c140c0001407000704c81a001d00c5510380c2c043c41707480b4440d000d482410303500b442e28080a0030103001c4503055100c2e003000303540214205400c0000c00c84500000b0011030b40c0712101510720500e4100b0942c80e030920b58602c258800f007028041008503041404000c9010801000d55461880c100c0000e0381e1903000781d01880b1900c0c800c8108000f0404507c0038610b05441008074112284041c003c02910344441c0c000d200000240341010505043c81180444003466202d0101c94 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 747202302 1250 747201052 747201061
    0x3060114120f070b0403110307030506070503090a080304030c26091509030706030b030706081b030402060d0c0801090e0a150509030d060e06270a05130f06090218071b0f020306 77
    0x500c217500074002950b40240d144041409402c0000e131400c2200c0d0498054a219280c0540c00c854588c0094000c000302c1c840e0124050200e500c80000f1070156101b0785414410b54800c3c41d103001c902c41e41901d215111083c00a1410b4003a05401c100da013000401c80f08895100c41010150f80b0034000c4000c429098810000c01003030380c0342c055010440084003202140c81c1955501d9046601d81d0040350030100e101c1000413a40c0002d01c84102450b0418070080c09103013070404800144081750904400c00c00007940a10041095142c14810500c0803800703038021b803100e1415078842c1c1c07006402d0003041c03802060740c550005144030028800c3e2683c06d89035a40a120003681d41c6002c0581c03a00c00e560480c490945110b03a4400b107940031054501c0c0c56680e041c041b125954a640e400000c0c00000c2c44640480c01400c5200d000801d001503682003c0d00c1075000040da85184c3c018090325005841440d5100011001800750183e041600d5424842d032080c9025803002082c076003940c00403030446000b034051080d0420310 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 747203552 1250 747202302 747202319
    0x6170601031a011404091703131403180f01110604050106080d0815040b04180807110105030c04030b0618040b06150a12020f09270603060114120f07 65
    0x150407207001d0900b4601d80725500d000540400c900b0b209040d0340740e141490810440c101a088003100300d0103400d680b01c1c18100383d203240314564030403181528040c0740c1c1c030105800c0060340c44010a41100314401141030070b4414021420102a03c0305040c0308030019543c58a06a05c9480140f500071402c200343d91281c1024a043c5010b4161805443c2490052030241c4a6003071184581e00d105128403119400c111b0380d1001400000c1a4141d1405d80264483e04008d40956600c40820101480364030202d43d245114240b814803d075030048500d04101003001400044116107050b2000d1360b4100c2c80ca40c4081c0c45d4040041c9181d10100c510348440903500041009222131041010322480d019242245040c040d0b107880c41040c86501001d201080b4014074400000b5003039805051202c6507403401c2032402800b0f00004840c0146030b240c51544c003600c1c00c250044589460101500441c09400070069541071102d400c3c02da80c0c3c1410801d005580308241341c0f04001040040d01480031030300054505403612421072 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 747204802 1250 747203552 747203563
    0x40303050721050301050120070b04050f18040210031b082e06050a12180c061b02091f0303090816030816081e030117012c010617 57
    0xe42e594001840c2031102c2c142450050564440c2e00d9540d6450760382003500646074902481c003003090142d440100070030080010008203000d4019824100c0d111840d0008000120381070b4008240074014608208000c520407400d00c80d0095130403544d000c04540ca88004400911154a07203148981c00c840d00c821ba515004510180903000303052a002071000800e1007000c12a80c2e51100300300e0040b410004202452181b0701400266409203801911882030b50007038415038824002580c58180d0360b842d48030412025000d150020801c5013091419981001b510f502e010401c0c0d48042d00a0303401c04009114546407a40e1040e131101200d004040780d0361030b0704008180c0d05250040003000e00c41c50104141c404181c3d0b12000440c1e600241c0186000315a00016407180c8419408482401d81031210001126424040e62041c1c2c480d0a0440d40380c1d071520b0105480c0018008000380c16900d06a010030803440d00c41020b460a560020442c0090300e8646040c600401499000e0181c0a1110141c002e400c40081613 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 747206052 1250 747204802 747204817
    0xe1005070c110904020d06150e0c0c0f0f070909020411030a0f0f020702060702041a060f09010305070311090409021c030e040b1f08040204061d09120a12020306030f0304030305 77
    0x70b540d18001c4a0070b1016001c400d89000c0d40c000440840d240000c1c241c3e4224140710f074030301da00454549a503401c500b6651031082e200e1030640240860750a10250f410484040002048802003a08003814242c45481343c0310341c080c1407025911100007000399280c80e0802c840c00707581c00c1c000555a242c00f01200c0014140c0001c0e1100042c00d2440d0401c50417580c3c0265060a50014101c600d0224590f082100600b98034624407480e101c2c1b01c4442c0c4c8180c0e1581d0140c0707142d0f81c1c0c80394199650b00920000400300c0c0c00c024245014107280c405200c20740303d000170594040703580943e40043c41000138000904000f001c0c00303001d031010402240427410180c0c40440d424801c0c40598003404092520401c00c1511f03040d585811150405041414010a00c6210201d42142c0082c02c005401c64403100705e0b0340303454a02c00d1b5a50030002c40d142030268452040050165450310412103906181d0003010061003244d84401000940b500800818020703a4140040e0082d15800b8007100c0d59240e5a02e00038015400020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 747207302 1250 747206052 747206063
    0x1005062d060a0c050f0d120915020c0a03140f0307050c07090c091409040b040f080d050f07120603051c0e0307090b1306061b08071209050406081f0e1005070c 69
    0x8a0707943e07213220000707081c0700760b0802d91280403404c9072071f4100500804031441c05842e0303400074500445501960b880140308100c5614054000c842c400e0401070300c2641054403c0780000f4003007080d01041000c80c41981d0300300e0014035045690b1102e00c1f00c1c0318a40103a0b03801040380f10f4900701c19810402c0e00251a001110b41c2c82c0034182d031a0013018104142d000c0200c6020b030a8034071400001e000111f0a071040c1110621858030795050000340e400000c12100121290400b4107054414410009d4101400034103030050640103000c20743c250b60b221500da02e14030805441040e00008d007482d9003402050300d558144005001c840c00d495442d15800042c1806144050140c4501d0750940d20402480c02030500343d0b0095141c01ca040050312a40c00021660f400040d148014117104920019007200324070b5070300d00b0b90307680c8152079503050004210455083ea07011000552140c40f00701c81c0e040480c0b00e481d1542840c3ca0340010205521003c06003001140300100f10610721707140800c40080e400001600703405000e40d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 747208552 1250 747207302 747207313
    0x70503160504030510200c1b030c130e030c01020f13050a03080f0304021f080105040c0c0c0b0306121917030601170a0f020c06091005062d060a0c05 65
    0x34141551144100d02018001c1d8110b64107001044082d07801c00340f08600d1113001022251003d1441150540004e8004161a000611640d131034800c0410180d161403421009001a0081080050503042801200b000c0035529584001d8000030103105580c0201e034128002d554406107032040404c60b41c0300681c4c7c2107100501c8440810f441c00d1600881c0181c0ba803042e8140d1a140c2101408005500004c00c1268454003400055800e440c40441195041c0341684a40303441d54101020042074031010580401040030890100d00443c008690200460346ca0300d00c010780da9101d62001c52140b09181640d190b151141000d0b0f04a10380300680714642003401418003030340c9076201841850040c0310681c0c030709000540080e0101a03200480c40076641041910400007840d00c41c0507449010b0b41c0050103400e200c0d40200d010070581d03c9081c8903100002034004010461440d060000804500860400c044054000d801115a454051040010100300200165101c02145400030020b10901404a4060090 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 747209802 1250 747208552 747208591
    0x2010501090e0606101b0c06080910021305010e031e1e071422050108030901090e0106080117160b03090d090806010902090a0e100305150609150d0209070503 69
    0x3041144c09803034002d040d003d00880442089503100d001220081801015481c0b0720002040c21017020000c00080d03c41645914051840d541030078003400000d03078414010044c8104003c007010440c01914008d0078201c500111080119181c22604c440e0701c0500c00a0004c5800d940d00e000805910b5900c07d40500c0311100140f040103520340515100f402031a06507030303210011601d41002d614030f0880324070070015041d041c0364404e1804d41c0e100703921038502a00b0000d07142c02e0742d5074050741d900080c0c030300d240d111b002a500d442c03001450408144210305100f9180511140403c80074003800e0b1040e880c081c80402100d0b2100c15031481e650080e10310705110f124251028032002d000788a01c00c100d9806a014101030703840c0100300c402079405030604030342c880707243c142c0070400540b11035840f800b46a848180214030b60542ca0318501c1d007480301c0c006a80446101081040d281e803283c0c44079520004000000c00c0f84124940030484c0f079060110002c0d0b002c1d0500713040101550b480409117104120614052000008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 747211052 1250 747209802 747209831
    0x602071a0402130218120f0105070e131a01050a050403060203091b01030c0828060f14010c0c03020f040e1e01150b03011e12030e04111c1505100201050109 68
    0x80d6000184003284003061103205e03283c2807901502400b00f485c261802c400c84c8001c13803421554125020004941459038000761400c00c1c4000d11510513000804011810104240c072850390018440d00e81005000030b50701d503487c1d108d00700707a80003950322180540d2203040c242c0d2060b44070341030124840e004a0001c002070120758401d01808001088a032150f5a4035100c0480c0e00545240d010044004000481d480313059844880c410350740104603201020b40c0da01e041814404641c50400b6902c1e04004184040758042044100c401e41102e034103e86c50074105024401143c00b40001003180c060038014160b00421521000c01d4249000300004001c01c0f2100d911601c400c1104c426028800480304240b00601607402c500b002c0740c02030500000594042a80c2d4515441010b100c070001b180000d0a61031040318a00f8240190700f03018201c040040e0a0021040b24007074440944a0701800780c40d150050684480d015110200142501400c941c10507050380300081d0281400f031043e00030780c0389050103140c08034a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 747212302 1250 747211052 747211057
    0x51317040824040201230a030b0a0611060c091302030a02032e03020f0402092e08012d050907030b090a0e030f0d0e03030103200907020c0402070602071a04021302 71
    0x8039000902c6480e82c44075001150160308205081c1d4241e002c803607a8580c0a18403c014182851041d0b82c00306682c590001480680a019841a4188907440a01c4508844003086031035000341110032841d12600194001241912000f103100e42d158400014440c403102c00307400443c03080c40e15102c0380025180d0080403031008444120b51002c1d00381e1480d810300c01403810059031151010020805070800b07654000055004c03040044d050740b003086c1c1d803d4083e44000c00a000e1944512141040080c0b50715200c006c0700501303070b219402080203040c17403140b20241100001003406450041c1c4214418604443c019008004803442c0d0361082090740b00250140e13800780608500b10040c00051810051004020a0b4607004041d4040c1a19103402c0490f0044500b000914021401101040485181910b0020380c0808403509503000e62584400c10101540000b0110800d200c2900c0041e07071111542400380c024080d001008003511103110008800701404c000b1180114003c4510090504c08440c8060403803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 747213552 1250 747212302 747212353
    0xf060f0204083714030c1c17011202121b01090902040521100908190e090c0c010f0504050f07051e090703020702042901050705060a0513170408 63
    0x190b05501446031154000f412401e099110b0442034207081200c00402d07080d504501d82800099010f4000d003c0c0028840e01d851503103d5060034111280b101a544120032a071050107507110f041080c07401101151980c0044200c506154401e44850381031900c0c0342d84023421103000311400904100c0020490700c60a00c200c5d000c4071802000c04c4010200c0c01d85c0703005155407201c007003230203030040e00c8009a00004034059280f040703100d0a90305503035400c0000c0c202418123a480303070346080014170b0410300c0071500c840e225180c02044c80300505448803241800140540072109003c412281072406001c100311001402c810703821070b0a410b8036035083d00c5800b84840e0003c40b1440c907844082446c4000528140070040a400908614025180c005180c01250541d0045050800101100d08a8030b0f5806104000080a01024a0010b00d440c04a80b00c00b0b0340c0340030140c100010f00e80d595011401c00106204070010943d03000010700980142e103641f034a880d0f08140b050204034065001c0e005507201d4610400c8442 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 747214802 1250 747213552 747213613
    0x11a010f02060f0a060e040507030606171e03041511060c0313080a0c0204090f060501050303091e030f060106110105161b02240418050907120f060f020408 68
    0x183d0b56010603075008000141c81c4480e8142e4400c07000c0fa9450301b600e40c4901c101e00441c0184441c1e07145144c403d085034016845080358860b07003d40a02100804524456621a80f1403128072424005114a046201e00c0d0b100c4046000c03820740410b1350175040100a542d010b440810380381c2d2965000003400c403d120490300155001210040303100060003071805000078105604e01080381c0b4240340e001c6411145407810076640c0d09640c02d41c827000c00c01035001d541e024050a9001d1410a90644007040050540360710200300d00158502c41030303880d00c04001340386895905408603061541c0d42d45015001d1903403001c4903030103542420000354400085030405080c420507580d401c981e41303041300c1128107800c2055400300e81c0301c000360300b00340300b044d540d00102d1041c80e6402e1804c55441e0b10b0640101410040748800284460900b4100550040003107a580b0460717851000380d00c8040304500e44048075209210001300414030b0150724028500b1380e6030282c0203403020202142d980442034a4819042c103481d20b00e1044 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 747216052 1250 747214802 747214813
    0x105060d121b0c0603050919120c06022106030601080c0d0303020c011e0b18010506090d03201614030a14030c070305030c010c11030a0e0f04020c011a010f02 69
    0x4854801c01d10ba00400522074040080700c1110795401c884030540d9842880000d84820501c103040d0030a00c4142c200304d10006000e0050b50269403512000a120480070090210420b1040c003802140d030121446403c0c18405010014000488140c0c8a1802c1d20400e000b4840d103000440c0c5e03a54005101d82054200900d00383c06844545da044010354420081c3c001e5070f540f69007074a410780241212041d003594029602140d52001030007030160382202c50041360035840340740c00100816154207086610184099442900c041140d050542e95212041104141c101c809040c0303c59007000460118030300c48520381408c090554850050100503000c140c01a4140c20912040c0300180c041c140d80d00300425680c05403070074050b42245043c1814003603401607445402c002000104c1190a11800741018550304090713404108458685036070b80503c0075001e091000074000700b80941c0c2c40060000d50b44000138815550b07000f400c1d102c4d03400b9148a01030f42124143c50030302190706600600d10701d00c50380c4035a4014003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 747217302 1250 747216052 747216083
    0x81812031905010b1c0f18030f12140a0c09050d060504020a06050901021b031603060906050108030a020a060533010305400b04031d19030209190c0201060501020105060d 74
    0x900411030340071b020050390b6460b0945a203040c2c005101e20502d50003504c820090052800c0041d02220500c014030001c28507002c402c01c440300070014029004000c140300040c045070b802e401583c840c6220b41045510220009500040200030b0308807920643c03098804140c0076030b9507001903e0314010f05112902581003c2c08240d481100c210030545c080700000e0481d99403800755003200f00b800202ea041654915286c16860007480a68003806004001981c000c2d03182004141000751200140c03040100000d4685c00403991a102803115803d64521040600415501c1c003001c054918000141441c0801c0c1840009402022400354803200b2103521140c80d00c0b002280207000015811041d50b81070840c2c01c1030380c080e02052504110511451103500d84641000b18401c038020354440e84001d19129060700300442004144111460701220382c10382d04005182c40b042045050b100e07100f040c1c03490107403a2540e484215a415080b21089540c00c2e00204129100d48061007108085c000e8080e18191038040c040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 747218552 1250 747217302 747217357
    0x31909120f060617010b0108010e0702070b0711190824011203020a060e0c120609030f0d0b040f0b01171005010e0d050d0c0c06020d081812031905010b 66
    0xea5582c0c800c110014030151940c5189481400341c003080c0780181e66400300c013001560422100c6001d4801e420f403041e00c80c5000d4034004d68501c1d071401420310303a0602280c1c1408200c801c625004440f10020300c16910000552142d01d14846184504001032299000202100314140c04d0981843c0112146523142da0900a041890000350320b0102d08511030503c401001c541c1c0d41c8152080e0645140260210103035203420411520703525182101c0e02d420003418409400b01c0001110390702c0380030b950015124400701c0c60490040c01503400064015041c426011390b81c1d111580700d0001315109807111055100c225480c04d54078007040f54014002c1200080900c0990700a5262054003039000b03040c03400c0d070702082e5140c41c20a4074802c2d02101007110548000b0800c01d516080340040d05441c40204003942c10403c000303100b407801505480460410994030440c0c0e1100380482069000e98501c016130b2170800005840c1d0008100c0c0d003035541d11303117001e0002c1104082281140c4050000b01076184102030b240c2d010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 747219802 1250 747218552 747218573
    0x21f09060f05040b180f03030f0a030c0c02030d030f0f0c02030405040203151c030206060d02061b070f140a060908070b032203050304120f0f0e030f060903190912 71
    0x703018480d042c0000035410380c120009202c0b0710044180703090100e8500c014800400d00c4060340340e00c02e80082c015408401c18450517124007030f0705450045100b00201506450702440280080d4140c02807000088807150140c00c918052600f22008101200111005c0005c6500e641080c10058004001c05c00461801e50082d5400c440654803076a0075811300700020340c000300b84800603003034180c100c52518141034040c0252603010405407450f1141035026400180540300350040521a041e03203100c4820030b003d0402050002e0810031030201c89254440c495105035003c0070102c58400c0c29039100226400d03100e07038810340032140304c80000c003030719400c158202c41550002000e2112145405100501580703e202c02c49101c24040d4540c07543c0e07824541050324001810844400074004054140852251b110704c1c0007524604e1494110841e0740c1c6080064103002d1a0b040d000d00a1044106218000c50040300400004180074903c9001c43c20024098030880c445e0321407031050a101e20041c40119041d01d80 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 747221052 1250 747219802 747219827
    0xf06010905100512070915060219020603010b0711190302190f0e090f031813111b0f0313050310060308120a0e0114070e0a21030c0f050a021f0906 64
    0x1a1740c806911800d5200c02c4504025405024a90302c150030401e07180c05001c03250076503000c910f0090444040381c005c24094030041c812025a40000079280c01400300c046081008040003c0c11510007540c9444031000344122400240e2003030180e1000700c6441e030032401c0b11400b00d0b80c40041088030705142094510903a1002092f0755002c3c0034134101d03011000304c28002040181d40d45a84120040d01d84014850010070300d11141c08140d1402a42025011540f0160b840b0300c000080c074080c50002d00942c00b42480200d0b100040248000700700346050201c0d5001d0042510f00035400c444494400b040740c08140d030300610020703201c1501080319034226160340d94010b40c0600444004100092034000f95800c59031a04280046200e2170701c240203d8a41c403002c3c0002c441012601c030381c496400c19018100c2c2c104e4071460420f840040712102030401d40180e01300241c4a80010080302000710906245480d03107272018049225044003c1103d40c0041854404450001c1695440c1d02d0707076080c403400b0342d0b540e0f90104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 747222302 1250 747221052 747221089
    0x4030e0307080715034b0e0c040e0615100e060324010c03080a0f060506040b04030506070c0b1602010204080f0c041802060a1407020a080f060109051005 67
    0x30640b600c04000d4100248002015002e101e0003c01c8018201c0709007190019031100c1d80e02c1240d0b80c8105007680d10188076071300c51085003085030000408642460203001c8018050909424007401c03180410703103a60080c0140d6040c4401c501d20039909454000c100e40500c882e40a0042c0e04250381040c500300e103141522401c1a10b00f10100c54005540c0da007044940e080e044d030507500c0090941c90868841955103400f800c1c8030080b112903560107099040f0003803610f540c0d55524103c0c5020004550051001441d000c2e200c140d45079245c54101201e58000d010a031518402c00011990042c845d0740c00b03088407034102c01042c0d0952030310301011060000d485003000456409000229000700300703022201f1548101802440011070901c18042580c048003d482d09001c520300d01507025031286400c0720600e403100e03e040c0f0142c40c4542c01900741030040c4c450194000c0001c034404034000b480003640415882d9080c1c102d54180ea85e40200b0019980202e40140080c000c0210420a506103034040d0950316140c40f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 747223552 1250 747222302 747222313
    0x170601021212040215040506040b0903010209060a0206042906041d01050a0b120d02071205010912090e060d021f030e06072f060112080d060e0109111204030e03 70
    0x301e414245802a50b00124003003000c0090004520709500340510700f9083d940402c1c20305251200203807050189208110340c036040041c000000b5038080d4101c41e10640000c280540383d0b4270301b800003075480108803411180303900035504c10004240b058521050b98a251000302001d5a07a501c01c0c000036200f1404407031213400b200140224462028054544980d591724400a201c403280b100304604035600140560b15a0004094600340030b0340840c140054445a580d29110751040d4585180100a50135001d0300e914241032000b00013650103c5084116249200c42180300e456450030000f6000e00c040c03000b5071120072501c1c054250340c2100c1c042d0810781124200015107040210419050990440c0ca450005002d888030f13401280542000c2c0540c0110101803034030b0800342d903650715030311070040c011424000c10740308440c406c205817002203500082d4461b42c00e1000700d5a80c20182c1d0100401c0c007412a4090070075181c0340005040e24203441007103203a13100c00140e603211504d0a0302c52081c8200c206400d0b0052 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 747224802 1250 747223552 747223573
    0x702030102120a020a1202090303031501050c0a0b0a0c0e030c0907050c0a06060303020f0610141f02010c0905031216210e091303050702130e010e0c0405060d0317060102 74
    0x2615041c07242d600d000d009a82e83c038171588010103d512048150800c2481417080b0452501c001013920381c000c01000ca030940c051044001610039014542a02d0014030507041000108a20700014030300500f41c0c03440a000303002c2002e10954101181600706038165001c0c6c00c11400078a03113010025080040c5040592506e440c401390780d0b08244850509944403501c8070b008104144d410400b40109642d90390260006040501240000600350710501c004a8100d07102c04140d07940c0e01e1321007003d048071000b61040885241e038010703000c0e0079140b5018002c182004800203031410049441d998203005000f120b4500742c0380e82d0000c00d0044a51708182d480c50807001d07011350b402d040d58a043c009101e030f544904405c000480100311140f40024070190500c801c058003140026000f1054418403a811076104c40714500544408006008011200c417041d803c0011140c40a0004102d20410600170303a800c1c003040d6114424081da01c3d08501c001000a0118040c00e2004c101c21031285402c03090510684018684 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 747226052 1250 747224802 747224827
    0x3030b011e080f0a0b0604030807020f210f06090d08040606050603131713030206030604090b010f0503211b010204150809161505071109090124080a080702030102 71
    0x1c00c541e568046a03145081c0101c41030441c440c02d601001e000e03001d201340c1803d000072641c10b01407071000508070103001c82c1c82c0c0704654840250916424000c4d1403000d403182c2041305542e212107421b445040500909501c1400f803200811410300c5910440000d105144002c6000c0340c0300580100241c80140d85d0303020125103950ba1070021402180ca04010b2000c900c0300b410004a8040d20015007020210100070074164212040e6003c0c04403601121701030b0300c90f911000860080d0500c04801492a40c200c00045031018401e2688400c0d600203800f121a2404e2188108030380c01100c200300701d4010800c0c071440b48240110000f21141840e600005400e055485001002c228100907150b03022801c1042040b150790b9040120031200243d07012204611854aa11130001e4a050341d5510304000c1d0018625050180001554401c40340c05840d494540c9041c480081c02010071a940c000c00311a4000c00340e10a465903200901a21460740c05000490000e83e0340600030380c0402d40480e003554003884891900d24 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 747227302 1250 747226052 747226097
    0x7170c030f06010807060504151d030105090609121e090a090f050a0f150b0f07140a06050702060c04090203190e0c03010609060f050f0103020c16050a060e03030703030b01 75
    0x38415070007001c00794101003107142490381c907410580400105201c200300c0384d804030810300c02d503c3c00c074104001e10030418081020050102202c0d00d8040d8202400c0c0074403a1400179100748030300070200694186401c0d1400300c41e601e00c18010140e21803584169600000e00340e40e0010001418000c0081c85803641c5c2d00d991500707032504001e034401259079680170001c0107450350203680300350b04203400200101c072410040c0481c2d0507958029819524004540f81c000c5c122907004603005c9540220070010140240c1c4000d03591000c0480084a41c1400c0c80b002c26010f81c00000c040b80900300f14040c05081c64185a6100000c1d000204506440066654500c1d90020548240b407041d803901c0c40603000d458114400d160a4902e29404001251b10b403400c10022252401d0818040c0d5108640713000308001c450300120043c0c0194890644140107504401c1e01d02c1029544c81d0301215070543c0c58200c05070340c484040e100802540d590303d4264004124400000303100b5444142d0f4880f05041c042507a05080b04062102c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 747228552 1250 747227302 747227323
    0x90f07030e0a0b100911310e190e0a030c061d0a020a06140d1a0402040b12090706050307050a0201110d140901090507050108090c04091a06090907170c03 67
    0x9070f242e00a002c180200351041001800d1309410612030300101c801b40386000c1c8103011024411801128004600c080e885920704401d48a80e400ca08102c0d0300e030003410054075000d0706d00203d1482c0e45120780385030368098000c110120b01444c2c0a0f20f000070558805480c00d14902508036140303a0342c0c4200e9200c021000e80d000041c041c11600a0032195858410305c01140344c1c40d040001401144080c228801d4901d808585841c0401400841ca075081c010358035001d2062580401e0348240049800b1440b400b40b68080c14540c1d00074070720f000d03464452550b03854680321107000704e80c000ba01c03c00001d0303205400b90340102002140d034070001130301d6500310700300040f650461881511410740710300220b000590282f0980390000034440007040080c516986255407031145208950503c20000009502600300b80010314070303882c7c09441400301e0300b0039140c000310141200320120b4204000801203106400c0000d2003038030510300080100744403410302c060f0782c0c110442c4040b02200c9110380801090507403428041120741 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 747229802 1250 747228552 747228563
    0xc03051503070501202a01020a0c05012d0203070218040309120212100518010e060f0405100c02010c030e15010b0f04080f012307020607031505030d02070e010b09090f07030e0a 77
    0x10785402001b110711201810042811540403802d03090114010084860885d8003d09001392404000000402e05031804d01400d40801d651215158910ba0048000d010f814800c0364003180040c0281d802a00d46070b400d81e03010380080d09128003404807407034160040004c640010140d0781061008000d643ca4a2070100619200d9900ca0702441121034909031425580301c011002806040e4800c0a19580c0b07102c014120900e03601c02d90b01060501c80203021a0350a034405003024405d800301c0d00800390180c000b034151000001c1c42d0802e8000c02c818085100120b80c40181e0304007030740d40d28203001d5540c69007043c80c00d80e070711103020040001c21000801242c20205011000070230701c003d6001101c50303820703480318038405c0d40c982200400c104103a0106c0d0302a071040e501c3c01e000030b0b2181d02d00c00d9000307104602e400c12501071191845145115800152003011070303500e403841c02096a03c4510100c0745024004010340c0100304132000c50764081c2031141c240d51050a6290009d5070103118040549415901d40081d00c9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 747231052 1250 747229802 747229843
    0x708120727080a0f03171302090c1c110c03131403010b0603161806170601050414061c050c1207020102120103110a03060e010c0305150307050120 64
    0x11101d11440c4245019400e0700d28a0385245000e11490300e0790b2000600030b00011642041c0e504042c0604400581c0011500c0881201d29017071800c052221a4150183e1207184c0010003d8441030842d000c89441a480c41c00c200d1940324000b00110142140301b18005800e0307820f1011350000d1100f00f0240004586c500d0250580a00e0300c8191340c15640c0c42072044e806641803240207a8181ca400c000c42e0f400107442e80302c112154050010840b8030b40001c81201c00c200d08546000200b81d640300000c1c00803034062842c201ca598440d0070056885105130301c2807032051542421881d05a1514a001c0e100070748807403404e10140f103500540704048402c01c94400140580201d01100c4006808a280340c0c498100e000031403038404800c440aa10780070522009003101e0a40310034a105d81c4408070703104011a480282808054144040d4501900410480c500041e18210000350b1303600280801c1041d051003d00a007032101e04001c011940c0051480304002c81c8040e4000300201040c08104884080c01d54a00042 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 747232302 1250 747231052 747231077
    0xb0705011b0522080c010c1703270604051e0c13020a1b0809100203071506140d080a030525031a12070b030a0908030f0403080f040b0c07081207 63
    0x2008504201407520108880710b00600140f0000641c21741a94001d081c0f200105210340381c8071003441e000100150400c1d40c0130080c000d8890005c0d18102c1110300b010b000d01039140341042c48035901c0340215800b4007a6030000000200c43e1400c001e50303014000d0103909640c01951000c02082041d810060340c2541660b0009c0c01c0480c0035070007804084010860394140c40c16507421748840b030301405044155071149001d20900928207008004441c4074903071015150a20100d4003602600511991003040c403003150142d20100070b860810b0600f170059034008441c6d030078000c606408038020807004007040c9280b001074640081d400a0010407603803103491582c0104140440c0441100e8030240d041d503441c043d007801c9100f40d6480354080b50300415601d42062840d100d60b01c000075000039003020400640030302c00010900400d001d01d80c013214425400790f1241046902ca0440c00c00c0218011a80501a016410041402c4511040050013103070300a1001e1424190340c41604c1c420700c40c1c140da1090104400d00b1020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 747233552 1250 747232302 747232327
    0x150a030f0314040e0a020d021c0504020a060e1513081504050d0503160e010207170106050913050d0e03150703020d0e0c031b0d06060b0703030b06130b0705011b05 71
    0x30790701900141000c1d41407a01d0200010110706014120b00700700c0f0303004241d10030100355942c1502c0f1000748004000c10403c9c10004000d0042005584c1607001d101c90a6001c19101d001e40ca105035420400f4150541c0d44451100840d82908200c0400900540700c900000c0c51040070012401d04103999896040035080524110f03140401092000301400014010031040c2450341d068028020080d00b04411221a0000102c0c18040c16810400b021801d0b01e01170580c1000550118042c0c81064400c000152214044440348841c410030041041d84080000e1003028421070115160020203000c40d4818a040d08400c50715141c200c8940c80040d501003450b07031007408203000f000c10703459143c2c3c0940780d960b45800101c5e4482c5503e000703203040f0380b80030f002c500c0c6a1344a04402000654000078100a400d4860780742c20034950100000f900000d0804c0c0c00c00d2541e203080000c40e001080c3d04042010441d18006607507843d50044a410b641d1950380358601d03804010301d1219540d0340d4400f56112503131020b004010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 747234802 1250 747233552 747233567
    0x30f070906030b09060105070303150b0418060308041e080a14011404051b1201061712030621190c08070803040e060d0519060603060e06040b04020405150a030f03 71
    0x2c243c2030400b00e044a40320460f2007500f10000f0b203003465413000c4e10b01301a4049e006049940d01d9021811000060080b24040070304142c03442515030082c2d080c40c100041d4192402c0307000180010108000400084c2c0708000300480c1c00003448007100e0096a074031011400c1c44003250042c2e4951003403046912526100f0f10074013500810458490900d4101901c1da40d940c0c01942c0d01103640140072010456055440200c1004840c801c000240324040d101c8200802c617044518038100d4510507250b201d980380300c000381924032039040a00302202040d0f000f039021540d0780c0000d4811483d0301502c3c120700303801d01c030001a0101d0b45000d01c510040481c640081585000295880000070341c000740000e202035040341c007900c0d0300f21100300d80542c0c0c1c0c0c03495400c11307604020304002001a109100821241000000e8001da41120b0280808110104c103003c10507031104421207006100c600c100d00040d00501d016440f0704e41002d400071225603064010400b0410f1034045400558480300032207802420107a00422 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 747236052 1250 747234802 747234809
    0x305100524031024020c060a14040807060912080f181e120d020a02040b0a0b1c050c180d06020c01020d0501080105071b0f081c020702030106090b0109060503130503030f0709 76
    0x1c00041300d000241c1d0007500d845008032418824007000400d918001e1151700b02d042030801c28508595039a03a14411503682d02e0030741c4642c0001c2030120200080c0180038041c0300c0c1d102034004109501d04510203016107a6a0300c100142c40304500341d0750030003425844030b8030701a04e076104200c96500f091421404020f03006880c405001d00e50740c8092100150140d0211700139200c05c2d8140d9003c103a1058550000b003809005c0d03002030190440201d80000c500c00e11455a040c200701407001004691a402c00401280c4640c000e10000d0000c4030b584503204d41007600743c542245005004c01030805001010041c266406500d21010301a154001440484000e00c51550071890034104800072502c2c0d02c050303a0707542001030030140070030254000f8a030501140d4021660b04042040d0000303000401c0d070022400a40041e482a4065844c200c0c0202e818095072107a04041c5070141c4850146900c2c145003200d640d400100890890407048903d01d000071000c00c06540a04810103c510076450180c0c4000d002000c180d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 747237302 1250 747236052 747236099
    0xf120c0a0809032d07061b1b17090d060e0a0506060414070c1a2e03111c061b080a061a0c0f0a14010c03051005240310 52
    0x11005041d81d00c030010303a4402454661380c800d01c0e14200305011009010740000074000358140a0441001001c00068403400c0ca901e442d6100c4614003511403102144554100509001c220020032820113420b03005070000c010300410030402180e25030303039003c01d41d504462800000d9201c804000304111050104580c00072094504010707403204c0c444c0301e0b05000405001c40f000d204103544540107002038454080104054032021081a040101180c024a03503c1000c244401d500f10100b041020940040c03078003120f4010006400300e80e1514104994009003103a002d0042e5990480440000d00c540140004084001c00110100c07074107100c00380140f00000c2a08810610702402400984111889500c01e4114981800e4580015640c260b10300b80308024001c60601c11029101c0800901c035280c036400d00010030091184440b035141c1641940c00c1a910800c1c040c10024081c0810f05210b441e420001c00400c40e2440709a01d40c0904c0c60320ba6000fa0b481c00c4841003191410302019040d8135540000d9854607 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 747238552 1250 747237302 747237307
    0x61225060921060c09031a1b03060306010510051e03070e1c0b07090b07140c0a060912081c0204091803050307081810050604060f0e0c0f120c0a080903 66
    0x381900142d507514200e0003814599036040c1503d0f040e00c074407403407005154030045100040362600e03040c656810084818040f51110014242c0c201d03050350040e01d01414005d0000d065507424103003000000790f600c00b81c08081140c144031000000391002d00311552200c012110568078203003100c2c003d11020b01c00305104e01410440006d41000301900341c0305200c607500094214195198640107c1d2945181d500651440030045401024003094a0300b01c40c1c03820003c0708413234204401c0c1061146841280c8500b8010400509003007020510030085411054468103170340b07103448a610300400b00e03602c1141c0c040d10082e42c049070620000d840f5100b00000c0700395080a500c0c490004da0350081c018403004ac0740608000d02c200124900c8520741e40045503c4100d00705440c480b40d05100464000d003801c41d2440e00ca1400d018000a01c140c1c4a070141059503600403914400b6a248054640d49070710480307140c840700b0030400c01042c48400c00313004103006071117020701c0703541d9054600ea0080c45028040d0090700340b60002c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 747239802 1250 747238552 747238589
    0x130b0a0e0705120a020409020c0c030c0a0506250501020a0c050f060103110d14010e03070c0e06031e0a0534060801060309020d06020a11070f08060612250609 69
    0xb11041d62000b0030500e0a00c2442d0343e0b90120140a40203075406041000d001154040040320301044000c4020ba0503402c455082d01c044041202c007810710b209140d001101002400b80d0300c400321190501c4a18582440d8200130f80b131f81d0341d05089901c0f0384004000070b0340201004c002c000e414050b540c04103858000600c001c1d41552220b01400c468154190b2003840303900c101804202408442c100340550303201c002c0002c014000320040d202d41c400c080c129086d01070600b000c5000f0201c6282030740540707409001000e2500c2003030840c24800320200e0b15100c240c440c03405804000b50080051100d0312105001080015840798581803491494007440c1e010004860001d100d22588200500e0440d05140340c003050b992686e00209501e0000b2039800b41a450000450032401a085054034a442400d5011a418a9901c2144001d00d9840b40115071640d000200032a51074981016616400c070b060300140c0d503958140e85050060f034204070001c10850020f20b136003005096000385000c001401c2584400c01110007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 747241052 1250 747239802 747239807
    0x20a0311120a110f030f0604030f020d050408121615020409180b06090c0d1b0f090303020c0915100201240308070b07170702010e10090b060d11130b0a0e07 68
    0x65400c4107038040c242d50202c0511175034041025244601c1c0b1802a1000e42c105410700070300c440740c0740b200d41c0094820f00d2621403049214000726422108200c020341500d02c002c015001c8640e101a183c0011400c40c100c624003c1010300b0701e1404041001c440040c1d4441c507092002d000d40304081c0021886044a20a00010901401c00d9950107007045a403042c0617500d41d500b50506014901c00c040b6010325104248203040e034101240714031620543c4900724405040001115115614000140140c001d42c0c07009449003020118107420078802003850ac49103980f0400703c1c2c07400701c172014408010f030344406420990a000c0e0441003880302100c1030070600c0702d0568032640b51a00c200c80b4010b0850000303d0020b0300184c8649400400c2400340100c402080c2042e8200074042c0000c800a1900f5001d184528018055103100b0300c40c490b9030040c070310005d0387e8a0310704010801d03016074406e440f40501f2450f65400d994034007038407030a0583c943d00c4c00122a401c19041c00720f200e4040d040b642c0c0c000b0022040c8466280c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 747242302 1250 747241052 747241073
    0x905060d0209091f091b08030a0e0102120a0e010e0f0a050d0206040806010b0a11010b01121a0a290304110d060905070b0315030109020a060f0309020a0311120a 70
    0x1901a5180005911000343c1207107031600704d1031181424050300d80ca28065548541200410500586402000b48817001079a09140d42c1442540c0302c650003081800140d07030190300f0381c000034a01401500d038004124661110b03a5070040e1003400000d947e200c3d09001c0341d0b030442011a0f10384410340700c4142c05888940426910f0816000e89840b9400d030010300403c550303a4004841c09041803400b43d0340f1a580d580090323006500f00c011103201040d405180820ba110052245920741c03081651020550401d482c0c1d410010310014204103450361542600303882c180c6504020070002c012640c10030700a04111210f600389811542c40d055404c0c2c004100303000126020a03006500044103c880041c0c4000e18607000c0c0081045003c01402800b0320b200c009101485c41c0c0182d480740030039014080c01ca1400004140c204c80148500a6024092450900441e88222544443c804c036500340080e08107a0394000a5024000c0c0d0f00417a4000c2aa44264040d0304000c100304c0081c1e02c05200070505c000113a6240301254 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 747243552 1250 747242302 747242329
    0x9111c030e0f1504120b07050309070e0403180b0417060402090105121603030503040311190303050a0b060f092b02220203070c03080106050a0c120c080f040609090506 73
    0x208101c00c05070903165580c40780c540346070041c0503500f50361380e6503403000c2d41945901c004182c840c40004070014101900440461344a001c070702c070203091403074201180c2c48990b00001e4004e404100921002e04c1c02c44200c051104047c01440002c1c9441d1071420801650b0700089140300030140c0c112805000068550929590540384112031501c68a26061002840c3c0498422405c0740124102b5000040c1504000258041d50096807403100313200c0c0d403a150039078402c40c4611001c4205030300e4020034042882a030241e6080400d4100c04607414507448006007c60f0814442165031100001c0d1034000e40c81e081400003c1c003080345416100591143c034404480960164010707016411103030b05040c0954625030302c80b03003000d13103807400315102c2c03c1c4580000c181d25400d080443c0804d803940000305800303000704182c1d91301440300e5482108484090ba0342240e85160003401c0700600c9a030b0303158800043c0240010300150030038415403545441c40e040b001010300c00070f5032204085602e050184004e5440e21500c03034420 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 747244802 1250 747243552 747243559
    0x100e2404020903030c0d0c03120207080307110c0a0303020312090f030406120204030f030c0c090b15130e0106020f0c040b0114070201020a02131a09100302150702030109111c030e 78
    0x11107000d040403031304501c01c811903403400b806801c00034100705420481d4107070854041e541d500c410088410030001248240e040240c10140180300103201a48988032000c0c00b6003000c0c0075280e5121b401400b1850903e400e81048025800114031081c1800d8500035030340d48408207100506d5026807030341119849100e00c0c062041040590f02021084184580496004591110045040160300d0400514030000c0303003030896425051007000148004035006050700080300400d80040190a401030b08ca0651000e07403031251803241c00c44000744078010441a0b5000344829005441120b41c50140f460620b40750881d818070852400d5120269079912100704500b40c1e200041181d036a882ca40010f0303143c0025418025403080c00f2140480c1d00356425004003074429a00b0b002c0c0051a90791908010700c8650440c4c0ca20417415014608001504e000340b101c2808503044c40c1c51034a024900e0f0082420754500100a845a000c2190111424241869407041440140760a0044000d0903600242010008441c2510 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 747246052 1250 747244802 747244807
    0x10031b030f0314070b0a0903120b03060109090203010f0903030213090c0c062a2c3109060209120f12030603010b0a14031204030f030c0317100e240402 66
    0x1180a40c1d201210318107a040203048056240246d0b0b0074000e081000780c12800141400f41c01d050421031805481230000300240a0032341a0309003451a801003400c0c0e80207136410340d00e580d4081802042c0c1e00c0740d13149007030183d5000744e83c805160444024411603136000e1100240b030a0b5480e00a603500c20004644c042d4080400f040c200d04800407200c01c40e0411803000b840c2046d14007202d076031940200800241b0400c050503000b000e680351030324a0350607003c40e42c03194000c015480348494031601039070307000c0394200180a1100c6c1b0681010a200031a886454202d82e050b600207602c001c0b914000d0b00101308400d1400083c041490000303a03170740e11010034081c203000e800c03c04804909166801e400c0504008009080103030403d5581810f200303551196104c190003400b404000040c4a400c620403101a40d802c1002d0310382d41c40c4241d90444661040d00c800350304001d0044801c41c1100500b00c019809900100010104141406220940100068007116206411640c0e0040c80c9804880b2003402e56003c580058 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 747247302 1250 747246052 747246077
    0x10e180606061803060708010614040e010506071406040305030411120c04090c120605011d07050a080c0f031e010801020a0c060518011e06090209010c060b0406090510031b030f03 78
    0x40c2ea08203e114075501d4040d036070801c0691075101034a035040310030302d503101224945a0020411a8070503405413000c400940380c01803006082000081c02202d01c21956001c1c1c400110340014204070040c0c0c3d01f1000140d000080c0018050403071202d4001c00b8045030f0800d0492202d03886941e6502101350014040e0b6201c15800c8180003000300c18500400d89048001c2d090301003481e01000500090103000121840990700c4111400e412104c0d501c03d001c1038444a251084002050724000e50080c5000705400080114502560f4080701440c00340b83c0844142d002008100301c1c507601e0340f03416000003825030301c18000601d01b41d41c089041040d1607080140001d084c0c54a039203c0b028035072054013101440d03082c04810300c51100030018900d5055072002003040601e4480c04194141d20403900b84500182403410b1000100304240e00c9003618000c000d00c0000c0b030b982d46501240c2502d004403013503800009180320800c203120503007801c80c0800304503401c0641028190760b507859107150f181c4406030070084841d1802 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 747248552 1250 747247302 747247327
    0x2040504050f01020c01090204052a130f301104090c230315040201170a021e0d0c170423030c0c100f02070605030a0f0f05010e18060606 60
    0x2c0a00d100d1581c002d40d60b50b961043d04d50301800c203d0740105c3c0540e25220010b01c00d401e54546000390f808030b85a01685103c0480c080407810740104a030310201a54420002900c041c80c1342c0c150004141c001d580300400d18103030034200001c204802540030002c507800382c000c001400d2006101c404230360032100040c1e0b081443c104000f030403890346c0100c1380ca140d09030740c151441e802e03c07000f00300d541004508884006929220301c80c01c181c419036000b80460810908610b80b9107501b648a50321040640b4014101542e409003200341d10441c0c00c924050744400500d4511030701980c0910a8204000c0c10403100750140201540312280c40200042c00300211522070a80d8030b07220300e2413280c4d0304244808582d00d40f640c110f41c590300d50380c00c0e260081c4a9406008040042c50040c0000819442c894011f444100e00e04402501d047c3e10040c061071701595a004070100300030040c4074281d9040004c403c001525814242030040c903c8003c0c00300071499840e03600f03448403d080080e4040d403002050380ca0f59100d02030030558 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 747249802 1250 747248552 747248563
    0x31303051b010501180c050c0d39120219060905010209090910050a0b0102100c0509030d02150112080301030609030302090d03030c120e0703020d0212072d0f030204050405 75
    0x9601c81035080100020340d140b8148030b0f820404840020404c03214600d01007d46903441644046c480e1900074a2517401c0c0c40e070156103018800d603421412180202500300f82c2c41d4441480b61860009806603840130414444405d030341001d080d9490000308005034506094400302a40c60340010301c181e8460300c0c014200082134040c4e4000e00005000c4007541e041401c000d5480340d0060013070307000e20b62404000030000030050141810340881030300035040e01d159900300744018080c9140044180082000840038980f402c200e05010079480d6030180c0080c81c044001018140c4069100b00e001c99081a07007080859807440c120b0741100e911020014108486240c1503000c1d005171000c0c0c030b5015440039074417024035406800c280c10750380060390742c0c503a05000692000110758a000350a180c0e680038040a00041c14400c101010b4107000a2580680240106441e4a000c0c01600440140c800386d0072410008684034445a040c1003803a258107a0303141c100b00c030341c582045091001038441e9460300c1c081820b01400b0b03c01e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 747251052 1250 747249802 747249847
    0x306070c0f1a010f1a0a0c06020304051c12060e0105090c0c011803110105132001050702040207050c0a080a030f0f03090501060f0f08010203010302091b0c1f06090203130305 76
    0x203038001c02c1d60791040340601a000600c6000c031102d15044003070601052000485800f0040340d110740d61100f100d92910380007074000820803242e62140300360b050455a50500941c05042440e42c070442d802a94054000030740301198881820030000030018846903544004245c0d0104541001a807294130000f050790244c012009114602d4a00e038110405041c3d220740142c0d0b184014070001e200b9034662036514440700d0f00030341c030107420140e0903030300c429048020402500c4802014944141001c0050300041c0407070b80f080f03a08944a038800c1340049102c2c02c0c0512280018180100034180080080d10060301c000e0b0082c000b901004440341c0b1a540746800396114040c1c1c690000020440141c58000b20b0503018482c0c001d60a9441c0d8a040c0081d41c1101402181d0603203038054041c0d006034880c546d0780c1050f441d484861241c540401d2020341075451080181c0d07200c0781600f07251460042410070700d1004880d190740145070114010800c2004a03030308554402486541403501c0b80c1e4504685910002060f454007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 747252302 1250 747251052 747251093
    0x51e09070b030103061b02030910050a0203070b130203061e06190b0705011a0402181504030f0303060315051612060906060c0203010e0c0904032307050109110306070c0f 74
    0x2c00072091201c164000940301c112689092032000c0b042d0001d83c0c0c2c034060038050035444856400c030805200c1c49100600703080f18080c0100e0b403c20000c2d6a0300c94907402c0450303041c03002c448041540c1c015840e0801840e600401043c0e840350060b07150801d00ba02280b802070445000c1c00b406468010401d04403401000240a2010195128103682c9041e40c080c01c041210003c0d0803010310310032005890144221102c42d082407002105c0c0c000210b00340103103e801e0080301072080c00c00b0320000001c1400d1400a44007248241e50000c0d8150951401d808200243c5000748502407829041090302c02c143e007c0c140341c4080c1802e121a25050300342d01c0001810036501308034510741c14071a0028040340c1208920341d405100714024820094040140c03a5502c00c0c1e900c0190380444910081004a800303100d40d00b0054003c100c241d008803074049500f0407241e008140881d03642e136403040f04000348052070f8914880c0381012409000d09041807507001b0205d07000103002604200d06424039804000140680c0b044811000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 747253552 1250 747252302 747252307
    0x7120906020d0501080c060717041d0405010501063923070b1905030702070e10230102030d1a0306130c0b03070516020f15040513051e09070b 62
    0x103203000d8000c1d4000b0000a802141000c00101e030740c0201107200d8503240c401410742170804056445d80034100d04102401c0346241d00400010400074118480c010000c1450b982c0d030031041c2401d180180c00c50300c1c164000c40420101060000c07030111100344ca031010080e11450907800102c002805030031a00b103504020310040c80780300d8850348200c0302c1c201d900d902c00c1c441c015604502d5039400303a4640391141e0701103078040d003268444201103680140b001d940c0007081d81c0704850070141c49081d00003000c1c0c0184d40807031f075603e44446d04126801403502e21240f800f02052068402110b40700020390350303028081030403800302d403202c07400441d00c10001c40060101138003e041f0350140c10a2020152040c44c600000d480070240c081c80030134248424011a4000d81840c0d6a9500e003890030075180c1a0800da005040ba80304200c0c0d1a210101e41d125071480a015a018043d140e849140504100d031150031350111581c1a0f040004214489200419602060700024004240780e604c0040b181c0c184001c0e80c102e01d0221002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 747254802 1250 747253552 747253571
    0x200f0603062206060f030e0312040f06050103050c0a05010f02070b09010e060708040618030c060c02130c030e0d020109080f030c1b10060504090b06150c01091a010b071a0712 76
    0x3641c022004441c41600c07000c2c0a050489812000d0f01c10701f00c03007540c156100700043c030160ba540300c10740c603402800f0710550703100c95840f561058199002031b8020740d0f181d800350350b80c08494648071109000034036003420300c12500720100030702035100c521038400c16241c44008590907815034010003800b0540d4400070711055030b076a56440e00c065160071038000d020001e41c5403000f03000e1010201c01c2e1141a00d4000c684255468a0144219108038481c201260010480c0c0034860000d92131b8040c1301111062600d01141d001481e84c0210718000021140208584c180600240031a080b44212060110f0030080540d89503a0080c6403140c511500503070044d62002200c141c4680c88001c22404e000c6510742c0d4050040300c0e50780c0100820b85074214005841054600301246291514058803503041d600820650300340f4a042d403541d42107a444010503200d0f10000350242684c04d49201815000d0310145684900308916501d42150f03110881d42c0b001c0c02c0c4c60010007c1111640201d03203a24400342d61107024491981d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 747256052 1250 747254802 747254869
    0x6051003020327100906140403021c0f09051302070b070203030a06140a0e07090906060e130e060402100c0203010c1d0d05030307230a020307200f060306 67
    0x4102c5000c100a030701d81d1421142000e081e4a840f421140342c80051100580042a001c0200b400c10002c0310603030b035600e00c3c030101140b03842d203180d00c01e41c004c1e0068103481c8648412260b000882003074000400060300b200818041d005011041910340c140c0c1d4101c81d84201d1103481c0002d10901c0f10280160325400100001c0e00d5000004500c42c1000f65418071210b03540e0381d00600802c0160000c075601c00241071040c042ca0f0070307201c072940d030146c03c0345401d2018507500c07055a001c45890340c20840000700c0401a4046a040c110b0001b1801c40040004120007003490b50419280c10000d40020322400351280c9070f0707a04a12860042041940003402000480d5a4000240a643c8803982241c070480007284401c5091410248403c0c002d07800ca4003031403855646041c1124810044c40e81411484659000c10144501d0200a49240400c81c1c0065658440c40c2c104503444a00b030f903044120f9a002808640708075210310601c0c400d030b00d000f80e403d1030b01c81d290100050203020500c010f40c00c60100a1800300d0600c0d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 747257302 1250 747256052 747256057
    0x30f04050a0b040b03060603070c140d030b0901030b01030f02060c03041509080610060e240706051803040302041e050405010902120115180b030609060601030606051207030b01030605100302 83
    0xc0d0215200104180e035090700140502952243c0c1141c20010700000d82e0300d0030107000555000035140341c5010100c1c41592100411038010030218103913400010b010403119010700c105c2007000d200b1500416158510354801422940c140802040030303045030103410454031004140c849500741c59065a8a5503141e2482403038480a550000c40020911a0b0010745a8070104015014221a0141d02086811b224050395030089880c1c00715005200c91451010145540e0480f4491410501c4c00ca03036140348900749003054560151601107138801803401000452400030403507044907411743c0d01099510940c03000c042940d0f5400038003015581440e04100c00c006040d40701c860340501c00c54600d607440c81120364071400c0b00c9440c0754500301d0075610070007071140411402d6404041c030719a42001c114030f0740080100781084000e881e003510b150b100c0801e01c4103968042c0507290250141c0e10b00305040c8503500454841c03903940a84050249030365400050040d92094200c00050712000d02038038106580701400400a6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 747258552 1250 747257302 747257309
    0xd0914120102270f0406080c040b0a0b0a092c0103140a0b1509010e01080a06021b01090803012c040318053c180a0f0504080d200a0c08040503030f04 65
    0x10b000704441c4c01c0315854648104000c1c3c0300f00b5002407054120803c18800144000d03036220b60f105190000000707241c2031501c01080c803140c26a40c0d11540f180b03841080d10302c40c5102e03140d00ea0341c2c52020b0171000070808812402e60440b0707040051345841303074481c2001300e040844920f809071100c0100c0d420069115407182003440c035482c0948800e0501d81e80c4005154810030300307008090300b5030450704920010a8298020b0850102c10301a22848040040d01d5182141c0402c00c003110030941c01300040003080d1100246260030081d10001d00341040120f00d0481d0054401040101406450b444c80c4407881388041c1c04101138040074014219070526050301101c0b82e2400494401d0900c1000d001c4c5103904000c0c29115041d040140039a804063b14035070a06802100410b0040d04c140c0c1d4580c0c4080440c0f5a004084c044d0b4080c2120517a5841214110000e855501415002d0301e00d1381028a02c14560040032110150450300d44000401224075150340140304e83e50110354988004107200c0070050940b4002c00c00c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 747259802 1250 747258552 747258559
    0xf06370605031c0806100203040801050126010905030406050c030c10050a1a090c210c0a0e100905040b060903030d0f060e01060c03031a100906020d091412010227 71
    0xf032090031a800c08a030162181c0001640742000c11290300304011381250307400e4180107407800c1c03984400d403441c03c4070030036406200360624003a00450b0700c10302d18022040c1c11081d01e0080c855074816031151075680c403132449040300b085400580422002c20500a4505030b03104107044d1040d0540d0080071402400c1c060b00c80342daa103854004110141450424031801030000a0180d41c841c0d940c038001c0e0074090308109845e2200584007034201040104c030f0400780c0d1080761034194160300d90704c415000030103034040b2111b424012100851810503840d041801c00045035802c0310701041e80b040c0340307020502c50300a4500c41c0e50148070105803a42c80400701d400c02d200344e2180d0001042903d80d9200c03510b40c1c40400b0b100e1840810891480040030038480e41040c460384c00b0100d01c4420602c1201c000c241c03482c100b600c14000241c5148000d10041d98144411780c0b1080f1103150104015040030b0b02c0000485900d40d96600c00d84490849200301c180a4054174080881d544007140c0302d12140f02445030b56100d00500c20722 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 747261052 1250 747259802 747259813
    0xb060d230a0c0f03030e1c0c030308010303080c040501081308220e071b1401150603020d0c020c010509091e0405030408010c031b030b030c0a1d01080f0637060503 71
    0x340a0f400040e180e003141c0d0942d07140d0145070408000d0001d034204006118060f44041250700300071903848200d4900842c4240d40d02041580f544c10020880b01026040c1d03c00e00804000820150b0781c4000740726000080090028600c040c0b6160001035446000c2070f140072150300c60007505000a4104c81d9108640d403122120200703a0b02c40780c04a60110700500c445034544220324074000860229000030015017096000011055842640b40340030011917800900025000141c0864000f500e0054500724480c1d1b000400c0c810720103000181180c064a081d0b18001c1c40440001490ad0321980c90f0030312011140000d000705030401d420125100c2c0c0c0207001c3e4000d1503090030321014102d0722a00c6800f10200194402174107a00300800120040d203043c1040319410312500c00d03c44099911445090b0003000e2510040c01c0314041c0c1500d41500d0302059111403030a0300702c801403a41c0300001080e0554000c100c0100755524044020700d09200300d42518503201446015008415503c1955000500741d443c12000c580c07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 747262302 1250 747261052 747261059
    0xe062202090f0a0312230d050402030f070b0417030d0221010e0708040f030e04050f060a060e09010605130902120f0f090c130e03030906060f030a0b060d230a0c 70
    0x510144501c00100420a1342804100081c8511130546d49070802c003042d04c0d100031140c0e030080c1e0590001821150980d54507824003045240070410f03125000c10017809052a1807500c1003180090095100364009405121200040e880082c8115000355141c80e0086442c3c00003410047c09500c0311782505d0342c80d505950000706a0315a2142091700c0350301d283d6201082540e459490a48540804200300e0a002159042040c039960301d020311482600401941c011510b008000c0082990380f0b40d04c0482440005d0f5080d10450701c4100500f815101c0070b050581c0d4502d01c03002e444c407600c0e00c070f44e00c47c20065201041d869171140326000110702503000941c1c0b0b42500c0e00c500900001c4210141c034900b0b0158421110a602407c0100080c4804400c4c00340014150210208090450740202c804101c0380d0402001c0005900e010210a41c03003820540081c024002d255581078030260019100714414401202c1e017104100700d007a40300f41c21741c8a407601d1403852040f991f0303110b684407007411040b24045420f03040030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 747263552 1250 747262302 747262309
    0x903010e0f1b060c030715051b070206070201020f030406030203160906050d27210203090d110f04110a09090c0c02010e1f11160f0e062202090f 63
    0x2649a41415805005600382400104502c8000140840e42081081c465400c0303c0c80309001a012240c007900d10122150140d01c00d6074102c0ea401010a001404040d1004048182d003a0580d035031140d041e20030380d81c2c0d020140010307031415140c000175402d144000600030032842e03403540245000b440320b50700c80c0310003000050b016117105009008132130001da0b00740100c0104424a030007045515140c0000c00442401c00c1c02040e102121a64040c2c520090804643c006255540e0030b5140b0028184081c50800f0784240c0040d00c8203840300f00203003038040f6100a03410310b55941e807040d803020000108108455501c560300700410307400032800c3d00041148614005480315040c0103800403106036039298503000d03c4130b50041d00c1c521000140c013500a09002c4040b403c00d84640704880d0042c00c2070f1121321004a080259915100c00000802508680444108407240740e100ca0b10058034041f25465100d542e80401252209400c4480004051a4444141e110742e001e50300816010310180da40303615000e040c1061 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 747264802 1250 747263552 747263563
    0x60f080a0908070b0a110d06030c050a060516030e03150412020a030f03020d0e0f0606100504050303040b07060f14070906020604080306010e0607140706080a180b0702150c0903010e 79
    0x9049603008020502c0055000d80b444c0790f00c58210f16000a00b2200103070410711a030828209210780941d1280213000b40305804680704000c2c50304480d809062420300304020325070f0140525035201d204142034a241018054800c4090040018040350460669480e403501140c0040e241a20381d101003801500741240b020403440b1000b074041d20360741110070120008600a601113441c014002d50764611041901c28140000003200300e06c82c00805070741c10b0039030801ca00700204420701018410200000c01803601e011007594201e51100c64100d8407803441e8140b00001d40f05450218505920b04001103040c0b000c004410340c05545a669000740300707a00d0b1030060b40d0703170f08060b100500400f20500005001d03605c64800351285a1003e0031641c200105035880708100110300e480c2d0b08060300001c8090240540c0440450340c042c41074801406066403002d07d4114990103100f02405490b42240010300c4240208022140200701000f18031041c9040f41408940390403032083c2600c25400c020300e4502071440060b2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 747266052 1250 747264802 747264821
    0x50304080a03080f0f1b032e0306050906010326040b16050606011815111002030f0717070c1115180402040602060c03130b010603200a0c02091003060204060f080a 71
    0x5444004d086c03120fa100e040d038100a1160608040180c041c901d10b142d500c100202d2201003020f140261829850440e0903a48000d040081d41c0d40304070b0040010800490305c0c2406e880380e20b10360354465504980d10b10490f00c41d603048800c40075000141100c5a8000c0c4800301082406001135524039118080110b503940308840503414440343c1c1c00300034484030700c0216140150448130704001030717640d03100070804e82000407451a540a2941c040100000f0809a001c1c4030361104191500c00384000c040c1041030741d182806000b080401c80b40c40c1c528400c0181e5030084e80002c2c54018808515101503034845103c1d68446240c4094005d411036441d42c03541814002d039025500642c01805042ea41c5410120b25a080200b950503c0d0b07a03d4100440482c0c452107269020b4a10786c3d4001c00c2c4a08418145603000300107007a20f000d841810446030078a03d5000b030340c448000394111220002034403043c0810744603e40d9a080038007214070020300002c1c00358021010b4503007541c461b1280c2c2c070f450350361008031700449440300b8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 747267302 1250 747266052 747266071
    0x3131506050f1504030501051e07140a03050702161e1703091c0b0f090c0a0f060302070512031003140c0307090203093d05061507050304080a03080f0f 66
    0x2c001400b42c9000c421900c0d80920311840203080c5503883d1641402e660049d0ba56980c070b403405200d80c507070b0318145181950b0300c4030960a0401c0124081c2c00864081d10030400700350201a520b401189000f4424851505102e94214624040540f600c00c1c0070071540e510a490800040c80310700000d40755004801c6200107085450141d800e001d110001d01c000c0e40e0401552001c84d1010704000000603400015941c02100b000c0c43c100b10900e041d03001382e481d080d680d0703401d43d10500300c0c000200001800005208284e840d10300e00540c0303410580c5006440d10440800c480c20800c000f20400045040804590003104d010328500305e00581d0981c0b10b10b0303c54500d10007842d0150400e442c113001ca03190f9030b0000c5070000e4500c070440f40c40c04499011014410000c4666980e64101902c0c000b48012500c0e41100c0040ca45010801850a20f070001a00c80d5078018003030402c1080218030003090040500c1501c1c010600407094600700d40c518640107050583c01c4554003803042c058404550048e0358951002d1040c06c030003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 747268552 1250 747267302 747267319
    0x240d0e0111120402010c0606090b09130f060c111e071d0609070c080a090311031902090c040f0801050115090e040201110102040503190b06040b011e02120313150605 72
    0x1161680b4000e00107000380d051103210440000021070f02d1144034002c00c501d000c0058661188800c124902c400903041c07041800c50b410581c17010032006105030000e036030301190020f0302136401e03401690032031079989020704107016a800d0303001501540c0e00c41482c0b596189080d1400d280d02d0b41071820945070759001d50024540910001641c0b810140e040d207800c1002070500c40710b5084e4a6072044502c8c0c4c0300b0f20f4000000f0344071000c01c10803c10240c00100d0142c0046001d0000314010031100b50240d420500081d1003a602207021400c40204041101c002e41a06460401d40c1d03902c03102c1d034030302a0100384a1940805950541140300500c11007074802514102c94a0800e141c9482d001140c1009260800102c555820440010307141d0302004459080e0903a900311021900c16420401038260000341610700071418030803020026a44a12084c45d000503181ca4410040c2e1450002c900d48103007a40807a9071080c2c0001030180c41c0c1d800b00d4000310b07418852074105848140d00050001070701d007144200762300705404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 747269802 1250 747268552 747268567
    0xf0f07030c02010b0406080d08070503090c010507021c051509011b0e150c0a02040e01090b01150c1205070b1506090402090d05011103041b0b030601030b240d0e0111 72
    0x260000c41d0344612510001c079101c500d4000203011142d00f07038450291130b03110051f203001168106801c00d81c04819403c00d9801e6281020b6000e45555240c0c00c40c1c0d0401c00c001a0308400c56669003118003e184240c82d0034428442c80d8600242d9942a02c124070240c0004000001c2d001ea505019683c1080700c0c01051420071284110706a4001a80524541d48030000d410041e83ca4014103001d07040b0342e841c5000400301c0d1070b09801804110380700c0451510407a41401035203400304609920040c1110404030b4200d03641100c0d15401c640c0004003250040c0410b0501c00d10201c065404005071510f540603000785140d07501c1d800f80d10041c0360903e0440e0358100340144401086441c107680070380380707000018110142e0301034541e5441d400c40d1356000080b08070a802005010501c040d54042c0c60360140c4000c806600c41c1c0c02e200c88080140002003101c0d041584035a10b02c40341d602e0340e4585600c0c032090b5501c1000c410520520220054000c006d031101ca003440c010803030752801e01c1405841c40c4d00e685030a189261164 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 747271052 1250 747269802 747269807
    0x901090e1305061005013c0c08030a0906050a020a020607110f0610080c03060c04050603520917030405030a0807020307050f090a3b060f0f07 62
    0x20000c0c580800c1051600e0000c1c0822002c0c41000c0c8205483c00310710000c039040c9000944901c400084007844020500fa18070b400a200c601d054000c480030005003601c01c0c2c41e0281c101c592500302c0c00004c150030008024811400c4a942201140500c030b0300007809103a6502194804034029030b04100c0069000c82d0116000360300861100702680e00300001c0c0c400c6d11a10415007803074010b0039101d5242d640813131760042104c113109201c0b41d03045907000c40c0903060600f4210000c28041c000c1f4000c0c01d1040c90000085000200c5030741c22440c60180c02c040405000c03042524110007135010032030700c4141c452400700703602c0c40404d6a04100d84d450020386031500c0300c034180070b030300300c0c10103040b03000f0b11000e200c10003001c03071980d030104007215046100c2e90515945620034814141440c840d44d1045000740c0c00104688180d5803901c0b4030a078000d101020016003075488081e02c5d0b0240032500b034130003801411451515520004a580200c4100c401c0c0c2c108d59050b220b0030035100d00d00d5800c403004136001c000c01d0081641980b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 747272302 1250 747271052 747271079
    0x50c0f210f0405210918011805040803241f17010803120604020d0608160b030c030c0d06030b01140a05090702120a1103270904080d0b0103060f080102030103050f03090109 75
    0x2c9004041342c0c20700c1040400304642c1150720424008407131819004009400d0b031289402071074035681d17400b8055400d1594400480d80005080d22101003940031440c14601000001441c03c04402007076241401d0758500546030044204101c103002400c5c440000050401a2801e01d04a4075400d00a616002c440161003e002c580541940c0d030282c0c08002c5801b80342d844d40031b00406440d501d001b070580c048a644030040b40710b50760b0b400b14040305418010000c10240440c152503021a0007001c03560b4640c1450009001458540c00040844068400215402c12071a000301d080d40c0041c1c848071907003a00d070020040102011250280140d001682a8100184500c06060140d040d03040020a46c0083d858150564102c02041060f4901d0311180d079000d1300c0c0c400800c00140070261140b50450070300da15004060320030b450b1040300070390300c070784042945902c60b80c0130400034110554402802600c0d140024080d62003031000341e07060b00c6070109601e0742c206e000c0122540044161900b102d0f00e032a0901074040751 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 747273552 1250 747272302 747272353
    0x7030b0d0204020c010b0102240708070c0c0e09010605121902180a0203161728090c0303020d301d01090201020d020d090306050c0f210f0405 62
    0x10301a091240300584990000d0071000b5a0007001113440300240d400245442d68000c496410ba0300c1c401d8214441000d50301c1d030310360441814a0883c0c0d0700d03545c0d80c1d000d442c80100d0a00040210301c1040c1e000031101d61a189481c003031031020000340002a6203a040040091450304c40c40140d07001012502c481a1114031484880381c40036008603141c007031000040d03421a1044030804940c0342c002041210740c019100c420040c0210a00b004900c0301a0750304c0c1480c9108000301884102058802a080c0115841c1e404001e44459407000b4003460500c0c2c41e0410304c1e0a4180705c124098400c0d03588103000c050240194034401c40124035041480c0240602800003c5054a0b4000301d1580c4d8140c0f038508501000c482c80c1d0078102c84000450401c00d140300091031b21101c1e003003c0c2c08640018071241c00041c0d116078007000f00d94200502051640b80d1805400322480741510801c0f90602c00641d499002000f0205a24118005c0281d00d007255100c0803c1c080315101254010800d4000312045414a500d0840c0400c60 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 747274802 1250 747273552 747273559
    0x6021009030e0909070906050402070f0308091e0c030f0f030304080d060b1b0c0103022a0f15070905010804030530010b0417160302010c03110607030b040c020d020607030b 75
    0x1c1400140428a40f40781524107400c5900903030018081840c0c540101c0c001003006803011441c0c694982c9455400f5005004002c0030041480041030000404001c0030041d20000201c0c90f1028080c0310f000b91341c0c2c0c1c8962100c240a8068208100c040c080003045460003180310354007940ca990b881e5554181d155006108070740c01031b580c40ea80494400380040181504000c0700501c0d0a03400c603a07286040c508046905490704041c0104070030122600034685241d801b00384020002c1c21041c0c052801400e10460000700001c903c5400044a903065041003d01d0054040761681c82e001926880119080c10040341d003e40801e002700280c0444441c0e02002410a604181405c59804e11164260030443d2007a07000002410000c20140100d411407070f03409100000d05070003031845030064240302e200050380c1e2001030f0500910f1215071061500420161756407401003c25140107192041c0b0140050446002003400740d890140109031322400040e840c02c403000503030000d00c19a9582401240a00380c1e0100c035682 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 747276052 1250 747274802 747274817
    0x60f0103110d08070501060909210525080307052d040303082205100605040203010f140d05030a03060303030c0203120f090c04060f03170304080f0313020d0b1504060602100903 77
    0x4580b003031040d80090002010003003450007040c107000d036041c1c0351020000221100e0300355001c0e0ac5600441103450300c01080650113803000c000103480d62440303a16000038003000320020400c000980d11000030040e00f251144800c840c0034a075044002456200d4036003504003601000709001190143d9941940002d540020420000700365250030b00c032104042046805d80e10081d0b0103540064140602c0d800b41c44151800c500f10b61402d03071803540700f24080c800c107203004010040c0c0c07042c541c803000d405044036904041181d50791044164010020903691000303800292418451840e200d10110072241511000140c81010380c81b69510424000006095160544120810304d66652220b0152000030700c5840009040c840c03841c148901d00c1301c00300c185800b007091308200300000118503034140d840f20304840c0c05090301e9036a01d000c0408081d0141c0c001075805400305502c20308012030020114890500728413010300c2202090103100c107980b2240039240140c3c03c00550010740c0001a480008031601a15242c078 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 747277302 1250 747276052 747276067
    0x1080f04080d1a0409050604030801080c01140a0302120c070b0610080a0e01061a0c190c03170409110a120b01090302270c0a09060507030909051f0801020c060f0103110d08 75
    0x84c12181400c20851301c980280c010001450341200d40780d401825140068002031070540c0000304000a201c10340f044900d4046030020724184070b0341c1998641f410221810304c0d07500f4151070360300d4140c0141d002281c1c5800400000344840c10314058030300d4009005d0f02c4140b260f440714004000034140b0403881400c0d941d6900700004c0d030155000d4880f0906c1502010190760340c0560114a420030301d2103000380d607000e00420307402d5002401245240048a030403000c030089240070100302d92070a00c6194400358a19041425048202c0b941070010300c0500c4d040d8848041c07051002d1186000da458034220b00c1c1c08252061400c1000d428080402c880190000c021034003003001c00c5805504990054400d1500140041803080d44d035600300c0040c030090075043c185142050490341c0c000b8042c904074003515145c00e07207030000300311044c100a404d443d96407d0000500c0c0300f59100d021a070700070740055803260018805c441c0810944904040b1050680c0d4104900c0d0f205416200180000c07071804007801c840d00c5900300b0101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 747278552 1250 747277302 747277309
    0x18020f0f0d0611070b0a09031b030504080709321311060a080609010b09030318030c0a080c1509060d0c05160303050106091e06030b0a050603010b030601080f04080d1a 73
    0x14220302c80e083d4501da242e2007541003250b8195030041c040c81446d0700d4410640c0100b41c104819202c20f146501d04c9051250940c40d003207909004a60284e083d52040c10300202c0c01d500c960f000039112203048040103a0710045522090498000301e003074040c10005440c0820950501c100040c0c2c00e503030046009503081c80c034050106445d6030242030800c0000b4071010601a030fa10300814981c0c01803d05003c058145101c0c0000242c90380300e42c41d051108100b003a2140901510f0611084070100030040c940305200d031f651070303041d601c80e5282184c3ca4490203400c203c5103801c1020b8030503a0304452015103502d00b810700390141d010040134614012001d000c01848034840d44500c50003c0c201c030502c00e03940800c40307500d00359001e45000d007641c20698070303003603240b2482101c8210071074000200c0b92145004203008a44a01048410350030f0742015401c40000400440d03035920b80ba00a601440007a6207540c0c1d02e640c4c0c420248050b04003545e00811250003003005000c0e407402c2d03130810594491200d01041d071141141000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 747279802 1250 747278552 747278561
    0xc0f011215031a0709141003090503030403030e06010605130b030619090b0112020304021e150a1d0d0c03080d1401090519021e070f061107050118020f0f0d06 69
    0x1120604a040f03107040030082050200ca4101d0200d04202c801c40d414910b110011001c180042c90260002c0b40184071540d2080c0c11184c140c64100040d01d584c0d04181c00c000700603004d0a034114103584540d500000d482d500c14011500c488189030a0584104e0400c0400501030f40043d08182c0e000c1482d58180042821403070314203000b0b100284000604016480000d0044851401c103210803501c14001c110141e250f0b0a41100b803144800c03600b214120149001a130000d10b140d5010714581808101d40c0c00042c0c001c0141c20103000d000f45012006180344003044241d524459004218403200c8400300002101a03001e000d0450308002c002c510b42040f8226000e480009038002c845054407801400703030314820b08072504503c031165001503150040034403101c06010806030040c6d010400008010040c000c82403580700702c26a021000b4000002192400f14843d04181c4056529510300150109801c0040c0031724492544c0c060103141e011704340c2c8401c020001101038030450308401288496400960700d80704 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 747281052 1250 747279802 747279809
    0xf090a060c050105060901060516021210231003170c1002120a1505131e06170f0624031f0b030106030b04020603060d060c02060105120c0f011215 64
    0x4441d00e4500a900740386080d14070161900c2d002c0c450242c010310445920100f00d516840c00364114010f190020b1002c07a0206c0c4221074040c009000d80316404180c010700d40c0190701e00d6248945005507000311030780e040c0660402942c0d040031a20a100d4200000f490304c00c4484003c1601d42c0c0c089080c0082042c0150600e03401c1e0107550300301d80e4000303540c5003110038000f09560070109466040000a51a25807520001c41e540103e500c80e9541000e40c4130149281d402c2006004000b160050300c800d00c002180000d00b04900070040d9003030342208170b251f00080000396202d40d0700030300004051a45420002d0303c02020340c00b0420354407120b002c1c0101010b89041000c03001c07400c5210103024a082300d0031011001c590b01501d4451007a41029000c1011681969100d900507404440840e5652036440015404880615004010307500f02001c00c410b0030340101d0414103d500c2652b0840c42c030300084040c3c507103c0e82c10382c41e0705034082d000761807842d0554030964803280c4448907507400141841c0c054140d02201e841650 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 747282302 1250 747281052 747281057
    0x1c09151a451602030c10240f0906050105190e130c020601081b060306130209090405010f0c082e23130204050102070b0d1401080f010e1c03020f090a06 66
    0x2050002d0210b01a40c076868049503840907600303040c4500d82d8181c485403441569401c8580314021404400308802200c1d07001032a9903800d039161aa40c45105c00c0b019400e04c6a005150f01d00302c0700142c69400b94045440d001042004041800480c200595007519078241d880d420801c04441e83c84200401e1181e0514006030f82c004003400c0d0300d000c2d2114130b041200c0c0480480a4480000050151144010749801c0b0a084231a42c860fa034180030303208001d001d9103021a902200d07043c01c0c030060001c103501c22848006052000c2c4580c0102100039a0103c009480d028088200328038080d0003d66400c84030031082800440341030a00355181c1e05d0320a0f0302d0707a43d4403220460071a0003050009140a04918219141401c02507041c07914020020f174840c80c41e441030324100b000008407402d400344194850300c2941d41010322032080356140d001ea181c4d50000000b489800f90b182c90710719000b12000045100c000760b52262202e4400d81102d0080b4041d4100060400c00703000c082c048000c165179070710700200c083d041c85d6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 747283552 1250 747282302 747282439
    0x9050c030601050a0f0315090f0c080c150403080901020a0203060106021b0a030812091504152a110708010c08040201140f09061c09151a 60
    0x880405003810010303031103a807040903469810080e4040c1101e65004598101e803006064421140076503001c4d1006140040c48104644110010060410f4001c0c040d200c1d001d00701c898507003541d01031052000e1900d21006525506010070000601414000c203007580042c0b0584d002100c40c0c3d4080f0349042d6081c0c01c80d2015030449408424040060421030000741400c4458442c4240f0795100d1086074825404041caa0540400c00554291010007206d0381c0345501110150305490701e801d10040107402800101211801d100500000315090100e4108803070509410100d0031b400c0c0541a0340051600580c502c19000726100019036080c01c0c40b40804403502038a40408a207464800101400c0c002e408082c000b00e002c0c40182001c60040f0182c0e1120901628001d544036031450f046402c404050b600c2000407070800101c041000340441d10b484103c1a0b04101348090307094601c61500c00d000c0e220203a80c20011520700034080c5003110344801036400240d01e400080f05003050090002816111070010a40c010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 747284802 1250 747283552 747283573
    0x6130e060114090d030e0d0804060e0f0f0a060f1403090c01080609040b040b042d020f0d0206090607020a1505090307172e0c1e050307090b0c0705040905 67
    0x51070b04440070842d6070191a151044001816285500c5009020801d01d0541046641c44a12805001d07a070014140354a17190b41b50b50040c140c8103840381c0940241d2482c2c0e418010740c00c1c402c1406801c8a00109400303000b0f403c0c404100c6102020400c18020000d282740441c0f800d5600c6402140038010075005000c05540020003d01503510251400b4080c007100c42c2000003003102e010b08141c00036032140c400300e13064a542c103105800304041c41514265a401c02600c0c0c5d040d107102c809a00c82d00e882981c44080c5000f0b014200040840e1406001c0d4104904014060072440c0000090040920007040c544c0c0d85501d4a0343d05603041010092500880c400040d14200380ca0b040002900511200780d41008548480d1440d54545451084e001550b422912030603804c1d00c620407500607914200d075820440c10b004150000d010540c05641003002002c181c01a00105105404903403150001d070b240d501025190101009165001c001880c88601800001160030741d12030149807012800f4500800c4190326 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 747286052 1250 747284802 747284807
    0x100b13030210050f040e0c070b070e0120120903071205060a0e0a080d0c030e12041707060203070f050f030d06080606040605132304030c1221050606130e0601 69
    0x6002c58002c040c00000d10040e203541200c0c0003260140c0d9040000408203071070341000d1040740d0155003001080350102c40100300c102c5510842c103141d12042682c441424900cad808590102c02e102c045030f49402d401801420455a000500030708019102404403640700b6524100343c520b4502010040300e031500f01e2420b00080c007419007d800c0c1115040809400346802e03540d0340300e04610401c01245410f80e1112100fa0509000b81d20508401c4488400e03507126005140720b50384e0651041c09180f8142c42d03000341c0b0060003500041c2510a0742c401742c005500d000140e8640358030420b40c00004807494843c2d00241c01202e81d0a00241c81416080107000c42c0e424100020181801c0d8014000c601440c40c00c0c0f002c10140d036402c29241c200c0c51003581c0c0002c28070225010908520110b4402c2811049071006210405a00082e0f0314156030041c45000b5001e10000d104071106c1c11107011101514003010030140710000281d101e80c5d0400c400905092030060041c420200be0207103580b107884040e9a40301003100a58 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 747287302 1250 747286052 747286069
    0x1030c06120b0109061d040509030a1407023304060f0e040c02151801021c1d03031b1b070504150501090b03060a17010c090501080618100b130302 64
    0xc2041c030052107420158000204210f1251164008004040038003001c1c40215481c2501160030240081c059464284c21040c4c0c3e82d403060302c290001036000300d0b103101c20114040642d020194001e117011010a9001d09040071a9060840900320041c03103014110025211b030000c01c01001d99440724403103d2001c68001d41400a41d80c50b42d4021403c1c21086205caa0380442e042c1500c0c4010803803190551a200281890144901c24004d00c942c80010201d22544c010150f00d64a803e68400500003034141600111200b280c400f541400c07540180301040103d860303568005104c070b030040e0751281040603100000d100d4843c140d90320300700e940040f441806142814050030f03000700500d0400c007400714138241c002480c6082505c02e183d040d61001c40800d44650300d060707035040101303100c4443e903896540644003d07000340b4040c1d2487d0b01040d040200000d0030b5008111491084c02c00800e9480180342c0d01d680300e4030122006011030ba420300f1110700462030000d030784044e140d0006c20003865840c2030305502c1031001c080f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 747288552 1250 747287302 747287327
    0x709052728150e2a19180b0a05030103060c020c1c0302010507030509070308090a0f0e1e060f0105070201020c1216080a08070206070f0218040203010b010f02030a03111201030c06 78
    0xc4180010003030407015001143d8038007492050b60000d040108003104c0101d00500c0900400c2d80c0d00b169405030380d00d41c00900401c5042c1e2052003204441d90b60201101c061050150100200b03400740010804142241c2c80800a41c2207070040e0b030310000504000450143d80c14858071004e1046142020a00d82d09200300d40d4330050a080070046810300d41111070b55601c0d5884020100e000010b0810385507107640c4d072504014000c2c1c129001c0700b680c071030f01110790100c000c032854018032144006d004031020303100b405d00e4004d07140580458645100c4200440e025404507500b40c0c158401c03440e40456580307911084030030300f60307041d00600b9007030f00b40c0700c078039844000c0701e610a102c594080101c800124500a08072404140d040f184c29503541e05074902030700e03034001c0400c2c084d5204010240e12148401414102e03842035100b01d0080040ca04d08000554042c14507040982c0180c0c800d010403091140650301c116000303400d030011107007000e070301002c500c113441800d0b0000c42e03a41c102c06404000c01500070581d44241c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 747289802 1250 747288552 747288569
    0x70f02150a1e021209011403090606031504080f070602090901150215041713080307150612170a0207090e010219050307080703050c04080312070905272815 68
    0x4a140c0800a543d03014200c03200c13503064000106035038103a02401103422282c10074640076449140a00c0c5294440da000c4520502074001c803030603c0603240a04552501c9030343d010094034141420700034007078250f80048000f150b01c079030b08104850725541d41414481c000c00c00e030100c00b500b011090074002c0c10650b403224142882c480101c00e21001a44110004c0c0324810210042a114281c10fa0903030946081544038078820301000403450184034018610340200041c055040c01034543e00c100c4490740448080d406404a04120401c2d041c090ba98002001a0130b0035104549005888151071800c81d412202e40b41103aa500040914441c0c041c06540302c07100c42d49080c035605500c2e1100c006001084001e000d107040690761000940301207440d00944024201c038004881c1c40701c00500e0524200c0205940e8100403d1007210001041e15041c0502090f00c640c90b50355100d40591302640c4512008003900d001098040c80035001c0317020401c00d81e9a00007004d10b1380045030040e140340b040500380000380c025441307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 747291052 1250 747289802 747289847
    0x507030608030a08060405090c0a060503071409010f030b0a2303060703060503060f090a0803240a05030c040f18080d0b061312240605130c0f05070f02150a 68
    0x119541066910f0f1748684d00b070300e01050b1075440712081400c1c244500311203507124540100110392541d201e0090b41c801c00340754560750300b0300741000390b8a030050040940550001c0c1ca81c11141e0030082c0b0039000b810600501600c1400b846881d40f8600780c05001050113102001850007211010780707800c014180e0451510700b410401070381030030082615030700d000b04941050752003032000c129956005c100c426183e64105400984a05101001181d4006841740c0180080d2a2002112040c5030009104084034002401840340456540c01e00018051041c100c1c1d40d507561701d850914010f01420f50000d0403e2240301010b907110300d0710500808494172041020b00940c0d007481440314041c1801990400c0d07654200392500c0c00301c480d00d0850007420003010150031807036581e03013412528955500410141d0b10100e500400000c030484486003111041c1038850009425003d2120303650380120001c1031f68501a5080300908807940d0040f6102d401180d40c0362100700e00002e4180c08496008440385403190b4035021191 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 747292302 1250 747291052 747291067
    0x50c090103120c050f1b1e06030c250303020a020d020106050a090903022d210d0e100f020903210a0f1b030507110118050906031006120512031b090103020408030d050703060803 77
    0x8c2032800004c100c04089040068229804414400700d940da0003007103040c0900320100c5160060184d04541c0001c800351042170481c003842c03401801850144c58020300410380c1d06140074420f41c0039124440c0c003541507001c6c00c810512045100004013441050012010340c26100c030106a615052040000742c10101d4405400c4d0303140d03901d20702254130900b103076600803880b800e0780d521080c108807c42c08c456803454540007050448102030b801074083d4120032800c0d1043d034910454202100d154000000425200802c00c4c1c2d040c0d1800b07022143c444503200c1c0303040c210481c283c0021100b00302644800340d0107d2030108400b0300300013083d60142d41c00301082c80d1000d4484100e18801580c0e1806000300d40c820b404500000d5520f440401c410b09078864000014461280d0310001d100080f60258016035007400740d8031a03001480c2115007200d0061101c81d0440c0281c1c540c0304a1515541c01203141c02e410035408000c00102c0100800241000d000c10f1200051141010381d4041c00f2154a031f441414182c000340140b1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 747293552 1250 747292302 747292309
    0xc15270c0f18040f02090703020c0a12031e021c0209240915090319080d0c020c090405060f061509010c060f020f07050c090103120c050f1b1e 62
    0x86514042a5a0700300003050000c0094904229201c6030040344044000700018040440c1484000c42d000740c500102d0350b26040720450a030710408940055980c0b00681c544000b80c0c0d04411485554120b00e40050180030b803101c2c442e0558004025040c400d6000304c0c140503800c290803040c0c01e56008041c402c529150303c80300444c42c00c1c0b840100b032103400b140507104ca06800340900308407a460500240100080c03200314400018607000490114041d00c10810300d0200141a061148200758200d02d0300741c2450424a001d00c01b405c0541c02c088114042da160140c182d07220310320168016841030018240c3c52520b42c071501c0240d4002042140300d01c103142403085509401c00b0468076070803020f184c12048580182821005010a2140d240300c40748000b0b40f8400c812081c101030000c180c8030340141c80702c01d501c01c41048500762080c0005811242444840c40e9040c0c0103600854a440c4103c00f5181c40c2010304400c1402c2580d100582440c10044002c55075842c5010584820a10060154140c4010071203011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 747294802 1250 747293552 747293563
    0x1b0c0d080417121e060904060e010b060f0a0201150b03040b040312051312090f0b1612031b18090b01020a0f0308071106040503030a0c02070e0103081206040c0c1203020c1527 76
    0x600042e5a071020509c02c03c02c2904202e20040c0d002e0505551080c54a42c0000d0135800606180010b51030208100c01c507410440c11401280c401c10f500c2411511652038807505982c01501c202c09110210030500000000c038041c0343d11501403031211424011007803e200b007203003030040d10900421416940034014a0305008445058400e69070009460342c8805105410b0400e2219024240060941500b00c0c2c070b540c16005500c00300985440401107039a80d5a091300c1400030b6402c003d00b0142c1d26541070000010356400300c1103243c81403040725040c18441c0c84001084001c1213042d00001ea400040200041d0441c0041c1028260240184203c2c601f40c0c0301c440d201c1c003000c1c0c0074800468940c80c410403828400c20041d4041d0201e40c4050709603580d030f49040800f035800090581c1c240c51280001030002d2800e480764604044440d1607016002d47d5a40d04d5020709050400d00301d00703041d800d20051060300c60400122540030f21318050403100b42003000f04100780c83d00e580e074000b0314610b41a4a01c0384843c2e01056 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 747296052 1250 747294802 747294811
    0x8060109020301030c0e04211416121d06090a030206160314121302120d02070806010501141c0e0d0804140705011d01021c05031b0c0d080417121e0609 66
    0x92456080c5544041103501c155212410b02d46084040340912b407400001c9008030700d083c402d5443c0c03c0c6038422041e041d01d10f05160410742c01c1c40500130b4041481030900200401201c18010102d441d841d4895001811a0f08034103520070005012900c03030003c00d41c001481030401c581c0c25003103030304207040c000614540c20002040e05000320305882d6290b045490303042007005c0003602c007000c2d40c0c903003180018001c1d0340f202c0c5c0d485404100d1241400024603540215103600c1017180b4403028900d4000790300c5c0302e140d00c42e22143c00d41242640e07550081e0a000d40c14003414012101c541d81c2c1124500303041c10070400391070190061894039042604100007503a0028207109000894421550010840341c006134100000380e01034640521450450718886035104004612030440c06d489030b10b1040361010b0310341e407a0041c0b42014155034000300c03032006480d02801c0c1c4107912510914903014020b2114074104003503000b294009044400c80e0040c084030414070100030800030b40700841d03240245000b90004101c1c507005007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 747297302 1250 747296052 747296093
    0x1502040f0302130626070f150503070905040e0a02010e0405061f050c0a21030501030302060a0f02040b0f0703120507050322170d0606051201061808060109020301030c0e04 75
    0x120f21011210b407036088076000b881349402c2e8188200740c852030f8040c1d028001e221101203000d41e02d004030701070002d130b144d000c00e81c1c082009000d000c5046103026241644081e000c001030040b0200f0001c1c483c0e4540c0103101d4462041009007005600d030b4400034000c28550800c8a11482c1804d0400c900f03522114604600b1004000c07042070070a0024409a40074860001a00c19900a0341541010702c0b001980f566003016904410604020410f13004800300e550030302000700160004804103100c1105500072074020341049000524003030743d60b59500d440b40d01000c524007154802080103010b268010100c0070102034801c40911a602e0030902c01005440001c4c03000000318800f5164202c404880c514428003181d001241a003d0416025132021503040203540d82d5026091000c0071034210700c2802511110a05d45400f69441d03402d00100352100300a021001403403190b980000940381404020040c000c00d098040180d80b0b5046013080a401951500442d402040ac0701c2800001081e0a020400000074031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 747298552 1250 747297302 747297319
    0x6030105030c091f0807050f0303091e060f0409060503070b1303060c11061009230c07170d05150d030503060f0307080a0317090d020604030302181005071502040f0302 73
    0x40340c004c5240100c5000d10b144400b542e0001240d50724002031048191402140e80e180840804020507582c1d200302d554441d080500106208507040702448c0c5880c0c8103000030719040c1040004e42c070a0a0581081e800320f05c60688403d02000300e4107044c8170075000b600c45410f07291301d0a60303110300c503400040a43c48010312240e920402d540d130700c0f8864085100c4225441007642c1c1141086000046614540d0180515062030038128690b5010f132000d0302c0b1144141c60a40050075520403c0b568000e0f044441c0542c0e1040f00c11480c4400185903000516185030900000101400c1000c90341106001064010b801107444103031440100741c10074103890b44034408031840e0070000c00800103e41401d015074408051403181c54000d008141d00002101c0d02e01105e142c6035040c90795a60711700307551150601020700260304800b011a021034420380082c00740c407141c4c1c035441d07104081020108154140c010b80c210300041d40811a80d08110802155510703002d50403c00390300380741c02d007022080060710520009100d02d001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 747299802 1250 747298552 747298561
    0x150f021b0105300601260a141815010f050603070c060510180b0907050304031107260609030301090c111015210210020c0d12020c06030105030c09 64
    0xc2c1d811104180202c03420903041440769040044a0320b4000003000903d14420000b0385294441c5143c080c14045158940009800d0602d030b080286a001c3c2401c4030385a01d4a031103c0450414548260142500070001d2180b4070340441d0322814000d04000c0d800080181e800100241003401d01031001303840c802c849195417034076425415154000140c00051445090900300003421804107203c00484140e005001448140100410219821100295405810500841c41701d901c03c001543c8d02900c40d0030402c68a00b090b040c9203280148a500c5112006494045044a40241018000c907803500ca40208001c7c200b03002d500c0d48038081401241402e40c0d51310610043d8070b200c0c402c501082c94150041d20f480304104114000070f851682c1000e001801044400110081c002c01308544089403014140c520301c0c1282d080014055601401404610480440c00000d50f15001c42050041c8204040408000020800390606908807582e5114846c00d2004001e19200800c8580b0f41d0807080300c1201c5144e84 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 747301052 1250 747299802 747299807
    0xa0b0111010f02031504020f040909020105220612090f031101061a1b060709120f0204140a1503030509040c020f0a081206270604061806150f021b01 65
    0x5101022101d40c00c08084500d01070680d80154015809429805a11150301003840281c2c0b0488003400001c4d00104010412501e6a6012203019881450442c1c540518a050140c81c43d10b00122000f24040303003502040326541204100c403035140503e00c148402001c540354800585501d010250178002c050f440d1150150080d80240f0150404010701d6460761181c03450410710780c0242e02c030029010030900744696403601c002140761259030203907501101d080c1803e4a04110441c122411204002c2010100740142e4840c05080800e14503440700c4200e0780380c100d02e10350a945030103000d55a244c0c0c46640610100340c1c42412203280c00c00565010800030040b00c400c07483c2000c440a0b102003400b0340d1262078200485100201154248121301d16403503150002000001102e80c07948284001084c142c802c0080c0081c1e90140d07010500505c00507110b0380e41c5c070346080d400d101c2c030045407584d41d03440c1000e100c0001106411340c81400c0b50b00d030001c052100c00c00040c2d900d206070000e407054881da8014902d296031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 747302158 1106 747301052 747301067
    0x60515030f2a0703080f010509130b100515040602060a0c0507060c020f01060f1d04170313080403030503011511030a050918040b101406030a0b01 64
    0x1c0325941e0141401100c00b5030b8800c0c20382220311256900140320003030240345000ba1110442850040c030703149003a20b0b058110b1031043c1020307400d0024001000751140d80d55940184110301c59281d043c12400407585070b41c0000d038800038403002441640103040c00b50084600c950200c50f0192100e48018040d00c16603241c1c040050300901480c40425074941041c41d000180e40141c8483d000340600c99825200541c0000e2403008607902c00304440390030743d00c10103480c0d000081140190b00742990b0310b45034001000b860160391080800401c1d0500e5140092000855100300503e40e9640e907460007034840d4101340b08460110380e111180300c481d2401003800d9400792020601661900b4016801540d330740c1c1144040c283c0000c4102000e44540315a05681c0d80200e010f40685469803920031001c00440c40e054110b035070000380507112040340d5225142600d4100801c5540450b1454903080102c5081 = true := by decide +kernel

theorem cover : BRFrame.Cov 747122302 747302158 := by
  have h0 := BRFrame.cov_init 747122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 747122302 ≤ n) (h2 : n < 747302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
