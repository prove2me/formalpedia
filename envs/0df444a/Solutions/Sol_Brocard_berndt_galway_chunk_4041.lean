-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4041
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:23:56.136809+00:00
-- url     : https://prove2.me/submissions/ecb0b629-6926-4af9-8aca-4b0137ab494d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 726618705 ≤ n < 726798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 726619955 1250 726618705 726618707
    0x504060b0906060405061b0d201203070e040f052e12020f060d0614130515060f090402070f05151506090406050310061a07080d090201051e0406 63
    0x20203040d02421220031040b03040c03002c04038106019a0140e140540000030ba51411081c1d0840c103910f02004000c2258000004624010003000d5501050b500b510082000b082c0305120120388440000130301c2061500350741e100c41d800c45451f40c0261155400c550742e202c060b00c54114500031107105070005801d801a80e166060061000d13840100c070a001c04d0045c2c3e105001c400340303015070440303c10303012103e0750314030b200300c10028403a07209904001604500c0c005001507220325000c10803015180c04c0700d040b8800ba11028101056607801c4640c14448111444800032500d8503201501c805041d00c11994100350142c008101240d0203007000340c03040c429003064041000010001c00510001ca500303200d40c0c90405244209d041c20583d20568410000400d08c00e4098413a0760000d4010f1000804547c24001c050307113088000c0516014213480c00c64003403020300040707a1010480d844103500c04025881e003511410076400404001d40120b040000c00c03c405010117844950300030050b2000c03030003a40da079850080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 726621205 1250 726619955 726619961
    0x60f0d0605101719170706091506060819200915072607020a03060c0e09070203090d050c060c1005070216050405270c090f04080403030f1809050406 65
    0xf0148507118454403800307200c01404640450010b1400002403000002d41ca00750080c480c103086009011100800d041c0207001d55500710203812401040681101c0002e014010103a401c140544030120b0400b2001c07031082656800070308504941d148000424407076900000d00d03110700103801c44002d114042034050403890b140315408996080d0203200e0346081c80315510320210b0904000c24a1440c000ca504149090008100b00d420b80365004202e80344550f2031f45801c0004105d940321000024542e14a800501c0c03c00018182c0030f40d40507002036060081400c20071580030507469089070140690400c00ca01303a101c07040170344501c07403641000c1c00d950000602c18000300c0703500510660840d030022201c1149095071140d210207490060f03034040355641d10925654114100b004149044007203a01040d100152301240f9055214422100c2e0030140d128030f10711083c0401c060700c024000041c00c100070000a4081c04100084241d00e00f800d5170400302c0b200948031182d002c1e07805110200e445104020810082d44 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 726622455 1250 726621205 726621209
    0x1b1b191b06080105060703050409021615091e06060302041b120b1c05030910051804050903030f040c0312020601030605060306071d03190c08061803090108060f0d060510 74
    0x500c84100e1440c28200805002c81072180034000c10000813610180751180d4203da0113010b00f02c40c1999500c981030381c1061816a420b0341515998184043c501016106004d02c8840ca0b0b0440e9114181e1000c0141700d8140030405002110700c2541c40b0700000050301c2d24003650052600855100441e00e98051004c0c000d98480480e6107901c0c0d20b015120b04803560744c071505500c0c2131541940003520703d90a251061551103090300c080d9214085400c1005004d5000e0000c0c0000c82c001100a4084207501e824041500c2050301c000055070401e000080803c41d480c190341d60700a000e503124405071550b940f910b055440c568074034200141c00400040c0180143d80c06201c1e040302c1c003903001f41190b1801c044014050584581e000d000c8040ca40f80350b14a55030100164862254203640c0c100c0c054015160248050341c19111325030039400380800144200403440200102074031807001651034904840011980c2080040072168400094945409591121325640080300d10403240080c6605040380c41c080701941039 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 726623705 1250 726622455 726622493
    0x7050d1803020d09150531030521030c0f070b01090b0a060807021507120c1d010203071a0a060b0d0504030905090108031c020702181e1b1b19 62
    0x3030704007041050705000c44404d640c4c401d840c2407a1a11f0405994074101c45411407071450103c101030011340d202c1c00386464076040301c2c0f040e4101e070790340050682141c907511000b108903155030303030180001100404031030000e10340d00318088915071421070603a48014600c002a007001d00002c0d0342d6018201107091040d000000782055040c840c00b980342c2903030700940d00e0649030614141c400c41000400c16444c0185000300e9540d420203030500a0024010000345440085400f04c1c0d00c91052402d280c8403540080304507503d0f5604442d8840c446c2c07021060840d1710340000382c8610390240d96a0750001c0c40c01d070000040d016240c21102d020400742418100204806c0403034000c43d1207480504010090131100104540b00403103d01481c9403a59903030140c03000280a06400a5004002160600502111135031483d2003500b07000d600050344031686114611440003107981c030f041060720a8cd4462280c3d4400054039004116613046100841618040c41c1002c0580c2c0018140704503c160350003c00030700c05074486000000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 726624955 1250 726623705 726623717
    0xa0b28050a0b1603020f070b0706050c03100b0a12020a05030108061014210708030c06070309030c06051320040c080412081b0a0509040e16030b07050d1803020d 70
    0x6261a000c1c00b80f00d143c540b04604860324200f0020103000340014400b00b5a01425210043d564407050036066000034002c4404038604800180341e14614002d80380a18052244100001d0800f481c01d01c55034409902e032401d01a10084021880256000402e1800d00360b03565542c5a5240441161400e58040c04001c40402c901000f0300a016002c00c1c510f881340c0040742d5000e48a2010100b8000c0b101c4030b101500140e000e42d0780c001c522040000000c180c1c0442c43c008903070b201e0b80c075068210101c3c2c44506000300041c14500980c000720758280c2000381c01c080503131602c41041510390349901d0b4012000002c3e40c680d110444170a20b0518251161f0440107071581003480c0304c0e1402d950307a110340d032120088800502a03800c0100c2c512200019512003008109456256941e01403800500142c02070719070248618288428241100c41c0450581d0a031450405121b1a00c0d041d41d0740c50010a40c01080b900c00c003d070900c5007020405141c051210024007070681804a51400d040003401d000c6420202401d00003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 726626205 1250 726624955 726624959
    0x3350901080606180303070b1e040f24020310060201050a0209130c0c02090709050306281d030d201e033321150a0b28050a 54
    0x41c0200d1001d51216084803036a030350329110180010800d4508445680501c03000c101131040202c4840719502900d035010040b4102c0449440f42040e980046600034a0403980c81c01c80d20005010b407403001030080742000900c1001803095005022a00112244140c0782c2c40240100100783d02071050b5500010999030661501c3c1e00d8001290000c901110384c222410350b20700c10a05030349d200e8088401c2d13190b8020708055060502c02c4000f85011441d0050512038040c4001003580c10014209401c0b011020300c445158074521341c0700c0a030081c00e10030f40c807000d00002d914403502e007804184020070704c1001c02d000014001e44603100c08508a02c414000c4910003204101c40302c0c0100d40b00d005003040b90100001a650b9540d07213815040038a01207100e2400c000ca035200d503242d4551100505601c96041604e80601c100003216020004c030b409503048003002c0e00702c1042200310031404181141e001c0b60710300d17000c00c4003841c080100d031f0b101c0d80c2028801c00d00020317202c0d000c5030f40d40384524440003044102d4005016038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 726627455 1250 726626205 726626207
    0x7080c0a050403022209030c0b061c2003030a0314061c0213020f0403080d200a0f0e090a020901091406030c071109070203040810050f010e090703350901 67
    0x2c416400040d21400780401c22102416080c40e400380246a100018810964940f50241c100c03000110b0444207000705400140003030515039401c0750303115040048400c004100351203028181c09144040206d284800700d6084068030100000c1100e81e00e01d03540003034582d10202000c506040094480c070b1007a0803840324400400d201c1c05843c0491034048506110080365144031100038450392400400c483d5000c600002800300b10805000001100b02041c1304424400100c0c000500c1c4001c031008209400340034007409181310f2500b07220b49920b181400e812100d50740c00020f24254084071543c074684d800203008041541e00201001c000c0c000c0e040059800751b2607000146aa002c0103001494113180402d2280601250844450700220b001d031000744c5504050380003e491750700902480c0c2c540c4c800d5003620315601c1c0d40e5118503403190002c0103181500d079080001030a043c0e40042d141c032449207d404804004070b4100c2ca0800070003a120140381c1489107031111030881c8501c0c1e028540d60500f41c180458109a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 726628705 1250 726627455 726627457
    0x5040803010510053a05130b0a0e01020f19050c07180b0402070308060910030c05090408071a01050f0105031e064c050a1103040306090b07080c0a05 65
    0x510800c90780018400244903003201c0e180038811142a02002e0502c51003d213899801403005c417000c10341a0110b004140061030016200c05a8000003d40c02e008030340c40205110b58002078011138100000708000301200c0b2420b0990300919a5000e00381c400050000c0307182050303100041411018207186041480e868012610b0703000303522032080d0708050704400d0242c16155a121121303041c8000c00464030b45000341401041c942c4112000350080c2d18000116450075401100d020480381e1180108502c0c1d03003010140541380344090002c841c282c0f4244001000030b611240c01082c01101d003400c9003000c0d813520081211001c40d044960703052040030814401102d440300020200052444403c0c1460744408020a540e0001d8046007081c13140c7c2d018500d00a03014103405205100309404080c050308039a222030800c03014075083c501020410400c600303501c507401140015522850141502c3c14142d490311810305492400b00304507147d0484a0403c0045604000d0f0b15410980c04040c141c20685001c0c800703805 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 726629955 1250 726628705 726628709
    0xc03040f231c0f0f0b0708010f15030b0604030606291903150509011701061e06120e030313020315061e030102040f0f061d06040b0c031227010504080301 67
    0x5007a28004002e000e000f255104604042c0d40120741c10075070139050038070382c3c0550019609500047d0f007803000080d035085100041300a540f4249624500704c0740741081a0010300c0c18940058120703500703000000104036079100e4a801400014950890109001e44020846144503400564843c085c020850741031080802503107200c029041c0010000340c4881ca0300f01440880e4400c07948848204d00100340b500b03400404000e19203500000344070858460400350a88900302c0308400100c501e8100070042c1c03522a00501510018455002408207580090f9505691040f034440c08600768494012086040420810202d140904040280c80c101440015122816507450198501c0312420591941e035080d41243c4c01000c0400c540c0c00d42540d5040d100c006040144203c1003c0780c248800303103a4044580403400003103140240700528180c2441d900380455007100610110300d10091000048030501415858000d08800400303089002403421000c3c003803207080c000c0c070030564142018800050241d50590381 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 726631205 1250 726629955 726629989
    0x7090b18130605090c090403030b010318080d02031003050102071a01140d03030b010e0d140c0105040f1203110f1609060b18010c1e0b011a090d0303020c03040f23 71
    0x106915021140d17842c120341038440903800482d00050008164055100f06034500d0203880178032190010110342c0c648144200d9000d80002c030104001111540c0e02c1d401140d008000704126241c0a4a03601c07505e089803c4420b0444980500581c0105511500482580181841c00c503840050b1054004180810101a0014181601d900001226a001d0110001c5202001d40700c416108041d003000c050001c9a00c0c0d101c02d4501030a40c2031010355104404440c15101c05240d10f014403480d24030340c030198800100040e8100210284480780440c3d080c02108600448000200802703600c4400c845003000c203030743c04080e6051411104011b401007034402e540c115012401c003044814941030041e00d0244403084000d090642102c41c071111801200001d6030078500915281a5607070301c951950405102c000035908190005015402541c43c06200c2c0181c05442442d004d42009007049003540b9542090300320704a5103803502400e021031100b00313030000841111900300881035003941b40401c4030b42c810b030458a4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 726632455 1250 726631205 726631211
    0x6060a120b15160b06090705070f030e0907030c080709060e04020d0e0303040c031415150d050601090204050f090c120406020913091104060b03131407090b181306 71
    0x11400c0e03403a90700048241d0500c1091641d030b030200b12101e80030040d001d00c1c1210400701132000300d8400d003441e83c40301c2e10407140e130784850f4074084072501c0c2c1040c1409142c40481c1000304400880381d09450f040f401c41e00801c9942c41c086201010320f04050316500c4014411010044e075100100131581d804401c9124046080c0c0e00140e540007881ca0b0003026214076200f100e0188400401e2100300041031001404490068208400040704036240c10340381c040400d5a406c1100002002c1000140c0c241c0e40481510300042ca9181c0c9407504d40e9505003440300903404180c6242e270114040120f802d0040180c005000200d0740700819103040e00703142040d8010400c2c820340e240c1449001808004c013540c105c3c1c020b07100c000c0a03a50080c0041011034054071703292508881910340505000c0141c2040d001d003206541d207020416082d562600000b2020b00154034003a00c00070600d03884450243c01c00e000301c4024201105002c40e1002c001c4003480b50580100c518a80c80204000800c01207000d085120090603034096004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 726633705 1250 726632455 726632471
    0xb1801021c241a0903070f260d050c030c010c020718050f07231c0e0f120d140108060106020105090d0801060f031b0c050c010e0d120306031e03020606060a12 69
    0x400007600a5031034260b0140300310b040106083c0e000c7d0904004643c401114a01d8800061a566040c117400003025480e607407200b01140003250091014100e05414101141d0130b0118500303070b803130035110022484405a0080542800f8682c0580e05141072480504000e100c2d90030700300d01c0700c105910010999010003503140d40e403d0b07e400c00180a00419a001d4031120b840d05a180c0b00840c440f038400c80848000c0b4644071100480c0070012410460840085000e8070100b82d0682894a0341e910040609840300d54460685682c1240c04c0b03034190280c11500300604403503051071000303030031198050301c03003601035003c0d003409204180d000207580e0554120b442e20504045800c5000e4000e800074841c92603241039451960240725034886035100260b8001c50484038141400401542c0703a94141d03101d02e03041103440d03080001280001c1e100490599003443c0000d032140c1d80380c8941c1d031324481304040141a040c04d80c64040c18580e04220054001400311001072800d0200c480140a03c146516000030705c83e190451 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 726634955 1250 726633705 726633749
    0x80c1206060913021206150f030a020112021b0a020f0f090117070b0a02060403120c05090409170301230114091915030609060f03030c0b1801021c24 65
    0x107044001a070203400e0070005e10300c0d80d00300c0d600e82400300c4205c040d0403540079044005142c07082c00c000e6000e4000d8060310070360201e6001114100d0060043ea03031020380030444a00507030040c6940701d03011903211001c1c1604e03101d6481005030001980402ca40b150004051415042d0345502d8007604442040c070b03005400922407140701307003080741c07591040c2403451000c100d0b00607941c0c0200302ca52155110350383e626001c0c641d010f00e81c3c0445900d60303201800a1000d202401c40e41c1402e5000903d201d018204400380c0c49101000e030710042e4800d810a1044242c904000717403c1ca500340c3d0000c801401c09007031240b040c2035140d00010180c010162180d107d96101c0c081c0c20b9051152074486005400c291640300c03503189034204050b000c1c103403501c00c45c6101e91501270000707401c501400301c54082d84d40c95a02c4a03182c070110b07281c5c800080c0000c0d210080e400d510004c92204504248002c0c41e100e90721080125409201007200c5003104c0d070400b01196a10340c17840390964484440109081550901003488800c4c000e2071107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 726636205 1250 726634955 726634981
    0x9010f0314010303030603030e090106080a090303061502010c17090316020f0411040f08210c03210a05060306130308091e0f0106080d0f0f0c1b080c12060609 69
    0x4403980110780702800200c14554150040026203000c0c0d141e8070702c40c040e2a4140132208200f440342d00300255448003c40c802d400c40d82c1040a00301d002e03140c0881d00503259885104038056440d02c04c00540e42d03070400c440000c0d8112020612050010408030b107203180001155403030348503004a542c9071040c401e034402c0440d650641508001d002c0a401045007000540a9801a83c00b502030380350104084100003620940001c0c000401c41d0a00b220503603041c0504d4404403503908807490115880c003080c441d0724200d01c20b004034030b800c0f1810f000403e4190304085801804440c4003910050003038001da000c1087d90800014070000c01a0702d4540403910341e440442960070001034050610500c48001c9006480a1000880c411035140c3d07540204600b1340e903201d49560310080c10300003e000c6a01a005070000764020840880b01e81c50034100118001c440396511000d941501c10003056000200205201401040014041e5600c080d54141440d101c051403a5542c1c00000b84864403410b000c0000807004001c3e46 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 726637455 1250 726636205 726636221
    0xb070c08030c01050703241404020f0c0d140304022d0301020c03070b060a080607050307090e0c130e060a12080706020309030c060702030f0403110406180e16050609010f03 75
    0x305998844a00291590190100f980c3c424000b0f81849802d0040725200701040064681d001d00e909401481d040b01c41c41912550022a58000d40c20b204518108281b40020301c081075a02010b1310f22020f554101070145496400c070111345400030b10422005031a125041d01d0100303401b0641000a0090791203400c403140404810640650020588991740034001002c1c22000388a5480200c0c95618481480740c610a94810340c5c50551143c3d0209484070b000740000c5400601a180c50683c0c1602e41c02c00e02d26a0780c0139112400c442c1c200290010000100d8003040c400b0f4524890b2802007400e041d00017400311a20b5004481940034202c40840400c041c060031a0482a072201080d500c1e85055138480361690020002004a0b0080d90f00142c00030340301100711101440d580001d90704003402d58a5060540c9c25602c403054100c3e0307481c01c01203082c010202000180c204509004600d6064000d061401c11410100400402200c49000d1106076280c0003136450802081c0f03030695402a000c130046001e44100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 726638705 1250 726637455 726637469
    0x20301060b040611061e070e0d0b090d17060f0a030c0b2a0325050a05010e0706091d04020a03170306040506090402030d1808010e0c091f0b070c 63
    0xc000006807811041000e0003c035500390302c0b105413286941c000c4645a140417601185a43c0c801c0d021180354822003544950803d24070320302080300038102400f06140100c510340543c2c00e841c40c64100112420204922200b150142c41c10700600c0184048011140c440031700f4061081865801500041c0c6402d4020402590443c2030205000e540d04000241c031b6000e6030b06107158210000180c1170a8210401e13809408024200031071802c024031030300311142c14489540901091b001c012400200300200005a130460181000241e0f1044c40720f010b92404503e0741c400d90502612b02010080c400c01000082c03d02c003403040c3e44840c10340d100d100050303c4800640004141c0e481101d200c3c40c54640c083d0240d48203c1c41623804200076142c510801401c884110f40c02541940440c00c00064244100c13005014004880e640500d000c0d11584e0860964071071010045850380058501c0d001c501c7d08011b0a500100791180d031084818590442c0c80001c0c00c2e40c00f40a820351000070300c82041260f40d41d500c400030421 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 726639955 1250 726638705 726638711
    0x30206010e1e0c03090706110318220e010c0212070605100e010312030b090c03150a12060207120e1003050c0f04060804061118040902040e071205070b070c1809020301 73
    0xc03d4428582580080e500e0342c5140c0301d20500403a81d1070142c10690f40c1e00344603400540c103200703159514440201d018100c094210000040c01c20781610b0427140486800c07100c4802150030a601621a42151071614801045500000c441c04a25064600f19001107422890209aa5981c1402c0301c000c80c00d141c0c041e200e000210400041840f0b20a0820031030409507980501084406c40100005000280e83d0201421400c1010501c0e0350807207904e03044411409000c1c0e004803aa5010310070070481c0c0810058920342e400180070b4040000701300310515070f06001d0501d00218000c040114502c4003d901074281816902c2d40882c82c1c0441c02000d4805140c0110100ca94668644c800203008480a807012940213003082d4080650017281d0082c5da08140e055410140095036220800c001342c9560f1000740d03041907880d010704010f100d080c00024060f1040108801081c0c86501d000ea24042d115802807244140c00d010703010010b00c202400804468459a10148044046409178000c1140e040004d50541c0703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 726641205 1250 726639955 726639961
    0x9030b0c0c0a05250501080106261e01080a05030f210406020c010f050601051606020f0c03130602030702010c02010c15050115091a030a090f0c0b070605070507030206010e1e 76
    0xa00185520707104044d4030b16218041180811440003109500465001c66281401031204078458410880c4410003032461150414400c0d100c05020300d820f581c800c04140201c987c03054000055500c081c01058988002c00b0300010302e88501c2d07181e004140e00c40030840400507030b20700070746c0034107a10164800f50000c0c403141c41e04203860308400942c8020401c9020b135080c0416048044a684034103403080740103840d160300d08070000850b281c08034048c1c84c08075091030782400541c40414031580a409240030000043d030341d42990104106045c5d036190720030011944200b10f00300c01030364010741c2000703160350a00f01320390785001600d040c540b40402078000c6204145813000010340e040c00040d002c40d08032000c0c0c0310100825100c0703030203204194020b4501821b1800400210799122515441040170300d0065072001e00c60140c0b941e8940c2d4541c0303e5445100040720200740a03007404144d00c40ca03074115640f41001e603e0840315960103500c0300c105108200090f1070480c00500816003401e90300076075800a641a4007145 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 726642455 1250 726641205 726641213
    0xc0d050a0510052d0115140f0a0e09010303120207080d0f1a010c0b0c16020616021c050a03032409060f15210609090f061a0109030b0c0c0a 61
    0x444111000341da058401a69030310901c0030294031048845507603160b080240c0c201804a00c0904425406d0000c1001450441c0d4200c7c218502030030140d580318041030364501c4041002040e601c0740303401c01407160494000420019401542c00b0340444031841340580c807020181001401801200110070240b410f000164105820b141d0200c0d51540400c0c0382c00751404200c100442d82c2006c1540010210348401d0003080034101b007040540301060003034003802d13100f04880d4041001c41e0082c0441c0721b01a2480500441149804924100b41c443d011b0b0003e9030358015900e42c103940c2c0e08401e2019040c180e0b60b000703000070042d4600404003504250407241c01c40942d1000c88500805441c0305104a42d41d0724100850402d40d0300d40680c8130101c29585003021041502c048034091500460f440c010207595040000b8480da40b8001d040403540642d030042e080454500b007138402d40b5454242560320441000c201c10190b030704134000c401560f820081ca500f080c1d6540411001900c1520810000c0d4070807102088100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 726643705 1250 726642455 726642461
    0x60503100e0a08040e09060a0b130b030c061308190f02010c03030b09010f051f02251511100e0d0513080601030b04030f020705150927150a080c0d050a0510 68
    0x46c882c0c15007103c005a85002c0d00208842041b1200782e84802c0b042800b00413034009401c0040840c4004080e91141440c0307000007211f81d409010004d41c0000c0c45401009860024083d066000d204040c0000c04200e142c0e076824160386003860001e060000d0401c032942414884d601c681011200544107040703a50315104407041c900850710600f48242c01d10300d40d0811400c0d000003002c00c0884913400410b0800d40009100d242c071400c82c030151914a56540700001d03070100c82801805042c03000d45480d844075061005050038070150300d05607003d031406c2888070064000c0008001658950170720300f076030311400c0f5000f2515014250382d00c054518403c032310020060110100c1c400340245d10a4690140c10001001c0907a120f0340c1e00c0c842c3d1a4040c120007000443c280c2544c0040090900007000605591101c00803410140c502d101d504403820303003540400401c02141002440e0b04081207601030021440c04191079981c07000d803402280640c08441400d4100b12040040144851744002a01e1070070840026842c01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 726644955 1250 726643705 726643711
    0xf0108010c0f0807020f121c0b15071a0703050a050702030702090408030604110c0607080121110609102339070b030613020f1b0304171f060503100e0a08040e 69
    0x540114400300072114070240709036000d2716005004800c03100b4a5940701030b40d80c1c200b480e0655000d44e82d00318104040c120404070500c0340986460008040c109600710138101e80e0300404140655004001140160340d0b03050b2050340c01513000f0ba11a640303940b0540414040c00e091144090010f4000c28200710b140300210b14284602040ea542c125942c0c2c1e2110001c0155081c100007a030340803400940c60010884903498001011b0001d0302d010314014030440480c0007e202c007520800000d00c0383d406110100d6112501c801003940b1f05a2003400c00e070748074620181d4a50b119048002c0b003080104143c51804160781c121001d04015020f4860741a80d80c408490254011980c040c860800089000344800241c03007a940c40300707a5411414100403045011075400d01069001055906c400d00c800100c0408403081001c4442c00c02d8040c003200900d20100e442c0c0310307691010040d5210b00302203045c441514001000080e04e200e801380401e452800002c21800c1150720f0700c020b45401c0d0005008241c500b800b003000d0340 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 726646205 1250 726644955 726644977
    0x4050a06200403081222170f07080a02010608010203160822080309010c020111040b090d02040507090501031d1f1410050f030c10140d0c03050f0108010c0f0807020f12 73
    0x714a90b2044900100030f6510322151080c1c4003048010800319906801c94a8103c01747c8a41a1921840c00d0004040390065042101e1000e40040c888890550a0103040c004094900086d420760820985e0701c1078011406981c8010820a0400100e2100010804144011180310701401c945494103010640c0d84c421500c0b50029030030070485800003441440340111041b11000d01c0c030705150800082c041c982d44080505544000c0d1480258056a500d02c5114000c0e0020381714450500e1410001405540c203c032603610b461005090038a00306a40401c86130032494043c6420b44c100d0701111305600041c451a40c08070140041d4404100054003140450800d84408491b044914034480301090b0340c2d02089802c0e1500a400401c200e907049024294002401039074121050901c0070841c0300c4021145884000c00009031102e092007100908603c80754050000304000340400a41d41401401d41d0035220302d4142081240b00020761414402d000401607031a0400589a04440b46401070040f60843d004903a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 726647455 1250 726646205 726646237
    0xa200105010f0608040302070308090130060905061e03100c08041103010203041104020a020708010f0603030305010f0b0f07080c0d0e03010606050a08060f0f27060904050a0620040308 80
    0x4200c83d409440014401c0e40e050780141141d41c20760382d510155800035208241403008400c44100c01040315490000340c50056108200d4031002e1700d6001c000d03a2800d500950900d40f0f0801400741540f2100106410300b102061040c165076545d0010a1611040103042a005c0e0300d0004003542c007030f91004809000302d01030f8a0008800003e0004c16080344010b54004003e800c041d0026660b0b400c05401802d951104c41c0180d51405948180355429a80d000940440f1642c3c2c1c1c0c60309004060301882440d02405040412002813400c0510b941c0881c841c10340d1640c0d0f540c8003c0381304010001213008940249030100c0c141c441076030071308001412100b02e880d4624801d500b8500042071b141d104e0004d072902d506059844190395102d03101401580320b4410001c5030011a404014042600d40e25a004144080740380c0301d03880b4407410651601d003038801130070703a44c4a000400288404030340000ba01941c59500200000780b00d10400c0040d081034180324582041003040070500009202d4060080c12281002d55016 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 726648705 1250 726647455 726647459
    0x2a1502070506161d1201060f0e0114010503130f0f0302032701020a03110f0106080303070f080c09040f09020a080327090f0406140c28140a200105010f 66
    0x44210604000020700080d01403159a022102c04015003440d40e0340c007500e5510444d41e152005401c2d518160440032003024490302c10400149d400c4c0c0c04070f0061a840c1415000d4403042d100082c540d1001400d1030028103136540c284001e00c1408407859800700d81c000101000c55500340b4029440341c02201d1800d801880c81c010f49407542000da106d000007000142d01404917855103507800d54060443c00c54488080c4545507400030f240e0b80920824000d080120004c540b0307032a18020003130131a25115045020042e03100c1c1885105034650084d80c2c0f0b051002c490104125059921070001031038618800303540824148000552000d010000300b514908181c0c4460302c03804103602c0c03005001d4088404c940c022078482e00003592420107500350f03500940710f41000310f00c41082034000c40d00d000081d142074401d0200002e03421032000c00d1403615214000e40078134a03500c4102d82c5202600d036102d15610b20204840004078074542d02d124000c60002995218101e0804020420120b070007801c0900840014085481c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 726649955 1250 726648705 726648721
    0x60e130603050c130e030a200d080a02210f010f0f0e15011803030f0306080d0c1b09090b04050d050f070206090d08070f0506010501050a2a1502070506 66
    0x50201600d400200a1103682561020f1104048203071004d0259035559200c8002580403c0c002480e01e0300003aa640180c907400c0445c10842c01c0000000881c480c0e00250f0403030341043d008091254002503074000161124104049406188409050312500c0a040c07001c00c140507400f09000d0b0f0507034600c030070b00720358054841c10700c0d24500c4014000c00c0f0700c14541000140800b0782d0b10018044058061410aa140300c40643c2c88107441c410360001c50200f040307034048200143c0e041c41903100619103e0000d010000c00014081d0100c00c038180c0260032020780d10101d4505940c02904a8000d020742000ac0010381a24140b518401c1c00a940c1252140a00c1d0100468184030340c090382e05030038280440c6850181d10382d00300802039100c8a10a6001104100c0780ba0100d0b2141001d070030801c3c060303070a0044149040c40d0550401070305030080d50600005100c0400e98a03806498000c501b0702044620b01030b409030352800c1d115016041c100905001000030341c00c0e18002c094011700481ca22410464075180c4805030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 726651205 1250 726649955 726649961
    0x20c1c020109083103060c0e0405070f0e0402190527010801060e0a0b030c0a020709061a07140313090b0a060c080a1e090303090b070b04080c010f0204060e13 69
    0x58058071000044c0505100384001000424400104400c0342140701501c00082d8103a0348039501c02e440b0b8550700c0400d120540d070814008200c0403411101040346150800025141c88400001d42080000b00d03007507222203481d03c1d4100c2d10400074080110b00030901192004001d13230300809810300f08680900c40030548403c0c4004030b102c0c03882c058444110320380c01d04000310381c50427203d403100358495003031400091420342c04002180a901c1c9070000b80d580766542c040c083d14002003a4040030050380f50000030030a0000b0380c3c40600380c5408911129690340418140000005a642e422240c140400107403010f580c010b007080c15044854941017444003c184c0c0302000380226003807103008046149080d0400c0007816000c02400708060b1400c0554800c2100140c41c02d1a034801080100403070410361050040c50380203440c981c0240700c8014418a800e00c240e68500c1c880e6030242c0002c000940c00b1441100548003908103154100c44580704540312655088010311300b29219503883d004040b201202804442140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 726652455 1250 726651205 726651221
    0x30c02030115090b030709090b06190b0f1b0c030705040c03091e0b0c12060d0614040804290912150c19030b1f0e09010306050709060c03021504110301020c1c0201 71
    0x340c84100640c0d92b503403e2107034041416401e402500c0f031000c0081240b00c0700a002d01010412800d2031178582c40c03019490710301c182c8807082544041d404031585030096640001d40368143d07141560041030440c2c003004150090310307031020001d080150028600316108440545501c1c0140103103401c603c0c03521006030b042a81e04c03030601d10070308464203413000811a00789000344104040c81882c0000b0000b210303442d1002c201206442c110340b0744600107402c10880f8804140c800040001c5200c068800d6078212003510360313100e00640305006d403c01440f0904454000e02409000406440e08200c0c1442c01d100c850006902c85ca00000c1c24041e9802101806440b900c1004a8018007800c4c0e00d1440440002d00039a540d0480020000c01000c070415101a03164615414001d502c41c0c50045040e0800510151141d0041d80001040001b04040d07500440e0303000035a9558650300c0da00c984030b251541d043c1300581080c0050020742541c000504900300c01c1c00011450105200702c80c1c040001052804101e098601e90 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 726653705 1250 726652455 726652463
    0xb1b0307230403120315050a0501021905010b060a020f0105010e090a0b0a1b09030c0b090d0f08070f0b0901060602071d0606090307030807030210021303030c02030115090b03070909 79
    0x129000704104240034125044010300c10403681e007010b59950343c002c608103013200c0c40030000341c8514081005071083d82c0307050050603080b50030910807801e100000350384800c03ea1409a050500e40000d10a00c6020351080c041008094519952100742841c0603580303003200d12034001198602400050302843c2e091545010b5000d0201400c00003110f83c0303442d0103d600c064078070444284d07200900c400d4151102d0622407000301617113130480400d15504181b00607000315072225881400801001c00c00d0f07601c0140083c895684460100152501418030403560300a1000062003814209140b10034844000705d010700c03e001e000002e100c250340b036100c120b803951514401c03200c45011902d80840c0881189c8002940035201500301400d00c0c3c0500c0002e440c22186920039144208001100c005060b4148207800d10f00306541001c2d40b0303000e102180d80c91060700b10702c07010741000700103030025045540a402888a03041c180c0e80158250345c8410703900006120003c501c1c2d11a20400c040020060074070300400043c5900 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 726654955 1250 726653705 726653717
    0x10608060103091a2e080d0f0203040e0c09040b01020705060a054b0a0c2d0c2309040b040224131e1e0806040b1b0307 52
    0x200d000550140000c0103080301c0000000d003004080c1e01c88a89060f2051340e0340c96a2091303c2401c202c800e880354150380600640d4000c01101800b081070000f6012000d907010741342001c000321041d14224210701507500803a0f4020600d409102c11022200060064004101c400300006281c1c0801680c0e10311031441a41d41100303050001c018054020b80260000007079109070814440300501081c0010b44440005411850060103510600302d8605034000d003c4000e43d8102c0d14041803000702606002d01800000c0a8902c0801c44681e10044420108950101d0308517030b0108100515044001030028080c0001c1d9590b4416445003c02001e461200c10240141071040d44e5291500e590490000042081c2d07001900c030000042d21000b0243c403441101e401486131038a03408500e0b86084101000c0e8420413491201c0c41440100c26a1041d001d411200051720105010b00d620a5059602c041ca80c08440c590042800300818001e0343c900b003170700c180880b41c901c04151040001c00c01440c042942c5040000706 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 726656205 1250 726654955 726654961
    0x403060c1e0203030f0708062202030a06052e090b16050f1203060402090105041a040f0f0509161404080309090c070b0103080d1e09020906010302042709080309070617010608 76
    0x40a107e010f83c0080300176041c010341d09251086c01944102000009400960010420500074010712800014040c22283d08140b04600c0c00d0444250741a0030220200c0243c0b24035003099940112070380801414104003060310785051400c044159401d615050320640500f114445030b15034003240c25140c001284d0b888a003181c4401c410301c8000e4120382d00050500c0820070010175003030715050f1074003100c1400c0703555603036201e0400c3c1001002e050142e0010100c1e8082d00342c10310059a0711844180c0c4107204142119007030013174940490b0311040b00c2e00e500801240c0001c0110721240d000c0f000f84019002991401241d460300c0540e0480f620490390094542c14121005000041419000344040c078804003021030320003c0c0054016081c00103c0348141903540e100d10840450900c00042d6038480002d080450a040c6000704d000d0320810b440000d90360641010301c18004401d040d501043c2102d070048519916407401820041d500d00c01f5000f590089820b819400840d00c1d41d0f289518140d44440c1d039444003d031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 726657455 1250 726656205 726656207
    0x2304061d0303040b1605120711040f1e0e2506110102120a02030105010807170130030f0210091203050a0b0d2105040f14060403060c1e0203030f07 64
    0xc0854000c15500d0b0000300000a9070141207005803502c03604603500140c084009180261030401d00e0030754a12001d0b0b00b440180d010680280426032032100c19178000c00c4c0c0c0c180400c071910060245c22107406d4004503141a2003a80203039540020040d0f42418105c0d80456100b48100143c2004028000300305c103104003083c08000c2c850703540c0040e4072205400160403c0205181002040d404035004010301c0d85c0070004100a6a100e02d07003a400103028241601c604d0450040c401441c0814024a140f0300341803591945102104003c1c100c000c404801e030f04045807510b1800a00c9061100c1c00300006118089603454400203611880c0754083e4070440081c03a5070f4070940141c000c0c100c010f04c075980c42a942e076804c15440d01c640040c0040d05d0b00c034015003024242c40713041100340c507441c041c0e0200401000740710500240040148031010746c2c0e4080d042410201340107000560300d1080780c200500781418a009000343c1e030f402c41003800c0007902d1070741c641c0c5060054690890340d0b4042204e9140e082c1c0b0020000c52015 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 726658705 1250 726657455 726657497
    0x6020c011505060712050c010e10060e10271503030305011a2b0213030303050a0e0703080d1104062109110d02130c050d0e0f0a060506180403230406 65
    0x1005c0c43c18004e050100b420700080c00c6403084116074250750801142520750b48030510481015120004854041c0e040182a07500010750a00880c1207101c036203081150a40240d1140b07441c44c01581c0000c0c0031510901049100c007002034401180442d09240004c2110742940c280842840c0801f011a402c00760000300900c17a0304049601d2840d008003410051890001a000800400690a1001ea00c15245203002030460340c0090004550382d00c5e10f240251032140214042d4101d90b00480d00680307940310109001d000300f0400341c003440004000140042c0701034000b840301216a2a9a80c1042d515441821420544440d0740b0003d014a6000b40c10071501d00e011811005050700190000c0b120b07403800713a07604084594404441c0041800403544004060480c003a40d040d520a00c0060700c40f00070b0913040143d403504544402440c941c0c031500080c006888540b4801110124580c1151040c10241005050468005190443d01040f103110307004200105088400b101d1300350342c42445400703010780c10b200e0b1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 726659955 1250 726658705 726658733
    0x110301090b1311090c22080703020105090a0e090d031802010503071b060c031a0d03170406090219090506010e031c11010218010f080106081518010306020c0115050607 73
    0x504003c0301c0004140d07403500b90145124130301040d00d2642c2c036181010720300c060041c400e424180d2420244820f021110002c6111002c40782d080c20541c0d00d130000032001880401083e00300c0c4154055103410056008000185180d0180440c0c0f010008000302d1241c400e510701d01c000c07020b80030170341c2040891038241c407541e00c0c3c8003003404034502c1030161841540c60340e05458a00700050f001980f030784028140004042040524118200c54a01e0301012641d00900100c0c00300d03c055802c0b540141c001000e11049801960401e03500521109400410100058041900e4003078080703001d14010010360554001d820a00050000800600f011000c000041502e040000914020801c4030201c1c541d850009001030442c100c408950132010b403480780c0004001c10058030a113003c024000004001068004492540041c003000700d5920b05025000031805000c00f4801d060014925240004207020145c1c0c081c00001e80040024030004002e0301913100a02241e01070341c3c0e4400b00030400103000072000f000b1114 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 726661205 1250 726659955 726659963
    0x7030515090a09120207051504120b07050c03070501060306050c18130b1804030806060f0f07080f0304050c1e1305040204140106090302191202131116110301090b13 72
    0x143e9040c01d952038180403d0a030035103c01607405004184800e02d004d11002403d0002c2807286803c1a1034110902c01e01a840b543c0507101c966040d01040415100e04111001c011004007226610281807401320b008001c54402507071440c0c5080045240404680c0480f03503100e01c440b0881044072424020040409200c82c142340c0815614081c41d4684e450f8000034001c0103910200045a601d01400d000d840750000414042c0f08241c1040b031a68190b001c07209031484d5490000c0c806885280c5485c09140c81d1040640a003058a4088108001c00c40b00050405c8440000d8407035100c0261015111014100700f440c0703841d4808562400e00050761016440745a109000500101319038100401024214a0a030804400201212010710a40c1404a0302005403100c03500c460341c81a1400c0404964800c8a000080c131031051110012150030b660740010052074503100c0a6aa511800f1080b9040401191401c56195450862400f03103490103105041c01030350058010380301d541d200d40030070441c4540310600311 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 726662455 1250 726661205 726661211
    0x503030a08090c0d0b160c150513170915090a090510030c06200601050906280906180903021e240406050604110901030c050903012307030515090a 64
    0x1000f00e54814590810043c0a02454030f5582461950b200902d090070010b6024032131015110800a5503103031494000700c03802e850000701525160009808180b2a560140194141205081310000780c03500a1158403401c0316822080400388281d01d50300d0042101c0e1a50100154400700080303140c82d0021540b00009484c070002d0144c0b00e60381c00c041c02c04281c002e800010703880c4505580c00000c50700c21104001405c00248a151301d450b0020303400ca00c008091501401902144601a0440c01e41d6081215030001c1d01c0c0b860a901c5070840c1c8018011803203580b810404801614441058602c00c1c5190f683d0544d02070034180c4802c0d1050101003500b008002142c0c03280c0d9001040006040320b8204c0100c0140b40c164805003040d041c100c0c243d0700e018008902c0f4034500354003040c600d0668000ca0700d03010310a0070003040300c12940509030340600a2200c00b54055081c81511080030481c1025128580b10340c0340c0d42c415680703e41508034200c5504a42c1c8482080369110201c80038500b000e0441c2d442140d8aa000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 726663705 1250 726662455 726662473
    0xf012405070c141908030901110c0d050c130908040e1b03040503090f041b0e0103091a0916060806061b03070c0906120203060a0906140906070f090503030a0809 70
    0xb011240b01d10750f200007040016400441c5092901d0408542c0300690b10103e00207041c00d084050703859210314101c0034140001c4a140b0781d0700400c00d020110004400030180d00341c980250500d540ca48001d1f220303280c86202c0601904070b50200a1003400c90158110800504107407c00d41c0400060b81d0242c4807401141d00702d00384101c1124004011407080d0702c01d0000d1601d505185050262500d05014010711980c180040c0414102c56105030b508400e0041c500050f40480c00001070380100340162000d031441700070302c08a050b0160000c0003070b03000716100b000b11501103207040d0344201480302034059136001401d036001117200352a00e80050f1440c0b501d68840002c40e00582894685560721603031084415411030700082040d5100351103a14020301a00500d000c0d844210780c00a44c40e03020041400c90f60f159541c41c08010b0081c958400715070541e0110030040c0d02d040001101e513540000700c0e02c0300c0005010a107000300c114800e44891045820180045003800ca04e03490944e407410303004012a40c944102c1c0b140c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 726664955 1250 726663705 726663713
    0xd0c0512040515010609141509030f1f18081e0d15090b30010920100c0308090c0604060f080f01030c030b07031b0509090f01240507 58
    0x35403801140328200909200864500a07041010141d009405214000c2001c12610880d10130402c000a000c440f100c2005450b039841c0089805600d041d2030305841360212103d40a400040d4048070304000d9000788074041041d800c6001503421301c0704603441400500f0010000070304000d000c3e0400b00c000d648480618400e6900a81c0c5030b400c0751200948140c3c03581c0702e0b440000340c00c0700b8041c041c2c100c1e10001d00881d10b8035804201b15249200d503084920103100b042c001c580d80c1200d4030900704072084009102d4665036042c42c105403001c2e941410507100030074134250094540500c1400d01e0540b1034580080c001c0d400d803001c2c0c0d5041e8000700b0966103401090388400d1141e4070f8a0040001d40903035161320000c2640300000401c20040203059400e030300006801840070804504120045951142100d5000c3d41c0d0040c003103016100c0c002802c81a0300900745581d00094016014114001c02070350203150b2580d0321820310517502c03000e2060221103078649007035421f00349004802e5000207140e428414541600c03566 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 726666205 1250 726664955 726664987
    0x105071e0b0712060b040b07061805060708010806090c04020f12280b032d160e09010902010f0509031e0601150206041110031409060901050a0c02030d0c05 68
    0x30865080e03800c041081001070308001c03030741c20404003000e0400c581428940e810301c05101c3c45c09100301c0108042900c508010182d00306441c58110081d41100801076441c21641d40c01f030690f00700002c40d041000100c1d600300005000c038424028000200412000032052000940c0700c185c2c2c0100341071080000c0d10950100790700550103060740041c0748810407134503e40c010188803241d0703024541c2410110b417043c5a940008103018640c4a0300c0c200d078054503909400c07038103090458180c4031030360060074282c16a952499494008540e5080b501d0344d200e80d00c0c005c5d914201e410b840c40083c0807074800c2e50500340d114410f0000d0714046001408640301101ca06c00201410701c81403c00d00c090383d1000005000034034908503000452807080c00181810b04195440c5081d5050205405001c0c140e6110820100c61003500101083c003a0445041e8842c100381900e0780c0c44600464081c0f45a60a00012440c52481740c0b1a00300c05032051342c0070350306021014070140301500b04c100002080110a00c40c9100c0000400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 726667455 1250 726666205 726666263
    0x60109080a120c06091e060f0c0804140a050d05070219061d030717061e010602060a0203090106150c050609070f03061e020a021b01020c101815030b0a050d0f02010507 73
    0x24401c000101c0651a0447c2a0b130700030815400c0341c9040c0f401450780070fa0055880ca41240d0301c6115114100d05ca04511490000782e038501038217520030051400e90154004004041c00740c000d498201070281004003404c009462849403400149100c0d07001101c9201d51000720207013803401410342d81d000ea038070180c880500a02d02103c02e2079801a47c00d10809402c1301c02c21340025130240c900b481c0f1a615091010703448000040642c4002600040001e91a00080d8010b0000d0820400e03411454040d00d10000d19411803190f040f03c1340d01c1030700c0100e4041c90b4001011021075194040c1400142e0a541d1080041c0c110070419403e088580a006058031180340058200d0031f07101e50040c00e82c00200c0c503900280b60b111705441d80c150f4222001507016a21420180b9144244034144607160201c42504d0210403051580401010800140800a1941c1c140c0201c1901a801c07160507589030b854204028450300c00d07500041075900301020340f1005501490161101038021441448003c1e8940c01045c0614490 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 726668705 1250 726667455 726667493
    0xb070c03270513140114010503180102041a03061212031f030204020f27030604030309140a0c0f050105210408040e0c040501410c100203060109080a120c0609 69
    0x13070001080400d03040d0304260042200c9414052070200c00c0c80040c2083c8005803900d40501d1840a40410055007501210020401d00c40c8514610052100260103a0000d0b0340541c0325804911040b48010b0000941207042ca407111096451a11400b003a89404800d0015605007131216140010160307446102070520589090280c0d65245085101e000c02640c01e042c00f84410301000380300c40050b840c0020450f501641c03500f0001058110703030802c0000a5070b03240b00d0142c6031080d25102c00400c40703480107401c00c5603000341041c103440341c9a40064940f4081d020022429818110340402d51006228089401600480035030b880c068540881c4840304c5011a14401d6071440090100940e583c084003000340c41d5100d22241d0b215083d810380d40e0014103c200991801e1144070070028460b400600100d0380d500100f041203c070b0010072009500041e400441e091408900300f03c42c002212078011440c618001c2d4402c4101e16240c04000e801d0311007082854007994002c2d07a0340e1203600084c0c00078681000081d89 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 726669955 1250 726668705 726668711
    0x6271c031e03092004180c050f040204150f201525030911060703050d0b01032403050d0509010210020d09060207050303091b0d2004180b070c03270513 66
    0x860140000d41b8000083c042d42c45c0b219560340c4010580b0b01440c40140c2d6811550300c10000841400a0085e0056802c5213aa85503445000515a900030312094100304213502c0e44180d07034440000d0503404048201c0c41000d65000102c030b510301c1119a00400d5404002944115412200818011f00040403c440c040c0442c1d501e990980501c0318200295246c0d500480d0301038a0b1103181e6900501e280651000705003615101c10f201d0226a0098100840114001460b0449c0200800c642e076120641880252242d0103143e449400c1c0307a1243e011075907c1e80040c0c000340030307075400103000200a50101c07080e007010541d60702c4c0c2d41d0000340d052b000505010380035400841c0c980c20880b00c403a0500c004030189524031031100c0f030402c005440d110f815003020360300f04024003040700032420310801c072921840c540c50703006190428402203c0101d0901d1005580920010b0701196984d140690706000e040e030f030140c0070034040407140548100701c001007074404804420171582c050761036000c184074594500f407a01209031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 726671205 1250 726669955 726670013
    0xb09011b1709190201050a12022b060311060307020f03071505091f0c2604030210050c0301170a0609060c020c0f0604090b06271c031e0309 61
    0x341c400580c0340c002401e080078080b40d10714050f0031108031151800080c140711022440890160007042c6207040f100f40c0c40404d540d58500803030041c54000115a9100e00711f5050b160701c184a56aa00c00c0c4801c0d241d03c040e4103105c1c83d106104200464000034000c0e8114420302651004025050001e482d48611030509031031902240401c2d40140e450042c0814881c1d400324901c405c0f0084108100d0b54616100d4400159100704881d0843d220a0601e840e0a581c0c01c032200100c0c0040040030419101d14002d0b800d441c240f2443c105801b0980d003040d510441c0c100700500041c49405115420b81e840704014804641c3c0341c810700c0d0f81e000161a4100b03000c0d40c0a5950b100741c0c01c0490307014080340e00b0807941143c80d0012210307403100081145c0203500481d0b00559560381c00071480d0301c0d001c040f03c40715008900001c0e03001c40305c550b1034112040500c90710f138029407a04102e0320095421041c4c2c803810751780c10380303426500003e10a800308100d00a500701f0f004040c1c40d81d0041c000b181861080006140c0300e121003000c085 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 726672455 1250 726671205 726671237
    0x3100f030f030e090708011e051c05010b030d1d040b13050703051008030409200c0106030c0b1204170f1602030607111b01030209090708040309050406080a0b09011b 72
    0x200042c0f910303a0181d102c11080114103a80000c1090640303040042021302c0c104d0340b100d0510b584103ea00100d822064807084880480d6581224001e0544104000e0140e24001c1080c5922907290300c0c400381c08924642001c04d44008982009034903500b02a100040c5c0e0508100003508000a031900700380c100e41d607a400e00c032100360704d400380c284d2000e10701010024070b92a04400503664480c61003034481569a8580030140706644c10711206116a020038102e80301e11140703d842d07008041c284011070381c0d4400c1e03038030010f0214504015a00c0b5a103d80b107800c41690390b641c40e010490b0000b80c4900c0c00899082025181c0154900301400606071003484c3c0d400012505e00c140751400801800041c180569001074581c00e40e40002c0f40c003162007940d4415400c0980203401a40030b0b00901c239025a004042a0400c01c5040d03000c0003d0b80305030301070740e02c2400381583d0780244003c83d200b50081890b580c2000c24500c011030842001580c020681c0000019501c0392010b0021800d5589021000010b141010707000c070352 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 726673705 1250 726672455 726672467
    0x72102180f0405270703080a090e0105042007051006080114010e04020609100e03060705031609080303150f03030d06063f020714030a1209021503100f030f03 69
    0x3071001d403002c12040c1009542e0000f0f040d54a510700032041c80380d0001460440080c42204000c50f8030400294803200d01c2240079003081031a01880c900450a40000121490b040c02034103090030307200040c441103001c0f06404d0a100e074042c01c000d890620584070012a410b9041c4110303c0148a018000101a801018036204040c0113a1080c8800c044141c148009030b0354a0381180d0a1420441d95180d03407990501c03058480701520084540e00d40910401c014031641c106e4021881070311005101b401c0d410001c0010360700c104203805131414584c03081c0300055142d41c441d000c1208450005004030301c110207050000c2d207194011040710440135103401e410016035401001748010300d0b40c40d43c50544078424042104151500410036007101ca006072309041480d42690703045503025501f1009035400030381a681d11079a2580180f505000191000070560b00e180c01e03501ca2200d0300e5038003d21802d10312140303d50010054002030502000040500000115480d40c244200e0081d8403400c65050102900c0c00c015080d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 726674955 1250 726673705 726673729
    0x12c011404020612042102011a030a15020306221521030305150d03020105010602160303020c04050705160309061e050702040504150e0303060306160807210218 70
    0x1900c429506000040e40c3c0c280980b4450748044520000680c0c03181030990b0007104540b91880001d81e80c094418606a06421414207034014510003040d104102c000d0555403160f00b0310142c6044030f20b850b1040c410400da0001d40c1c005100520040194400a4246000006007620301104030f0742d4404244101140d1501c100046c002036080207004d1403100300b46d0881e501d01d00002030406551b007000515202411540b18101741c006420210040054034001e13000300420701821007d8413911880091021014041c8001d030ba0780b65014015100050062001901c40604203d05020b810b0142d207110320413a2143c140550b011340e0324207902030715143c0068580b00443d01b141a0b00b9403030f810084a03c5420500726042c5c2031f41941c0001c0e8035505d9041c0a800480180d0400b004141006800c0c0e1204078000081c50041c001201036402540f20a048815540700303601c1d4101c0841c0800c0e000a450500924048203403078400c1403144525440800c0c084100c0c0e000354030315a142010400502038500b448903150030303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 726676205 1250 726674955 726674981
    0x110f0105010617310c080115091a091911040308040e100b131707051507030504091b030b12120702060c0f0a050f0109030c02010809012c01 61
    0xa650421000400e01201d19000b00800f072150000304826464000c07940068002500000d0490000019001c001070b44040007524203014180c000310700110180b14a141001503404195001441c00480401030809a141e00304420000345009003e512000d03a901e104600a0061840b0f800004001d1b80850340072400404d0294814002400010301441c01c480c142c81603c1d030307a1a0180e07200c0b031881f150580d07240c11100700e802010500e000380c03008a0010b05c050b25003008448404c88041d410007513480c2d10904c070300c80c0d01404108100c00c091510000130201c481c02480d282d45403540f581d01290a440c40303584050410000b8240000d000d039418419a80210422145084c1660f0301c01d031481e070354240d500c510088220000801d0400c650b21582243c0c1c500c655141030341d030b001f50300b01851902d03500e20700c00c03e0b00d0500840c8102c00c3d00d040c061240b40b2600b070781900c903011780b00d0464004540e40c40f00146100950f42d80c5401c0b8401451000312129024141d0104a0707000c000814850303801e42e00b1a0101d40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 726677455 1250 726676205 726676211
    0x60806010b0c07180e0a031d0118031101120614100f0e1e30070e0f06131a03070915030f1a0f04051b0f091b0a110f01 52
    0x60b4410100748001160801303519003100490900e01c20f0018601340c0c450301d406100b00380c03400c000c250300080c1e02d47e0701c07446500b140240c0600003070044d60300645058214519110000c010710000355a40502941840c041c5410940c0d8035481603c8800c0b581140c2080000200c807070418040f6180c10b044a0b80d5159440c5000980c14200741c1c4082c108084000d15140700707925110000030319004e4410a4181d9000040c10300b034211821900c0c01e122080612012490201902c04400c0c56200001e010b000301c1704054060242c1d50340325100c8400c0084060076842e84040f421400603042c0b1114020000307944c02e5103901d2150a0400003c02d4901003a0798440e4401a0820b51000e08901e43c2d0038907901101d400103000400001c1e94548010181c01e10307440000403c0c165018400c0c0c0d000e2b001841d42c8204c0c829800c86c1c2d840e0340820603800b00c81404c0c9039035a0f884815034407800e48a080c04030030950070010b2a22160300241c11603400c808144c001030722080019041109101c11000200241e10700b01c054030000b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 726678705 1250 726677455 726677467
    0x9030c0c4101030506061611120706050703030915140603250b0d02070c08070911040b04090b0a032103150602191a01060e0103050f0f150a1206060806010b 68
    0x101030341c03a4103110607a0615654000041854554408035840a10b850980010380440e0b49045100340c4185200b403402303505090f2203540c451500040580646006486142c2010f06a581c00c4002e85035884085600751442240540f2003002c9010741c5140d540a08424860352606070140f41c50000040c00444500655050320003819010300d00007815140042600781c1d45214020350900070303106221006241c0d5036032802c00155004049140c1060710000c400600c190492156030f10503a020341d0040294411003040100008a217583c0440a0040007500d109000c50b521b403039203982140a80300361005110740c4481c68000680c1881804403003565440c1241500b81004c1000b5512904803030300070410b1064100c00024084821020034010320805c9001505684501c0c2c020011400d01e080c86000c64107040c00b0507d01c040340b000340d138400c008010048080e81c2d2a6511410140f80c030443ea00c0c1c000022590110f12500c40711400403445024000100311301d840c003522549032000592000c0400e400501003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 726679955 1250 726678705 726678809
    0xb0105010f08041113110703021c032922020307091a1603020715021501170a02130e100b1c05030708030727091506021009030c0c 57
    0x621900910283c03070281035085c0ca101560002c02c101c502d01d001c82d040c0401c05804050780002e41007408031a880d01c0101603400d012095081d01d8001000030020302d0900501e40184c2e01d116401707000024020505660920b00304030841c050660b40c0100b003c400e030000200040c107074000800074000c141000782440303014240301200800b4000c491210a400c50000c20003c1414403c0207007801528507040d54500c01880ca0902a584161754040d00c070444440c00000036042c0c0a90b11301066241050001e0181410560300f00f00d91a45c03002c106050403170ba1811381413205a420400c414a44103030b601d0000e120312000c01000134040d444248008000030b05180140080e6004c4140e0341003e5200003c00e0316a101d6140503510f0b003900212b020800d518a02c5000c1d0441c8510711500203c4030307086010803c00407600103080e00c0313030f403036015510141c0d225080f41030a8581541c061040103020b890b20200c90306050342d40e5001c07041d49a00540c04124000100003105032000c0101610303e064041690707800201c080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 726681205 1250 726679955 726679973
    0x1051317030c0403020a0b0909070c0b070818120301081905031e1b0c18011d0a0e010207140d1704110301090b0c0c0c0d0b011505090604030b0105010f0804 68
    0x16449460180070000c608030000d01015140076603402000d010f07400d512400c0c00e60480d000842024411002c46c4041004180101184510650080305088081e41c0d903c00076102c04c00301404a200034104003100d65100d440500c20060329103082c210f81d1f0703561b514085005103011103000400330314042908280300011000011940802d440e214100304d0340412000065040c01140501100b00c01c00c0080e801980502182c1c400c0102401c80d01c0441c0200d9007004d01d0b4130100240100c0045c01d007100300c4c81c20a5500319880c01c1d40700d005808041340c40498510703c2c5007a604411411a4070050310080c1809008050242c13400d580e01c00c0c40c084c0f100c1b450040080c075291801400151000000320402c2c08943c40a40100c00d5090304013035004114240f446062107180c3c04070402091501a14020b4201480c1040c10050381e183c0180f41061035900b0903040c1e22502d500300350000d0920200304074400d1a505d546000d80b000314003c0e15a5007603076141100241042114860750380c10401054100000100110 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 726682455 1250 726681205 726681233
    0x200106080c041b080901091208010303230a11031306080103050607031119020327040b0306190e0a0f0602120108010506011d06090406030b04111f14040e070e0102010513 74
    0x215025001782c84038040e4500519948101419140d00a12140702182c1c00451482c1200d02ca5600c10641d440e41c00303001e03400c0c2554040802d480c00380070091011224460300710814604280016a40351601908120710000050741c40390002c100c045004006204090081079800341407410b082c00110090700351000c0307620480300d141101c10001a00200700f18400c0041d9100c4070721841c228003041401c51000200b01020205c414459030611511103017609000c910310740229203c01051800d00320013140400a0710309010009039500c5450089000300b801d200c24618007a01545c0c0040c2da51155404141c0e0246050300140d25030781c140014001d80780d901441000c0b8480081a50310191842a40007403058810459900e0f40541480343c04070078403009412081c0100c4c814072050703100488440c1480341c40355501d6604000300d8802c0d202e490141b80155a81c6884850414a81c0e10f03003034684030300405203032080c0d401d24002281300342001c2065070240300300e5403c904150082e0f061a0801c0c1d8a014206c0714107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 726683705 1250 726682455 726682457
    0x40611070b010e0a1d010504020f01030902060d052508060310050906070f090b0d020d0b1c15020403021c0303150b0a18120b0a0c08010e040210200106080c041b 70
    0x84000540a503115442007042c4940a42017040241e00810414080c140c00c0d14103901c50ba030070141c0c5204640c0030f48210202558045c042500b4100703100005002000000c0039100786100441e840d4003208007ca091304c0210b0074a0301c811150317060039420300d8540700c902c1d50301c65500352401c0d083c440758141c0010b100e03a1200c002e1400d20340c040c003040e0084409a00561000383e001b600428079800e0703061140c0250100151008c07082040c00201810071400a501183c100c06244c15407a0003004140b02c01c43c541e010f000802000340c0303015030343e901182c048220070320512480000603094100705036160050351000603451171030806041c00d00481d5202403042c0745070a8140901d550301010f9220100c0c582900801c2d894100851022450600020f4100200c5a02100c503141a03102800540211201030507140d1800600826a5840d802c4c016401c801104030020300004007440c0c1080c0750445000700c80100392038004207090749410002858001441c086620590901d6520b0300400341000c020380095441e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 726684955 1250 726683705 726683729
    0xa080606070201180803040e0903040e070c0602160308150103090b1501090803310807060507021c050304150e060307031806020f040609080a0b06060a090518040611070b01 75
    0x902d10041e00c002c9440c0305404042031043c00c000072080070110103441200c60394194a80c05942e850310854a920035805150403a660388004205c00c0e034411404544c00900c102401480c0500440e2070044d1500720344e80440004161108102030300c0c02c1140f00f41402c1c1c1c002e003024030200c41c155031900700014000b084001c90720b03d4280250074603881076450b10000c260315826241d0f00c0400f400c40c4800c542d1106c41103048105020030003202e0b0000300c51641d0803180d2610103040d8981c00c1040484150f402040e0503a80020f0801100c1402980c01144d0315580d840741d0700850303076103150072400700b028107007840d03811309001c00310f030149000c0c0e15018103c7c2d5220710f1601c2d00182a000015074072000201406002d4001840802c0c0c05002065540007003042d20f03142e440f454146d0380da070b030407841d681d04c10000c0040c4082c6080010400c10b081507401b07480c400155040c54424692604081200120301224190211840606100a10040e4031680d0000551042d081c0d02d000466140d40f843c100062080c1c0882d162 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 726686205 1250 726684955 726684967
    0x90c05040209030109080c030702091008030304150b130f0507181e12080408011d03120601090504110405042403080706140109141f06050f0d020f030406050c0a080606 73
    0x9020740c805c000303144e0b0002c43d007a200c0054103402c0f03a8a40010f04100c0c010f00c040d07808201e541b07400c81586012070308030300c1c011407455542d0f5403038000150300f0700d182e080401d448406520403590b8004401d1400125070300c00043e21003104424200703444010305a0814004246a4504590320815000058848900304102000b50f500c2d155800c0a03480d0f44802c140d84801c00c204800c21648000400807141d0800c0240000c0403458403082c80c031201d4400c40c9402c6d6004200301c0c0ca00007082d0142da903011a0504000c510300d81e80703034082003e41e46440300c03084e501c4a0001d001c0c0000c1c0303880c1c40362442c03044460008100301d600d0107442204074140c501001c0d05050f400300306c600400c011a00440d0402d60a040050030b1948d50f00080070142030480d1074100e110700750400046526800710036198154000748000c02c1e603107280c40ca0035507641d07210602001002004002025030034155000a21440c00c01e10051a039914060800000f190340c0a006041552401c00241200700d50001d1090342003681161050380d900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 726687455 1250 726686205 726686209
    0x507020d050c0913050d0305070813020d0c27020309031e07230606010e01050d110c010608150c09010e061c0507020d020f16060c030207031403091003090c05040209 72
    0x40307400341601ea40060304030300300301c022296407903900c013401d11407000c82d440011a04d006a041d070f40c04075a0f50000a10500010f01e40b21034138040445224005031012405160340c0e2a6040071420f19000546d020702d000703180900f030300590141003099200b0740e0011402c1d400c0840469490740b21303031010300f20b1064442c82d4101c2070440c2c5004494000e5800344a40a02d05420780d45003850408203080c80705680181070010b500b6501030740e2040403d580503540d02d498109103614a0000780008511711294140038000d03800480e009100b158042c020510052010800610904202d00401070240c6030101c1c4c280045610f45c1d8202004401c014411104a9102c16001c1030406215000241501402e4101000e000e1465000b00c0c942c43e20b20515404c0d906000701103600180d44020b0504443c00b8114243e000700701c018415042e010307406d8400d10658070b500d84d4903112010000481d07480741e2052303000018900c0842c40c20700c1c2e640008a0b03283c10103009161064131070308080b41a6104140c041c640018031250701e5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 726688705 1250 726687455 726687463
    0x40203040318030615050102031305060c0f12040509161202030c07021306060206070c05030403020f18040506070e0909191704060503010905010f03020907050d290a14010507020d05 79
    0x4400c100c0d0040c2c4003030741c0c900300000500300400308440541801400481e85510110403545000c0c1290702d0404102d01d800c080c000700e54000007001f82136010b04c0e250601c2024040c45501001c1c0b4504948030307103a50a05041200c0031f03401815464500d07860b811141082a00b00803c4000310400d1480140c030f903541c0c1c041c210311510603401c000394002c2812003001e100f8a036560080080e941c1581c04c0355070a5a809900351000c43d10558003808a81c01400100f00500d42403e00c40b50924000d4180c0300b10281228101d25821001d035402c845982100c0204888142d0103400c0c41c03220082150138107041d05002408680f21140000801c81d00207588851500740b10040140210000401454035034583d40d94134000d05981082c00307000c0f600c1c1d04002c00003408101100e4000e0030340750000c00101c02e94880d000107440d140d0106843c40451600d038821280007800c000359625041e4403403c0e1402ca9158600200a412801604039400700c0303d0b05000705c45541d0b805026906101d905980c90050075805042c00c0b454 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 726689955 1250 726688705 726688727
    0x1425380402010e0d0302060915100308030901200d05250305090a05030c010c1b080913061503050402121b1009080706050703110a0b060105031807091508070e060402030403 75
    0x2c801d00c50004c8041640c0001e2041c4184c0c411005d6411000c4183e0b41c0402c3c440b801e0307480102141c1401814404100920019904501820000500b121503801c6090410b44444030300c1d41d07100c03404664107001c43c04500501d54002c0350110a4031454010b103031002000c2011480c12010580e44200084503200c0170480b11f482a90008103c036264600c17001c1890280c80048482800100c81c1d20302030402042560141a07404e500c000082e00300200c0c0b030180b0606600101c448010a07071a03603400500105040d0684011400c40d640100350392500b801440380a03044102606919032140600f0301e03110f0300b116040800040110b54030a40d140748450211400303200d0350080310860281441c0021f045402400401c800c80c82074503049550030a00b403075252541e0341c5510241842076440d0000300e01b90722400095a105903440d260949050140141c60724021054101e0041c00740d44201031010008600b0900000307090b0103004140c443e0a2804e01d01c01c500024001c1405260080302080c00c141c020600622 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 726691205 1250 726689955 726689959
    0x40305070203061008210703111c0f0807050903070306110c0f0d090602030a02060622020705100e0102270f1801180c0c02011425380402010e 62
    0x10941400c00741184c15220390b2203190014818050354460107801008010040a080d150b0704e070411010351820398400344e150001d81d00b20300a01c12400001c404840185204405580e40d5001c0040d6110000e09020005001c0100f03220050085200c3e90b540020003000740c0390301100c08140091450380380340490251000d085994050104c00c403500304400a6400c4111704c1c50340e610540c2c03e03515041030380c5034802d20080000580101000862909004810111150042092401480e00c0c0d40184080342c100d11f20445494100303c16003182800503004044d90303407000c01c00843c58400d0b41d40c030651880030720b281945180c4a541541444554504125484000b4094411380c80c84800003a4404140c809016610407502c0c0c1c0c0ea0580e204c1c0503035210350b05a400d010740f41d2001e000c50503001599410031600701c000130020104580d510341c849c0014038900d02d890200c0d0043d00e04010345491407520b800710000000c81415000000250f80c411800002450004580b014403910341c0d00040f2217031044148a19 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 726692455 1250 726691205 726691213
    0x2a16030b040c0e070512190207151d03070209041103060403020303010608100302090105062b09020f03031306080910020a0806030d0c0b06040f060f090207020307090c0503040b040305070203 83
    0x410311408a0480344540d1240c2040c031000342d1504464141e80e6010b80d40306002440900240c29841828190543c05c148485aa201900782404001c42039a1100804413030b81900e049842a0622940c0a482220128a80e50030340100d81c8101c0c640c4d40c1d018a00307002c2e1040e4060313004141484a08011000704c0c0701c0150a841c1c50f46050700703029549900030f11507080021410400207003901061020703003061340c0d401402c00740184d00c0c3c68100401a00202c4494511010b4090324940b0325840392828580403c3d80100804d407820305004100801075011621406500100f00c42c6403c89144d14410096583c981040d1180740c0300c41c00c1785460301d05e0000c050050144009545045d903070f00300e80124410300048cc119049854420300444980d001940001c04821016001c01d09500d059081110418142100041c80c0c0b913803242042e07483c940350781c00300340080e034005500030a40c141801a400503168008040c8412a0701e80c41c000c103240310080020703204200110210301050322880481d118a60024111 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 726693705 1250 726692455 726692459
    0xb0406051005071205030c2b092a21080c06040f02130b031f150f032a0306021b0307060f0506010c080d090203011b08070201112a16 58
    0x2400ca0b50000b0404d850041507a2030840072a0710910459200390031008000d82000381c1c42481010890081d6598030113100540c003840c0180046108130001140a1002e2441b6404912104044510340c01a101c0c25600ca6080901c01c5070804840c10303004c0702ca072180e46060908030f400d10101e103005461000302c3c0d40c01070805100a100f00c0062030f04101d4021162400d81034428210002203409203c04141c0607003050aa5040391000c1b8444c5107014002444003151303500501802c502c0204190300000d4540000c00400c0c4240031408030900c14011071b00d10002c024800300480240341000500c001414660000340b1840c42114000d01c076200300b00c400b403c49848000f00d02c1e1500160400c1112094000d10f044c0c006200c541c480c059284a19401a03906454201108540c2000e8148040c3c02c0e41c1641d00c4401010f000c0212040031000c5c441e2a81e541e80450502007002420341d803031501c5501c9201824850720704003905807610076507000c40f40442070f4102c00740c40c120f4034105a07200b540740c00703d98804840 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 726694955 1250 726693705 726693707
    0x6030a081902030c0d110d0512040204050a0f110c300c0a0c080615031f020306040b120a050c0f010f030222120b060603040f0f1e120f0206190b04060510 67
    0x86c1ca04c0f40c580c0e80c0261266002c1041c4203c1e100d010741181031041c030056501060160170b1a612240c2c0183e00340170003240390386202d0401000e441408400e20020200042d04081d1903006028224608910710340340500030104008211aa02c4112103804011701c1c001810325407000200555030900c0e500000c0c40c1c2c441d943e203c640544540044486800034004991880514900450354104643c02240c420a107101d1075040d5100942008120b250401e80d2a20103d40320782c0c3d10b540592024010300001c0c0084607407441c2507400c002031564554001c0c02c6921401503140e0700180c06503842160b0b8640140c40b51b02d041ca405092034550b0b89407103c9003060150109204620162000d00c0c240030b4405092180ca480f4107112580c4408c407005411400f030300b100000080c0031009064a550b00585844030442c00710250484c1d84001d4200440311681d0202000403003503088000980103181500141c51a4030740044040c0d02e075286000a5584a95140206401a034403a44241c0c050840580b0a403101c0420383c030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 726696205 1250 726694955 726694967
    0x9061218060720070f091a0d12120504020607080f070c08060601030c080f04020103111e0304020907021f0b0409230c10020705090a09151406030a081902030c0d 70
    0x414000d8040104034543c00c1c0002c40b84200c80c40102580d03203907850104803030020140c0940c0001c04a1400e90303102038603036802031a80010b40c09406019621485001c01414110a00c1d8078031110710705100030440907944d40821394542039002600700ba62854008022011032098550003040c2449903c00030611500c0016003e1080000781c8082000b6840400b0641e030642040f2440381880080e0000940154801d07042880c1c1030004108880c10034401c6494008451249103c02040100202c104819441e1210100350804490b002508a4410400c1501061800c18034050310003074407003248001a81700c43d400b001859800c42052142c1408003044e100000620b44044500c40c803824420950a14001010400115180d0020020baa241206100758144000c1c4a000c2c01540d56420034040752100c0714201d030f0103201180000300c0c03014002d060050341c08040d01490280c0d000614a40c009951181102c51b1305c40c0e4180106000c1d1800041280b4520400203400d049000d10822805601c1d0080 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 726697455 1250 726696205 726696227
    0xd0c1b03062c0a050a02060a14040801020a090b0306060711060d090f020a06020c06070b0901020409090501020d050106030606090909083c030c180a090c0504060e0402090612180607 79
    0x46440d18060001d40b600c5a500c060fa0380c005000da0300900e4070130b40113240810090070100c2c001d080c04003034800502d803d50200d42166002d460240d40004d0a991000d81c00702c00340c07015010301e000e01c900750704014022a0b014003035290008c055503010420703004243e070340e1000c0d10400c80350940140040310443c81d08070010382d02d000080780291001ca001065444c00851600c103c01d070040c09190908000d6114010712403400b800056055500f0030010900125a00070980654001c000250b41c650511000d181100c0e0141c1c880e108252034150144101a400101441158070703103000070624841c5400c4c8481a07100300070a500700f8109402449003900b4115030029400100c51340c50b00310700c03c0518003000041c4012070708408498402c001c0800300b9030040700c0052100318041c106490441d00e680c076181c2101c41d4075103158041a07000c00d080107115070140b000c0105c881d0030744055041c0b00700e044c081501400740c441d9422100c10000f0016840da0100d4007e0003540c0f0760ba508030b070f60740d0070300308806000b0010072 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 726698705 1250 726697455 726697511
    0x19050907031a06030606150702190302100f0807050714030d0b10050304021507061503051606020a02031216060906061404050405071e030b24030d0c1b0306 68
    0x81a407154000c1c44405010f02c00c041c050080c00346a0388001c100300f20030100325840d07203040c4803d01400c80962585410347c04000c924400244c0064114010000814445108c01003000090444c0c2c190042c1e000c00c0701c1d900900d0f10b007003498585a0618011200c070100c6004803a207440045103c007a4035405401103c0414010788003d002c040f290305003180c0520040301c002e50040013400390702c1e01402100004012090007654005a00801c40c1101c0c1d40007003c50b403040e1a0703680002e401ca291410740301103203001409a4001808822020b5011079115640006c810940da2404a2640b42c40c0768a004070740091070740400100450805440d02d00000c113200d000301d082c45c010922a0140700e04152281600031900f240c01840214500304850080040c024940d604680383c2d0b500c0000055144028a805240d1144640544452050b02c023211802c0700c45c0194070070351141d9610010960000500c040d2240c0115500d0840b000040f0304001d080c0301548002c02036440c0c40070700764400e0609e281109143e008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 726699955 1250 726698705 726698723
    0x301240f0e01080706050d1407030506030f0a0b0402131401060c03080a0501030b13062d14160e01020304050d08070b0708060303180f0a030b090606010c08121905090703 74
    0x955581c0e6980007403d0003a40c0c42d5078071510f800d001e0b813405400580030b0620384600c04240703000305005802c0061302c191602d4000c20340b11024400781e403030240440440142c015000b06a05401c0d515101d51000c1d01602c0a80103402c41074114003640700c250010f000c000019261201d0a503910380f001030600001e504142c00184160303001c55015005402194100c2c3d403c05110400768480e965520100e50194400701d40c807035902c0b865483c4103881d048055101008401907065114100100d841c19552080c080303a141700c180c0380400c040040015046032018104e458001d598800e0b0b000103030314503c41c40d00140d50200300390708500e00b00003200c001054142d110705a84c1c00e0a44400307105884050b003c0c0c454503415001848261000007900712044e07007002c401082091113120840109110a604d50000d580341d0384a402000800341041040035000309084c641081075010540f12808680640d41000c02400c4c3d0104c041703842e40c4c0003071081d402100000c603400c10242c140044d06a944100351b20045a080107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 726701205 1250 726699955 726699959
    0x40e041401050708240a0f180617120a210608010c02161e121a0903031005090601020c030f07050a060207150c02210a1109130b060301240f 61
    0x4400c4903054050f41c174096881250340342006015101072024000c50780c00c1000e51000040d800c03010300c0c0c500300420400e10b40c041d00c04100d607450000e42d04540c000c50f220001d200200e1400e03c00c0056200608129400807d0700d501c00f40200b01c032100300084800c80c103001002150542c00200d54488000c81d001c0e40000c0004644c004001d907141c0c40110802c0e1130350320003203004004c6144400d011350402900703101c8588107151210700030300103510018007d44009200742e12103410303005d100c05140e4100b64994021811443c1400d1034209a285c140034450041100402059469000f0024500d5401c2c0003400d5501e1076a843e1030310390307075800c10303100f621701c41c81d0000d03000900d882c00031404030265a1003e801201140903010300381c40ca6070480400300e801c00d440c8488110b00000d038580102c1281100b502a00e00c06d4406c3c1041c980c1d4482d6920564480c90744841480707000c00c404182010455031180c0c051140707994020000c1d0042c4003040250003011a840d50042414500b03070003003c1510405491040095 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 726702455 1250 726701205 726701207
    0x6090b01120b010f1812080408070e1506090411030f040b060a030317092d160e310f0510060b030c091912030306080f07090e03040e0414010507 63
    0x800300300d02c00303022901034040c01d640c2d50b00c1140c0d502030803250100c0120b0941c0d42c1d001c0942004d01b08282c00c3c1c552160219083c82658070a0115400822510308008864104454400d6006c0c13585082c641c45114005441e98040c1c42e2500101c088000701c0328070303903100e10f040b16510a031004212403c03602c1d15103880004245203800c1d1860070030b407901650f132540e5140b40c100c10780c0c00c0200c010f41000310620030807441c41207264000700050240c2d00409001c07810030380c1143c0d030249040b0041e1012019618210720a00902c0c100e0b401c6d01d41c1c40340341c140307054006049240038000784501d03000f510181ca007040080700c02405007482a240ea00c0744a901102d0269441e28038040c2190014050314844260403c04640c48080b000050030b59450010300b07440c1541501c551444c1c90510a61280cc6808042030400c0241501440385100030a5400e000d401140c14120889859079018094190341503560700c0141e013141802c000341c9015200304402c004240c00d1034202010309800f64a056581e82d0b0a005c0041d03c80b0b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 726703705 1250 726702455 726702461
    0x6090c0e15090c1b01060503071e0602060408070609030e040204080706090b03151e03100e060a0605061e0c0a0f02190f0b090d0c18110903030a2106090b0112 69
    0x903000c03d03a41d080c10310213403804248030860002034405256480e814041102ea6090044400809080b02002d1040d005600340750032184165201e1002d5400400410000c540b1003000c0310a000da000f1000540d0603850725041d0b560040c1000b6107034200780f0121340812100b4000910304255072068a400d0440c0b40e0715450a101880100d680c000342d491030b0091940ca50030003d00034010082103241c0a080050700001007441c1a19129035401d4942e11002984546078042c01041c0e0001c02c4110f080c011a41008086134403445511141a4100f11601071168015031031000d07110160301c2642074400180517401e0841528800050a034403454146420b424008110300d6014115580d1030741c0044071b60700c0c0610501c1940c100c1c0c0305881d080500c4c80d40007000101c018400b02d014240c01c0948600303c035070301b03e000c0c07085910381141600301410400c4408240e95000013aa040d20800389803007041407400341001c00c034000017144254000b5090050200d80706d545a000010840e01c01c0e03a81484680c03061881c5e40c00c1e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 726704955 1250 726703705 726703711
    0x4030504170309180709080303040c0f05010f020d0e1c06020702010e0109030b0403030b01030905030c1e010204140904141204031b0513050703020c0f0c04050a0e071206090c0e1509 79
    0x2001102c440103d01c00d031302144210383d010f02241045003015584118441c20740c6d00c215002c580c8030682c43d0701800030019503490040500720a00c1d00505901044101a6440040301c07415800c0c0704030202d800d5030076581d0301c02c0c81d0905c0e4151420364040f41d41914000019410081003280400c20b005280e0405501c51540d0104581e0045042c081e113440f9906c05138001c3c9164120941010b40b983d1161b00895010001403c071408110024699561000000036003254000084c8080b64010001080344d40c00c0c0380301c0001030310002c40344100303e9140c80c0341c002e58001105400440b0b0380100c54544800c10584000b80003164041c503800b442940800241416454641c021545d2000102c84801c09099499009a910100c4e50034014507007180481303018030700341c007510980c000c0e58000313140d0114504190090a401405c100e0082c044a03218419540c0c40b1071560080500c030109c41d5261105105e41c94000c012401d404c1042600d2941e220070220b16400c008480b02c0120200c080560005030605004240c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 726706205 1250 726704955 726704959
    0x60402040b4c1704050703080304120f020d090e130f0813080c0a060e040f020310050f0f09040b07091505030a15150e0a0b040e0403170405030304082104030504170309 73
    0x40c0b010403001d0f4064030920050020303034003807003031a2012000a50301c80040d80201e010304050314045000d9000200329649124440c006c5402c250701098070707070390400010010b88800d05010840c61707440b03840c2d01d101850340590282ca80c01c4110140824040240000c01c00b010703988000300c0ba41074596080e2a82d402140e480c40d60841c2080b0340c10008640b203161200b441e0745c4010008120001240d40039410398005403043e500e1002060b40401c69441d1a07000742e080003000ba280004201d030300800003016440020005400000114000340c5240d22580c498409001000b0301c40007a501d400780010041d400482e1240ba0481c60180800c2e5807000048c4014220303000e0f0100d1610900340321408a07221449c501d4540c0d0010418031011a018022901400c05440a1400140241750605004000c801c80e6450701d012880414140300101d0701c0801240c1d03100381c12002103650f500c10940445c041da81c190410112045441003413008055201c0014011a158808242c10f44021400010b03100d200c2c4405180d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 726707455 1250 726706205 726706217
    0xb040e06180f0d171f09052a190507080a0306030c0519052b050a0303050f150d0305070f03080103050f19060f180b060a0e0108060402040b4c 62
    0x70400c00c210f81c01d900c1c5d01c01c0c1016030070321104441c501c07103844840040e008038045544610070000a80c1155001201003e162880b001035030104010360b2029201b40b0080c00c0031801032007880d03406d15008004403507400b54484143c60703543c2068200140180350502003142c540f03008600c0050349161840a0381c1003000b8030305180649601d0142000090b9941c0d681c0242044a9502000d40406c1803007480d59160f0f0090380980403080d076a180c0101101c01c001d01c00c0740750602c0c0c04203022010140003250200003200340c80c00c21b8550401c1c2070544841c001c505005000d0714903800c04200f01640005418100c80c4982c04841c10401041c00703880d210b00801019078041e15401e440c4001140050300106170b408190480065180c4a280001c060350b511440b040d55101c0c580810301c40d82c0d00b00451624000e0040b169402c08a50501e0700390f60b00d925000d017004c0d08c6291159500d451558a00c81103141c0700039401c0300940e0300716102d03514000d4148049102c0030306060100e41c1508501d61050303020724443c9196035103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 726708705 1250 726707455 726707477
    0xf0213091509050709291f020309040f020403080409050a0207140d021b100503060d05160612050103020a23041b110f060708070905101116050f040b040e06180f0d 71
    0xc09a1924200d410303402200d4002c1802c00702c80d09000e0355441f081e10f9024652740c990f02c40501090b50310301c1040128481c030403c02000403440f0841038030251100640301194075205c10818601a000b0400c01422100e19500031801c1074000242292103401e55409640f402c9216070034070b62030a042000c445400c40c5071702c2c140c00003161040c0015070b44003800a100084003440c40c1c5840e03260141c400c000800c20b0036080801d01615070049182040404541824002507056901090300104184196981c415100c0f04034060300d55888409118a031020308200860711014060722030086045030000c2c0412075010300403142078408a441d2104120150082c0107a0322090800c5444032401481042003081d610000f28407607031800c03100d0140700b00b04c0d45e944940900500c030942c00d1004407000307084640c011240c204400d86801c4540e586006085070300290100c0303c1c80c0894007030502d5002c809000e010304c1c2e081161482c079140750001c4d00d0518034229003001c5c908005c0c1940d11040000c244012410103442 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 726709955 1250 726708705 726708761
    0x1d06010b16060606021e0f0c060f12040b1503011103150d140d0815100e030c030111120105100203030a02030a0e1006080f03070f0213091509050709 65
    0x42410a003040d40c20100038000b81c03903503400c580007908a40c0050f0042402c9000303406042c52140b621400c0d90015100000d0321710002c0baa150201c00f41c003400782c1c07400300b140c43c0401d469409540c0044040c10f564045031030186095903402c6012070b01c0d0305001c42c102e02c0d841d81c0cd05051042c445900c5003c03808130b00e142c5984442d081c284007007003c45a0b01109441480e8002000c901c1c0e480c15a9606d603006055018150502074a0410f0082516100c1407071802e08404a030b4400381e0004419040b814110060951440441d0510b00101508d5403d0343c24a868030403800700500080c01c0e00c40329003a1040480c0d80321800c01043c0001070314203000503070052020400c0281e241d40150342216684200140b1281d1103020303117080c6900300d00e80c144140d1b0380e500100001d0300c0902c402a5440e003203101070b42c0b80100c1c0b503440c1c1c513580d5186000a4004c0748042e0160040303c07042d40c40030100542011400e2201e868104030040989034054044410b40500c2600180400307141c0910200051140d554800c81c90349449 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 726711205 1250 726709955 726709957
    0x714011d0a0215130b070b0606281115010311010c0804061b061d070e0c0a03090c0801091b0803041d06040b040e0d1403040807141c121d06010b 63
    0x200180604400300726400e0081c0c0c070002d00c48010000101c001751243c20f070703051948600364002c0100b8049c41040025040c00610300c88500c10401c5c01c40400f80ea8440000400c407204046065000c1291041d0045025031500e00c96200f4100c034800c6510003027002a1100445d03090380d03104401010560300740010700006004040840c0100d5144210040300340140d1560415075030700401d140707400c60108541c0c504480c42400740c04040d107400108071185003003440c5c4955151040c9040302003090754400c0080304101103807030180010003694001744140e20550411218404a140c07250030a8400c001d4002046440801a1422601d01d40d501c03080601c900c1c4445109400000e000690050762611180e00903501c0340310300b90307980710350303c00070301101e13524402c0a0402840740c10680f822000c184104130001d40360004440762f60703034090410b40c1091140084185080c001ca203c070f402c012440007042c03002d00d40c4040d9058001c03414020600100d0020150384c901c007011001041c0c1c464000200602c080a0060 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 726712455 1250 726711205 726711229
    0x2a010804050c0303030c09010e030a0305030105060d0603061a0117010509131104060303200a0b040f0507170105041e120e01051b0604060b1c0b1306020714011d0a02 72
    0x10099070b1000007403900180c2150700c00c5861030420071000c1403249843d40c1c403400e6070083c0e010990003000d810b040e41d2405041404140f16143c8070751000a01c0041c51002600504000c40c2d001d5030500000701e0740100415507041352219940025003402e00f102071551032010305e034103c440203040d12086403a4844034841c6c1c044500c205035581a040040c6401c2e40c0c40d05d02c0b0340d00c0110302079a02c5104680b25110030a1038020b03550a81401d65101c40c0003c4003044205500a401552185020410700324a01d0039034148440c681c040500e60500c240a1003603c20103401c081e21407445095060360340059108070800d41200742e00c01402514481d034407000c0c601d0150410b0902e4540505181d828140107100100310303000700d4a000030054121506000801c40a40100200388074121080721140c0c00c40c650002115111102c058140b95030600800e42029800c040b003081765420400655890f41c40b0f041402e8103020410000008dd803800300c6840c06200380b0341300c9198990309600a05015126a001c00c1850b2a0392 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 726713705 1250 726712455 726712463
    0xb0a030b1f150305060a05060a1205280c08130503070f11040c03020912030909041e140309120f0a14010b0418060b0f0f060c0a020405090f2a010804 65
    0x7110080782d08000004905a1441c1660f000324861500c1d4050028405241c3c1c49140100c40c24460910300c150030440200e140420b04800107080d50310301c00803070480349a03003180e0883e03000d030881207490f60245030304808000482600c0d000015220a1000c0c000e2880e551030140c41030b0010b21111000540241c00c0c001c52a010f1001e200c0a040e50000003011654004801c40129030300180c119994188081c5011510105401950615800f10003040000d88000c10040944c1501c820040c0011100c01d04104400c0d040341ca54030303d0400000d5213655030b5103c900124071540582441403055000068600c000c141644003501d6401102e82c4c4206150042003805a801d5407540035828568490344501103001e2244682000001000d003008403c40b0441a0701301e000d404046400380c200d496845800840140c2961000c0d038442c9054002c1342004902c4000941c030500f001d0a00c0505480003900303540d5014a036044c0d488258600505c0c00d50809500310115128552565138031403980100e0003141d00c2070007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 726714955 1250 726713705 726713761
    0x60807140337060516080f010503060c071401020a090e28090201020f06040b010f06021606050a031811010e09060a05101b05030d050114130c03020c0f0708010b0a030b 73
    0x101d42d4403d802d03240e003200e0000110441c3d090004546a01184450300060648501c0e6990350500d00803903144c0b5801459444c240000080c5e1030200028601c2d4200d04009110085490341c100c002c004002d914107206010450390381e000400c6000312078010b000c0140d49000314a0760052026155400901a41501681940603103030400c3c0b00c00c2c80521201d4821441545c4200c160341c14402909a1a802504500110351181c0d5810001210050f00201926140e04189495400d080800c601405074051060b80440044000c84208403001c00e54060010342620303220305401c1c0641c00c0c072082e0705044512030b40c0507000440400507800e10b41d00d00c604055440c503003120380c0e01c540308140120520f4014200d40c581c3c400150500440d0281c403030796001d090b031b6624426060001d00c0000f10501c030741440b4031002d16962489180643c0c001e40c100e4035030041c00b4050322200005c03208556200c141c20701c2441c0842d42421040002440d00200020a895120304001c25940b1181d001e121056580c5040150101e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 726716205 1250 726714955 726715063
    0x50c060117070b07050d08010f0303080601081510020a03032d0c091a0c01060b03010806070807050d111c0501080607030504050c0d110a0503010c0207170c040608071403 74
    0x8043e100601200e80100003d000c21041003c0081c180c00b8140e11a03034603031640040500c0001d0744902c2740c540000c4240f80011050f1500401d802c42c110f04100150380c4002c80b0b101082d0b6460b0045a01e0308924080d0310200700010030702d0000a010070391110720701d40400411010002a00103584407030507845191500c4200181c847c8003a030b5003000b500305a1744003840007090101201d9000d00a01000c2d0141840c4130741554501040c1540d502c0300901910240036282c40081e154074440e000385c8001d00c00199091054010481408009038032078403000340c4c142d6030054544c07580c03521401154100c078035074070040a0355502c07400c0031002080c014008803102d001d00c9403850200e0380c0c0c401c00343d0200c138050000004880900c208000502201c5c1e03010320702030790404100604040d0089000401c40b050700030107440c01c990f403205032804c100c03443d491150701910b080e4021810300d100103056400c0e18844011806444046820166260f0f00009003440f4401d201140005604050005e150000c0c407101440700508 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 726717455 1250 726716205 726716219
    0x115120e0307230c0a0e0727060903060615020c01080c070b0a020316080403122d0c110a02060306011b0b0a0c020d0e151b01050a1b050c06011707 64
    0x8241d0a000f010707060380b072040740c5050403028000207940f418116060f50034075181901c02e4018070402480c40c014004080c5907100328038503411a200d4000901d000744030103243c961a01900f600c49501054801901c0e104011441c40c4d48401703030b83c25841c99600103110340300c1400011030f0020802000154648070a20502c0c000a4130356070102d00500a5100144e12440c1680450f400074180a07514420401c2c40700c00c0c4000f0039004001c035101c00984030004101203198103c08512001c200c00c5495904084095401180b207070f6a0081030400400d99404e4030481e10103c5855507042c030380c180a076018070200082403007503000e00c1c00c03240c01480c0c00a4080d001c4110b511400030b000350031542c06040310b4071801c401541a605001e4818019024184001500032400c00300381c91007881448005a0710000410401251b40b40c0040c040c0c3c050349100034001481d10702c142a0280502c10039200c20300d64002d404c4c9030f40c68020380a449504501c1c40050810f603192071440c0c081e04100c1e103040c0303581c0d0164400c041106 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 726718705 1250 726717455 726717473
    0x4051e06061507170c0a03031406010e040f060b030405071706013002060c100b0103150e07051207020a150e030d1508010c210207021005090105040504180302060115120e0307 76
    0x3120041740542500101c90401406aa6001000107030030a902010465076a80081c01c0300a061425a030020300461520510801054107410850f1183d50110820080000000d02c02c015500055000004001000c1c01c5076502c4000780240d2112101c9070f01c40701b00141001d540c003490350307108031400c980c542d030325402042541d032181080d4500e41d04080300030785071000b8a00801d61400380a1904010785642c645414040b0303891801080d40e8502c03d1000300703604074420b6042c0d03604ca15540030020034a08040101030340d60807080408807402490f003195014611000d1003140110241c102c0610b140007002e1a0880091010303e030b40c0942c0400c80440031a0b6040c1c240326070138100741035803245000030700118900c980e00d4240ea5052010341e4010004240140c1300d4031040da11402040c182aa02d4882e96001620240a50342020343c026243c803689200905a41c0c0710012403074045c2d001d4540c40d07601c4c1c03010010941604500c60700490019145941c7c0b6045a6000d803008001c1071060b0382c02c080c0503613680c4e000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 726719955 1250 726718705 726718717
    0xf071709011b090b090411071a091018120c060501060e030601080c18071407030504051206270109060c020601051f0c0308060d0b04051e0606150717 65
    0x2569501c204804030030040c2c0401600c004003900740000500d01d0f0a05a00740c1d48141c00513540a607407547c28450003c28000c1c141c4000b554007504101100004103070210909078100c561180500c203402d42c552403140e0783d2040881c0310398018842c00d102801616070461a8509030092000c0040d03e002c0100811050712a46011b042107a650340c51100d211000c01d843c100040e040f070107054004220f031843c01e90320700070240816004429001c041c0da941140542d844241c4510720580748a00203036a004056001c0300500a680d801c55140913080c1c00e03031000d80d9403680120380703500000c1c1c0d96080c42691103042e41c940d009400c5024001107045a0075070b54030402d40c0d00030500000564003c0005014625145019004e10504948107001030100c03050b0081c401c00e44107001406120081000c2507030390302e88050400700b032078010014072400c0c10249007456445d03c1201c0d80f12510042107181c00c0d09510007140f428002c20004000c280c030900c000140c007586070701241c2c0440c0c070b01c2c00f205c44550b142a4140d02803c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 726721205 1250 726719955 726719971
    0x130c0302031006020f07090b01050d06060906140304020904060f0906060f17240705190e130605091803071209050114040b0711030106090603140c010201050105090f0717 74
    0xa2a420601c2c400c580c030890300c1d003140f402e540044404c90034000d00040c20804488113950302282c002103200041e10320b40704030f5044101450078000d01041407600511301d242184d1903942d03140090650580107a4140c0000d44009510821020120740841c14a400c038580f407100810001505000541c0c580084a00c50391103210075051a03d0100f081e04114005400e00204c840080c043c110000f10240301135980281854402040400210b071440d8441c07403d03142e500400a00e0071801c0d001c1010040c042403908045c1c140b140310310164544240807603002e1402100d08c0a0000701c00c07615841d250b1162000d4400c8840c0142c48280190000f107040b640301070040328420340b070314501c440c18440011b26402c40d0202c03070190000200400c2000010700e8084030181c9420020261040746e00c01c0020b07003d046a0b902400401e0f0030810044203014880b01c0700c1c1c0700f0b00815821174415601c010010390030307101d092281c00c1c0d03c011901c00040c241840d205426600030601d00d400e90021148091480a18400b075904030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 726722455 1250 726721205 726721207
    0xe0102090607051b06160323210709060c0303092603040b07020303010e01140a0b04090204090f1521050303011d070212040603090510020f0a0219080f09130c0302 71
    0x101c000a40c3d00070782a20b1000031703900a0701e015001021088540901d481c0101040844020001d06e068800b9280035146144e69149981e8400710194580c209220082c1e10080c11210020640003400340400c070044421640710003003040c0b40c5440a0703000740003003002603625440c660f51305400000e1003142e03840030111513464207440342454180a002d40600034809030540d80104010b100d1420180c291604492110003c01c9c40d078140140030035014102c80e88405101c0c034011501003881d0702160090815621000700403c540404c0a840d80152106901d02c00c4000600300828805e440300b03d050803030390741c0003954041700c0d20b2071035500d25203103038070990041801089002e046d90040c031020803620b4000d00284010040c2010700500c0c51110300c25481140e061540c3c1e100b149042003024001e220010130211001c6444000b901c20f005060380c8030744070060050058517410030040d0a101d0400307950b02d400c80f01b21420200f10102c004a903134000111140e11540010ba55101c800840c010441e40b4009580d004d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 726723705 1250 726722455 726722473
    0x1603050a021005010b0301121b060914010c080a05030702160b04090f05040b1f03170915040b04090b120307030914010c08030c03040f1a09060f040302100e010209060705 74
    0xa00700710b46000c1c0101810300740790041046209140a59040d122081c45800c003461040ca40300c03414802c00d03010514980b110420018100e81c11441c440c0c11140c0300200034000031110401101c00c07800408009007484c1040c401a0045442480910380c46240c50045038201d04079014090810b041c03a500a414030400000d040c0500031060081a052a00c4d8404c140401e00309692000700b0a4002003d02d0303600842d481044180211095008000b0b641115000111b40848540040654400300c031960054000a0510a1840b1003100b2601140c0c00400114205400c0c2000080034010039446541d000a18489030500f2107814802800c0c100c2c46034890b094400e03c0c2085038003407010103c035107074140180f0411550110b007a09080b2070340481000000799403581c841c644998070a0b03003031401400b503c2c42201d040c0400420159914040c2412904030b0301140d90701d41640028080c103d50080c0103800c014860b13100740c841a0400581d04100100140c00c0104a002088491700244021b80300e81c4c0c021118 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 726724955 1250 726723705 726723707
    0x215070b250c020f0a050a030c081b0333010602010515100e0402070606030c1205190c06200f01020a08090312041502210f1501090b0f1603050a 63
    0x40384800c0c84040c0044a0740008280c0203041401d540c00701038000e091900100c1c00c242e850039070b0500600402840001c1d01a240d04120701103510034001d01150b44604822002c404068260711514082d00070004d255503001062010082440101880718a42d03207081c1c1800d0030608443c440e4068170f81c980c0001140c1c5009883c180e200c51401c0c94040c015580080c0d6298596480789000c440f1032002c1d100944e40706600c2c50100c000308466440a456001f2100300070031404e03161007078864100c3c0643c4c1120a80244010100c0410f950100000c044413680b0030304029007409402c005a1558810941000d200d41c5402e000d8141002c28070071940e540d6000617204009a00503503515001580c002c025030801d8080d1010010a01001d030000c3c0030440d220851081e1181c040d01112054400c0c40c812491840300308002e1b42c1c0254094034072036200300084002034480c1542201c040303068039059542e008418903042e03188040740e2001402c0c100440c01081621134200c10b4400d8000900d02c03941d519952202d800070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 726726205 1250 726724955 726724981
    0xb040c0806031005010e0c0c030f0427060e130201021c08090106140a03021504121a0a0504170a090b0f07110a080a3309020a140303160215070b 63
    0x400c094a2074513110040c404c562050070625408070002242c990750380c5580705140d01d0b6001c2c41312441529000060302140891001c3d810078800d0031580154a20031f88580308140076a1694000c40c5241070070000024491707110b5170001041ca50042c01613603845411805070352001c0b41c08400c64008210082d0500c80c0300d29092094000030a2a0308080c0c071100c0702070380000d20f004a01d00c400b900c00c0c0482001380c1401a004021a0010310344140b450f000d03041103181909051060704d003640c40210035100000e80b01403080c05654440d642c04070529503507007440c0c00000402d03004194010708000040501140901c0311100400e01c00c03040d100b26680310100381c40c021030440c01001915001c1c49806008000e68100002ca03000d03003e900c007440031440f4040c8411508a40316604500c1002c911410f02c4044104050b804019a107000380c03800070041361510340c6001e40c119104d46041c0c0660040201e05084c0780102440341f000c91005001550902c8028000451a0000c00042d10741c896048280b10140522003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 726727455 1250 726726205 726726223
    0x92d0109030203252102010906080103030c0b041121061b04150215070e0907050f040b03040f021206100e0f0c09151b160503190302010b040c080603 65
    0x46000010300782558003180d21241448901c5151600301e0b2181c40c0e01c0c01504022002030301294003940840104145410380302020300c0810790114141e0500414003030b10900c00c1a043e03c0d05503c4078440c42030136646001403108020410340e007004001003a101180c4da4982850002e0b4903d4050f1101a50717240041030030154041e01080320100e00788071815070038004500703580807200303039058441d8000e4010406030b080003040307034150240344055001c0050541c2c01012030b0200035010307504601240c0c1c41d00400d40ea14419200d082c40c1d520801e100800849051000a5038014414804c00c4134590706076020134040031a10901000c00d41101d402c00000d22000c0913904004c04036040d4440c628248940383d51280ca1016002050089000a42281680f626654801c0703c0c90046050b41d0360b640c04884052420f181c1c00350010190082e00200d2940c071001030805800d5440040191a04a1380820b107090f44024280040b0300395502e40305410010b0b541d501c20900f401009482d408040c2c030341030341010308000e002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 726728705 1250 726727455 726727457
    0x160309171e0c030705060c011503140f070501050405060d06080313031406040201120203090f06010f060e0303130905041b03060204151d0405151f030c0c1a0a02092d01 73
    0x542c902201a540006041c3d048420644040341da4128141401d070143c94008194051000782520000800400c40c200c0c0501a0811064031020b02400f11031a4031071074a84101800914140000d22051a1501c020185003860900001e00103075205012404c6030012040100c403080902410401e01004240300806140300300043c001ea4605540080d1100700807150b520501540480000c5032000d042140c8035107101d9030b404440c2e041da5036150141501c8001c2c00340700d000500c0031032401a5414000290b641c0510022880e001880c2050b00c850024100103005136001201c0e1901e0302002d2140659040c00f550040f08007694503400c007c8008103034564025942c04020328140f042e12031780c0e851a0b2440c200c080446012aa9443d4442403001000c0c10020b050b070f001c03600b00d2444250311023100d030900c5404001c2d1000d00c0703e40c0036002d0540365a503103004003408070030403048500e0010b20441e0425034010290f5100600f04031401c004150001e52400c441d07a88a44540c2944241540c030f0907080c0b9030742000f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 726729955 1250 726728705 726728713
    0x10e0105030d0c1502030c0706090b190606020c060d02090d0c1a0726040b130320100e040f020705010f050609060d03030906090501020a02071505040b160309171e 71
    0x83c2d9540001100c1d054002c0c11400e903020011505000b401c4080300c0b1207607040402480002d119040600e51030b41e0580304c4105103e1006038422401302d0360b000386021505203401911914035140c00340015503000c50b05000301c151b0b0030000419659100409041c0c60744c0910130022100341400e217a81156141d2150881c40003905015040005006401622089a500c1140c1c0c280754410806107010380900c2c2c01000c49117002181b4008110340f8141d04c03004481c0207204848440e4002d01c540d4100d8284074800c141c01c92218120324941c54003440c078004c0741c02405000000d40241030420301003240c00414049409945030b1849600c6800c540c040c0340c2e0024070031039004450f81413881c0094014040c1600003014140c84043d071009020450f4080c0d101c441e000402555114004540251590864021000c0310380590704000b06da144144147c2c0d040d96400383c807183c6000b0201e40105040307200d00e003089042010f911408120481c80d210310401103160f0340d00804c41801c400e12400305450380c20300704008a81c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 726731205 1250 726729955 726729977
    0x31f0305030316090b0f280c170c0c090915070f2718150f03170f03070c02060705073b0606210f0a11030603071404090b010e0105030d 59
    0x1601c50444d482c40c4514620107a8815a16100150036107400000b5030b006a8202d503243e40c200d0300860304c08c003198481c0502c10260805148441d201c0c0c05505610026035001100300e05c5a42460703101c0302d4000a1150449403407020100c680754000c01d044621030001800703032198a821a8004e071401d4015900e0250402c02d40140c0584501448000c3c0325846031030301aa401c9030079121996015003130030028548450a490f0303d03482c1c0310901e0325039880211045481c1010120341c044031007055801e1909240e825a00d1510741c2034046a2140c81c920050b81c1c4600e040003030b90005a010070400c40103101c2c0a07030001a03404203620000c0030b11a1110914004042003450344051008503c01c02d41c020002c032100c940702c8001c51982e11181d00012480b4105034251006d00080040821409103c0c1409507418004100134500c07402c56800160f40e1280c01d98400c10b414415800070380304000030700001400000700404140c03100002c0100a80c0725039443c0e43c1100c018041403e05004000386007205080100007a4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 726732455 1250 726731205 726731219
    0xe1c0e0d080a090e04061a0d0b0a02030a060506070f0308011e1502120703050d0b0109051c0503090d06060e010504060e0703090203070b0d0b12070812031f030503031609 74
    0x100d0038000030310320388000910030700799800380000d00701a04407000030f1015490a40307002d03c020441d007540c0001480294a0f90092840e21085043c0050741c0700541480948840540001075000540024050b98031030700c0c00324094403074a01400800d070050602c0500091035044c0030340000c2041e000744840c00501603c01d1610102545c1c40070883e01081d00000000a070450202e003071500102c00701800c407400203440d02c207040d44080a400c40c038100507410042c0e01155401500d03040d1039071040700d400042d0084498100707004484005a0940140700340c0f40b904000b01b0004040d001003820884070a603a8010902c016150a11624007408050310308000042c20500050352100c4000c0c890005c15071544107150031505c0c144440c0000f0800000b070a83c640e4181c9844e071001d004159100d9000b8141c100000d10009000912035003101c0307517200a003589068040c0f02d110164401030000d8201a08254070210000300c2c4140000114010783c06141c807801c0020740d140c68a400d00b040d4108010707503002d00780415 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 726733705 1250 726732455 726732469
    0x51b0a020a020904060e030a0f02010c050a1e0c1b08010e0a032709021c0e2107020607080c07080d08010311270906070e010903120e060c010e1c0e 64
    0x9507011140c01c03c0780c1d5660320707003040a041c0715000080175020110b40d100080707400202c203030b01c1148036400034002505400d03c1107401e030240a01300b0300022120f05040848a180d4409801d400e500c600d405078041e1607a881f15019200c018651262180f1107650411240501788244019020810060890a10b19403001084180300c2441c0d01c5019810840009112031082d00c0e00d401070111007425501e44000c8a01080c0a500304403503a007101e41420408500c440000c191303400d8a0340c4600303500b0414645185c4018032030b08071013000c1740c201030b04210060100b205840944030070038042e401082c1d1036080c03007107080c1420091110a03040c0004040180001292550701d00307425039043c0c41c0340b007041a000716158a0542d09200c030036955500041400305c0c0341070100d006482102d140d2503014400d200c520045504d10540d00c0050800403443c079000d017006101d560b40904018005081c141405001c46689086502c880c100340c1c225401400c20440c000400d42d04001c2e2002c1d203052080c40b082c4490045410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 726734955 1250 726733705 726733723
    0xc150c0f0307050408100902011d0901180618050702010b0105040b03040b310302211602030a1406010911090d0b0c0d1406030609030322051c03051b0a02 67
    0x40c049000c40010b51481c428400c3e1401041d803d0101c840301c040c0c2038400c00040c82110402c0c1c1c002400e072820940c8403d40c0510361218400081c006640c0c0f41e1030300705044a40c0b2450707607503011041d417200d01c0010b11300041010718082d10030000f00050f007410443e0380a400c660000c00801d0600c2000c0c0010000800e9400503207610035003100e48210503980360000641c000b80143d550341a9076040048010101c01c4c141000300c5101c1c071a40071120540621b00c000304441c0181001804101070030420384d0605500c028003242c80c1071000d0102ca101c0c90721559100d5881c052007442601c07952042004100903640d502a400302d0950301c1846505e0088040007144e1988510000600510310040104000c8134200301113442d595400d9404100c900c10506003124034245c291016482440313081e01090b90840040101c1c3c1c0a20406149020084000c0d040080720300d10103c819141030080d54580c050400d20381403c4190009c040c0d8001560f031800d501c0c220240b10b004104134070303040c406101c00d03ca199000141501 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 726736205 1250 726734955 726734977
    0x10e0a0b19150b0c070b0301030501090b0708090a0f021f02150105060a0f030c0903020a060f1103130e072a060c020703020f010320070b0702070e1510180b0c150c 71
    0x680c0d04280e05031030b03141400c5e60303100c00e200c6440000000240901948000600352254007102d03c43c0e191441e084030000016614080d06402070305010f4005110b80c50304a11041c07020b4201c1140d40401106a80000301ea4120340700542c0100d024048480340c2c01d080c0b20b0151200b1900581480705403907008001c046200c200ca81455a2100c020f01c0300d60050f41124019507000300011007881d1620001042c580c00c1c54078400200b200c1c074040b010040c8000c000d58840105e5400b40d240d84070715000a84612000260010060004a4443c65903242003142d03041c110408584c084101090035203444022114421014811504903010920050741c88040c5501c0955091070046150111028201000404003903c403004c40d000250600c1044200e045441c8650402c1e000d549407180c0e908440101c0302c10071140e5001d4107400341c98038007081c54a200d444881100714600181a081020402007080c4281d41004031020000300e43c00090940c20041d030034070200180d0010a990811694066080c040c80c44070303034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 726737455 1250 726736205 726736207
    0x60c0406021b1c080d0609021c022511150309070501030c1101020426150c07030e0306040b04021011060a0b040b10051206010e21010e0a0b19150b 64
    0x4529a9880c14980c884949404541e1425181ea00d000c0c5021362011030301510281c100400007d800c41d00f0f1081e60071240c00c10640d00c10810008100744001d50069a0808014087d090341c44134004542d00c1c840d103124452040c0c10310b50b14801007000f501031482448001c80507010000c000468001251030302c01c4134001e00b00842c2d10000514280c1d083c00051001e888c543d8030110300092100e1004c12819040300c00700303010444141c03912101c80e0b11040c6103000c0700d003e103071a40c0100b116003041c2002040c10034024500240050f0724900000c1c01d1020130349056800181044c10700055180c03115440c2103000da14101000c2140400b0101034031144010078280e485580c0700700040e095143e03600400410100248500d01e00c540c0203001600b10782040b038070360000b102039000140740d5500507c0c18601403d8001e01e0b200e290003c040702d046803042c403022100520b5482d443d42520741e1800704240d1b004648547e03841c0c5564a4026207052003124000c110b05c05c0349040c140410300303c0d00e402443c102914883e9801c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 726738705 1250 726737455 726737503
    0x20a08160302101e052d010e100f0b090a030605040b04061104080d050d0906051003060c05130e09070807080307140703030903020d0503090d03030b0910060e100e04020a090602060c040602 82
    0x4076108103080368840c0032100f80700300801030f50182c07840040c7c10b960200515607041e40350285c0c800d100310f0050042661000480780d0910802110f9809403000c40d50080c0b55024a640b40e550300016030308241c40407900c080211042c030040007064000e1b072828050440400c3e092514050806542c2c09150101341f007807000000700c0c0f0007840002d070030a103001a0040d10501640c2450030107a060350000c1d00c400e50303065160030120b1038103601c94411190144c0f03001c10900c058504007003503103050000140c040728a52040c0100014083c60a004030070051038840f010b16120304107400c3c09440440d88404d504403980141e841800003075040002c4009a079010f0320107640285907458880d1442c841d645000b940300f01d00442490030961315402c50203000c102511054421744408110169100c100e00940c00400d00c5400010518200107621203060a00c2c0c0c6083c141c05a40700001c207040340e100740b03000d1001074403035401404002e0301002044c6d0003d001c0d003d0b1a180a1804400039101c074842031400136500801c080b4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 726739955 1250 726738705 726738721
    0x140f19260913090204050f0709080303040507090218090a15080712060b06311508041203060e0f18030a0f0c140607030e0c060a0915020a08160302101e05 67
    0x1603c2c0590b015004200a0901c081c0e0b0020110301180c0c514002034400c240803c40d00c01c040213490095034400001d024281c00d00d0b2001e00a034004110011351010391100c200d03259071781c1c694454040c0b80d03d9140016441404d40f00101c0f080c01a0b080141d42d98000c4e28200710111051001007a8681c000074009212a00303e00000d40d540f01e11000750841c43c2c0b80f884c044900c811005802d0008401048854200e80e036a8440484480f0000c403c07000410b087c1d40010300441d40d10038120b40e1168030361800060a603124281c80300030b243d0a03601c0e014114803100400c514240080101c1d24040303447c0c402903051050504c4003d04482140d0505010000380e01006810400300001210281c03903070000b525a140f500441c01001829403a540714403501c9881a03c00384d034207040c400c4402c441d41555a6003070083c1080d1900f8042404884940114807600c4c400d00c000c2151b0b40050070029003490503040c5040d40740d0070000d20b8541d0000c58400c0b0030b494a2092601041e52851428907540360100221342640d8101c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 726741205 1250 726739955 726739961
    0x201090311010905190509150f010f03150801151409010b0f0d02030a050406060906050a060c0c2402070b09060702040b13050903090114030f04140f19260913 69
    0x1210075003000041e1005d00d000d54050304400c09481040c0d40b000442c0e40d82004080307185500c0c0c846503070082140403091126502c038060040d03c5822504020039004001c2c0c03440030b24004568000180c3c0e0b599518102405d400d428001402812030600c02080d50315600c000030340301703141803040229820000458020b210b503804195a44040360b0041103490380340c40d901c42d201400c0221000c845807803030044c1c0420030040c10f1107004103a80002d00301c000c3c011304000c416542940480c1040d1030000c0c4a9200140791411101c111042c41642e01c0a4410310f8038a0381c1c0a03240c00550742140c46001400d2014a2040d00c9110603510443d404841c04a503100c1c040c008a1480c980c403203c5072305140c0c1454100100e1030800802407132480001c0ea900003070400203003408500d41c002900d01078545010b000100d4085881d801c081c5440508201c240e5581030740c000c1c5024680900426074022020a558111050100440032201c60203031110441c00852002c5a102c01a4464600340c60304c0750300b00c81051410913040e94 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 726742455 1250 726741205 726741209
    0x13030824040906050414060f0105041e09030c020108070f1202070f061103061e0607020d21080106030c020319080a14041109130302030316050705030a0e0a09060302010903110109 78
    0x1d4010048802035041880c0501003c030b0301030b0b0380d070804442e006100ea040015a280314013481f10111030581d00b49420403014001c128180011030b14a850403c1005a0f06e202d087d00d8a48a038440e0101195903100142003100001d0081d018407502c0101c02490f1a00130070341140c801c060100050340c0b0915860801b480e40c82045000c0c009914110369a400321814a00540c01620100c6403052071513600000820060340080383c2503003000c0300b0f2100c100141450000101c0e0a4458a98401c2640a5240e0506948240111440010b404800420030140c142c4038050201c034103480511b1411101c6071811071103401403401e000800c00b000c000119204e8540e40321549880c80b0541010300c43c28182040e11031407520031006072140d050500810400502e19180d03000d43c41c1e03d90061801d540e5000300c91551034016110410510800b00301032000910180000c1941203402e8640200c444603c000f400340c107014035008540d20a103400c105202603a000041c4608507607000012188640c15400129100d0450fa = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 726743705 1250 726742455 726742459
    0x1c0605040b103c080103110a050618060705150f0a060e04020d0602090d0804050411030121050c0d03020109200a0b030604020c0307120f0e060405130b060d0e0613030824 74
    0x183d03412141e0190302900c500c1c1264020358650300455100c0c0f080040000c641d10819612010422545a840c0340d03003404807081a2006009604003007150702e0703013828a213844542c0031612010100b008954411070850329006a200da104000341c40c204820f9241002005c1d1000e84104003502c1a00d04004464044582060002e4202103074001e2524107030170342c0d4129010300c6d4455401c0080000ca59180401a40d04032040d4010402882d60381d10328410700480c030b026064419001c0c5040466240c3c85960315503990310300c05e500000300a020350401031020460b2001c0b50584080c442c03652041540e0782451842500c3c42e60340d4007136503515030200040092240d10440000e600000c82c204e8288001ea9850b10811441e684907505500e0b04a40202c425901c80f5038036aa0155091105000c9420054160800481c000c00002025507035100000c14035005500034020040d15044907440a407002d10099400c54a86040d4000850044d078018190000040070301040da955070301d00354055401103000c580b08200c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 726744955 1250 726743705 726743807
    0x90909080307120912022410150c02041d011802060f0d1b031509020301031502030c1204051c03151a0409110a030506121b04021c0605040b10 62
    0x152010107511088040308080d00f0041c0501d883d00d4404803211002d10032500360344054030708c1d800c100950821800c4a03071004c0800501e4550103006850720700c64542c200c841260000d5941410102c1d2600791401c11800d21221f1484010035001a00c0d40b80948011001d15010551182c0880c6062030042c5442003880c02284600311911218035015404031289448070260707140901e8481c81d02009030301c020700c0300400c0040a01c0d8400715420441e40034580284002d030045140c0440440d1600030284260307010340709508130f1490801034140324000c0c0c0c0c00042241c1020301c207480031074070382d4202c04041d441144c00840784110900f0403454114229005003c0b071100401021454012048540c3c10440201020034a0200030580a01c3c280890041e000d0f072100060040b03211442010010000d00c3d04025042a000e102d110b2030008001d9422071520400000020210301d040c0400060324100f00810b40150b003600940d88845a20161940c943c01041d00d241c5415601e40c602c25603042d002c03041650074150 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 726746205 1250 726744955 726744983
    0x20903010e010216022803022e091707050d060e120d2c0d030b22020c060c0306030316020607080c0a0209060a08100b06120907060909090803071209 65
    0x130301841104e050081d140740c03070800d08002da46140d500d4884088110314040101c10001898079582c2c582c261211499151580c410b00120707101c18000d035642500100380106814046804071b128039880e0f840450009080c00b52504000c540011a00000645a141c84180408040e00304100d85400c004030b56402e69135980e66034000300001c14171003d84c902c02e81800d0789035803101c40c180c1d070042c1a4100d0ba0341c09040c080320f032020142c00400310400340c2c98220b00c11003d4041c4048854400d402041132482026983d080d0850741e03079040090043c00c41d80a08130900510566480010568000c6401c0d018009210301036070001824a01079106c008024040005070100030b00e4012440501d041c0c800c0c4d85040c0e06071941c48c108248009075000f441c0e01c0d40d10503140c1e0710400100750061420088003810880c900344001c81901181d800440700c62010303605c03559017048059031003a4604010803501c0c00410034210030740d03240031651001800c0c603000c100850315101c007a10425072040d41c4055202c035410304020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 726747455 1250 726746205 726746227
    0x1b0e0f03191203050c09040b0406030c0b0403030e06070f0b190203130209132001090f090606080916030305070318091b08130201180b041202040e03090102070306020903010e0102 78
    0x1000141c0403106022550034811001c1e001e401028002d0303400d0090307682064050001c2c07100905442c161907606c0340c1c99140000200e040c0c1002e600c007030900d002032903903141c1c00c604001c0d215146401505024510801c0a000461400d806203140c0ca9445802800c064482c5044c007e4050180050781ca0980d10010602c03800c0f20010a808400501c2a506010329540301d031001005445203c50240c134210b8150003070300740c1801c0d48ca051002d800050405001164480c030005114817042e8110400960340c4403001e11042d034001c0358541d84640c101c8000d00c420701003818402c4541c603440c4001824010042440c40030107000c0c1035001008030011480100c00c0759030302e0905010708132014580b03100300c000040e9181400c1c803516496200b0034400400c144d1145031940110f88050348608405100841c05002003010313141480104000c2ca19030325400d480c51103c0c01000100c601c540c9200f56242e0007003082041690700070809004a980101005896043d84804a805014030060b108915407000694151031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 726748705 1250 726747455 726747493
    0x30e0a080a1836140105090705160605150d080d0b0121200702030c091f0314070b0304031b080c03070602030a0b0907271d04030f02011b0e0f03 63
    0x8898209900862202c1d8500c3c01812103002102d81164004138200501840c1000301c0656040981c500d001e5142451281d90079101c003807a0b0204403000c548407000c0c0030400d20588021102480c003112000b0b0030b14a19911500548250110741c2201611100c40d211183e0042c6500c0310341c00d00070071614000704100c08107400104040e0078503418450203038444403036182d003007402c0d02c202c103501500510204c81d0300020484a91001006029820307460382c4403107401c0d840b0b0007244004602c1181901542040d00952070b0404031980c01c0070040800520400000c84d40c030000c00f02c0501e80a201409406001d41088146032144940c2206a44400191902009050390003184248110f43d810400c550f1614104244042e00752240300001d072280141d00700c450800b90703400e611921071a01c002c0640744d42d50002199032540c8500490f003840c11104020a05400c08005a8010b07002d1000300304401581c141103142c500c04280203820000e0307a120003043c0e6101e105000b20f94074402003c94017a010710008402d14 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 726749955 1250 726748705 726748769
    0x3051e0c030a0c0305071409060906040f0e09030306010c020f030f030f0d05060301060b07030f180e041a092d07080c010f02010c050301120f0b04080a030e0a080a18 72
    0x1000c1c0c9030090260000b131081c4102401071030290380740071807100454000b0384190411079600e41c0c0400100800116075a916004000801d050510b0020092408040b482580c1000b824421160010410040c050380d10030400c004071541200ca0446c02d10243d00402e20780f0b800c419040074240300004859404043e910050090700b00d641c0001e0289544040a060a0315041d21826403c0d0109000076400030f805181000c02c022810300d000c0905c1c5102d145a44c0034030020340e0210011020000c01d02c010721150400c8076040c4009000b54074100c0c18040c461943e1351440400d10900f1003101c040c1054518494404481d040c5050301c01c0b500310780d03202c00306251500c41050170745d40800d01002c54104401c0c0117000e0b405107070101c0d8079600e095030300e0300c9488940c242c890f450484004a0194031540000c00c0070660900039805804441d403104000c14015040714040c1080d540c03140d00900407140041d0281040f146440302502d03118410710102c080b40d20f00103070141c02004040c01000020700800c503000803a218 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 726751205 1250 726749955 726749971
    0x605160f120905120f211e07060c1b03030e010209060d24030308010e06010507060c0917070b09060c1501030f21121a031905011d0303040303051e0c03 66
    0x1900134801d203103a81c0e0155034000d13410340e0000c026a003005207900341400703402c0d85540e4401e4a0103c0c0c500a221100c140402142600d440c0803d0080138451248071b002a580c0081c140f900051103002c003140740c1c0c2085150b000b0f041684540c03c19041b40d00c2901075603e4054003404040d2603085c5106108082e01d10780c00e403900001309000d45c00d141840c840140c00c0450350907031500b02c2c20340d08003209070014440040103207050050410880c00080c0591140c0500c580303643d0340d1281d40740e040001008890010000e0000641d00046051056024500803203034a04000c43d2070070760700c0740000e11341c80c00d0500c40103419401180c1040004140446581c286408c3d80c4244031524840c081f03207000040a00c110800d00000501d4440041e18940b407036846000780610b003280301c19039162a40000381c980400c6260340003002030f850301d4140400409014061402101030303040700300d1004e5440503a643e4040103001070200358989001c2040b82c11140d40d403090080602114000328500f01c011310070300394070681d0501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 726752455 1250 726751205 726751219
    0x409020f150c010e12071e0b0109020306030717150a09060204060903120306060f08060d05030c030d0e0705010503240a0b1b0106050609060a2c13060605160f120905 72
    0x2082081c0218640001d0b4030905c1600d803d0100c0b40c2c880e000c0e118944002c458100d0541a09800400c1d8608c24080c000c2148480160381d9107000c8d0141424545030b03600a010301403585501801002e0b0102d11100c44280c1c1e0628150749650701400d20010b080b07000c070b000d020980b0004002c22402c0c0c3c030000c210140c030b00409800010f44011401141107800510580300040c44c1c840c0c1c03002842c0c0c450341800f0740251004000401400343d544902c0e0940e480103020644070790000440c900380707540a0248005900200000d05485490000007a11511000b080103101002011866206201c0e400346074403d68809042d0b90b42140d1100719000f1035034001c00c40518200d064001030a00b9900501030001650b0014104a05000c3c84000348089908580a00d40501540482800c440ba10200341c000c050013a1360401d162541c400c50520041c080511085500380d82130000601c03a442d00b240403641c2c070542044003003140e01600d0070302d03051000301090000c100b122a50043c440c519440003000064030411910781d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 726753705 1250 726752455 726752471
    0x6120c03111b070e09060403030203150306010609291803070f06020a030806100c0311030c0a050a03030e06070f050a27080706031413030c0213050103030e010c0206090409020f150c01 80
    0x1310703803007010850b8980703003983c011b80005000074803e4000e0340c2c02c1046010a80b624004500001f41014826041007000950000d0100a0210075000c00400001c4d800c0c214401000c040380030300740301c1c07080c180001103200f5103115880d900d8030304012410040c40458400c801a903101c460080d20784203002d605800207030020f03003c500b0510303007405820380021894841101c04545a5020b40e1400c400d074500d400c0600092210310b0100409211100007a4455000380990028a00d4054215041c0607500200e56000b4010440b000d40c00c0711020030314184070b007009600c1c2c401c0408201e50215001d41d0040c000e1080140040c2ca6150f240350400503580310209075a841e44c0c03a000c0c2181100e18616904400850800104420400a8060b005058040c0c0340c070840040c0f00b900072610070350b4140382c6041220350324030040040c1580402c8100c1072181c01d10f032074091032a00742c00044440c0605c02101d8403856440c42204215a58800340c1c02c50a81c001c0c018070700343e180400140312160450319588256500b81624 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 726754955 1250 726753705 726753719
    0x50d080414041a0118050d0c1503050f07110102040b0409020307090b0910050d02072a0e0f010312030b030118030e0625080403211806120c03111b07 65
    0x1d86002581551004003c40d4030160044851035210100314003c1d40e40b0000204040d1a02521056124021440b55548514100e61f42c14a401c042e0043c1041510701014400328122091100b900410585481c2d00c03079601d0711030098024402c0d80c2c45030010382c80006001034000d040380c01440c0303e0070a03600c07620041781d61030a1041142c8142c00025a01a44034103a400465003d1000780996041c400001410b0901036914280031030707113802c80c16892003280c18180c100c40c443c0503155030280c0340c00040c0040c10305281440701d801c44010b0000a00c040494018004e80c140700350f00107400c41ea0001d009010b101848ac85040e082c8240728001d80005083d6195041d0600f0b10303030100c0d040940c03032a940403c01040c2003ca41e10f5158031500407290810304200000105030070300c88681a01d920f4441c60300014403169400b41012103803000c0e4411005078581c4c10040e454205103041d809180d400741c08158a60b00300012001440450b140f41440c1102240300044480c80e1151018490383d038608891040d525545 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 726756205 1250 726754955 726754961
    0x6091041100309150e011104060203040e0a11040303080c0c0d08071814060a050403080307080f0f09100507090305150a0e0f0c010c060603020607210c0506010e10050d08041404 77
    0x2c0054000f4500f904140342c016041e80c094545c0803421800041c540200020001c401d5009030f01c1403005905c0850240281500100001d41090002000700700c508003103004005035005521014090006807000103030700540c40c1c0101c506070b00141c0240c030010703502da15010381884010b603014000030b00030a100e89007080d100e61450041d221b030050384034101c2d94010700300110742c0c0c8040701070740c2000020f03c000000584402e000e14041c6445840c1e85006261a01081104400041c807100c0c140d6894014450170b4040400d00188024081901080c0c59407009015a9a00196400104144140085526488030501445018002542c3c0c00c0c04014002820320307960b02141040b00441e5080001e000e00e030b540c01800c0d224000b512030400071074441d030349030009000c542005a00341c03841d00011100c1221070b110102c4da031140701064241038500c034440d501e9075a03540b0014010f0001e517208003030101c0c080b101c41040d00801007400501c414101350140c83c024070903811030320440d061702d0036030180540340d07280c030380 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 726757455 1250 726756205 726756221
    0x3060e061207030b040503120f06010e0f0120071a130602060903040e040c0b0a170f071d0f0603090d08090309060a03020d270506060910411003 63
    0x10010104681151509007401c131002e0421075a902c82040406071882c14440418400c40d5010707250107a501e172260025101d440c030950054850001c074909109640e0304a040b00b06c0c02000d030318440c5d00803413a000e40b05241030a0340d00224800300d001d0061509080060006203503064400820000455032100e0690740d0b080290382f20340907900280300600a102481d8200d035032290289101543c45595045050420b5100304080340000c0d00c0b110103201c0b04400702c441c0da5003002402260781154034002074020010315001c00310a1201e24103065003052030b038641c0000d80f02804010460b6959050141c00303151307111a5100e810b008204001c0006040c84004000c1c0c8591030300140c0203626065075030500300d00a602516200304460f50742d00010b14540300780c81180301d000540900221013500d6500f001454240005d1a881c420110f11007000441c62180e04804112881c5506154551998809201d46910124022000e03003006110a009030100c3c1e1070340010000040e1158070b480c00e40800101d0030741b0724403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 726758705 1250 726757455 726757489
    0xf020c1f0c020a1e1205071208070818070f0f030215030c030402010f02150c030106090f08030a0e15030903070606060309050601051c0f050c01090609150804030311030703060e06 78
    0xa801840f0128407401d440484900f80d079a05040c1c07074500e9554003503071041c0c240700a00c001040031404c4801c100d461090403090044900703114095280540c2c3c010100400201402001e821f03040c3c1540400c44100b0401c00500a4002808025911813440348074084c25840281d100e90340c402183c16022020f5000c0f41d0148038031540d65865681c03503400640c0c0300c03007404820000314407580c3c64654005001004550007511803040050f600d500d042c20081c086045500842e0150001c0c20041000c48000000c1b90b03602d207a0303424840d2000c0c0007100000e0f0004450954140940800401c004651602200800c0300611914040081030380341d2208800315840c019009040354414001441185810154207074290844030364100f040d0700607545c10a40301c0410300101d03883da111318640f901a40c0c025020002501e078510f000107187d407074211020000c2c400c40541c54244140703140800d051501c01e8200c20680340001e09840e42d00c0c00d0820f8001d00900140c418030002035085404039020b8904184d02031550010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 726759955 1250 726758705 726758713
    0xa140708030402150721030f06050d02130204170a0303051506090f041d010e0c09131101020307020a08102f09060c010905060f070906090e0603010f020c1f0c02 70
    0xb2982803045180350300c070810078462418024000058107003440b2007042c2e046403030701401ca00f54402026040c1e034000c100c44124581000e2013808991607a01e40c0c0012540c040f070304078911700f201f818004028426500701e03049902203404600240e00c0c1c0068000700c0c5612940d0100959901c000040214405818420764003000c20050305e0311070700d44518070951071400144006840f00881d078102440c861130071840319031a5100c1c01d00d600b16000a0000180c8481b05442007c568604855aa05030781119200100382c034810f410060704592003041030300e05540e07025220400700da40741c0a45e16510a0010000008030342440c00c11301080c4a48080d0050101f000c0581c100341000300ca40e0480980c10030202941c003c8410700c0392040000d03013405448000c50280d0064091030420342200080700c80c000f003144e0b0621464503010080b403507000140e5421950300c1004481c4c42d48410b0000303805089241d040c1c0400900205d02103030382d00300102d8840204000c0301816826907080340c00200580e00b0402d8500c0260708 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 726761205 1250 726759955 726759961
    0x106030c0e0a1202040f0b01021203040606050d060509010507020f1011071505010501020f03070519050c0307061d010e090a0504030c080c0d080a150b0903030715020a14070803 77
    0x8069048808402100e003800504003051901140c4004000d0748070381e0610050303242d40703070640c2480e1241500300c941c2120103100d00040140040d41d0340d20f41e5985c03a0002a4000001000d0010503031056001e071400038410380b8050424200080a850103480154455280c407010402d180d000103040075000318180003803c0ca2504910001f4000c004810101c2b83e034800401c031034000200c40001044038030442410014140d410003000a250410101c031403201c941c0b08000d10f02c003150000404103019004283c00c0070322000c0b1860308504000400c42e446802d0f214007180403d00a81102c4c010400740e10041c5070140002030b410046810000019803150004500b80c0481c8a0444580080d03522078000d0922040454150361341e12107580c01007210320b809800c08003102000b154400c004a0300071504010610008414000914512205100d140e0414400054284160f02e0503c1650350040e00644280f4000d82d01c0003090010307600090a01001907903813881c01001e00141002c1c1c071030030740e0400c20690444e030f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 726762455 1250 726761205 726761207
    0x11030c01090303051015020c130e030301090e16060e06131203090305010c170a0203100b0f0702040606030e060a0b04110409060e060108070f0302070c0906061d220911090c0a02160e0106 81
    0x6548071000307542c160300c2b00b0300c0071400c0508000650091404031400560b07140c440e00d100342049213a420109002e2085102007184540c001e4000030200740c100e0b280d0b556051803071741030030540ca0f040e4800007030b8007214944403041c5034100b2500404c4900401c020300440e0318201080f15681c0c0c20111440c082c00d1440c01060141c00654051541701ca14950321100d455183c4d0003521290700003101d10f207200d0000090507000c40c10302d0f0007000020803203418288a9400c1800d03900303444440042c100703c02c2039611400c801c8240c0c1c464100418081595807004c5c1e40e035860308034a1000d00024003954060300c0140e000b2480c954805e00b801031242c1283d175103040307001050b0344040f006136000d150203881c6010024408900f45815210340401000152203141c41c1c1003203000104901d20030b00008030f02c0f4100c5090380b08014030414803400c0070426105400100d21910380781120303180202098003a0090450010444c0380070741c0a0003480651060703000c0b07400d01580040d044c1c10f808500e0203140419040c0d200100409 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 726763705 1250 726762455 726762469
    0x1505070f110a080303071106010b0a08090a0c1d06030607080f0417120703200306010509060d0204030606031b05031b040f0c0921021011030c01090303051015020c 71
    0x2482041d14880310840400000d890410b00d070003045580e0000000d101c4416000ba40114150f8903410150030700398945034941c00d041c0981d40c8590306208175000000c80c0ca000500a41c80100d41c0320540c0313080c0d181c82d211104050b2820b4541f80c3c944200c4c1d04c002c94100e2600180e07540c1b01d00000d5890540c581d40300600200d141c1c070050021501a40c1281c42144440044405840260389004010300d01d450840c00003419103071044540360b100000300a02c030311444500c00489501c0142801c00716038070664000032500c1d0740b085200c9082c14501c0410080f0030800356400102c1103d005030016421180c501540e51a103e40300d103d4651315074484901e00c40745542d52000414001c074020070000c2c0c0311051294050070380380503070705400000380002018003101e103128424107030304e080c2883d84075582e040320b43c0414200c0d40215011024403000105240740300c02c04004a43c241110603000b445009807525000c0d000c0e10041d695103a50b64150540842c4191000001d541d14494550003014a02e43c2c02042c4560 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 726764955 1250 726763705 726763733
    0x901090b060d1b1706100f020a06150e070504081b040b09180d052502040e030f030f010927060e0a1104050702030a0228060606030b0406150507 63
    0x450414001031040742a00e00c10001c0c8246000300541c490f0301c07901d00081814505070392000700c0f800b8031001d0000c5038450800450704c104041c10400c1e070845140c2c506901e010b48030080181510b090010032501d4600a0000c84100c500e02d0130900041c2c1c40e1003c007620507020b1405090241d500022041400c41e0004c124034841a4028000068080386c0c0004902c031501c003200d4940b84098203602c0c0be0f602600800c5441140681464614101a4050f007000103480f41c1840180d60400e49112803019075030b4560180015828180403255504030030b8108072200d410880701000c00340c8509000003600b000300d00178505202070143c420041c0c034015010b1072a070800300410070358070301d030760303010641d81c001d030f0821032048410f00400c10f4181050302001000195040101200d0440d00706219101d0100d40006131010f241d0a2011907041080380300d0314010408001c1c00d07015010a0500c3e00018a40390103500100000c1000e9034140180350b1100c99124105581007030b0440054002c010503008a80003c40c00c0321 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 726766205 1250 726764955 726764959
    0x5010210020d06091121060a0608100b0a1d030c2d0301020414040f020a170705070b1303021005060105030a0b12060c2d0d020a1106090f0c010e0901090b 67
    0x18060f9111025081220050305d2034204005000a8000600401c8400d600000300c004429000d646480c00c0860302014181c440c070b0003070040c808042100024a20000c02c041d0154130304841d01c0e400001c4005150401424908204108102c0c540c806c908001c2030410441c580030713103601c0c1c0034401190079848003a181d60f001d400340882150f03c140d0990b0203000500060594034642140c801129040000300e510150202c81a5441000b80c0e5400c1e90b0072840f56510041455031031019559007035801e031024401c001d00142030300e00b404100030b081c40c000c0c00b651403400c0c002d6003120036407064050144200e410564140e800b140381440010384080b00e54024071034581c00503260a55030001400d42d9440c050040d03544190f08240481c250f0464070002c4c0c4240140c01700000401d08150b6082d01ca280d00b0b2140008007106a500014020406406103204000c13025437a021140e80b85415035226468003002d1010030014012450340c09415031240501040d054801444032810b64030305a003c900a000290040d5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 726767455 1250 726766205 726766211
    0xe06040e0f07051e210307080a0206040311030a35040c1a270604030b101505090906130e03030c1201170604030c020a0f0303120b090105010210020d 65
    0x3810010103006005a03841c4810080810074206000c01c43c0b61114590b00c80c42c0c9030350b01e0120419564030b00f450700c0c1c04041c191043c020b00c00041c80d61a800d5114240e00a0328901d000108140390359030020314a03102d40c0c000d0755002d900605120766240c40348100b141c400005204100783c0c1004c50b1014100700c040485904403020203061210400c1e001c44400c8070144c801600c2400204010040c3c600c00d8102414204c0c4594a8403180000410220305080540a4440d00d00106142d494036100c0031030303000d5a041005888140380c1280c0c0d0040c1c0c41054002c503d10507692845900380140103005a40046200070140001c90307443c0d1052000390510008200c80c0c00c0d0300ea004490800d442030004500074540d050b08180d9844450405e0000d5a030306a21440290440d100c032000b031000081413882d08294180340c03c25150126000007038203009103410074038906170039400000c2010382007494400c0c0ca1100320420700200a4a208214010009103e1640503030000303454034400c4003850f4010302d04150801400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 726768705 1250 726767455 726767471
    0x70b0a020c06270f07150504031509031218030e0301021303020d080712020d0905010503070507060207110619030513050703020d0501150312110105010f09020a0509130606080709030c0e0604 83
    0x2079440d146011551301100d42282d9018000180007a82c4011800914200f0314030780745c5903684180700342e500c150098105070355401d104020140728218080c18440520030034000c0c9015007402682c00b2128200071808252142c5440c80c50b42418000d03101c5200301403038000c1d542e078519000c1c81103861043e801118070720f504008000c0002c6858503181d03421183c1d0b50041004220200340607001c80c0107500200c3c1808024410842c00a500c54111a41140c1c000c00243c0c448040f813802c5401c2114481d0207550000020611025010420311100d403a824150380c24482922506c00035041d18410180242441d00210f03010300c0941055219060160b00c81e0300000740541180001881485140e001161000c1c920412416001e43c0301d618401404d60201c000c20180d4507181c06160a003099101c1e0300340f05600403400c02030003402041074070071818014046201c81440040d403040100028050400428000800701e0351581c85002c0d441c0903a40c0c4144c0024406080004c0f008881c0802440540c0c02a181c00c15 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 726769955 1250 726768705 726768781
    0x91401050a021501120c290d02130b09130207050601060503130f111206191503051501050a0803070b190b21010b04020f070206090402070206070503070b0a020c06 71
    0x4907030003845d4408171a099060549440c003404c52050344404080300c4204074406d1220942081541400c10b10310031199a084d0310440351029008445c2d0141150781107500004214404000801d1199400c440c41442d810400c000b4504a0241c5040034065a01c031500600406020f5002141c21044054014174510b00302e07522000d00d403c54502c03c55100b030400c1c080315001d04011600d00341001d0404060b040c0c1c0e00c0c3c00d076240350070a000214400d6009407150b88030a8030b01c0b902da0040c0003642c0c208042d80d582244c01800d503410000c0c00c3c414a4000c00c0c1030b0100003100386000c41550441740d4400500300c40360f103130900035401c0c100c04c030f80c0074100d19980c3c0d031201c500d00c1e5900348444001d00c0a40b000010291010110716007100c003078050050003540100320a200d03558030302f000c580740e1590403901c2070b84456028010074024080c100d4000c0d0041000030300c40060081c0000984486e40c030a09003049155100710a0405a018007c80254036600c2840400c2d100b00c0d0040207030071140d00da50303802c2c0024280014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 726771205 1250 726769955 726769993
    0x6010f180c0e15040e0c03071707111603050f0a080d0f1805010905210f1b0a0c1406070f02040b1302031005041506140313060911010f091401050a02 65
    0xc0304405400009080000000e00c2440951100f102c00e0107c3c00d52903d540301a007984281d0f0302c1400348004100c0003c42a500814400d03925a45800488a600a003602d00000d140d0b442c0c0010307240c0d80b0a104103121511400152138540c6580040940d0416500a60785005040140c4c3c4044a003620703410034000441c00c1c2541c64040c42d00810011800c901c084c101300c0d0415002d03060f41100811a40c200c0d20010301900111681d104411708280d980f2188e00700e10409086030007030300074028000c003c14401444401e010010649a0309009180c0d00078801080041c50303c903440300140f900303c0c0780c1400000b600c0c0c44e52010000101c081c008540000c0c00d9054213040fa80115041c41c281c4c0c0d03c0a00601c8107090038401c80e044080c05c580d6007550301c5d05100e009044c00c201d5590300d0303c100340000001103802509601c4203030740d5540550180f06102007840e01140d9070302101c6200780056000181c54a139940320f2040c56046072a2001011081c04050004440036480303e840b0340c00b0340c0318180304c01c1d48106086c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 726772455 1250 726771205 726771229
    0x801150f122003071211030711010212090706020f01020301060c061a04050a0e0c0901050d060506031c022a10030e120c010902030c06030c03070c03121401050306010f180c0e 76
    0x40780c035540c0c1340b4000c5009840ea1000314200c4480070700d000f0a02d42d10300c41d190101c03900b0640b24100b40c551107018950320b07030180c031504582c400c0703000ca80402c1c070042210000304041607507030726000d41e98003051064269080340024460400016010004c0034049001d036403181c1e1095000c038680300e1800e0101c0002c14180c1c0d83c1139814907403040d9110020f04610f4000e00c0142e01503c01154015999403401c0001184038000c013001034102c03503031074001c2507140c0d80030000428110052180f2522309004510041c0d211500100f0700302200c0307000d0301346040503c48402c003403080e000008d001400ca0302403c5070860050158400603401c62080076407442c00300035801d002d050110796680022601c8401441403505190720081102e0280d00c09009001c1e440c0c2e051015250302c100e081c6445858010079080454071100301d5290203111a2a0036010300b2180f05058655060303543c00d4003150b445990380e2080401078242c3e4491540180e0340c4810810341c540503034010b031203201454070306049810701e141d0000e003242c4844 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 726773705 1250 726772455 726772511
    0x31406011502011e0f0209030a0305210403170403020f03040305011d06060d20061606060501020f031c1b020a1e020a170f0f0d0801150f12 61
    0x1850040000300044868030722511001c1c4000e11103040010211212450002200f40001d511000013903034500090f81074401c00b00e030050031a101c84440e4140a0810303484280342c110400008a07004650034140307101c9502882d4103982c1c20303190809242d54280b2000d00544100c08500500c054260400300401c0a0006035004000000740304259030000101d01170644450102ea0b008041084413641c3e9205603002110341018081c004540716401c00c2d4029041000e506a0044001c2403007031000302e4040c0c010054070722582c01003003c680c688005a0f40e4281c15080c9110740d510401110421101741c2841740070900d14490003007040304102d02801c2d20310352440d00307180043c2d00c00030160043c400d150320210340340490340c60700c40320391400d075000305504c15424060040e100700c0c000e10441e03080500b00f0425140881103c260390b030041e10380c401c0304c1d298038410b951000060404400450000b0f5100b502c06a044004e84500381010b80d80d0506403032100000100100712541c8000842958241c0034500d0250310351 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 726774955 1250 726773705 726773713
    0x22030204050717090f1c050d090605010e091b130902060c0109051939030c060f08090c010f1205040b06041803020601090b1c05100c0f0e06130314 64
    0x1058400e4910f0000810f0315280790700451480403580300128440380601c4c0710300c204040710303140c41c1c809950500c00d038080841824034005081c424085a58440d9060700c2222007100f055450b0004440d0759681d03c61010740c0207107003404080c60300d40707020f1b0b100c45014040103002054502058001481036000001a81c000740d440f100c1003001c200003400318014003803d100c05c8914419040d268032003001442c01c4404601700305109007801d0040c00c051800c80088803a850b040c0c480751207281810700217102c0d11440d00401c80090fa4038040d1401007415520400007080180f900c01d02e18001100e104249681e1181480641c203040b100d00d00c118042c25100700d0245080c281c1e1400d01c0c5041c402241c01090240300311406100359100002c1d40801d0f0310f41114480880410640c41d134800040b02c0c07062075103000c00c2c0a54981041020010b01040007254481c11381001c0041e504507c0c03040c3d403a4030740c0300316440004a01d17011058041c9031200c05440d80d4901c45d0301507060140c03207554003038009004100d000700d1980 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 726776205 1250 726774955 726774977
    0x1c05011706010608070807120f090f110402040302010527030f0303070e090601170c0408030a030b1305131202030d0c030b100908031b03090a060801031a040305220302040507 76
    0x4000c0d41e401000b15240004a9240003900145450f0001c0d05810400c104403111502282182d0403106101601d0071041220200601c1c020340340c0418840125500c1d080d840200d07081d031405100341e4048a8044c1c54503072404418901c50451030008024481011503064001da405450411040f40d10841400c0110755905103428060b0000010b0390400340b01d400b00354200445a6440b035400c842d00d0041d20320740342c182c0d16541480d040c68001d46c0c0204d00d26100214941c02882e5042e00074101036041603a003a0484c0f00f40060724400d03200115980340000140c0e609510001b400c000b0346084519651050b2400d0550131010101940d06c40e100b000006601c9100495440c40d048a1450040400b030524a262f90700c1c0c00c0001d0780f41d00801005640300c0c00b0a16140d40611410b100726489104d00030130585089407103050250980000b0301094540180c42207590340c02a110990701c901540d01500d8003414805109101c4e44900900c0c40031a1800c62080000001070300c440c06841d00840d06a15400520780b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 726777455 1250 726776205 726776249
    0x30b0901050c0406050f0c0f030328060303050415030b06042312250504020301030602030708070e15030601110a080c010f140c071a0903180d15021c0501 67
    0x1e2001d0015504014208001c20200307030020101d034101807403042059115a1803256990400c61003583c0c00e02c4600000040203c0f02e441d00410040c071080b00210b018904003000800030032075919000060114208000510580c1410349502007544607500d000708400e00d103400454640c0c1c200d40d0156501c4079511400ca240711500d41c40700005020180c645012507102e22040543c2c7e198110310f01d401c1840306000c010314086011081c50301030913010b0000d56a95a4901e000c1c0c00961080b1150b6002481300302c0494452446880185915a0010402d02114410011408844e403014240364140940c181440e031100c0340502076500c1060154150382d480d244941c50181c2500d180c2050060391601d4000d2100007032501d12155a000b400c6055265110380c42494030304500c203a900e010b0050a0541c1c4d0402590303140c000001c0012030030300700e0550f280503081018081000c1c02070100900920801c28a100d1110050340900072080c0032240c10390720302102a0246c0304490007a00411543e800c000c0501c4980 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 726778705 1250 726777455 726777461
    0x40b0712080c070f0b090f010216030305010f03150c03021b102d0b04090503030a0903090e0f06012106060c0215040e01030b19110c1c0c020103020c0106030b01030b0901 74
    0x70a1181a180c3c2c90408207585071002c940f68540002c1caa41c00c40c002060018204211640c11018810300031992003c80f0f030000a9103d0b001070701200001d080c640045003160f112202042100d40c4a00024041c1c1269400b50000e864401428010942c1c01d200c2410845090034100b01c8029100001e0051030303400600b18030540b0755100e4024003c0d0100c004800c1c1c032030410204040f03081c0c602080080c45c52116400100035000301c19000d40284401700c240927000243d5409202c0561094541800701d640c0c0e060101c1c40b6000031610303280d280f80418002207081d4010401500490013200b908044100a0f100c0e04049661a820002c00940054050030840c00c00800150811250f0210303541020300c0c1000215140382c1c14000100610341c0800403c0c16001608460000104d00800510114001010480440d0001185040288100401c0c41d003458524042018000080e0707940d00841c440540040d0040d5104c602d01409665071060b0000210390a03044081c0038600c9801042a2414111a01401c2d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 726779955 1250 726778705 726778711
    0x4060c150e070e040809090f150301051e040f0c090f05010f0b0f160c0e0403080601080105030c121c02010b010207080102040f05010804050a0506360d0311040b071208 73
    0x64584003401e1100c10340040c0c10403c4400d2550065800d580360300d000c1805004450030281c002c4014002c1c0710302902c0c200303110751040c0184004501e4141c07801c0c0402d0b0030303200c8c10b441da501100c400d403040d1451490f00c4a940c2d0b0380076001d640c802581061940c4d540020301c0e102d41c41401000c0e540d002c00740c203d01142c06503c0c01090901e6001c0724141c240300e0b9034102e611440c0182035126800080c1d020300f262a5036180c0840982000c0380081c1c10f50350301c0481030314010498044000400d680009400780d8000c0c0745c050705a840213401007140c1a11030342400540100640310030114411140c8415514100310030070f50f0100101e5001049200106d070001e480c10f0300c1500000c51590041c00280301d001a80000c59007150000d00c1c20501540750350038401c2c00c1c51055840a055409003804101a080d1042010740c0f004003c3c0451034228000000140440307800901d07501020740100c07010a0030b1510030303000703030320b00ca402841b600e85080d6581500000c1a484005c084070683c0d01a142d20a030241c04c030040c41d034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 726781205 1250 726779955 726779993
    0x303010506031807150305040b06011b02040203070302070c030606050a080f0c040504080c0f0a110402040324140103150c0926070b1b0d0f021209041104060c 69
    0x10555040100081c154040181040359003841035640b18000790041150400a0a00e4041c8804000903a07200901070101107900780d40c03490080022407581d51280e040c1000c401100c182001c4072104507409c00c0044e6202501c02420150240043c002241b01319010030003c62089a001649038601428099a4101640040070700e810a07210003841d207070003103a001c0700344a08940c00181c556503072034600d050f400b5102d00b070003203881500d002031102c6100062030b06109019010002c0d10024000c10802640b145010003007600401240c40c405402c14200c54a00000c803103d008180410140f00410f0500c40c260b209940802c8429070701c09000e5030794410240c010602e40b400e040c800c0e08140c086003101d0001e803c80a078101d145000d031441030b4821701540c2c0103050b22040c15175440d00321005407401d418511383d010440b4010b00c156460395901590400508442c56000762a0218612145008a4010582301e81d0010f48490030303400c0303c1c40c5990003003010b0040c036201c6140c0040130341028000c074070300c80440c04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 726782455 1250 726781205 726781207
    0x10f0c0e060a0f050f0403240b0a0501030b0a03060c05030a050a06060c0b06150a020723090417070204020406050d151a0c2a19030c0311031510061103 66
    0x249050312040112030442c1c007a401e1460301ea040c2c98408555a1042c035103103100011005c9400b1040180c0a071503002c000d42c01c200c0b885154a1540646000c4610107501154410040c1208010ba54004e0704410120440145069030060b80c070f84458083d10025039030b04001036000404c10403041c3c0c9034410b140d00403001050411540e410203102908401781d81e00040c00c105208030020751940d5880c1100941d224030b2140e00c90f116180d840c00a51380e01254020000e400c0702006e07400d030500324600303502802c4c0b0800500c01c40640d240c68807a25000350003240d140c0d4418808102401c007680303c900040c8010421941c2c0c0c0e41d5264458502e5208941c502528030842e003c89582c208080d040c121212010040300580840d503461001c540f084c40d00403619900d10f0700301c1c40c0640c1260788001c4100d1480d5820707000d071094143d26540001c4110308040c20301000b002440718603820300115000707103c40c00d0500b6001d0101c85175008841c2103070708201c1e421100c01a5501d5100d100740801c0b6402160207000b005c1c010021 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 726783705 1250 726782455 726782477
    0x1140a0204033215101e060503091501081b040c02060f060a03140a2a12020d05010f0608011a010c0b0603190f06110c0318031e010f0c 59
    0x22610703c81c0c40c4080c0c00d10b01c1240f80d0701500303c0380c840c10107504060350200f207505100800f01c82c0b0103111011981042d004c150180d00040140e40c0c01403a1180c070446000710321075242410707000c6d00d13650400740c52110b0724407494504a070400c3d5280314041c06031820304024920310340103000034504250b1482c5818021800d1055900d1034580010707150790002c0481c0d409501c03903506d06011600c0c1c480c081c0d001a2000441d500c90807414800420380503a440d000b501c210141d450108111110051104c41c20b8401d1216048204082c801c00800d0328500381c401441510094860b450303003425904280c3c10f4080503540d8160400c000c0d1024450545d100100c1c01d4070350b904508803c000703481020501d401800140d0550001141035030113000300d56816002521208000c00340341411807241071840c80032201c2d0b40c503180714a0444050720081c1c1e0000d07040301c0000d5191540310000d0341074010484400316051320409076912000111040b84403a401e03411400000c0d60301e014001e41003170340c4401c0d25100c14003c6500749 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 726784955 1250 726783705 726783713
    0xa05011d0d020f0d030c1202010504020904031101020f12060f1203040902090402161202060105030a0b28240f050105030402120c0301110d1d0d11100e01140a020403 72
    0x5203009444003100d2145050826001148140158101e00eaa1092524540b141016040700c19440360f00d018001e1545c0c0d0800c0c42d0410303070881c0c03030aa4011703520a078202d00207000244200300e4a8016201310001509042d52660310003e20381084d81844011001d010402c04241060750a510070b11404403880040c00700400c42d160303120b100354000c22000c0c0f40c001940700100d80f00c980440b903c030030b0b1040310440650118181546c0002c00c0810305401030003104000a050310b000200745000580109504201c0e03298580e6100c40300d00c4800032043c18002441d025070b0300c030001d80709004595000854940190b040b6041c200e07002c03c40c5401000e100c82200760103001d6664040700342ea500990640e0700c550381d491f614080600d84a28180004d03410360030100362040c003180c0d942c090005001b08000500c40410712044412041c89002ca00351655032040d038072400950710031001d40b22400b4034013098030050070540708201d00f9038450b968031078090b80d198081d129040011004050380500c08200c2103003001c1c1541d076 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 726786205 1250 726784955 726784997
    0xd050a05100903020d0221130e0403030606090e0c12090a0b01180e01020f220801090819111f060f090203070906110a0b0415090609020405150105040909140d030b0a0501 74
    0x20011f4207014010480c0100a468030a686029150083c0e568101d80791518000303010f42170500845000800001c00001c5580000008078040d10052807a0380c01d001c3c080310075041ea8000103101c3c102c14850740108501180e6940e41143c081e080c0800424100c480e0520b41a00317135007000241c005c690703104008401901d55050142c88401000d202000c3d40001d80b007400809000c040d400c8840c2c1135280010780010090010001e129200d01200203020382080302b4030580c3c05011641c646802a001024031a604054108007a0032040401038000340e8246c485401940010b1284c02081c0c0c8941e001017400100b03030300900f03c507000b0803061a11000c46840d1004c0a500c51151040c0146080d14017030100d41000004030900c19003d040c104200408082418404042d004100003a8095450040812680074403500650703404441a1a0740d85840d1820007410020000800240c9048941000312700c40880c3c140950807032080c0c10b60f0045960305050041210001c0940d0015043c086d10f9400444d9007081c00b9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 726787455 1250 726786205 726786253
    0xf0d020f061305070308030f0a0605011b02090a02040b070605101a042310021011090f0f04060302031f3819060c0302060c090f0d050a05100903020d02 66
    0x1480d1030740042c0c0c40d21504d403100310f070002070203032030040300700241d0718920301d841403081040e800c06000c0180e0b2180152800380e0104603021042e04c402142c83c002d130130590981c40d0000c041c1c401c01464250341e840002d081e43c2020340d044525640b91400c1c09441035504400c440644074044054480c4041c4165540c0e031840f45110300b08042c884610701700101c44c880b4141701310028010b040320221310f01c401d1000303445440800c2c0c0e075440765180c0125004100224002c0c0c8a94500242c510305000c002d241c100f1650f585c03400015503000e070300c441001c001601c050140803082da1403078402c80310048104800c0c4003541c880200d010941d0179004035881d900061010501105240010b400d08211b5143d030109508040d4800c0d4144801403041c40010120341c004110441c0a010f0b41c20f59901e51203400c600c0050740300300c05d01c0d1a44160b46003000c0e443d03840c2072051034041912480031598001c07503aa40341e50400000e07152854a29540307809901c181501403003008a4408d65101510240d10740f55041440c1d03030315070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 726788705 1250 726787455 726787471
    0x15040b070213060b1c0225050d02121803030d06090209120105040f080306041b020708070801090f110622050916020a060c0210021c060b040f0e0a0b120f0d020f06 71
    0x1405d010121998a0341c100d07044402031200e07848803000740302c240d410024151402201c2c18032440c440e03054280d00c0420816803100d8400417030f601d02801e20008000c1480c2c01401c456150100b00314a100c115458030490004150600c40961101c07130500411103188440c0c426071110744d060004001c00120183e031400c200983c05006191241c032040049401003c003901b00d50513030841521030b0248a600002e000c01107513018412a5005520344840030709a030000207005240c4090f41c1102c000041001050107030500000d4000c5051070504100e10256400720800e0038000890500140514141513284951103d6601051840c02e80b40b000000e64800c40003001803c040d607142d4403046858424070240701c0f60500b100d41903448980410456805805140f2043d244034982500000c44204800983e8101c40280c3d010500131494103c3c0c0468506008000b40c019a5944005048075503425102c007160395240c000030a28040c89070081352910308044549811756000b07945000e1083c0c5d00003503d40d031081030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 726789955 1250 726788705 726788737
    0x6050c0309011b06090506061e0d02060a030b1906030f020405011710050607030306080105090a0206030f090a0807141e0714120f0a11010f0801050405040215040b070213060b 76
    0xd503d111152501000c401800d00d400d04007150148600029002d0040c001160508200c064000c0502009501040c0d03103504072811b189241c0142c07812601400b11050340341008690f1307d03400e0001440c580c2e800c3c4400614008034500c1402265454411208004000e1008614007420400007070500b000c80b48000440c1d00b80c1000041c0700d030b4007001c0420000c0002605617500d401c81884c02901410300f5010725803081d0f103024001a03844130001030310040310350040c0100d0324640b541003044820800007811905148a407110030000240420000c080c094083c03448141c003c2c0031049040d05100d0002c181c129034801d08201403065860120b4041c0c1182c0c418481c08110780c1c038400120340c07420342445044d8484e01a02051116000001c51b65404503445080c181d5004c0e0090801940c911141d8034070980010140d000600417424181d0000340c00c01c4c0000c0c000a000e0061040c40106944550040c80c0b1102002c00d4030021410100d0b00940c05686519040c4000c2d814881b240d600d07402040804900040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 726791205 1250 726789955 726789977
    0x30c070201090e010609182a03060b040b0c19170a031112070221030112050c09010b190504140f01110609010b0f0402122d13050706050c030901 63
    0xb0044050000a11100403109081c2d0b94844019000400500c0b440ca0340503003405a0306a038149510404010107a800e0007420845200a0300c80615001c1c0f15406092540da0340303000c41c0040010007e04010007100c82c800703590f1207008142608142000c40e40412031003501e0001c800081e42590000f0065860786413194480d441c0d43c00c12405032140d40ac448000c40800a000041c0000c8040f00500c42d070036580840e078075044e43c000f40e488000481903120b43d040e0f505000603c428014800c6c04081c06004108031641c03048007400081c110318080e4004031060400040c3c4507250008030900742c0b241450380c140340381014904200f45961855a0b40014403498008242c03150f180e020f1514600b01e180b5200031079032a440d0080c00d0034002c2031082440707032091303d80726841106031030540201d0f154104150740c0e9000c1520381c0084556402ca0980c0ca82481d08100942240c803c2d0241405034420103030320164225410311170810f50b0412449811600400100b00503510300d2000000444000c1e20307081c41c205031135031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 726792455 1250 726791205 726791207
    0xd0b030f070e19050a0f0e0706090b0d1b022d030322050f0c01030f06150e040f02280f08010e130c1d011e050120060708010f09050705030c070201 64
    0xa02c00710071803c00c81c075080910035040104d070300444d41d4140d801c008101c10109000802da80c0d108902c5000001016903000b4003140c02d844003e070142c01e81c00040401e640c60014a0000544c012444543c0180e00012007d0b23200035040544216442c031034880500104626091640c69100040440380055082c050308a0581c0d10f050080c00f009801406445d0380b42003111f403441e146c0e1100140c1900103401c00c00c00703100c10b03d410311504084072402e3f0564507541d50004003d0b43c02d0100400025030042d40c5030208841148240000e02030954a4410505150f140300c1c0b5007800ca146100144040152454070b043d0281d0300010540d055500281e00308256070b481504002c3d125101d040006c0410110030b030300143d400380159000c1006841b0550164031680c8440c180c001540b071641454444080040b000c01555020b080c0341c00b801c02d80070500e0b10030030301031150301c030300d08041a500a40016110070041000300c2c14080c100e03015150f940014460750400080080c03039404050901b02c2401d000007000421a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 726793705 1250 726792455 726792481
    0xa111606020c21031008030322030c02090a0c0206150d031b2001022103010b1b0604051c0201090201020d050306120d03020a0f11030f1c060b0d0b030f070e 68
    0x109191502c02d8083c01c00708801e0714010b400542d0030508411807264003040340e110100c1980d104640c81d95212860780351585500c0c600341d8481500303405102519120b800942c641c2d1360304078864030f0007690204900032075100080c0340c000d0082c0380e420a00300b88816030407160b41c1c0c000c1075481142c041ca0a4004c0d02c21084181d502d01a60200040c410340c5003000c041c40e2411201c2180048600903000c1e80d00300d002800e041074840d680da941e1401c000380c0410050049000a00140c40c07503090103682d4034000c0444403109854000b040d03c0c1075510f54030507560792143c2120f9561804046560380700034484030409074000703551400a140a00300f84040030002078a1503d5a1440302405440b500444569000070040680250f000143c01000070300600329480c1014040d0b4050b204484904004500d001d4090b40c40b400e540d00007440c81035400d064020111072b0b428050082c41c025050072088249d44514000b03e10f422600a070268600a80000d8101e0304c0e90f940103d8480d08440001c1d4a40285503a60070300c01d03041c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 726794955 1250 726793705 726793723
    0x5090f0a26120c010506100503090d03021326250b030601030f020a030c0f05040b030c070c030b040b15270709080a0c1d1303140d05010b030a111606020c 67
    0x181c00b8010030002080038054201c64000d001c10398202c10390a0301094100c50344d00c03080380c18002c5588810301e43c00300750b407107039008002030117500003038034038413078413507880e18081806181c4e1020740007500d480c0344c60680c6081c40041d8200003038100a5034800c5007064900c082d080c0510a4131042c80000c4001003d40e4000d4010710490003500c0011941c2d08400c070400760007407007000d81035000110910b0f110070b00c00d401241154140c030342440c08241035641d42030141040b0fa109500490700400034010000004091868440c02188a9422440700b458114083c10302000b461842c548124400281500c0114a0307020b800c00030f881e07581d104130a95031528015502c685441d803005403036202d25990329040c42144c4c000d000c2501d152111140740307040d0103041c200c070f50101580c980ca10814018181000280981c20034030f0790440390800a0b0500c0a8079003c40c08442d000d034070005001c0d000004100e45c201d56407140b50001f082c64403c460900c0c0d03180d2030f100900c12842c80010701290307002510316403840c4100710700d0340 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 726796205 1250 726794955 726794983
    0x507021f02010b0402071407082d0a051c08061008011404090c08030405130507090e040302160609050f041109061303080c0c120c06030a051f030305090f0a26 69
    0x1d0303a01403600d4000d03404607044410040f00c0c008c1072000700d080c560119070703c40c08485004000c1c03110083d00050100e04800c603290420684a1000103500240e0709111146802c00c903603000042c4100841d801600d103810007880030f032045405d0100003101c590070200150540f070840d4078014070200707540041002080c003140c020380b0045d03403ca000507181c80c1c000018416500c09a941403000d803c0c0149042c2518403c1c1c5000020034001241030011921a03640c076a84103020348105c1d40f102ca148403040d60019007503000940081d0500c042407113030b420480e040c0c001aa030260b8003000a510308007116941c0d402000311240c4a002c001425940f0003420210000146800000da907645031243c1240d40c0e95080d2210b1028003c0b074044001c2200b500300490b01417074145000e0800307441c42e50b40b4800a0000c00000341894840c100500118610710f0000c40c80c400910722035240c0542c0d85240e403040061750055091500d10071383c00000248498100c1008011034004504101e15006000680c001d0400e00d940381220 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 726797455 1250 726796205 726796207
    0xe0d110d0203340812090102030f120403080115081503071805060f121f091202070504110406020a11030304120f0606050d0b07110c151201060507021f02010b0402 71
    0xc20301e0025180c5401c41003444002ca0303002c1402260800d07854083d5482800f28030340200c034840100c501c46000400c00500d0503c181c0741385c400703200000c0d440d50300f1800080d0b1030411094200000c068000e403006024054041c00050320444900009240722802040c80d1462000c0a14400c4a0b842c100401c138050040c0c801e130104440d10f400c001c08020b00e021103082d4826601403e0200c01403c000c041070a034482c040c00981840a41c00422002c811220307030500f24011b41d1141c4140100e50502c1c044802d107021680030f00403e9203130400b0841656549070a02400e040104010001190001540500da60b4464400c02d0207280060000307055000742c2d0701403406000c11916901c100400103880d12055403040348100211520b81061000500b00f00368000d207c2441d10011800442c0510642003c15500004442503240c503070022920055851607000b88640c80032541c12000d800c2c04000c0f0740540340034640700d8107101c0903800141d101403c020014650702240685026081d02c00e401c400c80c40030000e4029 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 726798561 1106 726797455 726797473
    0x60a03030f05130b040608040605221403040b1306030609060605030420040c030c0806100903080f04080102071103011404030e130e0d0f0f0e0d110d0203 67
    0xa050f00c5034040009003c1d810003004001416503650355100c18205032034000c0c10358201401e810140c0400c0c01c40801128400d00300505101c1d0040b0703038541c07814002040d65003144255006020740503800140c50744000803c1d0b81c400100c034001e03034040156555402800e4102d46240c018580000d004002003400304074000300c10525100348207119012029000000340454050303854640109890340b0080007096000541301e82e101d00700b510003040007254544c0081c00703404240001041c0d11400303d4080310341c182c5501610003905400340215035541540c103101c5c0419101601c4103110398240941550020818400c4a00940d8162100d901003078482040115003c4003200c21081581e4898648448141c10464101c01c1030340d58507108000b0054620081c52403050750261014020411070f00180c0b0b40755003e4080f0b0040c1c008101039180c041d00000650b0071144100040d40c184210f03401 = true := by decide +kernel

theorem cover : BRFrame.Cov 726618705 726798561 := by
  have h0 := BRFrame.cov_init 726618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 726618705 ≤ n) (h2 : n < 726798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
