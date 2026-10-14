-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0708
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:16:13.206896+00:00
-- url     : https://prove2.me/submissions/b21b1897-6a4c-43ba-895b-ca1b5b1182f7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 127158273 ≤ n < 127338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 127159523 1250 127158273 127158299
    0x708070302100c0c0b040305100506040b0f09060a240e03070b09130605041a0307090507320304060603030305070207061211070b0f01030b0f090a060e01020717091c020307 75
    0x450f5180180200020074000c145c001d0005948114060a132900320781d103d41040b900b004002501c641d08106452000d034541c15040701c801601903488041d59582c89020a0203c14946d00400b0349800b1900c2c00300260001003004c08800c2695512561010889020503545000034003c0501c4514100242c1815240c40d0700c95542c05400428089015a5190f0019044500241e68207608084a04c0030f50003e00d021300609000d0304154100b0000ca06140304000c002c1d65850308800c0070350a50851080744000c5c004880b4112144990283c0d0b40c0307190038542000138048511040380800d040c8808900d0050021078850203554031ba40d0341c040548961100003010303204500280b4050714003000090003003241c18203002e00c00c504240c500316441d451031400301c0504400911054141c0208424812080f40c00300f07442012580001c00419030300558241140284684000106010000e182c641c0e08458441c002d4103104104980a02030074203070040d40d0718072041050000758150420039040c001c000e15020 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 127160773 1250 127159523 127159547
    0xa09080910030e011e140c030c09011206030305040501030e031905090f06040b041a21060a0e0a0903020705040b03100c0215040f02090703110306090408090607060e070807030210 78
    0x2c0e000c159611100701140c21924130380f140c40e801e1001d01c0c0c600d040c5140140528881e1041d40d010981c9180741648140f1440c0c00081c00c1c10005a60000b44040e84ea84903090110b121038081900300200c907130b203142c080d00e29032007441034501003400c2803c019518440841035585000b4100d00110300041100400c40340b542c84500c000b40d10605d003c5c43c1360401c0d01c030300b400740c0040d004a07661203682c3c1d41040040040d00d200065807003480c2404024020107402603802c07580c81400741c0800480036450360744c0060012803050f00091400500d680402c0180070081c0c100d5200c0c0d500a40940d142d81d0b850713205200c00d07221582c910a030141d0200000c1c2da550030040d4000303102c0101d41c0c41a0f651000001c9102c4024140588080d1810700020000c03005500c0c22040003900200c03103041c204824120303401c807086030b0f000c02810b2501c214044000074091013240f40841f40b00203001400c160f521003aa103007080c01003011801c040072a04c00c0c40008102c00d8400210b680a590f00203086098900101c0b1046902508140d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 127162023 1250 127160773 127160777
    0x10c09050d02190b0a02010504060b090108030a080402060702040c02031305030d0c0b090705030d09030302010e031204080702030705040507050c010e1207080f09060a0507050d0810060c03020c09070c05060a09080910 94
    0x205001401513040f0f8060300300b07020168008110707420141003020a581038505168400e22000004100040300001202d90030880d50030031101c560340754000070b0094010074401a412600341031241404c0c1e0780c04001403034170708080c101c2469196210000d0660300c500210700740000c15001030100d404184100d0350558084500400c80e005140c13124003003030500011854182c00310b0681c100c01c0c020190280103500740b021445000394140828642e40e52100c01001d080503020750400595201036480c00d03c01c00c4017400c0301a200303104e0fa0808400080180d409156510311700e5181c03143d49210b06002041d18400d246940303038114105003142e01c074030703607240d000c00301d50000b1042c2005003042e252141d034098401c10303440e9203880da10b40d0740d103040036820401005851000c0049107010000c140d007140304181d007920090700d03101e403114134640f40591501d411991030b03d501c1a81c0f40704200b02146d120b08001041407282c000d9451b680c4070700401d8800e40c0c4188400410311042401003a10608202405c48c007464694 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 127163273 1250 127162023 127162069
    0xd050c0307140f12030606040b070201110a0b090d020303040f0b10080f0106030c060c030f030e1e031806030906040b07050f130e07090b070f08090a1502010c09050d02 73
    0x95034480c01c074a107491440420307540080e40e00f41c1ea00b007402c2c8035105000c0401c000b4030b45540380081c00920b05100b503014486c21202c0101d00700066901c585844044500c580303049903d0300d00241400c201103c1d0481e1440c80601c04e840300e40c21014030100549000d2035000054004902065440c0c00710346500070f00d181003282880d07800180f8100c00300800980c8203058000051014258100032a4000268009500348601c010300480080d030700074200400c000240c0350004002c4540000c803401e1688010050040ca032040480e8600004084010150f80e8141c440074102c06070800c1c2840041d001c1112003001d142c12000c0018040b5415104442d880f04940c50014945104022008441c0c0c101600400070700560403000d024440514005a821160906150501e189424160074030751041d420000d00036494000303844100722480055407501c00c8000e0800341792544558201000c00c82c4031400500642c286a00d400203203000c0c244aa042d0341c800b40c002e641800b02c0303409201329565580c1360b6000424503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 127164523 1250 127163273 127163287
    0x90a2a050f0d080403140c040c0e0907020120040f0807030f060903051b0d030506060f040306020d0b060a021006051e09180105011d011d1f080a0602030105190302030d050c03 76
    0xf2030300c0200b015611a070500e12141d01410340c40707803a0a4540703000c070340540d24001d90b40202640110608081040840d0351415541c1d501d00124090868078885500c0e1a01c0c01c44080121115600030700143d81d41566461201d0b03a0722425596103e0303a520001d064103002151403004504d003074000f603108500906181c0c0c504080941c0c42032858404522200c102d802000c14000c1d682d40c1805542c1d0019422106181012024a440741c8180b160344401800c85600182c52550038000b500502c03038420b0000c00d0a0f40b1070342000d1000c0d488404041c00244118a03160b00450700e80342c0210312450b0750301e01c15a10424218854140941000d000e003008001d1a0340c4910403005913000d01036039002c0c3c422602d000f0092050600e0517220b004041e00110f840164108001c1640d558840030b00d82d00c44507050b445a075800400707041a4502c2110340140714070340034821020040c8640740d0011412502c060f200d0340740010450a15100300c000c10b02009506400039103030144c517588104041e00a010540082d00d00d0100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 127165773 1250 127164523 127164533
    0xe1303030b0612041a06130f09140706020d08010305070302010c080d1b091410030c0908060a05062701030b06011115070e01080103031e1205090a2a050f0d 68
    0x240480c0c070a00b10150300308805c0148000440d0200c95614010349024141b881c005003250007904216100541c0d2010200c0c03092100c0d8020300c10035a041022106a0484d2040081c3c4524650003940058880c000000048510a00740e242c1240e4005002d807400741d055900465030181040e8041c0d031085018040710015002900c540d04881c0142c800c12080c80340090005030404205074001210081030b070502c0005500c0300891b90740c000105140000d50191030072810384006e9140c2d0400c52081c840d40707040103003401c015886135010b0741d41254241d440c140f51681000a02403000011501c40e001c1c04010000612405162604103005041024100311050301c60740c500204001d1801183c000d441c18004170541200c00715004013400e18103000c0350340c1940c401030800d030003203000c0620150040c1e5245220511801482c2c0180360703581030600190520f5440325076561130302c1000343e42d041c200411171911140050007000030440880c0c5901c0805151000300800071110017003c0e43c000e40810480c1000030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 127167023 1250 127165773 127165777
    0x50d0203090f070f03080301140301090b040303020903071202030d120f0e0307060b040204050307030f06090803010303020c0a051207090f020f0c030a03060e0105011b1a01121b0e1303030b06 83
    0x19240000d0203600c07070018410303240050740e602c2404d08003c042414804249280b0440b415100030720022a0b0540070f80c0c020900414003541c001c0d043e80a24800d1004240d41038005102900084045420f29900c0b002d00800e00701600100035030550045256200307513401010000c214851115001681c01e180c2044c100542d8048100070440d41c10000c1e0110400c1954825018150000d4800714282400d08020954900460101500d8171000307034180410000a134102280c107170344c81420640c5959482c175010795074407d01c20056105d03460800c4080303441d040101c68001e5854185006001243c80d040b036a1303009100c0001c44000c40f03a0200208002c2184000041c03501200000c000d40d0794001404d0010110380039030b001031301c1c035a02c550010440d81c1c4c3d01041d91030b40a40c0128044030703403815902d00075001d00182d1080b44028036900c030001801800d80d201c0801e600d8082c0a60795221403460989441e040c4003400b400710070030300050204112900c00c1c464a4800751003802e0000d15064408000f503066 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 127168273 1250 127167023 127167031
    0x20114010f0918020d0b0411060f04081c0e0f03030f120108060a1e05191d0f07050319020d0804080105010f060c05210d2a0206040c050d03050d0203 65
    0x180740c0c00c01c020002d010107803150507101c50400d0340000c0c040080e640001c0850515100107001e0a52040101d02440044400549000701c0100b1240c1c1e1038190101584994105102c0c1c0d00085c081d40c4041003071032400954205c80c002d195521982c1e8051440700704882c2800c16170307040d0b4061001340161700031125210010482210140c81c480103542c07514030301c03070301e03061005007900f03000c504151611014040248003103c0403400c00c040440c10395030301140c2581c1e1000ca00e0b01041c5113810200d011b000c003d04101502e50581d1100c0548032180510808955540f03040d00c80c07642c040d80404980881d20b20440d28244103107100800d0b0560f8038046484515080d00507070000155030b55100010840f1a48950300e010080c07a1504240e01ca04882d602d1306901c0316441c44010542c6028564812100c0c4103031002c6801c445c100c0303001003054052310107803180300c10580704580441960368400642258000189035224030f03440301c4a41e0b5214200030520214a424940c110140701d81403050600c0000c0c0c03400603600c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 127169523 1250 127168273 127168289
    0x4050d0f11030712060b01050c01240506090a05090a09120f0e090f0a0f060b0f09090f0108102a02060a1b0c02121207030512010905150d020102011401 66
    0x8444036070400e079141e07158a94600d0301c02d40c0010f604010796059000d542c501a50003030000142d030b000020040e9058820152801c18a5203040c0c60740c00552160f01c003910b000301040901981c4a0b0f114003c0c0120380c8502c2207000d6004104500030490340c500001600ea01c0b071240000414080c00540d42d1b0b66801984440b107602150b4019180e107500c0354080710301102e000044070b0720751003820010711a00c1000c2002d000c404041e03480f07200c050341700c2000d030b0411001049541500c40d039a40d10340a020102d50810302035180301e4449000459040541440c1aa059803110806011813803c0800b0070070080000500501e2800c4022481c0020005c100c040790701c0301d03651a006440ca030318015103680b08440b00000a45801021803003010f441680c0300290900c1c0607816559604403904407240b16113407419000c407d0303d10500001e00082010b5004015004400707110b00d000300280d0301c2e140b00c00c0507150103c0e08604407000450036980f4503d0b103001c80b0700c02c040c0180000542e400d403900c18001d10720001d80100030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 127170773 1250 127169523 127169543
    0x6030b01080f1015050409030e0909010605040b0409050c0112200307020d18060e150c1c0905060d020304060b13020307020c03010905030a110f01020301031a010602010915020c0304050d 81
    0x20b4640c0051000003010310001104020140310781a44200c00c032440c1c001e15003d142d07100324100c1003500402110700d8450008100d4005403800300b1405001c0d01050240c1c40c025403c011082150781031600a140c103080d030000c050519a09030740011210390400d03103090721000c1c3d11080140c0d2042c400c68100e90f40082c0740880746640c0e1902000180c500250b0343c9040c002c101c6202036910410b0110340255050b43d1052400c01426403840000450481c948442d04404801c0000e411000b001d00180244102d9050503584450300001503040e540700383d240c1308590f000841000b805500741415402158000c1c410103000a000042d000030800e0003042002d0000ca107030b80001803040058040107200c0551504a00900410b111651910f4a0740074031034000301440115880059014000d1141e41c00b01c0301524021502c0f503960341404c08003030142400b800c100401c08000410028030601940240d00c0d001041000424540d0951000070350200740b100003140010700000c166580d42280c0c80b0003490141c64a50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 127172023 1250 127170773 127170793
    0x306180c070f1b12020a05060a02010b04050112020307080318100309050607030c0306090b060708030403030e120702131a19050a03150c030c0c0609110607140d030608100e0106030b0108 81
    0xd045443da4000c01051600c1030324920041e0303250546042a10815100eaa8684902d4402a400341c0021006582e00074280f40021409241d1403140100c030354001c40c1121034a550300c003890b40d182e00c150100e000c06180e5070141c4ca0f5042c01e020500d202102110310b00000c45401c1c64540c03504100c0203590060003c2d4540440150250341800b0744000f405c0406e4042029200b4407002400034494118018001c2c0400300004003818001d03170242d80023030703084400d650040103882103a81e407e0740700b403508a11600049100c0000307100d00d841041d10f05141007100c6055084e123241006501d0824905c05100c074001e02c3e1b00072800d41c54064001c0020740c42520303001c00d080f0303c400c1d00740282c41549150408051401e41002c0503c1d6029403d02440c0ea00b245002404110760b081040c010b580c80102190800c02c0061f121040102035180841851080410349800c1c180415044040c4c41e824401c09000d54080307650411144015400a209100754000002e4070076600c0d03a0703044481d070099111410a0b08260001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 127173273 1250 127172023 127172063
    0xc0f0c03120114032d010501031218141309050d0903150203090303040201180801020a0f0305101a0f0c01090602190305011d070309020d120e03030306180c070f 70
    0x1c1c034090b0640321120320b02c0d0540c1d500469035943c4221001804440c621003a40c01c4030703004800075000d02001c04000d01140d86c59043c040c001e1050f4000d01c500143c0c00000545440852081010544059000007406c18032082c042104044041c4d400c840c1c02036656a603907001400420820009000c107403214101f0394a1424680c2407910090074950203203004008101e01c141c03003c400c4a91040c0d090a0020680c030b024200000d181c00780d9044841550300c002480c0c4e40803904501c880390092010b035400e00965480340c210221058041c8034410400c83c0342c80c0c4444c1c4860280002d044200c40303598405080c032188030200c0b425140201003d45625a0002d0318840303500000ea4202c5502000d803d003030005515002c0ea9811104445103901801d203410710105100c1d038480d4101c0034820307400074084d221010480c1041c0510003840e04110000c5117140c040d0290034240401581d2040000a201c50101e915a64465600c41d5004040320b42d0400c041040301e0000307e1686400b0a03540c014135401d0b54042c0c1080310 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 127174523 1250 127173273 127173307
    0x106030c0f032a0216030602030f1806010b0903150f01030b07110a03030b0d0204140a0f200a02070b0a03020d1824060f0305010f0c0503090d080c0f0c03 67
    0xd2074040505041000181100c10003096803807004090740c42c42261000304040b82050a50018800b034042004d4000083c003003641c007d5802042030340048403064465404008101e011a10000319a400c80d900400020343c842c8080d04003110003030141c0e145805c3c036004054075440203d40346180390390008014000c2c01032110341140d12071030074104026004000240141c0d1500d40c00c0c001010507840b200c0210568880300f2032801400d60281041c400704174002000402282c0440304000454a840c031891700a601e0741c0501504820343c20340f010064404608903a03110f601c040d01d2407055100b40040054111001070060030180400d55006888a52035144030303013aa0503500c0c00701c002d0510403660102107850910b00c1e201c452414180580b120340f0450506000e08450f5114000d0226154400803e01c40190003280d81c41c0c9008030100211101e4460688480c001902c0c000441d51003001c1d15450700c2c0c002d0f2030311074200c420a0343c1e20f4203200804d000700b04250b100852410703441d0400b1030805121200584 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 127175773 1250 127174523 127174547
    0xb061c0e0607020a240609020a050a031406010c1112030324010e0a06050304050c090106020102070c0b0a0c02060f040302031902030d090b0d0b0a090603030e1305012601020d050106030c 81
    0x40034010880e03058a0f88001038a0100080c0200900c131308681710129202d9001d8802040c100c181503444840345a0702803d9030b084454030601003070800003035800511034082c0c140d01c07a0005856042c058400f5403601094205544c074801d82080700002c900c40200805c00145106502e0031380b10080c9030b50103003011842d01c1003154455060000c0d1843d01d0440d5620759880d032081c1e032050324007070b030b20303a500c0e42030030707854103a00e4020550001c6c41c0700004075100d64107400400d04a40500945010142d8071205a032161142c100400d00044161500758010300d4044000c01a4a0092000c1d44c14541c41e900020304007107001250344461441c0440321421828244441189120745081822400e4071b495000039076881998224040c540d5904d101c00120b0740c8030802c90000d0140e0032003c009642e2203184c050302d01d901c1c00101910131a001c01007510b901d0003a00425050700c44d01c079a500caa0910014104820000c0f100c2c61041c05e540900c420860000e0b50b00c2070743d000b4441035070081041c130403600000e05420f160758 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 127177023 1250 127175773 127175777
    0x209011e08010606090b160b1005010215011202010309020a09022701020c01020a060b01090b1309060e1608062e090603020705190c03050703030914060c100b061c0e0607 74
    0x5104100072a0040d100390304403402100d445a4447c1e0084040c0101d8201600080c0882401c1061005603410101d041043d6203081e002c9450380440c0b00381c13a5052500c244180082460b05800000040d4821b130060103245d0710290583d583c140d15182c0c0d1500b0782c0c0200c0a4107103080b0074840c1c000b610003a0031054860400003800540310360401400001e44030307508a4000ba04550300d980c0e141400e80d118118101c010840c003040d02d40c5030401c000380b43c01d04030303014443c410809052003008203622101f104081e000704000380e12940000f520030015294000d0051842d0361040c00c50703a521258182c0c0790380b9102d61034010004402e181c0300800d800b510703840b0203400c444101407040c40307031000203000043d00109105154401d00c0702d59481e0318005111100b140c000420b28002d43c00300000301900030b5150400c1d41e08510004821f802c045050002c0c0c1e001c0d44200301038642c440303010001f464030294004110f8810140a141c5031003c5080360707c80c03c0c09100a03d2002c181e440040320000704092117107a42046542c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 127178273 1250 127177023 127177031
    0x120f220b04020f03030d0606080f09010c080f0c1207020c1002011107021c0602070b10060509011d01030902061804050a020903030403140109020306160f02070f1e030209011e0801 78
    0xd49800ca02118010002401041403904151090360108113490350310701c00440a0103a50340300e0720014044802039903002407800110021800012040c09258000c1d480d0345d46101240d92184034201c00020040d05d0750204d0071082220b080144001a8107500c240b800350020300c0006212428000c40307002001a490071a45084001582000401c0851b00d240790126465920794070040a6500c443e0124800244060b100003001400c00400034410740c40b910407580004a00713951982c05403204e110380360082e8005040c0c4284407c01d00e03410884104a00340615001440708250b5010588a50098010b80c000116202189000b4540ba01070150302000e4044103500707000002010a41d02d00a41c000100640404d80c2c5008400070250301480398580c000781110300c607080042c0044512440e00c1451800a480701e80712601b01800015074200f100c0d140e652054546142c2241019410384031b40d01540c0108003c0070002c0540e440c0ca50550181c40509000110016101d0084e0007100c1c880d40044003030703410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 127179523 1250 127178273 127178341
    0xf0212010608030a111203270111190c0203060a020c07050a03080a03050c221401020a020f011b0b0c09030c03120319020715050105040c090f1505120f 66
    0xb0100c1078610500f4182009078039400307035040880c14801c0780c98004515031004020040600321014100c41e450043e2100c4c0b40e80d24102482441c03d90b410541c44802c2d500c02004508a030450f4804420340e101e11a151171304102c40141d000a04040e02030300c2c0e404400360089106041800140240303c01000c1c21a000b541030b41c42c55407095030381e019180050040c140d940000400142d101c4c0c084600d60160001812100411800342e0004203400c0d00401150301e0b08040b05861650000840321011070f0014501041c5118003001101d205010f0080c0c10444500d8603414400511400e22442c000c00505003155255401201414546644c09085c24802d5000c00901d00010342075800301d9400c140c1d00c4400b0517041d180013261001911071207800410f04000500102c40203101640b1090603504116828045594000811107002080d40501d81b801c0e021060b04100b4040c862001008205150420500f8440c0c010b4402180d014110707100b09845035150100f08203503c00e08543d076207440d03101e8000e03000440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 127180773 1250 127179523 127179539
    0x30f090105130507030b1e01080304030c09050618040303060504020c07080105070207180b0402161208060f0604060309110616140a0b061201110f131703070209070507020d0f02120106 80
    0x1440d07100c003070300c6c104400000c100020740c14440058500021354403034889503914039807203547e544284400e0301e0740d2014031404560002d080c0107081c0a42802840c1903804070b800d5001c04400300d00500114145581c600d00064141c6070380c00601141c030038681c0a400803500d00180c550079140001c0269046401080c000d018030070054812139801c000106c00014078003540000700b4024071906550782001220309004030100308400a6601c10013865540e501c41586405c0140403064410140d4140d128806003c2401082d01c40d0344030326401c501403c03a0710b042020100c040340c1c041d80603100003144071070a00c0c4580140700c4556103240500d140d10004000004154503002001c100107880d1610603150100038101c010825005080340031090740f1040c0c1e84003c41c001449480d071142c0a848040030308400c0006081500076070045904000001861800c011a402c01c540d4500090a14060000601aa2000d03803152424a07540502c030b0408001c008000d8010080310324002e0f0840c018a80c1445800c0c04100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 127182023 1250 127180773 127180783
    0x30105090a1a09150f1905040507060c05010f09081b1b09060102030d0c081f0b0d0b0109080f10110c0a032f0105060406080d0503150f030102030f0901051305 69
    0x4406002d11482545409100d2403c01d1015121100c011000c9018020080700000089000c0e0203504d00746c0300c042914100b29000da0341c0844000d441030b004000c0410080380a0910001414407460000070081ca620751642d048543d00c56094030007040202c3c8114142e1607501100c420a0340200003400314031003d15600c010303000b1081c841c90065480d80d0200d40564000c20540e40202e6a20070140701c428600c401c014680c00080318006000d1100803c254510090f804401d41a03d6201c54824a03003014540f80c1005080c1243e01c29040000c052000100c20100384080481001d294018250099060642c00c05948004c0e54480c205c0750100008800b1140000d1040c82c20360f031609040c45407032220450103c101c1c5900e07414002d0f05086040d5480503c0d419030203244140c008490070031816840b04201d61380c0d079215012000201c0d00400c04580710440c00d01c0400300d046801080720901d006501e0109003a030700305480c1c03144120381400611029a1080c051603030702c000c44805c410003004032900c3d40c0c0e40e50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 127183273 1250 127182023 127182053
    0x105180f060c01051501031109060708030c07080403030305010311040e0303070e03010e0d03140912040e09030904060618080c100c060b030a1a010b03010b030106030e0a150209030105090a 82
    0x2640c00c11190504a440e46425038488400c00c074000c01007803a01c1c100014020200c004c1c114002031602c0d00000070f005084003559504140a00321070b04101b100c2da80c400c800c0e4000350a0601c014000e00c00d400000f401c150080019510943d8041220f503d03514080201040c1c2010f00d0b0700c00e0f403e0a030345140c1c0507000410340313174450701c5031910f076000e444801d010038010186000301c842940200410810b070036426801c4003030340e4406141c1c0c0184659401603226200d94081c400741019901c104003c00891540c1c030512504196004180e91610400000248c11101d0690000d00032030221072840040c800c000e03501e40001d04194018040c00342a0200003030424030b03150a0101440200e20300f10b41403000640c41b400f03030704c040a411290007414130704011641d401d2244003900c0a400d40d00002c1030855190b07040e0383c100c515441020b400c41c0d08001d4150040c0c80c0d18020b12043c0d12400002c080820321005120030102c80c02c040c0165507a95480505080d50030003000f03420b541c0c1c00b003110500000c0d40707840c0d44580 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 127184523 1250 127183273 127183279
    0x40807140d0f030c14031c2310091508010b040c1b0804030c030803041502070b0c1b06010905061005030c0304030c080c0106081006060c05064002040b010518 69
    0x340e0009140c103441c0e040c210703130003e400c161004180300b01440303000005102d0b00d250110381001d0306100914250588042c10000c40450003950700c2c09028034016410550001c12003600b103403d154903003000c0003ca8100c07492065188010410402030030500780305801c4401030907170f814080199410381c081c010404507001e4101e1201d81080c03000038000e400050700c01440d4003a45400b00d0329070303901345480ba0307400a81e41680c030300410140c0302d20303110b11038802c41d2040c0c2c0c3d01481c190740940d00c900040080e0b03007010040b2104241000d513196080724003031100c180606400d500008527414140140600f880101d030303040060140070014080b1183e1710005407039000381c0c94070300b915102e0040d18140c441c0c1e0140400307119556007440f10108180c8000f14501c003410707064400800c201d40d80d0308421100000b8001c001f23441034100340080750040401c2c4040391051200103a500505030300880d03698141c520f08170185640c0314800e008007002c524190052140300542468983c2c2041c18000150703025070844054148 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 127185773 1250 127184523 127184543
    0x180115090b040e0f0718030222050f01150903080405040b040908030c0406031104060c060c03060f06050c0d090501020712060906140402090f0c0f031b0c03040807140d 73
    0x800510038800280039000300440651580c1c0c0e0354401d40c0f03c9080544814510000e070400050a80e8400c480d95100d501e05180490a507034599000d201d02d0910403840c10415a1800040104811081c01154000d1051300c0c0e041d135240d03150a4120b070200016680c400c007045100b0400f04042141038068500392032048070005100042500041d000300941c100080403048080308101d40e02070f040d00078000302ea00c252030a01048020814403c1a441640641000b00e00034101034400300d172031a401001c02070035a0500203403d640318004481104402d0340000c00040d4001600240300e24103024401d03c1074800d00380003c03844d04000001c1d441d4002c5000701802d0b05030061043c0c1c18030686400090b2126042201048660000d080152a0301c1080300c090380101c60000101d4411007000c08460302c100c03030a400d05810006001004101c07940083d08482c0c102c1e4544c0040e90708407230040010608152110000c596a92030024070324100702580c2d01445a020f1010581441d070b03111065002c1d071641c0e12044000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 127187023 1250 127185773 127185809
    0x601090b012a02030604030f080705040b03040f110303030a0b1203090d0b0a020f2a0604030206010b0c010e0d170109150506030c0c100c02010b2d1f030f06051801 71
    0x1101c808030024081c0d45440764209101c00c0c15040788a4423150002c65880780050b40d43c44c00203903118812846240001c1c4030410000d008620b01c000c40300e803514844c415411f0300c046030038000703403450308165031017507280d960780c401c683d41894076034219600c1d140c0800c099420709901308001100c4c901c2d0803030054283c203400b80000c1c98008003941151545410702c1c40c495113581d052880c2030f0f0850400c8121611b80481c00b51824409000080e041d4440e0394180e000b840943e0801000c075105400021a180e1259210041422600002e100c214200c8900781d882126000721078884948615045e480031400c1c2e85400407040c090480c44540c40282d51041c0d55070360761fa480710360310900e03940320f07051039040c007030290340303102103c0c23901c0da411020b40130000e40e0003404009007450803c10322009200b90f005916845681c44800382c1001c00c41c0c662a044002c00d44c06060a05050585440308000d14190010341d6814040420354801d2040c1e4002c1d100654442241000c4120190b90241d418064155460452460301c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 127188273 1250 127187023 127187087
    0xa0308091501090b0a080a12050c0a080f071118061e04050403080601030c0f1b0807020a0b030603010609020315090604060b0f130801020a020706030f06050a0806090601090b01 77
    0x380aa80c0e140ca9241c0050340c1d403510020000c20741201641d00c1785505e001c001902c080c000a44110068020350302c80b01e070002100d0180c0383c0f5805946c0d108401e02038400c144000c10a0318000c0c0c18140c0714180c10315034962484c078181034864984503480b4411000d12485900740c84100101e1580048243c1c2d060101c00c8091002000e511024038050f40c4c02404c00040004155104105074081c00c0e080e00d052102544c0d504080c1d5410010301030180020380c01803254410000300c0d160a070100380c01540c1d018a0810650045075442c2c019400c0100800400001d011550909215030401065445400c50460528200c0c0c1e20400c40382898880c403424684011504554403503000703100030300e00801c519a0702d141141c01090140c1111202850180509400162109040c000c4424541256001c0c100303e0381030003410341c020240800d031240b0a0790b40d04004103035503c40b105c80f072000e0320b43c0000030710075885e0551081b45003a805030030040300d0a041418100090344c000c8250541d9105440c0960040b907140104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 127189523 1250 127188273 127188283
    0x9031101030b0402030103030c02040e06070e010c0804211712060d02220b0f1e01080a06150c050105060f01050f0f0c120a0f080408030a05090309030709021809010302030a030809 78
    0x2c42c81d802440000000b003007503001903180d08024401e039001d100d406034011909860716001c8401801060311109031008543c400c138504d42041d403199640905081e2a043c200303440c4691104504541c03403c51840c1010702421042c1c0d18000d625403030f46a0f103065640c1c40343c298078150151040d070059044083d032108650307583c400070459441a2407000300c1c1c0749214100030040c1c401103824900482242140d200381341048035a85110b036070b185171449207404401d8011510304000a043ca448c196550300e0100303042034600045c03140441956200645038109040032401c440d030180100384a0034510840100d182d8100081c0d130031172030400240e00c0d1182c0c600440b030300852042d552203000a02800c041594401004c1d070103003100b181540d03500c0c040720b02c03500003d650307803981a5409802544180300140008281d600502d502c50104803e6a041c0441ca00c007103403806120307400c404283e40d0045201555000a545a2089401c0484014045524640100e501c40031100c80140800a182c1e0000f4018003003045 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 127190773 1250 127189523 127189541
    0x10209040509010c1202090904020f030f0a03020606040e030903250302030303010320060301080a080a0e1903050c041e02070503041d160507030f0e1306090213050a060903110103 78
    0x10041c0060718207080c24900078100c11907584041012002440d402c884207100b81c511040c0007900c005c8058540703030200300b41d00b41104c01a80d854480d0b021003140d60700c400d01c1301e407a000344a60024001d80c18880704100c1507174071250071444c03654410b00102010307a8002605910b0544400c07055000446d5407060000e41ca20b440c0c001940500c0300200010801c0900c1030590805000019030003161007008040001e54482889510200da200c0c40c40134001c9440c09000300442c2c1100e08001d404552168082640a0310044802c408070780c04180400030b109040c0641150104111020064101c842107910540c040b14510280080e501151103020000d04004032809003058440c41c6c12031001540368012200d0b801c80c1c0c0b08c0340e010501c8044201e52030160040e1540c0c41d40c191241d4412000e11b0f9421508001c5101c0703140d5101c07916a804d00460682845144042c05000001503544c10115140f0005402c0d036500642c0101200300b01000365551003662401960b074454600c41d807030805100102d02401005c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 127192023 1250 127190773 127190779
    0x170f0402010915090801110f0a0e131e0501080f030a120f0608031e0307050405040207060f02030a02090f030c0117070c120f021504081615090507030c1e060c0203010209 74
    0xe81006990750000349520445002500030300c0880545440031a890049605000d00c0f42c2341800b210241500a51070049084800f03010b240f4100001c1d42c04000f130f0f455040d881c50a940c0c40000c408440c140c1070003200d01400455000300a50003901194070340d248602081c0208000c00044444a02002d90f0401c0c40e00030a400024442181c0b01c00d42103480b584001d86100806071000c4820554a0400781564801e50b91500c40500b01450542404082e501c81041250790356500c0070a400c1ca80128400340d405007060300c00042c1c48885040c01d2209806603030250f28807952003c0e03264003091781e1109500c08250180d88602c003003070701c44100c10f032820842420028044950b01103d00ca40540c00190b400480403180d0071070f05401c45414070310449020036500540780d280104a081401d11040008200b9a445260300020a8601c0d42800c0c045440540c82110260030409040052022800054010b0140c9460300100001d0500300b400100819215403010b101c98084a0070955a0039816109161b43c05 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 127193273 1250 127192023 127192049
    0x90f032401060801060f021009020f0d06020c120426072103090b0a0f182c0702060702060103170f0c0c040608010902030a111f0804020907170f04020109 67
    0x4410140000c8024001c08001504080000901600c00c08009166400a0f00607000440c803000d07090002e00032500060f030300540782c2c20f0042619100c0d9280c00c12990b014140040c0c40300d21180821341000002c1000000c000320500044c00b20580d0a40b03046241c00c0c00074541402c0041d05c01c00d043c01c26409610100c05100200e95003840983d00c070074440b10b401d01c25074404105640b154803444aa002e0b68603140c0000e18107030034500c000b40c0030316a22000c07140c1d04201103280f5581d4440001e501d0050022048074002144820140c03d101b5280301c0c1e411481c5400902954130f008000207580e048148006005500180c01202c01004040308650902c940a0a1259164091121190754507014580f035401645480030000b55000d061040d18002940200a00141c42240d25030850003030340154900c8c0e200c2d061012010f602d070351075240c180504003e0340794441d50b4640790041103080000249010140030104224070288410340e2141944481c8032942582103840340d000482c0d98543e40d4000c9029a100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 127194523 1250 127193273 127193323
    0x92114100507030501091e0e07080316050114011805060a03060c020114220303240303020d02060618070807021c0c02030c04020a020c0913020d060501030b061005090f03 74
    0x10741c01081c820b0300b03541c40600150340d80d001c07505d084800700c0e5845003040b800b28411188091842d0040b035000001d0341e04480f101910344a0725819603003c40f904c80c0d40024248094800c0210038085c1c84a07140703200c00c080d00d40758501078451402d28810414201d40300e070340e5000280c9940d101c410003006107403c10001c00520b5000e01c8081d009001441401211104a0b00003d2420300c8603c041c0540494040d03440c40c1d15402982c3c2600545000d0703400340300060045545915450712008510004d40c040e42c002d001b20510004003a04240005d8400e5000e520034802800e440300a0200c1c0d66040311440c0303000303032130742d699010b00f203081c01c48031409032041030794454120715180d40c0005804c01d0310380210700b80e40720090b21200b04022803064185003000f40e000080c0d01801440d2105c40583d000d007030510b00c80c00110181d80051820b079042041190b089684500510030b001505441036400041622200029200c940019000c1d004400146114207010040044291810b02012004049494150004200c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 127195773 1250 127194523 127194553
    0xa05040b030a021206040b030d0c020103060308131e0602030403020603040503130306020405152502030f01050405060a321308030a0902100206070f080a02040b0c0c03010c092114 78
    0x1c0000c10141010001101041709071030b0a10403055100c40080c020003a42c011a00c2c242d9a6282c0700340164141f541c0c0312000800300c0e101e84000c00007485030743c01040002d82001c0c8041000d84002025001c00f0ba54040d0910441c0c0c3c000040701c007520780444009440740d550b803a0051951003044461524007001603000410000381d43c0242090b120201ea0580090040200381a51406007210100d00c0d0b2140e04070396035814448240310811180043e080c3c44460700c5c05602103084d41c40559045409611030010000c43c0040b0744114a00303400f641c0031820400944104800744900314003d4000c40c80210780218059000c2510b072442c40c0c2d603110301000d80700d1405103000c0004000707840c4140d00840c3c0780034110380258400708103d4840c041c0394440040c130b009040c5e001c172050301e0010070002105078200800b01b20a564100600600721082c03006101c5049804180b44c00c1d541f007251035909103c0003550038404d005084060501c5400c1d041c2400c060010b007030400e08a01854108052854016040250f4903d6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 127197023 1250 127195773 127195777
    0xf0709060c0f0321022a0c010c060207050c0907020303010501020d090e0708090f0a0b01030203150103020904060c200115050a150c081909030605100312031a1203040509180705060a05040b030a02 85
    0x100200050054842d825010a6100c4d00c107840f402c0e0000308150b009c0e0000601660182078007a00490890300e083c503102000c07c007649020740d40d840142e0b001000400aa40e8100003a080543d004d00c0d00c1040c6a02d44403c02151010241c0454280f180000009581d07000030090280c03416615411110381c40c0640c206101206000c0c0020f1340a40950501c486601d20181c0c002412643d004c2c01c10740a1b543c03540c5403403000f044a845044204001c55400d4040045500035034207580c0014800041c1050000c10841c2012100e0740c426801403d00400801002c04904500480c10b49103090444c00454a8034120551703204400c448103289103110402826650f100481500342e03132280d07a007045140c940c00068402c90b000707803000411800b0000f84500103540310350082030300c0020714164910b08400c0c40000030801e400100e100200d81e4030115080025192500305d0a81000250701042092020340140c0c640740e86903070059500a000010700500850300c41c07070441c0c0c024000903044584904004800078042c0d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 127198273 1250 127197023 127197067
    0xe060108044205010b0901120b1915020c0102030a0f120c110610030c1a0702100302031b0403020f0f1518040f0c0903110303040e0f0709060c0f032102 66
    0xe10707208042d001000d000c500c101c906807041040c0481c10071140d080111007400c100130020300696220f400844090305e507a4510b902d50942d0030028212a418001d0410220343c5003182d40302198890103078143d0990300807041307030140800e500d0500d032224403001068402070070008041c0040d52614141605140c3c4c088041482e5600784400d5038040d441e0198103003005145030001a0142060080c10040401068130218120a00c00e070303a1828000960002221803c0104911000c660008100303ca000c0e10200e400c46000824401c40d410c0c03d046030003150090011620940c00f665005091141a58805501c0c40c072100c55004134a9446101491490042e82012010782c000c500b403100124011216018850841c4115a10120081d00e15200c0d03040300c20b04103c105415000420000c2040002e440c4600e100d9002c00d040c84505040c440c900030705810940d4001010402c415202c907000a0110f89038040c16034040c0750240c1c1185001502c24803a41030030039800442840012040001c005c00c3c441038880e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 127199523 1250 127198273 127198373
    0x6020a02070f03150b0d05100b0109091103150d05100b030607140307030f020c0304030c1d060904030804110405010312080106050301080726010216110a0e06010804 72
    0x10241d0b035200e0068490407103000c010421148105138a804400a80c0720000325039009142d1026802180c0b1050700b8010b104641e0030140342c03600c0302c0452550700900441c0080c0301001c0108a8903103080000d00c41d50001401d5400004410b400c01400d5035034103140c4003e0702d60400284d900100040070300340b00809001c5000e5010340296400210405e001d10307503040046034251086451940d07890001c500a0103400c0c5d0480074241c0c2403001ca00c0310305c41080944091072281208151070b50038036001060151170b041c602c06c2d041c0c2c0c5040c00c00065803101c64403d600143d040c24a40d0464440d4542840210840c4030444e030843e18240c00003007070040b80c030b45d11902c3c100700e6250089966220700341142d05200034001d80c4181e0780044400c10600000c14030102c05400c8024500003103e0607111041d081e40c3c440b003d02c0c2e414012210f0501c0600036080c0018010341e2003100d0f502c141d40d00c0c02e055050015001044c0e0341c1130102803000541400885690b103940545031701030b05100c0d88200c0201c5c5018404806801e91 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 127200773 1250 127199523 127199533
    0x921020106050d0b1302031507120b03070b040e0c0f0f030f090a020a060e0607060203100314030930010e160801050f1308041502070e0a021c02031b0706020a02 70
    0x64a080082d40598459045401d4044c2c0d03541c0c1c160808000c0c1e0a40e8012070301481540c6507901118024480580981314650307540d0300001c009600141030300da1060f81ca510981200100300303d018010340c2124115003400100003450354800140807428001c011805124010000301c440101c03105a0003544a071103081003000031500d03110320003991903101c01002504050034600911500340260041c2c01603080040070a860101e16554180590b0010380e42c8048424180b030080c010801200b803000804201400114209205007000844014000c03208101d90320300300404440d940701010060040c0b00091000b070000c019107102d41130343c070020801d43e88108814003202040194041c020b460050300d0f0704200e4545611039041000079220100700480383c9240401000410003010004400210543c0d00504102071400d91a2a0400350013001c00c6d0101e8810028000c0325120702c22060212820341c04c0050700ca5031060441541c0c1050070820a0602001156600820070240c004001c1d00d40d070303503080e54 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 127202023 1250 127200773 127200779
    0x317031e040203060f090c0406080c0108012c0c070b040b0a0510080a110f0306011215020901080a09050f01091407061704060e0a120309060b01080601050d0b03010921020106 76
    0x40511098400030f515800040100d0580c50b2a242d0b030a03040301d4403d00352071100c80d00100150460740c16520580b81504080045a610360700b10500e54010100354003810704031a820450301e4001c64900c0150250030070100c020520300114a400d40c0c96150780080104914142820055240c0c0350455520005504110020b44501800c403210f4007103d040704000e0003003150300d0742e9500da209403004a054100c80e01483d43c03041c80e40d04100081c000c180115103038640721010700b44889004500540c20302003a00402200802d44d0380410047d60042c2d2540001580101c9442c0442c1403194040c3c81291941c03c00310180300340100181c003151140424030894011607507464042d503080300300c00780325108000f4140c0001c0c04100d00d50010b14407010103500b522040000c640c1da07005008200c00c058000290307540d03580402c0098038480c450220009090081181c5401d0000a107984144800c4080345521002d516548e40c8094100c611510780c0300f81e1540c102c0c80a40040030030107a198040300015801d00c2000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 127203273 1250 127202023 127202071
    0x1030b0102100207060207021804030810050901030b0a1103070e031501051005030a0b03010207030e10090b042c09010b010807050a1b03020a0f03020102270603041704031703 76
    0x285008101a00030b8822040700002200c020f400006003074503281c1d020403044006980d4213a00c0b03940d007070f9440000d405c2d82c20315007070007025900000d01600a000003010b0601403035407080401811258003400c1d00280e560340800381005800301d01c2c2c0c60311502e038021040c001030a03045400c80040700c03c19021280c01010303020107000010820701c5900c1d041288803026082c490301c40e20081d90300207458400030400d181424040323400c80e0b200203400c2c1c000405800311400c03a0324201117013458041d0701e4039110520a0801e8100501441544581004440341d6509000841050702c00ca030740d400030030501c04045107003c529070741c00f03090340b150f00d40d000800c00303000608003074040c209607004c00c08150340e1150051075420fa62242010a0001038003544122540c103000140602c540300d8800b0300c0707940003507120820b41c41c1c5200e400380407500e460900d080036035540e0100d4542e02c00762544a500b0000b0303103044040c5240c4440c014400d90b003014002c21500e0302c01c0100d46110340001c60080c0b0110680301000c003d03010700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 127204523 1250 127203273 127203281
    0x3050706020c0118090e1c020c040b0303070b0114040b04090b040203160f15050c030a0c0b010506070b06040c0e0a15140306100e011413080607020604031704110a03061a0103 76
    0x48013000544040c008103000c3e6014254501804084032800401010084107080c80001c2c218010fa0019060310041c2c00c1034000c800c24401c0942c001e40c02c10001d80d80d03500c006501401444005000c00c4e056154540c3c0b82d070010084280060010084000181004c0d2440c0c8801c40c2c05078024400e041d0001040c11100c908182100c1c1d0982a014040742005880c848000019002400300700b0280036011240342d040c0018484e5120b547c60381c00d814a4249040440b00c2416030040d80306a406002c11800703e04c030030001560040c02260300180342c611101c025038000c25078450036604001c420070040740c0710643c0103c8445800710794544000754114400f060000344000c594a81c0c1040313801c00c0c2645d456025100142842d2014100308011488113101814150840d00c885460300d0640038040100c09070a210207504401c5510140c200c44c0b4242e00c0241c02c0030451402c00843c4a818800613050005140c04041880f60081903d241c2d00ea407030802d200030b80200788034007200400c0201d45125035070003441 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 127205773 1250 127204523 127204547
    0x2121617011a0708040b070510020315090a0204090c110606041b0503040c080102030a090309080303010321031b0302180f131a041b0f0302130e07050c0703050706020c01 74
    0x1440c1103a0703820110400c2c540d280b440401d801c1c00805101d08000a60050054006800d090740708a45800b00c50038500c0c0382083c6207443c102d500340f0402c21f0003100d2010510030902e9900a4501c10315a8450042500003880349521402040b0715003094498900d030301c180240e03c00c0321f000c82104c2c0340303807500d40c100030442d10114402045920b0410000c000b1502882c06554800e0066081500344c6645030142800d80e0b0088541030929555480c0071800c040d00010303408060300340710b00118103543c150b9442801048447da004031000350364500c24140c061181c2c100c2c1c4d1014070f03210300741107036001100000f401a400081036131031403981640090200c1e051200c103403000381c800188003070b10710001c1540f414020302030440030311140040705103100c0e110b4459026a44a1280b0896804110038807168000e04402c4588102010035004010041c00c1e00f0800450b0380548000d2040e014264440850945d800d01c5030414100c4c080c00b039181c0000501c100440d880c4c086a0701364080d00c00010124004480c1c00d01c0e00a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 127207023 1250 127205773 127205807
    0x10c230d0506010203120108030912060c030601050c030712050403020f01050703020606120115031220030f13030212060405010506181303051308070f12050606091504021216 76
    0x100848200c4400da82203a5003007007060041d6071600c10b80840e504e240c00c10036000624254400a08075440381016042401d1843c094005410b46007807101140350184000791031141003010101d0440104502401210340f420b600050040490042c07503006045a001444182e1041e02c8098900740039502840803901401d03810345c0139203055510502045011026580c0c000d000390b5a40c203080d603403407070118110b6015600403001c0c2200465401d0000b0178100707501a0002d00019109101480c1c440c000050b42c1c2c0300e9941d41030700f50319009419030122200d00e040d44040e5001b420780000d0b1540b484045003032402a40038000901090359401c082c8003004410040e08404800e0280c0000c10b02c1180c0da0054a140b4400d01c3e001d4905041d240b00c01c5141440364120000340d03040803000704840b20941031030400a10903510701000c0c011903071701d4103a01c032040104020302504a91002035001028000314642c03881d00140115112140f03070640c0748001404541c0c03200b92050480064580c03a0084080e108140e0b0701c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 127208273 1250 127207023 127207027
    0x9060f090a0b040c0e09090705060f0705032809050301111804020415050c06090a0c141302130806010e04170717031501021c080606070320010c23 64
    0x4901801110000180040032056035904407180d280d460340251521040b2503501d596045070303060208903003014003900300c411540c4569400c101e140c54140a50749219420b0a01c3c64884a00d424940e046201c0c84210f034940c581c150800404c20349200c0c1d0616800d03046540c440c50b10b1a01e520605080314464162060884030500014a0744a1030701c048020019001d00094200340d43c03100010440940d99800102003080412000800c0380200100c1e5030105208008086031616911101c2c810100ca0241c4691a00000c0061056445000c04844251080642150f0310515032040e00d9012200f03004228242c0958000004c0c825140a401409641c00a81451000803540802100c1c1da0041394111510b5800005006002621001651050002d03280e480c0203072500000080c108030b030324020070b250040000006a01c1903400542e4952024042e0340c02e0782d551005060980700007000d001424051000b03c5100d07403000406401c0078900e03010300c1c0c070f41395200040001201d11108000315512003003482 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 127209523 1250 127208273 127208299
    0x2f010905060d060e040b04021002010911091f170f1c050309100603050706110105190b0102341a0703030b010c06020a0906020d09081902030319030501050406050906 72
    0x400e5005100b542000c0e880000c081e540c1e00c0500e10001421501078840e003012400300015410308101d01c0240f824144001c0040c420203540c0c07401c2080085e1003c0d401200081d002921582541800c2440e05070894104e201c0c081e07580600c0c10802c5042c00c608004e900035010300c01400e00300020100025421044400181c1c40414011500380e00700405020142c0300d9103904020406807072155802540c020009400214200000a8171031078240c800001d00e40e2500c401c104000c5030f9041c40c031002144640c0702040304901640100d2a1549a01c10003c195a0070034132409900c00d40042111460308200d6140c03065a52400342200d020031070342010030301c0081040300c1c80000c4d101c1d038407290781c50105050032001400591100d1049070001d0350008042500c012040c852180c04000c0c081e080d0039030345000c9a4090401d00784546400f201031150000207410716a40c0119a03080c400e03146204d280e5030340034195031a00400140944020311403540154940100816141000d456035445810040c1081000d282 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 127210773 1250 127209523 127209529
    0xf0106060806040e010b0a030606030b0115050d112104060b01050a0512100f030b09010b12030f031b0a090e070804030f050c070f09020d0f06080a1202030c07032f010905 74
    0x4813900000400d55036807080480c070350364503882140554010080045c02c0d504600d0402494030040c5c0204000581c80780702242425400412221607408080010a5043c4122100040c500a5510b921150020140ca540303507031081d500000e114500400d4107100c0e0350100001550188518040e1b0300004e0010002150220940840c4542024111070130841090303840303642d01003840c0141c004a03100302d1901c1c02d0005e50320342405044e900e40c0c811920041c860f10070500c51640c3e4881c0a8020701091000b000040c050b840300d0068542c3c25450703074009a651550312500030300c1d00c022401500a01883c0c030000c075419510032041540b199525444036002e180001c4016241500b0403819034a05110f60a4042000b1036001005001400a454003684441c140c003041e600344c0c0c50b040c140881c2503251a00410100f03a000038010f0f00380e03410008000701403294003070490444c8203e120012017446162400030400111094040115406a00140c0c0b87e60022585040640b6117a081d640003c280703050600140c0703 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 127212023 1250 127210773 127210781
    0xc01050a06050102250321021506030304051201061205010207141204031e0f03020105011502010b03060408030612060c03070e040b010f0807020304170105060f0a030f03080402040e100903020f010606080604 90
    0x88045c04030108500c0da20758404400c45003141c00154a03200346519403000f2074040016900940a0111614542c0382042c08070365030340114031540c3d126040c001d80e150045142940100003030000342c0400404038045080490107544003d0046429094104070212403440101e80060401000700500e032901d8955110314200c1100040d002d5403846112401e4000a00c00700c0042da8031a02c07a0700007107420741c9404090014003a002c00300c0410b5905011003040b9903070b400301d140741d032281d444a000390326074582401051945c4c000703400d5000740b80708200500904507d83d001540c85a5000c0c0c0e140351089020300c00344820b07504001c25072070104080d1078020380018000e8107002d901108520440c0c1c00c00343d0310490141101608947c41556955442c184801e60908407251020502c0584140c0300061456841074000e14040d000941000b2509000c0780441da22a0441d40362403400100700c0b2120004103042d031000700020107045001d441668001e00100006000750000c840d40e549401c0555661b08080c04050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 127213273 1250 127212023 127212073
    0x9070302041701140702070305030403080c010e0d0201090c05040621021f091508010303020d030e030d02070803060109050a1d06030304031b060801140f0616080a050c01050a06050102 80
    0x4540c0078000860310441c10384407904820072100010510310800001c40d600b000000d00420210f411410062012840c008201c41c102c0783c0c8070501c3c0e0b5403001b061540c0c07401801030114108803401080f0345803030701a905410980303409005060010000350349800304021202c140c1300d1500138130745034040d0760000024038888040550014190030007110088031010610b84003803003441702240c0e240109112940100158800c030022506122540394110b4038040e603141601c0070394030b003015101d262600103004103000391001c000c1030003810b640715032440ca05035541d60411141c9c50300151041000080910b070400440302103400e65541141d42d6005501802102040201910303011710040100000143c0b90080d00039005018441030410030b0b0030311200411205044c1e01c40d0b0011070010b841c0111595902c140040141c078121742ca995680d5260240c81c0811001c0302c00580840400b140f1080c1d501d4110004081149650008001a540309000041290094000c0d039005a00a900c0c1c03a115141d03c200100031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 127214523 1250 127213273 127213277
    0x308040215041e05090f16022b1215060c0c08060708090610081e0a061b030b0301060308090f190308070b01090c021f0e0a0f0215120103020907 63
    0x80381562118601c0c40b80c0c029402841d060300152083d80d107420807643d0080207440c013118400c0c2d203420700031100c41410300b01420843d0505001c10948081c5802004104854441c1c5080140b150390040107014402c0140c3c6100804a06003076088442c8580c1c0c1e00c54500034842d0070224241141c1030900482d10154608070407613012a01b5580403540d00405c0118034860f680c9641c41451610f81031110909180e4007400c068010640180280202c407000b00f84102403440040d45001d05020440b40640b501131500e401400840c0703050340800116003100c2d0302d8240c00072a40c03000e01106aaa0051500329070f02032001500300030040c00681101e140650011182c014002c040c0805418103240c86001d903c003d81c07040306c0e1703084001000c804019901800500500040004020180100308003035201c21540302020f02140d2441074001c00c00c2219409065840c0a40044881548191600d1080002c0092007a881003c010b8800d4622005000458490440c1d210120549074a50703400d0150311039001d4840701c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 127215773 1250 127214523 127214539
    0xe060a120c11010e030a030605180a09020607060903030902030609070803040504020f070b19050c0f0d050709080d08310f0309091118040b010e0d0606050307061701080303040f03080402 81
    0x400400b003401454406181c06024640c0c0c0c10018501400700d40c2a0b80c01580030b0f0305c485840482c1810300119039070b84205242000b00f8107172082d00c0001d199208050008010b5480c2100703410a1680c540e00030b20350517209804843c0252140082d41d5a1030309140f18108190f031041000340064100740e0060b0501c1d184247c85682071402994a40b00c5c620f2040b296001c841c1d0820b10140120400340c050f26400500c606986464060851011011071044101c1903c40c5a01c4902181c00b00b4800c032030800c000c048540903525641c04520300240b0340d2505641d81a089503000d01481403510a00151451031078840b025075100f1001551221500c1700603080540500034001780006014880d40140b034204906003035469070390101c1e00c1708200c2c028003400c5886d004500d05122609240d0700403c150304850300c125031500c084541454071101920580c0c000320381500500710009403803500107081c19100c6a003012608560783e01c911a041c0c0da4007040780d02409145c10440c1d2400801e0041001c0f5030081c1c00988807607 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 127217023 1250 127215773 127215797
    0xa0204050108060a060603021305100908010e070905160f120f140603150721060902040602061008060402031908270a06080421021e0105010302010e060a120c 69
    0x180456409900c022040d8008604011344c07050325100e16005004141003c50074056012008403a030030881c050a40a22034103850f055803503000b003060130002c100481c003d00180125aa105446e103503d03101e500800d500700b40101318041c3c019404105c002015035186041300e503030354904856002440011800040d0745400218012105000d00c0d4038010310003c00701c840c3d00b0b0490074180b410001d4185c0341c480c1e014503030521800d2540301c0c0f100d141d1000031108050803103c800070064000c2c4050f82c0f2590b8160320020b070028074030744c0220310244510245520066001e54a5a5054407084222002135068003d640d00c8011072140c07103e407552444c01101e0703513030800c141d010000f100070219014070079140403aa81090300030319203464554044c0200389404645824581e0790010345a080d0820035011819844c00460558403c110b0b490f09400c1071079100c040c00702d5a0426600800c001e000582c000f41860003980458144401201d1100320a0703034840480002c4a190400105010540d460810842c01000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 127218273 1250 127217023 127217029
    0x10c140601031a0c1305040b01021029150a050a03180507090c110c0f120a080702040c0302090f0405090124090c09030507090c090b070803040c081b120a02 68
    0xd502961203140d00a10148181e0502409220020b2050090080410103c40c0f00f026105255084403001e54020035035a062000603414503108841c0803c07018542051581c100058100c00807210303a04d500994003408420060000d51907910b074485e00c2c0c100041084200e6141302c1c40041103010800c0c40e001031100c0c840c202202a004031004140c1d11a8060003042c0200500c522610203103d0840c01c18051070785403000807980b0340c01242441803040d1800600c0e040c2984402d01c2c00c092091500003070794607007901ca00c1c1c905610303005020186d01503850304e0542400280a80300701c40842c0001020f40440540c01010440035090040000c4036654a9865a800d2031000306540d07580c0c612030884844015082215440856805021f0301c0100601543c0820202d100469410140e0b0410380c00131a04451960301a03602c031a00e035000b20710366a000a8107030309204070100990f0154bc806c10030080070350b84e2a1f07911070361540d050681a001000c0200c40755403501e85814410804000c02c400d81e12880465000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 127219523 1250 127218273 127218283
    0x306090f02030a0e0304050109030305070606090e0d0e031212090708100207030206060a1d0c090603010603141506031f0803070c08120c0318191509060c02030a02010c14 74
    0x145200c1107802105201038071000e4000c011801d18008004c504161030840001c083c24002e1002409000740001c0d82800d020950300240040e240e43e220a112240c03c42240e144d40d000e650202c04005804034950000a1a01043d844400c0c1c0500307050504000941c10341e0200044090100501403003252400510424140044151810390800c01a00c4440760b04020f41040c50090090344216031007070b0188020580322040c0007411501d0150f134485aa108001003895208903045254401001700002800741da25401180300c82c11604041a22512421400e240250307001c1e0102d64054400d0000401b06c0c1080308021190070350030060349250666034402c503429030f40b001c482944e084070403940c00c0c0301805c0100050898920782800c5180f81c0744001c4440da03100d0082c00003007820240340d00362004d015681e29001c201e44810022140082036543c03042d100c087e450026040002c144000c10010324140104209100c0d0fa801401501e0003000541c01120418545181144d266804080f805002c2c1c90400c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 127220773 1250 127219523 127219541
    0x18060507020124031707030c1e120e030a0212030d0f050108070803041505090a0e1315021c02090105120906010504110304020f0d030e040218090c07030c12030609 71
    0x7400d44100e4140f80f51001c43d001102540f4400d0b00c1c3c100000f4407600e03000380c40c460040c201151100d18521f011682503403030b0781d00a840c0e0000100014510002540540c88042c800c10200c081c21031a01c00549580200b20400d5900d42c0260380e8001c05802c0002150147e82064405d507464001610110000c0b5401a641012020b0783c800040c80240010004d86000c0c000ca0001103080c24644641a10560030070b007007400800001284800c4c40340c84410b1954050070f0f449015070000e1400c605140041e4412000507a48800341d000702c2c24010030640700321100600c0840b40401d44100005480d07019500c400300c29030402204001c00321703907042d00140d0140280c6034107015103e1541340a0800c4180c0300c10700200f1b03101603802c105200043c0d030f6401080c0d8451000b62542400b48013141015508846005003e680240c00001e40c03403a420305540c1c0422049000311907400c0d05813079405c0100c103a800f41c0c04000700414070424441010802e00780c01340240f54903615000c0344a50b1180022015031711114 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 127222023 1250 127220773 127220777
    0x1050c160305010e0106030203030a0324060c0302010c090f060c1a040f11150409051005040e0c041508070e0c07020a0b0a17060906040b0607140c120d080a18060507 72
    0x22010300800c1004e004100c1510f42c07410090245600303580000e61248908202d83c002c0c56500c802c100c0c0d039500c5818540c2c21420060407034050166413080042d00000041d641200154a0b0002c1c1000e01070041c12a503050756082ca40140d94141407000a44403018581001d4070b0900145003100e0300c400350380541c544298455094240c1110480c0b03004c0804034030035840c0e24410b022100030b8089949941082d60110ba10101012406440d50290300c0c2d408412504405c7c0c205092003c0131000d00c10010b600b4001141c00c0c0c604100c0364909403c02907881056019410a80c0c0104030100200c1c00204c00c65908240e40050382d0345404140d6002503c5814158442e01c0500804210010155040186081d101c00c051411040c2c42c40c2280000f806203d0041820b40700b0b0386d5035011824941c8038442959034041d480040b0041e80c002c42e0160383e03600c5610aa5aa1184d28115100981d02ea000306000a80e214a074980e8441034903008c03460300282020b150507840701803034003000f080415050301949019403c55 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 127223273 1250 127222023 127222063
    0xc06060807030f0c081b06070204020c100203061003110706021e0c1f050402010906030e0717031206030a050709090f08030709090c0908060f0a060b0a03270f02010e01050c 75
    0x2403038040303841d130b1807540071010507003010016066007004121202c0d69100d04462041d0b40308070700d10000e0000e000754810020144168001310039811581c0d80103501801c000c81b040440288035140403000d0300c1550703008903844481400810700180f183c2c0c01611850400300d40000b005610071116003140d412008404a003580002e0b40350040101440c1010b00300c200400d81070105150a400103010001c0078402c0d07104060303440d192030040c0d071000d0001101070501903a80e0f1400450400202d6903980044a0030fa04603020308012400f00c1c40d00281004096501c2400303843d40525101d4400300400100505a51615202112900245030b100065108120b00d80340c03d10094105800001214a19203071141131005101c01030100040005810358000301803c51139800d5511340d2249000740020342d005900c4601e0102d0701555047d019003009141075008079031000c81040f05d0482c00c0320704a4400d0090418008920200007552007181101d01460701810540c0c540004507009a141003c0341c03000521020007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 127224523 1250 127223273 127223303
    0x20703051b2811010e09040210050d1a09090109030c0f030c02090f090c0907020709020924030106081302060a0f03140106031d1506060d0f0203042910060c0606080703 73
    0xc00a003080103c1000e1815035413030418034012403828100900081d00c500c0e07150740039000c500c1c4268204e4100c28130f41c4600b84207214000e030032016548028200c49200303000000006021010511480090740c4e010ba441704e17644001611081c0c88103c0d4900c065041141510b64000503171141c00840740140c1c910240d01000d0301e4140245804e041070845014400d88282c0e05010300d243e030000e500c6094840740365006948031080000298900401d0400c44001400604103001d80b010006c0030303504036070740c0e41c0780c242c2c40e0f9859074080427009110b800000d60260301881000c1080784100380b03030302c080f1207a03060002d00c0001d040e15400d52000c0981c03210002075201c4540304080d40d050344454000c08800402403446e0340b205c06450141e00c20080259000b03610105040349a02580d4020240b4112421000c40d6681002d00b0502d0542e519904e085000317201858124140205075001c06100e0503803001c0503949503080c69400c50b090070700318609580c0c0c05e4035407074080740c414024402c0d8001076214001030880724203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 127225773 1250 127224523 127224533
    0x40f0c030206130819050303060f04150e16030507120b0613080f010b060c1905032206030522060c0306030c0b0a031b0206040209130b0a060302010210020703051b28 72
    0x603905c034804c89101d04113021140000c0002051303c4e01701004131400201e404010020400a2544100a00c500701d0038100000f100840c0503a241e001d4040300028505100307200d14150103030707001580d1020006023a000594450320840e403003840404002049540742c1100d500040440314071640041586d03401040340c4007940b003001d100d402642d0009991041c14100c04006054491200180b000f480106044945003001828422505200c3c030600e09510082c00c0d02030421020690760054034046840d01004c82e651802002c00d890380d43e5060000f5690069181d500c84c4060f0548201020905498400100000f41c0c0150400e01900c2003802c01603d459009a006040e80c0302d02e0b0301000041d408a41d9009002d901080c0c0070380c002d4050700e0804080d00c54854442506041400c05040e204076a0107001203003005800c91000c49000340d0803540f40d48044c10414040740b203034410080100e402001040410107a580d58240707024070740b07026640d01c125600303a07440901600d00c10180035243c90105a13001c103c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 127227023 1250 127225773 127225783
    0x100b0f010309020a0b03040302010605100c032003031b040906090212180a140307140a0c05030d05041208070209070c0b01090b1804050109120f030501150503040f0c0302061308 77
    0x82001d280a121540140c2c02080c4100c0460041e42800280000080d081c9030017500300200a01e4094001915000c6c4640020260700e80e14204a00055111542080d00d0080c0e078008150307040c00d800658a1511030400c83d4041e81805c07a050300d66190280000580380c8860301c80c00f00140ba0603038000d65203404107040403805100081021180c0c10540d2080305007a040094281078244d80048284a035000d41e1914514500812000401c008502405042000320200c0c8003012107109424100c0002e0303c1e0410503803595820b5040038001003080c401000545400c0c192848501e0041c0314036890302c034054010a10b820002c0303070000c0200b5807043d480410400d03c140003d0044c01650000c00c0304413078141c001500c0184003c851030100d010b0001290070300800b035001100315a4800a039406070a58480d000c5c2c1070504040040c00032078508030000940f501e11410500c40f0191960b201499966680e0340c00601c2540c2e03c009890101005034013100580302c0b40c000304640309a03000080b42c064500404e8501d01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 127228273 1250 127227023 127227049
    0x6020102040e090a0f0f060209040f1a0121240602010b01180501020304030818030a05060a180c0506070f3c020109031509050714280504090311100b 65
    0xd6400940035502040b1410481802d00361b102c1005124a0402d0601c0e801a000e00140f641d0300510f004440c01400c881c6600000e0040d10380101084000340c0c520066409001907000e203103c640d0f07081001e0401c0c10766588a2001600a94420368403030251540400030120113030454030150f95640c50281c403561b04100fa03a4002890402c40d00f00b03440c10400000c4d00d070700984c4070041443c03e0201c0c0302140d0a2070170310880c90911003d8210350010485042c140d5950500f0364007a240a880e288015040e60400010240d582e03411468400c0b0701b518190a00140b540304501c140ca000050380114400070710404111100c1a05a018a402002d4881c204c1c406480b000007220b010418503061000c0140d80018100040380d401c500700f4800c003504216a08003402d0b071004000d0203801078400c0804c2d2880f41a4100703805400949440d400b6003040381d12a19421101c0f41c2d441d0300d640251400304120314107600318501d024803070305e00200060018071905240001c01904110895201e4000c40d10f1030410308403211103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 127229523 1250 127228273 127228291
    0xa08070b0912190e100e011412010e09030f0d1512030e010e1504030309030c0506040612020a02011d0f12040506090f0d05070605030f060108010b030a0207020d02030706020102040e 79
    0x10030301001082c48002d20071074007101402c90380300840120340383c0600511004001c025202030107004c6201002890210039504031400304581d00c2c4404c6101201c072059620340c59840c212a011b690801510740c0c41c41f0b00003401e0407034620041120850440b140c401134aa800300f01900880c4810350020204c42001c20390f0020000031030401c0100c008240d00030720343c2c030401340203003803107080301280c100403400c03609140c0075075031010f200046c000041513070203001142183d0254000d00c0125403510308001840c0724522821000071059050a003d00c4200d9000341844400c500000415a032003003101ca04000000c0240c82c107582203510503a0090000340140d15041c00103642c0540380504250024110b4022070101500030b04240b8003040841d00d42140e0302c0c000c65009070864400c1c83c1d40c2d0708001d069a004a40f1204440358000100e045035000720300c014141d60340c007a034280c01c0d69500d100101c0203400008041e0303130200c0d10400c610f001d41c909003c500c3c042e10403607002580d9107050814ac103446590280007000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 127230773 1250 127229523 127229533
    0x9080708281b0f06060f080106170327040c0504050906010305070816050f0301080c24070204020c010b040507080a20030402040e0304091b030b0d0f0803060d050a08070b09 75
    0x6901c0d507110422402100c41d8055181060b03075581801d0032010008030004180750710306640810310f07032082c00d01c440485440c01700a0050715116901131502007486007608039182d00074000000080540001211041e100d100f05100c00745003400041c081d6410315842d00046100003a00b0f2010741080078103654041e0382820188035038103007040010201da00040045401005c9140000400c7d072240302200c1c40b40d141c00403041d80f6941c6412000d0b4403540c0451034944240880d480f0080c00b0802a05240112070071312401a0409a15400b440084e40c40000301500305d558845130401e0680c1c41c0d03c01c1d140145a955204001450700082c0e0380112981090340341c001c404503251054001c20400200d80d4400c2d81907402240d0400310540042c0385004a8224800395410038501c03e80c20b804400080e400e203104c956051010410741028040c9000100b04081c02c00380381141c820010850402c000e6801a1001e060440c06ca0840d8a4860500c00b030800100c800e460002080f00500444040c641d0308010040c010f01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 127232023 1250 127230773 127230847
    0xc060305040f081602040504060b010e1002070b090a15020624030606040f06080708034605220305100c021902190602010f0c050301050604140409080708 67
    0x21190154984004016000008130810481000f607100a046a4041c1c000e0185041502c1c00d000500700b8000000e0016490727005050f15882c01300c1c0d46100f181000d8010b4103009080440d2402c0c1d50740028440b64105000780d00c001120843c1e070703100700c0c2e0b00314065000d46440c2c1400198485030800414940c042d0900347c1000311296580414801e801035070443d000600c1d190900209005868036a002550500640f0030008220501000400050307810b1801c00701c1100c2c003068010031542c41c0020104081c030161a5032101040303100d0700451000700c0d609100741081c41200c04264801c4090000160080c7c0002082007084006c0002d00d28582ca468410301000f840d440000359100c41d0741c0c1908840c0322a401e01c00040d526089a590340001d0f494022520850b21400082c0c081d050005171020600d00e40130014103000d11803820359043c1c4000801551400b8546052403007800b550100450340691340d4549880002e418a00030258144114449600c540e1000918001c4640c2e5a901e03640d843c40c894001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 127233273 1250 127232023 127232033
    0x9040b1b09030d080a0f020307020703060b090708010e0703060e10050109080d0c0f06110304210e130c020106090911010807020a03090b070305070f05030c07051f050306032401030c06030504 83
    0x1c9070403214031385084400c3c0d944405204000d04070800301c2e0800070744000140f0418903400318904098a0088806210007480b120500485a02c08c449100000c0c0a05d001800400e1010394500e03048003003403902080042d20341100c1609444281c0303414500b19104481008256048880c03000241641409024010071211010346042e00b070702002049403c140700d0740300420400d0b50200d1080d83d4052000354032807a00d86400c1c8c0d61150032036018902d03e00c480c0398a80c102c6100e5188403d0241c4081c02c08854810803401d4100500a0000c059003555246c4a010528080300e1040a94560050011b048030400b0f600c0050421b4030058800821900100c0c1c8410100ba04180050100c07080585403d640d03114038102100d050044640c0140a503a01d81d0280d428000004007400200c4502e03030945486541d00d0702041010100410b0700c13840c081c00c54442c00f40c3d10b03020b54040c0d940840050291200301101d45c241d6a40f104a40141a403040003200041c000e01a600c05010080c10b8541804c1000d400c0079161 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 127234523 1250 127233273 127233283
    0x92505070b010501260405030306040e011802060a0e280b030c09010c08091012050618040f0204140406060303080f071d01050f0d06030b1f030303050903040509040b1b0903 75
    0x10f464140442c0100141c8502805800308050444020401240d42000c0c607000b03850b94000d0391200e2185041002013408481d06118800070203c00c03400d2000110000d500f03016040c1c220700b00501c18081075986480306921f4140d5410300846e4103450b081a4a0160021458080205d0304040b41c170140500802ca070391400030f412201d2145007400c08100008540ca07140a05100d0300083c130b500130041003600580c144d00700d8a000c000e840111810b0002c0d035200410701c000103043d00c43e02c80c6407140c8500810042050004085030b04c0e8005040840d2400d00c01d8402105d41105880c00c4480359500c0100b0400d05600410725508640303005103a05250070720400060030764408140e0040b0854025004000710f070f02480c100c4800900012486485640c01c0390008014101c42c84240d503110403010020342d182c0e11026040c1a00c5540090300740825056031412001044000c0c54050203200401c404185580c400e100d0a1240740f242c010090034cc03402d105e0841d0b0302c40b803040325900c0e011424001ca5410782d40200d8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 127235773 1250 127234523 127234529
    0x60503060f011505130b0f0703030b0306090a1e0203060405031903060302091f090e010204030506010b070b010b212d25090923070e060703080a0b092505070b01 70
    0x50710640703c080107132259001a85c29400f40d5007482c0c0029480c2d8015601c40081d1a5581c0240c03405c2258501410905451384d8003110710081c4ad4010b2408040041c8401070300e01d17400172090090303a00c02c0d0516808240f805000740c2e0141c80035800401c0104c049443d80405501c0e14a040c40d007801481e00c0c0d94042280210041c03e400050040c1405024010a041c80700c1c000501420805010400845403400d00070750040c04180c4450040600105401d0ba20f0411600407070b80c82070018405031310304841146540c2200001c91501c0c000c00400700e00b507940340084280264904145c6200c03c02c00d42040e14080b080b6a0710011026480d42c04015200b107280c01103020130345190b0843c0007020f11440044602e9a03054008000c8145040a4052030114081a42c0d50a80041000342010340f0340c0d5a0982c0d5150368201c110354420010491000040d104072269038200301c4040c1c0c04240f405625000440803c81101c0b1900c2c0700d502032040c0b420003100404132a035810000d081c074034502030080d140c100031448140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 127237023 1250 127235773 127235777
    0x60314151804050f061008120c0601170703061e0f0b150d0e030304050d030501120c090915020711090a09050a0f02030c06070303060608060f0d0b06130c0201060503060f0115 76
    0x1c001034140300c2e06025240401c0025404d4604510b000e640d24106004503000b0003513984503c02400e00034416a0048420711103043e4001d1003e60301e07141c441681d9407000700c645000ca000d56030000001031054041c10209603003004407a80386400003400c44040320280e860f82c0c040e590401c600721580703854001c080081e4000d80d03442e1999401c2400b80d490040c208000900702648000400c03c8148200407850700e00b0302d00720f99024859079070380d200e40900f1030104010281440070100000c210b18a2b00754448000c080c4103556165140d800c0320024401c0b41c01c170502c10f442601c500c03202c0c510b0307501d01781402e687e12501b98035040007241c481391202c0b0350310302d81c4503030040c2101e100d40401400d41d80c0c10000003000420040040381c2c0c9908924008018007881d100c0c1e000031030614400b003501032420342030416040301e01a010026080300307030302c45409022010b04510340201030803208185002e403a01842c240741c1016000031440c0e030b1034802890b00d070050040c200600c0807005070051100b0400303544000101c0c003141c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 127238273 1250 127237023 127237069
    0x7020f1f0804050106050a09050a0e010917181003020901030501061d090a02191e02030307051c0e030c151014090703150e010314060108060a110403020a06031415 71
    0x2e440d289004200a40103160310510714400010342041e103800c100d04c0342030035900502900061500b407a0980302c00d40740080c00312003020f00305401c0031306041c0034110400d10751500a520b45070080108a00449201e207840000b0f400041c003450341c1d6010301660740102070031f00e414804074540c0f03088416041d1800d030005100c3c0c180d080118001d400250103480c841c030381c800d00f00c409040c071043c4080c010070b600e500301104403040c0340d10b0742080c40e001005507071107207520f601c49524003107080486601801c0301d0a91600c5069444103070142820040000c0c1000c11020001044c45100070718a582a0f0307000206070b80c10542001c0414849007504450092a01c1001d85406640741c036440c0003a40545240100703264084005500005c160300b80914460403240071b068503002c41040c0801c056142d2009004405c01c980c400800b00d9603070980c3d075206512407080c0360b0703400f07090a80300d40c001992405a03a00800019031200c10204145004030201a08804901c903c1c81c00201c41c074012501105404100b81d01403080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 127239523 1250 127238273 127238281
    0xd0206070e041e020408070b030c03040f02012303010f0902070c050f0307120f020f0913021c08030f070905010207120219080102030925031a040f080406020307020f1f08 74
    0x50b40c0c21950398031018030307005904544030b6851203009400c0780c4109000c6206100001603980c005000b2213006101002020b46103903210b4840400c060b0040008078108900c0e21010044801c02c0620b11031000c1c55424290354039450212261440c901c250003042d6039500c104003034030025003080075010444034261411484504224006401d10035150b02c0405045102d41c040010017500c80d000000c82c910848038644582103070030908c40c811000325569250030070703035203000b4015103821a000c542c005526840004043d0981ea0b81d070703c0030307013091762010704000000043c02600d40c0c211440c0000f4240030310040c00f030580341c908526202501410301070701402c0e852614501c0c500f50030404038081c2144130700a6650341858600b0550302c1c501d1216661107500d512a0800345e550700c01c3e00c84801c80b074102c1c417450002c0d01072501111780303803902510440e00c181045007448002281903020f40010110354020f1078840c042030040c4000214a034010398844d041c207030542c1c0300c18440c00b80103009900c400d2610388030030383e2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 127240773 1250 127239523 127239529
    0x908030301050d0c05060f0d0c050406050313051e0601050901060c08120703020904060b09010f05090d11030c0916020606030111030106031e060f05150309030f070602040914010e090d0206070e 84
    0x20322508501e400290000d1240c2d0148580d200401825482d404c0270800702d052914110b5043c0614002d030000541d080000c00c142114960100c0103090041094400c0410600510000d00170384100c68200354004000401040c41c2600200b80101281d0402c050401425038a09000d84a4003840c0311001ca04800403810030341c0310341d059450708040079204000c41ea85520b40c1e443e20b80c00604000b4009000004540001441007050310301329080078100b0b0b0b820002950f503c040901c0c0011540c0c2e018842c1c07060030b45c10740d5034042001d8040d0b600180107500c1d800400c0f031700a0402c14001c00b8580668100081d5900c11440b0100f200e044842d645800601d21400440508141c80c1e6048640c240d9030038800040ba181803400034103c01c5030412150110707507000b003286096460104540f0044150014850701d603040600380020180b40e172050700018945a242c480c103004036074030ba98825408040c0b1070700500c0314807110144190402c1d80e140003818042c0c2400c100035541c60004110000704280200c0002041e1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 127242023 1250 127240773 127240793
    0x2010f0309050d09090b100f03020703141902060903070b06010804050a02040c020606190f090231031e0210050d11160c05010c0519081605011a010908030301050d 71
    0x65004090f110300e4407076003000800040d80c600078000003a10301b13446c0c074800c0e160a661144000c0c406485e83c10710309000110560094000c24005c2d0b0911581c918102c50300e1018100810302c00800c501c141c00d06091000b0020f00d001703c020f200c11900c1c0d00800c02203004c00c20800c40568040c3c000d2810044a9941e4a0518204440010025001400d04024480168010807400d10984056407000300210503030000020685985c80b424420120074803040c042500c20703400820382e03003151110304510382c4032880300c00d0401c1300d02c00f480201c10640b0000c18410080100d0300e898020780400080170320342c240307500080d00316400300b825141030000c0022030b000c0e00080f0303402c01c2c0488407283e80c0e003039220385486844c2ca0641640103811a000e106204003ca09036008050059034190000000e064040311a441351540c0c54804030143c071051800d018075680404031400812810384924004074440f500201c5140e040340340d10310086d05001208000b40088403000060700d04541c401c88046c000d074442800d10b02080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 127243273 1250 127242023 127242041
    0x1060c17090303070b0105010815011d030102091512060d1124130503060105041b110a06090503090108090105060d06091a010b1c02090604090c024305060702010f03 72
    0x103000104100091004100c5c1c840d040340d2081c0c070359040c550382d5181c02d400e01d090b00581c07842c0800c21241c01046100c2d1050700845202c400680010300e083c0b5410001a85a0300c200d8005a0501d000116448500810700419401c580309803810745101010b540d1b40c09115901c80340300740c052a00440d11407128104243c0c0701c8004000101e4450381c810300b203041569201514000c02c0c1c020705c60302c0c0000a07070b41410701c10341c0311556440b0380405119515150403a00720300181d4140d031242c8503400150300402d0f036520030880051310a000442e0388845c07403400502040c100414420480e4940b80030881c43d9200c0411b90300300180d1003d40023440d98158508096000c02c11006c922012900e039001094011a40d00202803039044210003100d012620401c82080c3c1c4074801c006508078000740802c00001c94160050310301c000301801515500000f1107421481c0004040125464100c012040310010602058082d03190075145410102d081c00e00010800c1031288032402810456040807100c0c0c0603100c0d9008040d5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 127244523 1250 127243273 127243279
    0xc0206130306060b0904060b07020607021005041802030f060f010f03110408031206150310270c0e04060b0306030d0c0203030c0d0c020f031603030f030b0604030602070302060f01060c1709 82
    0x244c6440c003c111380c0d0044918140030b2845d03c0804030f0840b04a8007990009503004124500d0150a50309100c0e00034880348003003042c4501400701142144910400b42d0b203544641e10011385928140c41c5d0985d5918014042c40d0040c0c83c481d0740b0000d80d0760312140e0a08040200d0402183c0c106503c100309100740301e1036004c1d6045000120b5803440800513491464000c110441301c80003140580c10070841c80d4407060380e444d443c410030b4580c100064100450403d400c03a400b5401c0d20f440c080b04048c8481a02c08090007000005c0743c0400302041450a4800c550140c20b05042c403504519100010981e0703400305a59407414441c0460300d0030704654040044030901041c481c281d07194180c2c1c134440645001500402207109040398403110115080015100380c40c850265803c4072220716507102924100c0d04e480102c2c00f0541c803076044c000030b901c960340104000c5104000050343c17444103040007424800080c107204000c40c280300041103040d03803081c02540c1c85500210350f41074001c2c1942d41a0f1803480340306852a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 127245773 1250 127244523 127244531
    0xa030f05030c070f120b04030e0d0b1b18041107050f010c0314060f01080703060801230906070207031502040e0a09020a0f0b1213050a0507030302010c050403030c0206130306 76
    0x204010010014002c51000301d0308481501d0b4503614040460490340c045c2400750310a400c03100c404a0510a112a0400d00908000c1240b980240c0414048030b0b1000050320404446800d000d030236852144d020201180380040182099840d143c050f903041c9444042da4840c90b22002c40c1c80c859440d130004c03100c0e065408001c45040d0000d64482601801418030701e4004030346401c9004442e140401c0c10390340310304401003040e500300c0807543c01528040c1c00604210109a40c4040c085203882c3d0034410a10002c3c25809034842c1040c21410107401c0103001881c4ca5021740019040c0301000c0d40001c2d0040959900181a2480c9880341c0d440c03034001e01469005903a070b0703550303682070040145a86e0700000042c2d0095904a100a13100c12145402d800746101d21a00300e601080304c51504001003020341c0d0132100025041044406640701c903407074081504c8050720b10742c100c41401c20404d502486602071045190400c02d013000e1440c0c9000e4148030782c10b41c0c040d005080001d40c11a50004020109010b0355014000700 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 127247023 1250 127245773 127245803
    0x9030715030608010b01090306051510051e07020d0807140102030114040e011a01120b0a1e060906050702270703021902010203010f051507120c0c12030212090a03 71
    0x1039000c039088520300031a00d48600855100c0301805210940c0c0410703160b5000580c039540c1c07100c001300002085c4601030b20100d6880d114503610000d2000d00e101c50b5503101d503111000d5040e810405d044000c030081010390200001c00058440b609a1010f0607049a813554a031516400c08102111241c1d000d04c0c410b502c00000420200010b0805100152003510200601003030440010b08030380954402c0c51b070034a00c480f007000702c0f03600c503072005032100510320808610380c0d45c07101c0858600442a00400c5656031005000030349506c3d040c181341c00510032858014003280c030b0300304050041d1250b5100079000703488051020f246204c4038112106807801e51040e4580c40d2501000003030082d00903d991001d18154034400c692a28414000e4a050f1003180140c0c03030985161a00f04481c44483d2140c41580440a104003070104e46c030011022880b001d00d881e83c8080c0950b41c81c0100f8011070755040484442250020440400d50006549185449900300140e5880b001400145616400d600c011719181c14007040d8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 127248273 1250 127247023 127247039
    0x7050106030c0f06030c020c0f0406050303040311040b06030106050324030d0221120a1d0d1d0114070b0406060503070306090c0608090d030203040303060e090604230c09040206090307 80
    0xb40803215500318280030700780c4500c011400c1c0d039801c0c4450001644000d00005107072030050809050a00001c2c40045c003180c0e036a01180c11038001d0b50095555440d00c1c0440c0c20303542801c1c0034078110310340c7c02c0710340e286150704241d80601b01d4013000d0924010307600010156003480302c02115200c0103100082c229600c1c0303c00e00c0d500070b56420b00007421040d0890000450081e604000060f40c510500c10040b43c0307241e544000310f1000400d850022440780603141079099418410610690304403448d107594200c07000301030519000456a800001904000380044120714090509080c0c800b010b52012003c21140c9443c2095000340415030002549805005ca00008202c041d03481030070f083e4441c4003000d1000399140d5003034900e082c0403203440701c840d04001c040c0700d4101e1181e4011039100b4881c0c14006800ca866001c0700380c034200c04580c240c0c0301d5807002c0288014001031a070309080c021103170380c038001c103038507003200c0040d01c480107040b200b805181c291001c00c00315900c07101030b9185114044c044070000d40ea14904 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 127249523 1250 127248273 127248293
    0xf020406120204271119080601140108060a0608090f07060201091a070e0d14030304030f120b060910020106030501020c010b0114031e0606160c05010210090b13080705010603 76
    0x7040744154548041001d0404041c0c84e5520044440c0400c0b41c11840d4580b600f2050702e843c503200a6025140303020b0f204980d25040510301c06400301c940103260070740c10702d451803268001d80506030381072003002c00c1002416510310400c10240d600d1464040007540b9119925403400313515440e5425a400344030004500283e05500c21405e03a030040d500f2000040c040e0f000e2a00e440701c01d41e520b81c00070390a1901913026061141c40030f00403c0c4030718907a00c40b0441100480d4203540050b00d08400140d03401315a440d10540c0000d5103515000c41c03400c100300780b240140002d0304e20300c42e00b484203016030681c04195003094001c0d4080c40085170008025541d415030460034034001d20625107040d0110b500742082340210410300041d039124210394562403800024035960020b406100501503a8800c80030441068001c410001d900c00d07451040760342c012420700b04000607003400e9002c01040100ca1a101c0724101061071101a6038000c1040b41d80c07091120701504014006102d2504041e21960a10000104011800b44 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 127250773 1250 127249523 127249559
    0x20f07050a061e050c040306090804080d12110a0f1d06040f0518010e0402040921030509060c07080d052a0c0c04052406090a1409130c0e040f020406 65
    0x9030481c440031246540f0044441c00d80329001805002c0c00144005070b540d9022014050142c0741e1141081c0d0340b0340e0a1481e080602c5000b50000d84a421265007007403581c011003400b4081a02c0c40c504041c003441c4020140040c50600100704400800d10b810448000c9480100e410000741041e5601c03601d9003541ca0f02c0c1e20091103058003031108a001482d007050340301a0340d07058a13008007900e1810348454003044050f01d001d02e001d5541c600114501d030b0a03559030500e0889500602d40380400d5500e0b007a4803450403e58020700d43e9000a004200c81000200030004544940c02c00007800610303134965885e000f91200c1051000120f81143c25801020711110102410b81c40342184101d80c0c43e0080e11060005580095900d801100580d90310031045600290000c100d80760702801c1107082c0117044002420900e8203900001034260040c078001c40314103100e00c603240c0c0a0000110091024810b0344c070014190381c24072542d100e1404100200f020001c80161240368960010414080e49456100d203807041f07500c5071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 127252023 1250 127250773 127250801
    0x40f0f150503010606020d0507081b100e120703050c07090e100623041e051f0f05031e0a051507081003020f10020109021c020111031903020f07050a06 66
    0x2600081c00746014002c1e50706441a5502504409a1425041d035498000a0003107806a009101c0d00710710580010365051980c1035070009062030080884084102d94145102c42155003260110008900800c0d048a00c01035051800390b5031402e01126560800c0034a4011280d80750410f50707200d408207000a201d020a030028401084056a2a904044100701c40400925412075844041c0032914182d0701c200d098154008800c0075006002c04c000c1c048450807a2420315112004803506940d80311004240301400d89a00069901810700e800284d9904040789809006a05402a1042d440b420b00c8039202c0540d11034116003100842c00803210325250200c407260b000a20304400144514081401d000031030b46c01404011882c07503100d040c8080420041e00810556485410b8000103844079401d000c40d01c000a491003a201e00d440c800180b0b0f0414490a403031a40c0d1041c0020301c40100d480d8481001c2411501300180e4450030500c03090b403107008a42c3d018015004012280d82401241e400c90400c5100038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 127253273 1250 127252023 127252061
    0x12040f1202011506050c0a0c06050d0b22020310080304030302010504030e01020c0f0112180b01031214030114120102030f010905090f03040302060901140c010b0118051e040f0f 77
    0x903400c038202c400010084003c0d01c9009820840700380994010503801071810155000a111502d50804100b6590722200000b04001000c080309d083d20721071280e000d0700407141c032016981c0f2518504030303003101140035289503075000020803041d407404c80c5010018001c002c01e0f40d44441d56414064024002101d0641c042803840758440e40302d602c00b084d85181313800001c0140b40e0050312100111003200309a1294881165030391522810401c9140031505045d1140020582a60446c503000e100364031ba402c100003e0082e14100e84c02c0c2a4040c42c2602d0643e49401c1441c58004501c1c400030f40101111010110b00754400010300500d038048040050586420082c140025141c0074059075981a1500208566802c00c3c00b082c030041c50010004d0000a0341450080c0c0c2c6411941ca103c09113910503280302080e40c0d52011840b070607581000c0f600a8240300802c9032080c0b249410041506491510b505072254102d102f10f0702d4403a40e5aa100c2c168014030000c00b08503800407080404002c0c1102c60b4118910303100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 127254523 1250 127253273 127253303
    0x10501060e01050a0305041b0320030303040206030a050a0b06033306070b06130e0d091d0406050603010f0e0d08010b0301030309180908300103050706050f12040f 71
    0x1c0c0d00c8100604106a460a24000403218110010039004d48100c500003090499138a8120701400d598000d14000c803014122801e0309109a11041100c0b10b03428001d420900410001d42d40f5101503d0780007405030000319131a42d91500101c02000440075640e8051804004c4c04089680c000c84960381c0541e0a400e03880c60040301c0420f540100c503440e05581c5c490307003c000e82e80000b40182141600035a000d0500c9003640b580e00300b1901074a1031039002e045198041d801d10307540960f04c03080d440000d240500f51486d11800d11424103440390030003400604180d45507004620591800d40c4581102c41b0407401c1001031000c180c1ca5151030b903050000050008050381c0c000328058681e58101c0341280c0d8981c48840801d454203681c0721301c442202041042c080c0e40c1d6108100442e20312801071a215049040c01c80303404a1400785050104140800d510142c151000140000352000440c42c09403800d030b05000352a50407490480000e44110300500315020368031400e020802c200071145080041c82010314141104c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 127255773 1250 127254523 127254527
    0x212060414012409180c021b01050d11090d05030301050a0803090f010c0c12050601060807050c06070e0604170a03030b030a0f03140f03090c0112060e010b0f090d08090301050106 78
    0x203000e014010700456182c4140810070f41c00c5120030203008031403c2c4028542d82d25000940050035040040381c0340c0e03407201c03241c100450781171090038141742c10708030800d0860034907200082090245118070003c043d500d04648150107500000e942060400605004251031685031940e240c0c0c000b0710074107001c3e0400400c08184c0b5800401591225a80901440c1e202c0d0700b00801160b14007292031095a45c044103c80104007081d1101e60003403014010030003002e003545003490003440c003180101103030100724080c0f12160052402241c440d400017210300c1c03d009800c900c500007402d6442142d000150400c50f40a42900c1c0d4180441d00740e0005000362020410f001d0f440040c90744480344018010030344403604400350f0000f80605a4081240b42d035901460400c4641406c01442c0d0b842030b62807045585c0b110750003107282d40c0c0c0074503078400e42181c01c40140318452038600d082d481c40406010350404548045004141c054088095842c07200000b0701c51250390085051000b40f45c2d1150000303d00a500740000030425074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 127257023 1250 127255773 127255811
    0x20a020f0c01170a02072a03120f02060f190218101b080c1009050c0a0603060609050f03192607020d06020d0906050c041701110a1b050102120604 64
    0x1e5002c40d00391060f0b1380c011810000f035028400481c0c4242e4415015621080c0b4029003405502c0814441103a150440c10714030480c5a1000c003500404c010304c41032031421a8045070a41d04005000d0300130803223495030b40394100450031a01c5a080320381c1c400b062044048200c40d02124000034140c41481c4601440c040c03c40e0224144040c2000d1160401991303400550402c0c020030b0040100c505444000d046690707401c1c1500c110034070665255104c0e50060b04c480c43c001446c04000c0255060030860076140c4080586240d000340308091044c40f4403c2c800c185501c06001211200e22074070078801040000d03241c00300b030342020031102c3c0580e650406504440da101d80da0842d903020342c006188402c0f80417039986110203984040450514a034a070b515142c001070301c40c01010300480084040e580c40b5414000ca0710115680210200e6080e03040280900300142584201c4400192916140c02d440543c482e4030120f18807441170080840d84001940400348003540e45031070003000f08403000d000308118240c51010300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 127258273 1250 127257023 127257047
    0x605090303060f060304060b09010b0903010518060106030b0f0a080d0815030316032c010e030a11060703050418022502030c06160b010e060108061503190609020a020f0c01 75
    0x45483c54052403e4600340014661080c81b400c0003003940a0110046440303a0b00a0380003965560303001c6a100c0701460700b0300600e030340240481d03080d07900d5046004130759a46d060107104100a0603600c100550540d160a086203050b5407000d007110640700d139a000d165031f07110407030b08841d800580c1410100c1c003101c600481c1442160401802141000f060310100c08070260040b50450600107500d021150300350f411240d400b207094015100c0742c40c2c40d011000240907989040701c2c80d8440e0b0405046840010448683d1001c074000560369181c44107502c1c44c2c00d90b220301c0b6603041b5440804214451b01c03c20792050b0000c2c0010944000e000528022604400d00040d0b09450b0080d815001112866100d04024000c0c00660142c6e0041056185841d125182e80f01802c3e04020345205c2d0400070044603507041225107130400300540d4580040b40c3d41d024516150301015104910a1500a460781c014220a1700090081d0400c01c50071941c0711200c40c0060744c1c4060000c4048050b000e2041d0a200e198003907404001c0da = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 127259523 1250 127258273 127258279
    0xd02060903030c1b0d0f02070f05030a080a18030c05030705010f020c091f06050306120307080f03070c021c020a060302190e030a082209020a1e020a02060d0603060509030306 76
    0xd50726092840c00180d080008131a410407650902003010740d0b41001001d403940260740700e8210340006901c00909010780c5801542c10400000010051510700143c4020aa50414025034845050080841d082d0300804091221881c3e00b000200c24400111507902c1121012400c595003150340304015600040603104010241e001885042010709221045d964407100740e800c4815500c0d1046040030030102180c00c0b00000030700200030440c1d181880014036000c0c015a50040d03040c000e0990321111544100f403443c2100032001710102c2e03040c50048410341e43c060360044c064619080e00309410701c00b0344590705c010b0348503403100c0c6400650107001788200c400b4404000c0c6003808825140740c0aa410b440c000d0700c0d040d014401c40521602041003034014000c2c08000c02c2e880029134944000300402d400c6580c114240075441080200d6285030485003450030381802666070101215014000d9080140340b40000e50008000541c006040045038000c90941c1c0c8141003c001ca5103130b12a4040e0799001c200c40780d1b90 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 127260773 1250 127259523 127259527
    0x80304090f0522020a051005220806161101050f0f0a0507021209060f0a02011d010b0d1e1205030601021905070303140c01060308270a050f031e0f0d02060903 69
    0x10721801c070160f00031a450001c0e2648849550780c002241003040070742c2580001800c0841c0042c071070344c146550301c80ca00381480b010302c01c3c017420300010a03222100909802e410707107103817a0300181c0e01d800380b441c4620b0101030078001c000c24504410342c1c5e00c9101c0104c0c0c044a1800c10800024405c2800d4460b050244003680e00401180e801210701c3d6150f40d201030819075020509210711030b14050303140001c1c140903485500205d510180c0749030892607050b507100522580e0b41851072007410b0751a4600b5100e41947c000c440881c5407101d50300d85104100b4140d002500c40c07800fa40d800980580c1000065001c0e41c420f03801c40c1d2440900c0222600c500e950344d880240b49030007404081011038840c9031010311200c546607810340340c030b14140c140c07500b12645a0304c112000d5074089000e0f88500840311942a101d940d000f8030301c0d8000130181c002038400b141c2d8090144502d0024100c0092a1010000c02e5610449e502c0d0204d60803011202413552000103105800e803a114266180560a10104100340904000f0b00218 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 127262023 1250 127260773 127260811
    0x6040515010e03100e01230c090114070f1101090f08060c03040503090307030510050a0209030c1302040f060305090c0d02031902010201180812150a060e060d020301080304090f05 78
    0x1900d105128540035814071070b524190580780c500780709401030b40c001040000b5803007131503070547c1d04c50100440c481a00c10081c001000860811102250882002440c1c080395003813001101e5201e6010720030028100c892510303090000c00c00121504181507009032150030071a43e8607241c000e1000128061001c090308040301154484131507001031070700144510190381c107002407003000c2441e2100d60b40c8251090340c03020401e8070b0b80042e5842a981c01c480300ca030f000e41c81d0001c14004039964051a004190244510842602c95100207a040d200a44648004600d180c1da54200050141100341c0701580b442c0a08085814103240c00700101e07848a60242c090044021600d01c00503880d10316540070b81c190754a403181c030000c00008030505081c040c4a69403043c0ca03a0700e03000003410b9110b401007210b1012048084400c4040d03640740d0178801111140d15040710802c030301002081d600e002d115403c044440c0003100208900402101510658485034010000d85404000340b0095410039590340307c3c40351109000b1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 127263273 1250 127262023 127262027
    0x1811040605041404021b0d1b120503070c0605180708070302090103150f02040905041e05030405190509070f0f05090603060405060607050a0b0114030a05060109151a03040303050604051501 82
    0x4411500740c0100010b0410550401e0070100a4020325908647d810800345941d0540e00306180850840d6041520381844a81d03907260246000e80502c200144000800050042c0313104900c08010f5603405502840340b0b00b851040c081d942c01c04111461100d00425902160300c2d10009420000c490f002002c1c1038450b483e58450f038014052095000d52803036141c2c10351014a03a001d000520081103040701c0002c4901c0c7c070b82001140750405101c010040c1511001c11004100c00000341e034181c0300121064049911441d940803040c1d62550b0100b03410040001c20810100d400a045a0b41d0481c2501c54904052002c81c2c125040d1091452080d4070132011b10101e00d150600798403041e40003d010b44680c0c03500f0306039102ca43c600540301c07000b01c98818040d401800400c00300701080701d030003102f038000700074880c8165640d80c2c803002c0500500c20301c9560340c1d00284050900c4009080141001c11040250f400401001c0c0441d62003142c00780e01003420440411840d08082c8112031207440c05070800c4100c51611001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 127264523 1250 127263273 127263299
    0x41205090303070f03020a0201030b0d0b15030a1b060201060e092505040513060e0a0203030f090a030c180b0f2103040b0d0b030706030902030304140604030606181104060504 76
    0xd0340c05100901a210002d6810007034604075034065001080e8060451000509907840d51180c603001d40e800180c4c034800518150300316030700b002030424055115a000c0d0040b910300308190300301400b80003108102c02e54803403512a000b4180c8200354000e2001a885044604003c0d07416218042e080d40220301d40c046c19491402c50000c071015a03200c0f400f00603a00e40000e01900d070f00b501c5140d550103804060000300071182c41a0301c41c0e03400c00c0c0c0190100d0007030b036000261a4060324034080400b90000425480d15920807206401a40e88200c0685015072151000b1003607809020a02880c4c0d85001c2140c2c003146482c0f060360004007001001c91140008000340c40414440415090103240700034040403594085400103000c400f4880c0400240d03403c40c02c0101454011039902000c28945440d03000c1c40503031408001c03202a00c0b1807881580c1c2e440c1c45031010954900c2203074005400c00c2c0ca800d501103a03c00034140340200303004d010103051129190303034503c2c8201d40c8954815480428800c0104205401803d28 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 127265773 1250 127264523 127264537
    0x1110405130506010f0516140607020d030c02030a0c0203120c030309010b03160501050d06050604060e01120605182809030e0102060c030a0b01020a080a0c17030c09010e03010e0f010e15041205 84
    0x7c410400300000c2d51180c421026110100d6050f41010080200040d0304208800105101d49010300c000e00c5441400394883c0f00e40301c2000e04204041c0501825502d003081450900308020414030f0365042d0081c1440d03129041620b6035036095081c40d088072105d03e000220701d07030880314030130743d440030186004010f4803940c1c0304440821825841c1c8000003421ba468002410040050f0b8486540c000c000344001040242c02d400c3e0440d00a24000701404203880d0301c05400c0b41002c45002503c51619150034040b80d40038072181d1100c1c203590740b086103140d03110641c20080100348a03850301345501a25400590f1507041c12144088812418030010b401080710350048030544406005070750000355aa15011520b500c4401c0100128400d0109034040000811920b1741c0f43c64015001800c5051580c1a01c510388140c1702a14104000340c002d000c155502944101042e185140c1107a0030100c4461009001e0000b22081612a00036960b07802ca00304440c0b00d00c1c2c7d120319172058401d0031120038054180c031142c00c070b11 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 127267023 1250 127265773 127265797
    0x80f07050d1a0c0903120301180e0f06010b121635130c05220f0209041b030b0d1a0c09060408070503011505130504060e01110405130506010f05 63
    0x200000c000c0201e00b240e402d02409809040d9555003068a040c07525002c0b4400050210003000c05c01044036203071008040c561404c20303290208140745904922840c00b0300804100314180611800003840c00008001000048080781408200740d64500940055403003500d151808600c6141c04003001c0711400341b071107044540b0b0041c2892400c0c0380ba030920000d130104a0b041c040280c10903450205220300c50380040001d1030101c0e003540f918580c82c0041c421075440810115500381e100c80341c0c03400042403501a120303c0800580f00304071340100620302034180f200098140e408203203000c40b60400c90030301e42604100250040c00d0042c08003603010034082011401401c0c0c0c140000d00784440961585d40c400100000c1c00401d000302000350812040500f1942d49019460714812050020080d035202c171680d0890301002c8040004881d943c500301580503241194a600c034035480c059a241c84001154098000d840c016030751103c0380c00c0a0005501100c406544041c085041a9a00e0013018460801011000c1c03800b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 127268273 1250 127267023 127267043
    0x5130204051f0308030f0108061006030504030201021e1e0301050d0b09070302040c050d0605180106050a020f0f01090b06060c150c130905070f0212090f030f1002040e01080f07050d 79
    0x12040b4840c44449410841c4c000000006002c200c0002d001c5c190b000d13060500140a0300d051440315080c11045621541d02419114000201814001c3d0705590a4a428211141d030b211016020070960344e1000c0202e1070b02c04031401205100d03421751410340741601c00140180000c0a800d0f250500d40c803000400302d64207071203418400701c0181c540b4000d40c80325031013a8580d01c0c1c8404c2180150000c2e1103003500b2090254104801c0420880702c0300042c641120307003609006503650b52104c03049040240000c0048141c2c4521414550281815809086e03610300800c26200075844488c00c0040301e02c500c2100f44541e900c540701003c5480600c02126402c03604170b50003185000556280995500003541c010a41540d03038a0800004075000601844000711600c007a04102c424005540e94030300400100300d010b02100c08101c90f40d5101040180d201e1400c860840b058080400c8000300a944103006684100080c5000042c41c80c100040b90884800c68502030840e99003004240400500246015680340e446 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 127269523 1250 127268273 127268311
    0x415023708040f05100507050a14010b120d020f06010305100c120e100b010804050601090506030c030a060c0306080f03030106050a14070303140c07020a030f050304030b010e070306090513020405 85
    0x98007005100408000201e5000c8034504010000c00401c2e09100f80140a4100321080001e8030101d001c2c6007055221100c250300c241440640d03401001030b003400e00e0700031111201510b840e110001e240300c200807841c0d00321000826809062a11001d00b80310050280c2c0c0400321110100526800071250f803000c034a030a034800281d02d118002601d42d282c903501c1454008454080200c0154081c0d03504215080c20301d5201070038266205551401c05201e1102050740d540d0200d507140da420f0200302070b00302004003150303e038080230700b041c03002008609413134030100e441d000e000a80b01c400414003a441403465070285043d80c0c038195060300d0300e07803001e944a03042002c441071341c0740304c4980341000e410500d010356000100e42c440381c0002000900c024003140000b100500c827000c01644c0b440b41340700640382d01103400f07c6140711a1030801d14500454000038014101d041c000700d100702e104805907110309582d6070240600b42d40c0380202c0c42140c10546500c21260304610391000541882d42160703812000d07403803054803000c407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 127270773 1250 127269523 127269533
    0x5010524120111030a02040e0109060303080a09080c010c03020408011a0a14030a0204060e1603050105030a0f0f081b0606042003040f240b0a05010206060d03020109060c0504150237 79
    0x801100c241707849035401704040c0448100400b4680c050489007104009071402c6403070240071100002c02801e03016031100070200800c0301c0203003070380e103035402c0b440007884060002e040c00b4000e07400c5809412000d61070441151070510f2031405a107840d4001900b00c4800314100794111810440c0d4000141c2c05100780d40803100141c840340700305401010340020f01c3d507507420515014404620480000400c060412340148590b5038041241210b4550003a000401f09209140241c030410082c0d00142825101113050744510000359000c2c1d50b9545118261209640d03604200000c50311005040d020441d007500d40c7e240c03400c101e44021500180078218151000c102e40c2d8032521080b800d0701d40701703407103681440c002910030a540c0240e038111501142c0d404192414103000035071319040103128601c40c00c0c0c0300101c401414002e5201007000d81e0001c0d403d000c0e0041e1710802070720329801482090307a1040c2008002e80c041c0c0c800f080c600c1c0b842d05007148408103644600140214594441c0181030322482012201000030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 127272023 1250 127270773 127270777
    0x1501081b03010f06180b220b04030c030c0e07020a03210f0209010e040b152a01060518040302061501021e06060301110a0509130207060509010905010524120111 70
    0x440c01c020f2140c0314034140a070080180d03a01005060410701204001e000b03a400410603200d08540a500d6440241c2d1464010041001958000054108002004014064008201c10a0700d01440001c071045964888482d50104121031140c0182c10940003000024031800348c0c9030460340101d03c41c0755000e166040e080200c500c0b8004441c0c501341d0010301d099180d40c02245440040104840802032039403102c01203090000080840b0700030110000e0303d2501020000488a140e203400c03410410230b039940701003850080c2442e0080034412140e240c3c0c203a81d108a00500940310307032341c158040c1603c0d45851454140390a442101281980200c1d01c113150001e1460b440b901103078040318024043c9060100603d80bc41e0802604c1380341202040044800c881e40180031107010aa0503140001403003224903103034000b8010154002c21a0703080c441403200e00401504080703c1140114005c2000ba00d800c010b0803030f503444503800f40c140320000606045040c03805824042c200e16580002203090782140c1d00d81c000c0c1d6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 127273273 1250 127272023 127272029
    0x80f0a17090d02010e0c220905070806040c12050a170903011503150c0801061d06030a15140d0201050c0118030f0f0314190e030a0909050903031501081b0301 69
    0xd40d202064041c11181d09000d0f00d05c3d0102004082c114a170a90f03004140202d0b4548040c5c4246801850741204c4558154001c03002140c1290589500342e48500c102a124401580c0596845810000c0400c620810900104070154024002d0255560035076440001203850320041804070f805118034581034400303000706028485400914203030181940b405085d007002e118203111030180341406c4250141e41281495041d11002c1c200840440c10003d1006404104160a590040004402c0c019101607941004503a9000d00f42011503240d21010040201c1403100078070f40c1e105100040030005540540014107410a8120001c15050010206045131544215003140011040000e40320081d071700c4807900c8009903443c5001e02140d1402d440031928010040d20024280c00220442c1051314040d0344000c40043d4001e05482d1210406003000d060b40c40544500490542480e00007162409c0206c05c403446410026081c0844890403401100d074500000e00f030700c07075610030305800407000c800e80c1d4080c0d030003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 127274523 1250 127273273 127273291
    0xc06150b0d0207020427021c1205030105011d0105030a150b070803040210031506080c0c010509060a060e090303040f02030a0b0a0c17040b061302090901030501020c0d0507080f0a17 79
    0x501d00c80c071301c1840211003480310240e0040074070a81e03500054909103048580560104c0301f0303040701018601d8540701c2e0b03101c0303102c0140a8220002111030072600840558100c9500342c84541112090280004180512a41d001e000403030800006980d80015403003a0040d560007180c404d641c3e9200c501780001070307100300342c2a0b0b0510404000c0008611b050b0b041c4440340d9000f45410b104c9200301c0106c41c0e00e00591405840244803d0500144030a01708000360b4080140c084000d2046041801a0546544041d68480c00e81800e080c2d02059603140882c0303490150b5007080c0214910784e920f172100d401d985190315003207074540503581498000c94080310700c540c040c240354400000e04200d000400b07000c03109640c3c1042601401181080041003000d007002d5070001d810740e01881401022490700e070003480340c0c041c102c0c0d001d400100080140881540a01803041c140400c580c0d0741500820103030345038007c003000202048003c109a10751043c400000c1e000704a1907080c48041420311441e03800040c082103c0c2641 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 127275773 1250 127274523 127274527
    0x2060a1104170105040c1a16020105090915150a020304050904110607060621050a15020d06030c08012301120602040306091a0a1b110721050c030c010c06150b0d02 71
    0x511403940c051b5001403d03540b1031520b02d003074407000385042ca0141060003031030000c0407810030042d0390042046407484280184420201c3c03902c01c40c0c5034101c0380041020350040c40c148102044665580d000c03181c038117250b40c0003141000e1801c402c000c1d2a41340140122040c045a09174074425031924400380000741c1c0720300c002043c81030900061840001b128000000e041100703d4031000403c00101c2d078000055084483c0d50500c1410010110203441344000c40d5110510740304000003031182c00c06440040e10741c428005e000740300000206600c103003450164010281c002d44010000c40035514510608144146809400c09640e030b1100c03800c850340300000f9108a00b2a1088000c1c04141342c121a0780310201e150204000000b580707800c803400b00740b2456001030108140007200e1000003000160001c2200003049515038043c001c3c0b0100036500340a048550b44242c082800c5603203404190b2146801c41a59295040076864580e04040d194003040e510f1000008440070070141d00000041c080f500d030841e0096 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 127277023 1250 127275773 127275781
    0x90709090e12030609040309080717010b0603150603091f0207020f0d0803062e2001050f04020904030e03010c020304061103072012061509090d02060a1104170105 71
    0x3505640150340c0d10300d107540100055000621411060300e40058096403206460713981c41c030301502d0406454008281c0703840f0f00400050003007203012901c40414000d00c02800034030b1804040c488540010340e0507014003c424404002c442c2041000b8550220308082104c0344e01e59000d050201c8860201440044c8980005c0c8800660418550004c4c00050a0f143c0709910007181d1694400e5000c0a0f2029106100701d10346a8045c0030742c0781140b03a42e80070006011170316110b003503000341030240c80b62082c0c01c0b521901d0081c0d480e2800b0610466124070413500207029907941da03a0030031441c95001030044080c40300000b90320945840910840e100303445241c00640d511400c01c4c00140c4070b4144500b07801d036554001c000410005060b1078503c1c240104a4400412a094000c00184110788101e50102d41c1d1045108021a0711000011940c000205440c28140f60f114074000f00d86401c034a8200c1d401603445200460f5400c00554003980d0809801e860303981c02d041e145c9034070041e00c1d10000d0210107907039143c2c1f00788 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 127278273 1250 127277023 127277039
    0x90105011a0c0c0108130209010b04030c080304030b010302150c16030308010f140d060615031401090603050d1d03030f040e0708010305150901060e01030b07020d050322080702090709 80
    0x40001541d00900346410b0402c0c001c02c9503543d414500702581002640760100380014009800c0d03440899000301007a02a60312101c411445420920081c0c490065039880090280c10200440c0e050b01d0304500118800da0a6400f4807006081024154030f514000704480350140da0144030002880701c061a4502560380745041c0208100c0c4180c0001c14a20f426000c104820504120301c0800e050307069404400d40c0030b4900b0000b000342481d500030344075214102e0307038514030306c1d07050f80120300d00c07507a00d16104110707603c030800c8500f29900c50000410a038419002402130302d000c0d1441fa4071001e09920840308900800001c241141c0000c069001449000f140500c208060482043e62009c40c51030500210341c03564031020380d40d01c2d00e54902c03010204c603c0c010841090081d0084005819801c03003401103541e4034540500c0400c0211280c90050291001041c0c0c401d100c1d000310380c0900300c032000444051045016415a0f0076000004403807050381001701d400140c96030351034584a82103e03140d0301402440c109070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 127279523 1250 127278273 127278299
    0x170406120c030c1b0f050f10060603090305030601031a04020f07060509010e07060503090316141603020f10030b15030702060f010f1a0c010f0b0f0402030c0a0c1a09010501 75
    0x80e0750501d820324660312030055000107942c4c00310310080c550600c090800e090222030305108440c05480c2c2d002c1d4042d168980040001c41da98184064401045101e07610f0008504440d2600f4000340003440030000702d08903610139005450b1132942102103511102565000804aa1054110201014000c1070300000d020140c411160b005840394020301000780650b5049450f001319000301c3d0305110b404130124000901c00c1051740c2c003203448070842464401c0e46080507080c503803042402e2000c80c440d651042e4011012103112100b07c83c1d000d4880c04440090808000307200304200d8031170707081640d43c02c54210641e4544140380000e41d081c2c004030369281481c0710024107041008024030580440e803c010001031003440141003c4031150409011808060641e07074030144030b40e0f2100c3e4a15804c000d00b0000031040d6a201044540c400c484210764404045c045c4401d031b000c102d8680a0f0040d0502951040d24014010021401e206500c1042800407030001919036004c144c90380d00c142d82d5074400500104041000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 127280773 1250 127279523 127279541
    0xf01090302210f040905040f0615030c09020903060a0c03090813170303010803030a09030905180f07020c010c06020f04051903060b18070e0102030405030d05090406050411030103080717040612 84
    0x282c0a880c1041044150741c003803046115a072411a520000101401440c070b00c0b101031140e0104080c44180300f404510b54007a10607000a8405c0520301b41c00041c01a0144200d0310943c0014001e08541d23515030b0204401070800b03001110501d602c1d00c00d4100041d699a004202015075a048000075909207403040e03c5c3c14030b4104964589074402c200501000000005407a881140d03400041100c00341480c0c00c80f0000e40e20741c0150b40156a00d803004c03601003181c18010303126070640e09400e9a40e964218041b81d4880842d882c142c00b06203824031280118036a600104031800800858a14155943c0f000c00c4400060301c1034038941e4020700d2070031710030030200d0300460910300d004650711011901581001000e8140180240c0244280300910221a90013070083d10020080181607415650100801602030f50000f400103100394a0a0b0021600b40740c00d100303413081b1140b01c14200e0b040d44c1c2036641d00c5c030702a0f010ba80140c6404074007051646020702c442d40200041e010030381e14103ca06000c1c803c110181c0d0300b800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 127282023 1250 127280773 127280833
    0x605030a0c0909020609090a05151509010522030f050d05040605040e0712111206090c040b130f0311091b030604020a1806021c02030403030914030f01090302 69
    0x55980119819540741c8055901c0300c50001012085880014136610840d1000c58000c0042d00030000000b031958403240c422400d01ca44031750405660010030400700c00c68440c0d215541028400000103501c241c000d0030b0a00ca860003010207201d541c0f620018108881ea00840d008000703040001308001301440842c0d0445500d0420b05e040034104440a05203001e94020505003100d1180040c1d03090303206080d0825021404202007000072680f9000c0c3c00300d030340031441504250685002040d15820304424140c41480800c8001e070030706082068919595004401d14035481c01d03034000c0400c242c0d01c0098680c0055100e4503c00045050103c103005211a00818040030201040806c990201d00c500440f0b5200000f1a001603403201041d60030380b4407070401c107a005420760001c6000b08009400055239100448242403080074900440300803030703591049000080000d440004d0821110f01c0c42c2c0d0725440c507000001c080d00d43d07018010441500f1a40321500541c0141d001d12074400112011146984401e040c3d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 127283273 1250 127282023 127282033
    0x903030105010f09050d0602091c150605060f031f080d021606031b08071218020906030303070207090b120607180605090d0209070315060201140a0203060108180f030d0f060503 77
    0x1e41b001c064881c0183c0f080c3d40004080c282a40c0300080c10780147c268070525248904c50b410200c8111780c0300801c1c0c03000d4500e4501e020609150003000d44509200581c07415140d41d03106103126980d00e011540d92200713110662000306403202e0038000300d0f0180c51640d0041552140000417030396901059030003a000d0511748504230381c00030400005020300114500348407401e0380705d983e011034540051481500c166440c0a0701c03200009008594218914001c9a1041c81511035400700354030b038401581c440015070701c510410000c60b00b894004a6118600400264032a2035115440b42400422200030300010401e0f240c24007406000c20351070000e85a02d01d84903040900c00c0022032980c94040c000644548040c13000100024842d4000002e46c200405c04030529598840c80a80a0551511000d602110784800658a14464820341b840351a05955a81e0a07451390780c1005808174040d20548994055001240c600203400c0000340801c10303001000003410401e99070800c049070456001a4441d40207 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 127284523 1250 127283273 127283279
    0x70c020603040f14031810050307051204020f040c021c0519031503021507030807030525021203130b0f0c0a1206050a090911030606010914180903030105010f09 70
    0x684000d40b40e00c6a407001944076100e045041000c09142180c0c580c00362072100143c0c210500001c10f0a080342c060041c0c1c0c0810b50100d00d203a0995043c0000c0f101500050b0060022101591403881c542d60042d0020f4202c0c0c03080598200841c00340c1c1c021880810260744032141e0301240d00300652035515140c09915205080030111406420400e40120704041019190380c18882d8008803843c20740011030340104883e002010079a0300c51030540114805038045031003074001414081c000e014261080e01003c4e1460001c4401c0501c00e0703484203582c810380c82107120303402401c2c2c6007840c0d1000075409401c9071440d00495104a103444c032036080005160341100012001401b600d2114282070b5a840c58203030420000450030b102d2a080180407aa000c51351108a48000007107450301680035001c0e4a014104444500c02c0300780a00d65158001e591a0f400554080300c10030410001d03400d80300d002d0000030302d10a00308102c48500c441e140029a20340710642c1000004204540c1c01c000d49106030f031501d040c000301c2a4a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 127285773 1250 127284523 127284529
    0x70c24060512010506061b0c0604030b040c08060c0906030403050706060801050603010e011107060b031002030a0f0e0f060106080606120408030915100e07030219030e120f07060b040605090717070c02 87
    0x1141f045c00c0c00d1000e1589903492142c002d1000040c40a400307803995444682e2400c100744000d40035101640c13581210180440c0c08200401c2503071080340c10403601780ca002014418800d10760b000070825030403c0024008400090128040c880007450148008241401c040042608480d10500540026850709412150008009066958158100400084514120780031034203003000ca440e1038200034400410020303402c00d03690021740c0c407840310341e010800d0040500c079550350b80b20a10507208042d4007410042180d0fa200b10461035001d41d01409440c10f00310000504842c0c600d003500d080340d02c0f03c0040b0030031003000e10410040400f103904051155444c02c0c0381c010b81c801e042103130085e03540c0d81600e0400990f900d40a5011030f0780090385840c8205039807002c0140280205849000300b42e550142071100c0031004600002d0702e801a0070103203290b107001030070f594540c000c1400924003070700b05860361000a190780d1140d58591054200da25a0f2103081d541c5050701101140081152092002020815003d03072 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 127287023 1250 127285773 127285777
    0x6060801090c0c0203060c030718031a09030c0304060509030607050306090f1f030515070302030915180601030f1b270605030607020c0a1d070c2406051201050606 71
    0x3601c014000500040003007021074181c0e520070006901032040c1400d2000f018031002c0258442d000c0e5540d42d2809040080c40c2c1d6803001d003e0b21016146421201c8a54840d0b200c51510640000d0800120b9190822480005003903801a61010011410100b0160030505041c0710141d4464a1803500c14610700e88040000c1c0f14010140c100104200c0c150001354451022038080ca10110804c10403060072a41c0e0315095540303085c5040e000040035288804509000d009000f945e0203121500c0140003a0050506083c90801d801090940000a19050700d02603610a1000d503000e1400340000d05e0a2080e142444070084010002100355030610241c20044070050071403141c3d424981e00340e03038160801e502010304045c08841c0c200940c1402001c080c800001e40028103d82030130015601203100c1603855001d594042044003192030b20449100004107194032407400111f00c0b51049070705403000c2255404142c160012001c12441ca240d503400300307104503e0b01102071140c4112020081c00145444000b240d868 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 127288273 1250 127287023 127287029
    0xc05040e0406020409060e0105120d08220602030a0518070305210702030105010e010618150c030207241202031902160b0901091209030c1503060806130c060306060801 73
    0x605030380c000324082042c240c040310001e010401040c0700311625500070b10180c00b401c1c444e007849640e01031062144a1000b048140c2c00d660780340c413074408568505c00703018110b030b4100c52401c162460300740410f800241148041c1d4060a162600010f107442e05615080d14101d0007900c185541e032161108000007100040e90344040c808403200c45103002c9294505007114007948c0e000951650a080010a001c5002d0396018121183ea594028454142110480610050b400750346a0b070115a8002c1101500425100301c1c01c502ca481102d003401d0765040d08500c80441004501c0181c010800100e121581c40303000c2c101125404042149103040c40603d0304418401e00102c01d11030b98011a00040b071080c0c00ca40f8a02c0c0d03d40152445d5040d20b481345e5014001c108140c421580380c180c68040d51075041c85a003075041520360210190382140c1c00c006c1401d007052026030400d0100b50f00c1304008284c0c94010300442c0d0294a00480a130480303070042c50300400c0b01c01c55400c081d080500d80081004502d0b40f00340c9041c11 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 127289523 1250 127288273 127288289
    0x705040e160e030a1109010b04030c03060e0c0315060306070503090c01080601050c070801020301031b0303020607080c0d090302100c1805040e0f24250e040603140a050705040c0504 79
    0x51a0003001c0c140c9194820007282daa00d03000e800c0030b50041c403079421510100c03003108841c00f0100e6a00c030110703500c00e40501d0001410b46406420280001b844e5075203c40c032604c220008540003440300310b00080c03904a081180c038a0390030308002400030a041c100901504078409081842c15898902410f540d6030004507900c0b0b042252107004a005c0e42d001d4000ca0303081a000109481c80f403501c03400209e010390b00c00c0c88200c606801c041460102002c2e4038180300160b03903250f8041c150545a03084111007018000c0c010140c9407034204944107686802c4d2103070441c0180700b50007030074000c01b00b45529001c07205010014024001d000064603030042241d0010b00035244104e9000520010100c240b62621b04a01d1110403240300f007540704002c039840c42004504090039000f4402e042d546003c060320342c14140e90740c1001c4a0031046608811107005030740580d03030410041c0002800a6407505e134140908101c2c010400c071034110302c2e8006c042c0441400110082c1030181c6050180619142000f0824450f9102c0e80e02 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 127290773 1250 127289523 127289551
    0x70209070e0f090a0c08060d08032404050403030606080a0e060105130e01060807181e020f092808060c0a03020a021002180109050f130b22020904050705040e 69
    0x503042d0758014152981c6036029100b408503240902c5800700501c0740405150201d0080c130000b468038504041030b01c20383e90703000a1060071500d0f02001070495511070482d00d201c200c440750403400c4c0c0751140d10030940f0941c060340c0c002c00d04030301d4554041e000c02e401502800440e42030034200d164071040003420f5030440303400740d03003a85820b0783c130b440325000070814441c240510354200070000079800f00005a601c10340c1d40e41001c054003a50a02d0701070b021a0850302c0c21000308002c00b050b40c480314000f070b400740040751303098081e107407406a2000c006503800150201d00250002c64041130f04944080c0101c0401802c8480000c0c505420a080c184550303004050f040d4040603000181000d826100344000c80c4050202501075444200440040c1c5004880090050000740856000101884c3c00381600c01340950240c04100302c809500003c10241206209030380d0007500000041200c03100c81d40310140c0fa80002d000058881915100700700036034501400075000c1140a000500c4102c507881e41058108401710ba06c14 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 127292023 1250 127290773 127290797
    0x4020a0512010e030301090b0a0b07170f070206030a0f0f06050303041707050d030c02090c09090a0f1b030912020f1c09031a070305310602090d0f030807030207020907 73
    0x3a002d0320f0081407450300c502000c40005206242d80e0080d54145d00115840e800c902d0b141c4004040a008030074014040c0ca25542881d000b00358440f0090035580c24410f07840b460091a038021a45640c0f0a9900807802544d46180c44001c1d0b07802e1081c418540c040a0082c026039107071000080c0d90340640d008003400b040c01008058911441040014014400507042c00c200312070b1810054501407031580181c3c040c0c80928002001321032000d040303500c443c0300105061490f444e1041100700824803034a80450460740c610300c40702141c003c003082c1c40030761a5654010480c80c0f060b01d4068480000c1240704815540044030414102c10041060500d1500d44049420f050782e4070b48044401210315807001c0d101c040a0503d001009106810040c8100130544090250740c54040000064601c141541c860144025080403040704090b800c040c5114002d007005030819030b525001551030b6851410440b50410f0300b800da2020560803468140d4080400d04045042c60f84540224001b5003000304081d041284c1040c0d08 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 127293273 1250 127292023 127292059
    0xa0501080c0409140405010c051608030601030f0e0a05010e07120305160804120302251221020a12030507080a09080706110306040b150f03090a0602071a0f04020a05 72
    0x282d0020020f100c000d02c08800c0b0803e9940d025401620300f0b580710350034141c1000f10107004504440740500032000b0380b0000ca4a640328135075550000340c2000d04143e210155030054840702c5c051000307050392082c05410341180d0b9241103404c40385041141c10a941001400304428007029440050b041c0e01820155614881200003001610cd4000000e081c0f0b6400728003c682502120b04032041380c0d1081c1c003100c07082c5c1d0700c4901c6c038803d01c41000d0003009518464481449003007000e01c08060041d00c10b91032040302c4410b4502c038480c011001d44250b00164807050003c006d10848070043c1030f05040c241002c0000d070510700c1c0018003405c0300800070381c02103456094034420860680103c0e603030f4035000f02c2c08000701454040744030480d034000d1f40c44a201c2c80c00e11004c43c00528240c4641c00400100400041c83c0200204500b42e40d50802000c524050040152200100b400b60004080241c07050034a0f450620b90007942c400c05000c003034400d208990842d000c0000507103e4030071200c2661401c540f8210b00305104001d07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 127294523 1250 127293273 127293277
    0x60c030c070f050106060e03061018020702030f10050c0c0712080702060304110a050303160b04140303010909060501090c2007050a0f05030705091006080c0d11030a06140a0501080c 79
    0x10003048407040c07405482c00c0c007030190f000c1000c0d00c00a40c1c80c900c0c4000c3c098205603070b815080d80d50b4044a00c85100800c41021185215100c1e410050b00160808031142c00190420716185003100c0e550308085802044c1c040180321702ca6118114408407400c0c5068441c445588090350b014002d280920080000240035a44081c2c0b903015900404640d030301d14162400c0800c0d5014000d0081c01010000c00c04075040c6004015186152040c440c00100010140c46004840402420568002d01000c0c0c480b6680b103401d2000b5806001c4460005c1484c45d400e00e4250100ca0059000b01590351500980081459000358442203c0103154041c0c804007a0412085080041d113a10880d80101c107480002180072140001c07000301c4004900b5100f03038541c1c81040c4948140101c4100308600d0880c2010700c944c500400d0300f04c2d0809510340c4443e05041454070170004a81c948400000703002e0300402001405c51503030140102900464060b0000f460088012600a24403801200c1c14030184d00700145c41c10180c042 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 127295773 1250 127294523 127294537
    0xf0213031403041a0a0909060b090d060b031510141513051e12031204021201090501110d1b021b041b0c260405060f160b18010608060c030c 61
    0x5400a80d60035a000b03c0ba0264017089419020607141040044c50784294440d00c0f08450005450928094200c0108a0303503005d881402c0350f841d99143d4901056071030400c034945181d440786050392100c3c249140c070b580f030300f01c00f80d0301036101000a01400c201c1602c980c12400c5240d0403151001d6141e03275400384040c2c5056042e4221940261203403408100641000c2111036000805a89640f66030104c0c1b42e04030b80b41c0c4610841c2c2406118850040360050501c03112594100d210480001903527981c075501c00d42074a8420700440a01c0c00013040c002410b405030700c120208504642d81c41603091070f44c000e01a4450550041302c3c035030085001c0d03101410792941d0b0440010795168004084590a03920f00181501d114940e050b03c06107203000489a00700b40c2c00c1c01c50b2120030144006581003500d01000c00681d90300c4a101d1401400d424401e144070035031280346034140385109061025080c03501d40240030409440100511aa0381818010000c08001150141d044065210482d541e07070348085c104002da1003060 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 127297023 1250 127295773 127295789
    0x51905070801090c09081e071203030501051008061503130b0a02070501050606070330151703070305040e061903080301091802030c0f040626010f021303140304 70
    0x4000025030301c00d4400381a81c0440c0010803816108400444000c841c50007000b03060307404800d21460300285401c0140600030420300b12180f03261541a050000180c000c0c0850100381c99400500c25840c10074851148070701071303180c4400e507403410100090001c8008041c1d40400400000481c440b8256030000141403070b003004d00640d003801c003c1d5102000798400c46007070303600354030f850041221454944102c030b10341070301940d607102c40c5034001c85440c821070340080340d2030002c2c45c40c0c078003800b4008491f005000c2e400069500a01c155440d00c00d40002810100103562000d070802c00580e000aa00074041c1c400740e03451031110910695070003000c621850740c1c000c00000c00e0f40c40074000000304425100118182d0700c0d802800d1160603200f00000c404011f140304020b505402c80f02c214015420249618109004001c0021418541d500503c01440d040c4000b4000101e0905011000b0103000340554445c020031044d0861800b0912080c6559011040c00010705100300c3d11002800c2c0c000800c04c3e40c0c0075003481d03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 127298273 1250 127297023 127297031
    0xf0d0f0f020c0616030e060f070e1e040b09011a09030111030c0301030c0e0106050a080603010b1c03140f04150c0213060509070810171501030b070813030504090519 72
    0x60445182d5902c02100c551900c070120000d02c00d5050705c28010341101e4840305c001404a603c41103601030060f90010b1413101009503400d400000e9a0b54604900f811104505126983c1e100050a01c0191000c07405618080d001c950f00404c084258410b110240102c0040c1060325040428000b80c007620030a8121950300313102009000358200c40c2c1008504a81c0b213110800110399a84d105502500401d11914000c2401404001d130058028414107520280003000041d00c0b01442e000200d48440b40054520b5406450000408154000c0d603620300301200c15140508060251a9541280c429401503252204c00d9140902c401801000e07201d0046030300400a45508400c000d805008205500c00c40e4031801c817250124144a000f441064011414200030700b41c042d041021041120b210022010b2142c410310410000880b1100300c400d0203144100010780050400c5003004003402c4000d09654100190030f1600400641c101084400f00c984030440405c0560f40d240301c40c03024195201200300140c5c14 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 127299523 1250 127298273 127298287
    0x5040501030b160c02010507021c0b092508030a0507020a0308030f0f0112050601060f090f031b06050406090509100801020a080402012a080304060608030406020a0501110f0d0f0f02 79
    0x103504014418420480c4243c1e500c042c01d28101d64691200d08040d01203142000818098100400c8500929000c1d20541e01024003d03600c10703402c1d042c2184c0381d04242d006580c00c00304840390100100111840000c29242c150300300741c03d03161a407182c0d411700c20610038001002811911150540d10003103402080d0309482c0d10305044039015440d4116282c8025103034200000c947c8200c03503004545c180c0d4000008023031396070801405680220403024004103000aa90000511514903240754000e903100e5880449032000360381c518010005d19800c5101403110030320040c0035035a071200c01d207401c076801211050130603203d100524a001c80b003508080d08550000501d40303c06600250030358042c0380300380d03505541400301c9514808030f00058010208004c00000c800c50100c0c0007203000d144c005010341c100086181d5141c0c02c40740746611550001d000740c0c0240c0c812005005c401c3c45002c150861a80210b440c02e100031040310114440c2811243c03d0541d05c018100200100d41d10206c00c00c00c0a9108561f90703ca = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 127300773 1250 127299523 127299533
    0x307260604050c101b060c1e0302070c0b0c0a06240b0c0706090522111308070503160b0711190f0b0c0d0c03050d050115080f0f19060504050103 63
    0x6078807a0381805580004c0d100d50704940300e220b2410500c2c442c6003240381c4501103595084060b02180e2148403c021610000710700e1020545800e60f04000c180c0c07001680c50b01d69140c8009045852760103400c0c81d8000b4050f50b0761000c000300346500420380c401000101c001c100701a0145031055142e011056140301e003004643c901110f4000e00341074103035034104c608040c6d40b080c040b1140140d90180a0300074103246050700ca4298040d000e00018084042d011070108000f503481d880b5a08031b0080c0b070034400844c44042100800612204010f040c0560103030181c101460341c0c04007091403e02c101540d880000444000348282c0e01002e50107000020000b06000040f0800031402c1e0201d8052001c2080203001c0004e0301060610840b440c01d10800040d04299508001c143c86280002c082501800701c00c11040740e07800614802c0c10702070f2402076020480751580403402000300400518112410185005021b0f0b241c4240928a0b0b012420341065018003603014056070280c00990302454003e0701740000442000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 127302023 1250 127300773 127300783
    0x7030305010305010b03010509030418090218010e01060c031e0c0b010e0a060816060c0c080709050a0c0503090c1203040801140412050313061107080a020d080105030c030726060405 79
    0x10780150f00034050035040000705800c86c0c030181c442650fa079204200030008100715040303103401039101d4240000c41c00091703004111243c4040240c0100089080014488140f50001250240005191140c58515544d801034645500344030303440ca0140f0440705140105201e0440c40a0566025224901c42d503543c107038598080c0401e8a2400541e42041c901003101e5400003036010700030800e0031070316000500d000c2c4142c1c0d480041043c191505c403845038011a804008221940c01000301c3c18001450f464220528800c40e0b81d00300c00070701000b9042040c4070040a00280c58243e080c011254180e41a0340c0e038004078903510541c1d020045035405c0200308030f01e095550381a14815401046c007804a00b24000c012075262008462a6292503120780f480000310f070142d400107108040205400b0b28004c0709450301070b050b410404040300141d00116880480641c01106a401844154002d26000306a50000303519a12580036260040360060940b01001c1c541b103036601e01d100075000aa036000e0038903082540e101c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 127303273 1250 127302023 127302029
    0x90f030f100c0f0c060e03090d050319030207150506011803050a020a09050106080c0d020706050405011505090106050901030b1807051909052b0503030c070c081b10140703030501 78
    0xc54034080b050085180942101840d00d141903454400518160f5181c2c4000c0000102900ea00d1100340203184c0c4640300e1078004c0c6029800b40008580b2201ea0a072a43d000c5151110030000305801840080d0000f420118041c10119040c580451140e03581c50048410048821040382c6481c0488400024041c000c41d040500c18000da4032482921380329900381007278503001c0c8105030004035a80009818041900040d044120142d50094541500e0f6120f041c140c1c0c00c00d07178007910130ba551101810300c0ca40c1030410000c014681500c0d01040c941c90240082e050b80141c088a905040c0c48003501107150340c8044900d90f92280e501c5640c0001e040490004006401540448041600c26400006803038058070a100484400501400c1c10107042e0591102d200c032055040e00e088d00307203c0e440c41d00140052014503c036480b02c040c0c240c4c84103007a0034103070640e0500e80c0c04445035400180f64000d16005200d056070406105683d0400781113000f49046a0103840955010320b1440003180d41c6040640c103400103812 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 127304523 1250 127303273 127303303
    0x30a09050c0402160b04050a0c03110102060a090c09020d0e031206090906040f0201050d0e1c020d0c0506010e090f0303010806070e1c240213060801060c0b010506090f030f 75
    0x75500050030721040b8410fa500000704404070014020018600000e4264054810000da682c02171069035031501070346c21500221a880383c0090b4201c06540d04012141d40300354a41c0042c80142e246440700302d01d0106500544d40d2840d00041d020540070039a800041c140a14032080340e546808151070121602c4058500e80e115000b08408036262400014030140510b41102200c0c148030101d600548032a8800911240d640e62141c03245c1449031010700018402e030084031182000d0b50b000b51002070400c0000c2180c5010f0000b2a11090003250000076100d0558440514804003a1152501549000303484a031824542c07000000101c0c080c80d010820b140250119106c181c03002103a40204005d91036500d481c0303803a00e1a0f0850403004682d000d0302c844070541034054008045c00741c0d0582c41050f81e010691414a1011040c003c01c8507581c000701090041040785444510501c09940300402840103100d01441001c010509004540d611907084d03820307480c010103c0d84200030b4003240700e0f00d9000301703910188 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 127305773 1250 127304523 127304533
    0x20306071103090405071e0e1f140a09051210050a0614100905030109050703120f0f030e070504051807210f050a080307120b150403030320030a0905 65
    0x16200e4011051203280034209805141002120410300c001400000c0205040207180840d00d0f1600301c00a003c170440402590324024012005000c0c0f0a00c1c80382d0208000307101c41c0030f40112103010b40c000311051050384031034a01d546d285c4903408212620340c01904103550107060081c84c4070070030340300040e01c290640c05110248925629005100b040315034512401d840f11994442c0c1100701c3c6410480440d14600310b0404024540d140d00109084940030b4030f0441e19680034110500c103201c0142c0103070b0b2950314503140460f244906084000c0c29a040b00344032100781a1654010410307004c0038042d020140001400401282c03818041244a5588080102a250181d424003142024000b1103800c1c501c1e85a1941c0c0448481d039507500b05907034aaa00d010b8546015414010000070710703120081d4003480050f17441205511142640104036980600323041e128020035110384070200700c2d00d000d581c00c07640c06040c0001c01c10220ba044410030f2424044d0034440d200000b04010005e90350390310045145001c4c4046603 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 127307023 1250 127305773 127305781
    0x50901020703080718030c1d06030307030e190b120718060f050c010f05161101090c0302040f1404080409060e1b030907080d08060907050304021806040605060c030304020306 76
    0x508030300c541c000140c0003035400000907503000c0c00303085800304880c8080c0865402540e20381302c10142031001e801c64920000c082c032001c401464507124490300306030b040740914505030f119900038200c03c0900040b9401f4282030300020a159a0704640d40d001050101040340c0d5803040c51290013940c1c181280c1001c040390900c9100201c40100c0d5a680d800d0300c1d4071340c031a110b403076000c0317041078400d90007440c08c07080351359290740548640c00c00f54000c1c00d0069000140d50030083d004401d01400b200c0203880300d04002da150141100101c0e2032694103d041707a8050b600010400181c60802c80604011140a542103280c00c0510080112650050044640c6031504100e1552255511039481e003003620828188044102002002c0075818011900703c80100c040303c06440c0c0c3c0c2c9504c1400d00b6075080c050000329000104118203814242c05842e440220752900500e949484c1e40000e01f0300e098030b00389009502c60071001417602d8030703164007400290178000d041540300e02000380426920317842120300728000d0081001213 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 127308273 1250 127307023 127307041
    0x14030906041202210c030408070308090a150801150306050d1b08030a050f090d050a0605090c0d03020a060b041503080d0b011b060507030902040203090618060705090d020609060408030a020105 84
    0x1410598644e1020203203010304030468625044084064440e020820002a0407101080003400031807280c980c1545075001034042043c0c0c642c8981c01000000300c100d40c120b0034694008410340c150380e4100726214920030041c500320010320740c50f04069040310f402c600b0082440503190890151402c2560307907000f45034a602c1c120b5228011b50310594007088051103461800d01c0044080c0c01004d5011b80464002e030700395210f061424045410682c1e007075584da4103000440302d06112440c0104030903101c4c04611042c41e980290343e440307094405455030703546013403203a40340c1e4554225200c80c02c1c900340085206074690a0064884d0b03c42c229503c003c925002c0e40410079400340d003581c0f500f10102d026039400203102d030f01d070b103009468010180002c040d82c0e940048010394503480a5401400310a008101c0ca152041084803a52405000058070394002400c00c000c05910800322046a441070300e80103050040362001c035103240a1100d904e940024045408120f406001000d0f1120010581c0280035075113441c854 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 127309523 1250 127308273 127308283
    0x50d0c050c0d080414011404200609041d2a0a0e0f0709050d0c0306050609220213020705010917030907031101020a02150414060301050f010f14030906041202 69
    0x2a03019140c21051190400d54000c0101680c0039019051781c00d10040d00c83d4031942107610134106c00c4280c0b1504030500051210b0382e5240740c00c0928044c010b0000c401d00f10009000c3d030003039580d00c52007030303454104011025100214903003464800c01701700c0c4d2640407100d801c1c03108855404c10151500d13003c420071401d14a0f10305c2200c0102d411004078004240c5440180d030328158402051074080c0030231050f00007043c0e100ca05040308814040c410035442e8074110f280c20f00644001400041c401c84903503081c0310b00c125207134800074002040005100b004800501c04204494030b000ba040700c92520200c0c1c01c030240712041d0401e8942d00d1003200c840b4001c00c2100000d50540c0002d5580203800da00c001c40900000d02092036521803050140115902e550540d8001480711118006070210080086000c028402c4107a51541e0003450898206046604040204002007451005181000228154141882d00813440e011507020004030781c503960329007008803035500e00055808644120354407405034600d52010070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 127310773 1250 127309523 127309537
    0x60c052205060d0b4203070e01110c04051305010e1506090604180303150501020a1106031b04090203041208041a19020406030515010c03050a0c0606090606050d0c05 72
    0xb002d0403c42d074004024010881165480d8211051680910701c01c10b071044032000744d01d94458100c1d0381c0d2003840c59401c00d0b5003588200080e012000d0050010b060b4201e805000481c4081c0b810305911642401d21600d45186611141e8006181c1814880e072406500744660206008000900401d00384507509035503030400c0503840c80102038141c082070f81450050442600008002e102182400628105038034920581c24210003180c2e450440c1010b050650382450001e040c2400a4020035040b0348413000c03071400d00040c6070b2042d00d0000c0080d0b2120303082d0040c1c01e4802562207005d47c43d1616032185100951003039900382c8800308030791420b404652140015900c01d541c4110110500e50341c410035002d55a40207040907503901c03000708202184180e02d1001d030008100030f950201d0300d400c21109044c06e04070020700b403c2c104000c1c0e440c00f501180c0c001086440c0a14a8901480800d1890500000401980d08400c8107036060502c0058000d5024014010303040c0c40380d07410045400c0900050b911841486 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 127312023 1250 127310773 127310779
    0x1415060a02150a020f190908010b06041a04090203041b09050601050708090a0e09010906110a050a1809060609030201021515040e1207060606080903041805070c060c052205 75
    0xc1000084842d8516507040030303105101605050b80410040159000040381c404c14441064207208000e5002d80c45800078250517000300001002c04010512512a6004500b02c070b403518400c1001d260030b00d90490300184800c142c11500d030b0a280c27801c14001c0922441d5230f1030b04040d1140106a4024611480703004c1e00058444c1407600e50305a4801e03919821140c520f5500c840c10380c9000030307150100304134603200302e2520000150300705440ca0510126401600c0e43d269130342c0c050194120303854128044446842140c14455840410103040881408280d00b10198641c00d0003000246950081c60800c01c0d603100b40c0944642100c1e031310411201031b00442d0501142e00c80d0010715202400c195000d11400240383d402d40d03030a0614043c2440071517001f02030481382c00b9902e00080094690002c540381e0008801c00c0554505464520910506402c040c0e000211695800c0400d10040c09801641c000690001040c05a40b000d00310280c41da802000e10740c118005550076843d83d60700c4181409003500c50003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 127313273 1250 127312023 127312033
    0x20a0803040503120c030714010e0a140d0207030b06010c140708010212070203070c030210050403021e040605090f0121020904120e01090501140d0e03070f11040207020306180106091415060a02 84
    0x40d440381940728040801d603404555852b003809601d000240301016403207000318011405020400c0281c2d1400207100e80c8003085400c010300600004001604058101d0b01c2441e2a803a00d030101e0400342da4000203911900303020b100b07400001a1162040d0094940782d803280301c2012165a5984061f0f031207116100000700003140d03141090005180800d900b100e4640146003150515460740d010840e00e10490695508840686081c550540740c5801444054002992201b1540c245201c2081c0c07101c1060040c3c002811080322070b0300c207160718921604282e42c1c00a0503480181000c0c24000603e0705921030f0100000c00301c81c1c4030341e11940218100720032543c043e52450000070f20280c03100c07800e8020303131161f5030080d4856a0300c5205035002c0024000c41c60180303075009e48080e081d142c14080c10070b0168206001d6030061200d400540e0f0086000e0341d015007040d00d0300004100c411001c1c1d0041c401b079080410010324111080d48060048000c0701d00c40c045c0d102c50003545031094420030445001c0c400e46c000c0142c0c42 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 127314523 1250 127313273 127313287
    0x80f120402090f01290f1b10020403020604030b0c190302090111120d0203090f070f090c0801030b0c030a0b040e0c0f0307030b0c0c071802030f0a060602061303020a020a0803040503120c03 82
    0x105c080103a483d000304542103080103481c0f40b00c1012507100c00c1855811f50320b600c3c031242030b04d0070900c4000c0907000300342d00440c40c1528503808902c00740150311015000c0c00303028002616440141080307070f07141400a00c48084548402002030000d401070311460b40014106a2100c21034240018a0084600801009400e184040c40d120b0060350008082e14882c1c0200218200005000c0080700701400c10700910034a02801d000d420b104a840e00d06007141000581d100400210722900c1c0c64030f401032100e0b03007803503901e0f03072511400405071403100007140d0030601d04050700d0221000403441d019802e03000c070754004c00400b90740c080503550f00c460b00020b0195409200030074544007221000344603810f1404143c0b611103030389140d5070381910103507440310401d642c001080001616010490685c890000c4800f08452402c1075030007035031800018070001d041d500c0707841000b0a143c02003006480d81980240242030741c503140d50300a41c0f00d4116200d2a4000e101c0d099035400d03440e80d003405a99103545100015424000303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 127315773 1250 127314523 127314569
    0xb0a110f070c1502010501210c1206181b060509030c19170106090501081903050f070f20062107050c15090708010b0a0e04080f120402090f01 62
    0x3001450845401d1071020780000c1403d0328a1804214100940002417151f14040c00c52195154084420308810901251030300020803000041c003e40750840c440410b03010300f900c1c1c0b1a0043ca1080e0040754003203010101c0c10200502c0c0204003004582d050b41c0403411aa90b03c0701511180a950b00e0039a054005076a0002d8600302000340c207440905142c10340d41a290360344401105103450030804401030351030b09020b004080301405028014040074000340700a00c4580307c00850110049802000c0160000d50704410001000c1942c510030b4004525100c0b280651403c1c010483c140340381d810104e88409d104d989140340c1401a600c6540101d1411030410060036581138208000400710414088180125143c45004011840c444d00c0c580d090762400e4100102424900511507000c0c0500b60705007400001a0386138001c41f001154001031107940581c07070f54504210280210308400785042c0c1c0114070080071814030300070a80514020340e22005951141c01c036030100711009000e2664034403504008800c46007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 127317023 1250 127315773 127315777
    0xf021c0206180103020403170301030c0506030c1903020405030d050c10060b0406051e03070e13050705120a02070503030c071536050106081608010c020c06070501060e040f0b0a110f 79
    0x1510500d130042c0741507107d9940b00140c01c00b0b2011401e2001c00400180100186440c940028100072602c060551505600818151050300078040d1000409403040c00c5250081c0c05503406410000c094401050070310100a00ca0b070007200c0700d00400e2003886e1910b003c01d8024820710003a1002000404d160a04080b01520351307074089641c0c25414a0400e0041d80002d40711300c003450144540743c0c1ca1502260b0048200296201003102a0700d5040c039001c2401101c1e40c10200310780040340301803581c0c1c00644d554500b40000380501c64010b040341c000001041200400070004000e1248106810300441c1c181d0000c41040f1400c1200104c1140319424410005041c800161741440c801c00d08064080d012a50728182501d441d948602d5843c0d20402c1e41c000c80200c1c80c8045400341500c100200702d4038101c908000e54500d21071040303500030740340080d001d4240002074010700d000d001c02c49507981c4c050a01e840c0c0100c180b0b110410940f5a85604000301c0c83c1c00c807042c0600c140ca4a6004100d0381409010400c4810756 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 127318273 1250 127317023 127317067
    0xf02090a1a091305010302041a09070f0c0206070302010608070b070f1709030106090f0b04140408070305130b0711030313031b092310060212030712090f021c0206 71
    0x2201050160030940e550f00340b0b2208001c0e98420700410b080d451481408107072000c103000d0311511400d0100258440e101e030f11030349a1096042c9001e03444c4d05000602a00c4016a110000c1d42007400020483d05150701500014201c40c0d012046402e03007591000d40a069005100c0001c1c2030701e107061407500100303001c4c6410084a44d0080e04051a21704804000790855025074001002d507511290300c5d8034002018860444036800640c1d050242c5004807850490781400144014564080401c02009041c461800e6810ba1101e0003981248c5a4039200c0d1890290001d00044485d001c00c0c4100002c1814040252540e2440b1104510f4a1034211ba46519100356903c844900982e100c082c005030001460081c00c4120380a45900e0101017074980701c0101701c82001300100c1c50300013403010400a60745e00003100d10b5071001c116080d94482d11600300450707a40b0001f4210403600380c00e04a5a0003804901d036041c429940c030888049030108061038030001c140c2041140a5448002808030501000c417645c1c44100d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 127319523 1250 127318273 127318319
    0x100612020901050c010f05040c0501030b0901050d061401060903051615032d0203040c0b0708040902030703151d010e0601050a050f070203160807081203040f0501060305031b010f02090a 81
    0x1c000031902c104e401c4a8006210603106900c03441840144620340c0e0041000e04000e21f07081c44441c01304008180003c406100312030050b0004030503101403140c10390106080c1000b1a40c14091540d40e503400034518110b0b40401d0305e0303d004840d0380c1c45112214642200442d01e410034100a111920302c0b0a80c004d100b0b40d03806c04000c1510324409a0700640d031029a00500640140040c0c80f4240360902400148280c1c1140710002020490030000c18046401e0b80c007150240d40300981e80382d0356420202c01400d50303c441c40052001e16a8081000e028554245082025004890703045a07607916010080800c180da030035000c58010440000010712400040012184145259103442160342c042843e0494442c2d40740005a4500d8041c00051014032000e001400702000400c000d07251442c0d01c038454400508001e145481752001801001803e4103c03100464101c01a02d1700d4014495400407a001d0080d0580015460248907103400c201c2e80c8207650281d0400b61001c400e80d070401d900400b290f1103003206005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 127320773 1250 127319523 127319527
    0x60e0a03080c031b010c09030807060b030a0602030a0c030902011b14030c0f10050405070b0306040b1f11010504050c0904150501060504031e02090a0c0c0f050304080610061202090105 80
    0x8103203001c0081c182402e4920007550b460140810042c0001118200c104859040445112006a00650b50b00c01c0c1c0b50800c6019980e00441d15042000380840c80900c2c3d0140640c9100e2018010254042e6210300f1f11117800b407012081059085013124542c1400a000c03400c1c044000c241c00f1301c10780000c4241442000300b445000c50300300c5142d186800c5018107803242c1d03010070031003c0301100500c584007070700c3c1428001740070b982040e5441e15103842d00c3e8000c4984604c0b0100004406039101c6d084150704c1d800280060580745040c031001c00c1c0d400e03d05d015a0002c0707950526103e00384101407160905c80ca410402a03e0440a817804010036003e015006603104400014402400f00075403145034000d00170380d00c80c541e4403861840c210702c1100308220b400c01465680803000000d40c40d031650860307211503c441d0015103880b1120b020789807103000c102d0181009d80d868010350708100000005205650159013140d85650f2020381d0044d095950340282d00c0000c6085910601030f000b15000750954034014100a8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 127322023 1250 127320773 127320779
    0x40203100f02160b010303140f0405040b0a0e07080709050d152a0503010504150608041101030f02040b070605010f0803120717040302100c090503030a05030a1404120e030a020901060e0a 81
    0x352250003c0039913418200d00e004008041d0450150101d01e80072801850070011880b032013480340e024a101c2c1c0c0e8000e68548100ca0300b01e90f40d11503000c0182c18510941500d600303180000601503101150403a010480c8040701050616104122580456225a1403505a0034115803a4041e007050030384004008055243c41000382c14a120b500100b55542d44c51540300e40c500006c120035034142400200101d6041c040500040e0382c4004400c0d402034100031032009074954000120028050301e008054224404130b8041070f022401002002c0c500d0141205103c01d0741c807000d040240300d085103e8204207030f10030810703090703840303280080703168480f44504011a0a0380010710250310b080c0112405c5005070005550003803c42c0e968400d81e0500011071408101050604021a580c1c3c4510804801400300100c0050210a01e90b08801d40c440c000400800d810709061810500d81c04441400c000801e0140e00c91f10028100050300c4488260000c02907207840e4039141e41038400755003076203250f44c0100310b5a03004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 127323273 1250 127322023 127322047
    0x110301050103031716080c0715060b04050f15041205011506050705160b09010c0c08030a02010c0f0e0f060c0c150406030606020601050a170f24010e040203100f02 71
    0x240303000354040d84600e5204425100a0711398180020f20300d020301c00302c210443c0c0a4903480080d16030b1041d183c40c080eaa6030400c60500344e6956040c011041c1c005820302c040801c43d98018400740040302d400380e80400448003650204941045440c52014002c5c1d030078802046440c2c24208075031845806540001040582d0b2001601008880e8002c00c01090b0000307a08410401c0030445042c945104800b9119090f05080c8488a28400d1030075042c10043e80106041c14045001c560400811402d8116030b0f441d548032001034040c107a4a294807011078a1b8800d003454241c081c03042c150703801800409554a00745214100401c07a040005045024030803510540c01a850310380040482407a6034500e01e44035860004000c05465194110000310341190340104419210302e080300d426901105181c3e40d682c8018035403107160801c4030034408403d01c0f4000b00072124108040d000c02c001d680d0903400400c40d81c0c81c0c0510000d110410740c0c009400d40d001c200d1b42c3c5010402c039401004400c1440b1405440c01c608841a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 127324523 1250 127323273 127323281
    0x1305090d030b130c18090902030c060904022104020306091204050d030e060711041815050921030108060a0c05070b06031603050f01051f03060903090506030705090a0602031c09110301 80
    0x385000c036100402105d030483c0c9451154009003080e2000b400120724540c0400d0321004a0340e0320a016140201b2004445e6845070152441c0c214210310382c0c1c1519034000f0060301614005d039001d130b000e409540c010401c03e4402180c0a80003100214849203014500030921200400d003002c194100244101c12a2043c1c1c3d4000c000c00a440c025001011040c4205d801c00c4111107105e048014559000c0350b408000803080040800049003a1030001342540d59504440c1c14009100522000107a0b0000d107250009840c2018506a4020808890703055413100c200c10200c40c3c07074003480d0b40400c200b4813410000600400040d98801005000e41d00c0f103421508034000c07004201d41080f01c403500110004260709109100d0300f544040d90308a100e00c40c505914035072804401307e00001c0c0c60070380c8402c03411041c10b0040040c5c40041c035018050315941c1c904000d004003c0e030051171920303210b01014580091014400416142407403040c01145c44003079806c40e101d00c001c0c100d0f602c1c1251070503001000c07a1789960f001c0c45 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 127325773 1250 127324523 127324541
    0x2a0309030b09061e0a230402040b10020c1909140a060f14090a0b0901060c1103030a090e090a020306071106090a08040b090a05040e0d091d01090903022a1305090d030b13 74
    0x20105031b9090920412094680702061180144e118005610015600113032114030140c05540c2e400c0041000611310210a1700d5030846116142403002c103900409450300c59a1240801ea0410004207488480030380744030000744148001c1100a030b40400b0030303140100d003242d0401c404c4400001d899038040003103034281000340c3c4a00040f4940050103400e000341c1d24035206810130110099071078050101000350410b281806580400004600001c0010804001d18043e0319001403c0324010710b0280d0004000164061411100d4005c1c240800c4c0c2690300041c990b480c042c1e0101d14039080500341529498140c000407007044d4400c0e0115400120b0303071658828000954480da0142c04100390094002e08440f81550080503025101c00b80085a41c0040d1103040c19180310303041c0403c4a0038141000ca1a02900352044400f0441000c0101c55006c2c090b1281c16170540c043e60810920304502002c2001c64004640c8124603400101459100e00d200f41d100030841360f401058441c905403200314a10446030121 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 127327023 1250 127325773 127325831
    0x1204050601081209100c03050412110f09040b060603060f0d120f0206090a06020d061809030f0c020f090c0c150105150702030d2a0309030b09061e0a 65
    0x120041c044184184040d100c0c00c0410014039240002e54404115460420380c0b1205c108013112094100f0036100700d00b200e004142c01d107144003041c001820400b1200e005108401d211b49000c0400807000d04219240500c600d0700109203614035a01c15003031200d1079100600d40d540c800000240d0745619170b03806049404150103140c4028041c42d100b80b002d4000010380003c801594040020011400d0300000c2040b450365010b0400b42e101c00c2c401c2c441c4409030246400c281100d455001c00e106800100b680402c214601a680b09041201e800d032055450000d4544c01075042514201141401d0030040c41c115049420341c031083e480c20b41e00004040c1040710b94180e622012550000420451402540c104400b00300d0501441c070f0588141d000940d14121005c8450a00c5086140c0084182c0746156048100d82e0244540d03182d0b09507483e00502c48925400304442c2d409008020903254007002a1651141d001304108036240304523042d12101c507800c0201011002e80c0c80e054901001c0d1840c0d5500308052600c0c2e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 127328273 1250 127327023 127327033
    0x4050f0d020a02030c030105010308041217071b09200c0a05031603090f051305191104090510080a0f1707060e19050c060a0c05010c0e15120c0f120405 66
    0x203204040c108103002110610a0723040100510115030040b0440d4112510301d0320b842d0004507a4038080320a50890003034880800c001180d03441c284050391000c20b102c500c999580010f91515540b1510071030700c40b41151800e171280c1e00c00b14104500014000d1903640c0c01e91085941c0d42e16a961500c0c615030140c0000e0303c002140032a00c0081582195500c4060021b06c90300000d480c1c1070002007003400e8440709034210b009407684046000050740395140a000040d8076000d0011080203180f130381d01507001e8030581c0b1480d4508000911849003203c1c0007001d032100c600c00b9008101302521040203a080c3c002040d18200e4450100c0e04201c40300710f004148440c8035900c04503032001b6003450302d428801002480d082c0803003d500c061000640116481c5c4800200700c0b042c6407542c810540c222035480c01d414004090751728281e42e010740c2d140c00c0b41070342c500c3d241c0c100e5600c100700d0000b844031038650085001c100c00c9500c41c0c80102c1c0d2042c1001001e00300a404c00d04181d07080c0440164410601101600d09070358a80107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 127329523 1250 127328273 127328293
    0x21c060e0d05030705180d0b0103031e020a02030a120207240f08060a030308150d0605270d030209040f050f09011a010c020d030323150103090b070804050f0d02 70
    0x10074401c190304248141030203819460b02c10f60107042c1d03108400c08214803810b0030348081c0040d9078003d40d5403282da8002c10400800d6840b403078050140001403480208082114940166032840069200403065018014004a000781e40e503102e01240e0381d02110003540101c1c00003064136051614a0f9551030b0440700e000b400005404400f6040c0380c1244c5030320080140c4542005820f85400074800100d990518014a041d91011031001c0300c3c11141411540c403031100c4c20030b201030019a07008280103941c03000c559031905904046036a415943c2ca080f00025811103060010001d01990144c2000c00d005040881d0100c01c41c01031300120380b41114003050910000c000d01401040c244961f6250b0400d40160200c08100d02c400030300080d100c1480207110360804114841018404c1d001004508102102c0d0320220100c6010f0810380b10040301d1012882103258044100c0b580701c1d01807100782c0b68000e40b5880041c1c40fa0f0314200c0b080e2900500a60b40c5c1e206144a16a4a0100b00f101c107081d46600d81c080c01541c03407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 127330773 1250 127329523 127329551
    0x908060c130509130b06060f0708071703040201020601090e01020f04150e010e181302190e070203040b03060d030215130303140c03060108040606080619150b0306010507021c06 77
    0x1090781200380543d03191000c02c011555240f56010304140c10413030802e003a984040002c0ca03180714200e114807000300081801c6080000f604084e100b10b80c810094940c1c460f100784507400250204440190050340120010401c5090750fa00084c3c0c2c0b503401c00d0016262002034148041c1a510560101101845240c3c2c1c82c140c842c2c3c400041d6207039100910741034800d4085c02000400f40021450000a40b48144000c2070704110560045440158080d04817450300d406c2a401e00d0f08510584a01c0a210034100005080d440c808400c840550b010240e510f41180c41d040103000320402d4420088056201342c601c2004034514002402d442100c0107002201d442d0001e15006042d684000d20501043c5400000d0040103614241520f50101e0b080ca410b1405607220304294001c1d001c298040c94140c00b0710700502c07819900f0705c08011044285807805000015030b030304540000c008113220703020a003501030010480f00e40c0705c2d800800806000034103502d2409800b0341c000042015056023140c0280c0e4a59404003040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 127332023 1250 127330773 127330807
    0x903050a0b0a050708040c090c09120809090a0c080f0621010501090f0603020a0924060201060617060108040813030b090c04060e01030804030209040f06091506171203070908060c 78
    0x403456142c8104642807d9540d45008203181c0036090841d40c031030207001c80ca648134070403407001402c45c81041003000c1e6440c00d204110382d1200b11240e003d50180d20000301080458080d207808100c4a503203003040c95071030401352501080003600c04c984c41003900c14810070003070b10b0b01c0d80b100b04110400000079080d4909010441118a07040180384081c0c24194100050394502c40401c0480d000e034400400d041b5108601c1501c5000312600c03880c082e4881c0302011640981c154000d405030707886522001082d0707080611601000404943e91b90008131403d0000d400245044003420382c101810002c11907060b16a560b03144001e030125004640c0d544030050422803072405004440003062402c807240d9103941140c403103aa8a11803404064040d01548011608000702c0f4220002242d8021030b040040c0c004a00e01085c000e440f6a403518605070400e030000c40d401c04001c40d040a900701d0000245600c0c41180303c00411364000804940c00e10007000000100f404080c44824414121030310104d9840214058045c102 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 127333273 1250 127332023 127332031
    0x60406080a080d0203070302070f0309050306220f02040e070806090c010c03050d0203060118090915051e1503010e03120c03060907031d030a111b010c02060a0903050a0b0a05 76
    0x1507441400c410011605410403920804810140541c0da60340b0580168042d2041800050000040c0c3c02900181644905d421080d0b40e412400c0e20325507162800210000010710520b12000c00c07102c2c508100080c0174151803c0024809040468a080100641c900340072072584007400c190429410025009002e204942501e0030034280088801c010ba200280b040c002e00091000d80c40e80000411900d81c090803951400382950b5140e10b407601c0d150500400900505441100c420012206441444805000e0244644410030003103041801110304c00f02805805001c60000e08540ea0020302245c03000e0007400c01c01244140255074403821100c018810b12001000301034558028810300c48a0f135100c850040d0094803600c0d001c9005440b40e0f99414042e107452950794cc443c80009281400710703412541c06010007184d032040c3c0c1d045210704441000c51112141569001560b2112000014a4010b01a10b1542d103146001c6460545a540e150b280060f40c100a558503800901041301c0d85c84180195680 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 127334523 1250 127333273 127333289
    0x30405130c02030a1d0a03060209040509152a070606051003020a080c0d1410050a0e0118021b030412020f0d030f050c0c13060611060c040509100308070506060406 71
    0x1880300258000c1d03c9000c1c0f90310762410043c804003140516000803500626400006101d105503030b0356458124004c0d4041d801090245081c000040c03440c2c000410040100c62400c140500d0365941c04007a8208007842c5c03070104040700300390114404900612805004d0f514480c03e00050117038100410020f00c41c000440c1041054010050340c41040e500c11102500941000f8480c3c2d1504010403540700501102c0f44d4540d141c4101d00d0400040c2250382c0c00c6101101c0c401da030600000b94451200740700d449424040c200c3d190490a030003803d061550b42c02058a01040303000408110640103540e402d544c00395001c07400da00903a010040075031410301c0901c01124008c59010300380f4092550081c00f808101c01c2e020041c0034000c1229660311714207000a03c94114010040c40442e0780520a50004101d58010b05001a003038030841d8580200c006031320f50081401c000386a041528150401c175920000415040c01c1407185040040000c0091002c1d0200a12420182000b840d00c0800d03c012034201c1d51000320 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 127335773 1250 127334523 127334531
    0x2010510030f0f080f0a0c2603130201020c091009050a020703020a0b060604120506010801050a0624141602030c01030b01200c030712060506090105010e040903140c03040513 76
    0x10b2491801c03840450740c40501802c188460f0705141032180280e040409075a45d0003e14040e0a541c800b02c41c495240c4a4016082c48070182c001400702c1e000b00040c1001842c02c100003084400c940c100064002c188140704691100c0d00e640c0c0070480204045e03442000d2080e28200a200f04000c170701841d41c1c000301e040d20443c100000741d03c0003940c1e10700551014001807080d4002ca01d0a807912011200a001280401e4603030400514100d69a0b510912030768089510b400003154039000c640c0540310813504c1c200441c8120785401125002d0161100441c2c00500000c0091414501c0c0e5080107002c1d141424043e07914122090b005060501d5285400c0278109031601030110103581c1c110440034680302085003141128124214802e14040024104603890701c1018000036503d900c02c8040f0061034130541c0240519240d0f2803c1c006800d0b0700b805900d001c5100550030b078401d810682c1c40041901e0107403a10045c410f007a01000c21555100c581d81d100f00d40c00000d400c1c846410a04088507640c0c2e03000740100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 127337023 1250 127335773 127335779
    0x3051608040605101a0c150f07050a020715091508010501020601140301140406150e070f05071a1503010c02071406030c0409020c07050f09090a03050322110102010510 73
    0xc1000c8002000106110790f15400b2030002036204440c0c50140401c60580341d00c1011004030080f150f00300106100f4203108929400003007034a40c900341e5010f96151207020b022030312000d9041d1507903041485248218400c540380010b42c614041c881501c1c1680d42e403030712509a81844040031655948445c4401440080e400400450b40d00083c107604462056504000c50440030001901515410603a07500d4011501d0911080c01407540c00010440510702082d80d40c0c656641c0c50307841c8040120398420100b150784041c5d50441d80610002d00490b4417600e21410b045d0804615001e40764800c0e01d424944424082101505050921903120201c42500007801240d140600540c025040c0c0310070700e80140c1c0040049006940418161405884100030954540007280701d1160f6070308042c404d007441040c16400010701401c2c040c51650091207400042c20001d84543c4040c0c0710b035880500040e0440c450b409001211100d44142c00304ea00d0b1183c03540504840b5001c00086c00d4407005026402c04d00ca10711010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 127338129 1106 127337023 127337027
    0xb03100c080f010308040608101203020c0a060302040e0103080a1110020705070509090309010305042316050406080a0b060402090a09050402120102130603110f0c0706030516 76
    0x2030040303544144102c408140284006043c0ca4020002404001d00c05c190b0644c1c81070004c11289402d03a03642081f00c1c0502c01d42d480c160b005801240c449141c0c1e107000c0d1080d800070119031400f0740c241030414080600d2150b0610000b0002900011035000c040d0140d032241c09036480c01000da58094501c404000007940c0b0480040b0361b24090b45902003002c0c03030541070240c00ba40c2880021414007120030015001014003810070340d40d8112000303c1e100700106001305114500e142d90081d20030048001040d140541c046e420440c4110b041c06030900c10403400060200300d15803c100492000d071122804a0000e104564040d500085684000302d005425500214041ca20a0703e0300e1014031485d5041e1802c074018000030814811000e601000004e21a0308100c104000041c1d48601d003e140c0199842c0f5540100d0703d070286074009244c1000001d400d8460940d008410b608008058480c0b6800 = true := by decide +kernel

theorem cover : BRFrame.Cov 127158273 127338129 := by
  have h0 := BRFrame.cov_init 127158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 127158273 ≤ n) (h2 : n < 127338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
