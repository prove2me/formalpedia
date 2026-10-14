-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2396
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:35:51.077799+00:00
-- url     : https://prove2.me/submissions/0715c66c-9159-4411-ac4e-5423f61e647f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 430755395 ≤ n < 430935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 430756645 1250 430755395 430755419
    0x30907170c090709030c0504050a110c16050312040e06030c03030c03030103060b0402030c03040f0302010f020d0e070603021905090a090203010612051b0d020f04030c08060a0f020307080604020c0c0901 88
    0x144081c800d00c2c6078400710380b1041c05440c2c1c580607260000398000002e0708110a210103000060a10303074806548007000324035040f0041c058410822004050306000c82049440244003540e034204922030717000a5801126040020211000c9582d6580b800355241c1d15035000900304010403e046400d80400a41c5120313a1901000850503644549010019130b541081031000f01c1c001241c1c0c2c888121300400105012511481c6000c0882c0c2c803d200109a80c040c07064184143d0300802c0254408940f501c01c030744c1c42604c0c14410000508030350300c0d04500349503181c0a11030540c14108051403d00c4000150b12901c3d03180c0030a1a005424900c0080d580c030b50b900c00300105481e00d0b40c100c8001940c5080003140c01d180702da140d540404070002c0340b81400c0600407810b16009600411080032100010840003000900320750100c401081c591340a884140303000c01c0340702c2c251820384403103600317480c410810880050340124405801201c2aa0016114000d52441130301c0c2c05800c0403100d50140e10103000080e400100c0c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 430757895 1250 430756645 430756663
    0x30917160b1302011d040b1504030303050a0218090c0f07030f030510030b01090f0f05070302090102060906071706010c0c1517090330010905040b0f1b03090717 70
    0x880c0c0240749548070703aa10120400c0944000740081d0110a08110f11442e080c3d000d0040e65004000203840c0c240d0300005100c40800070000d40c251040030800f04149609171040550011141c0300651901021040c41141d130307502c1c45c3c500b40c850f400000101c7c10840000d42514014031211000a603107a1142c14045d016100c24540c0400007420000010200300c01308048200312948a480d415144c0d003005510340183c64241c004a140031740d141e004540107080f602401c0c0c040c00043d10010383d103110020009092803001081041140c0c4084144000ba070344c0440e1140800d849041e204616480d1600103d5004510441c060080107810301e000c01d030b421b030705901c041c1034800d80e403105a10b007070210701002901b8100b00d441c0c4103da0002e005001101d84004545421700a91030a4444001c024410071500890b00b030b004102882d07070b604100f0042040c0403842c00e07009103441c941e00005c0d28000310840121903200c44138005984000c4082518100200503c030090f18004043c1ca03c504100c40180f40d1b9001c102d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 430759145 1250 430757895 430757903
    0x30204060b07150e0120090307170a0b060607081318060e011203050702030610030303050105181311040c0e0301050a140106030c09051e0306010501020c1003091716 72
    0x1100040c0716006101220b44443d4400d101c000c1d90802c0701c0641e8020082d204198034a07540f106820181d80f040e400105410100306c001158030303a0f020000381841c264242d0869100800000103040141c1800250700c800315074810355840803541e0791b00100c0e41e18017600c440241165000302e0065544004c0c0d007201c1c42502d80680384007281c01500300d80503041d54424464140e01d081c2400040c000c0f880d140103031400c07003402418640d18181143c4c0c082450314404683d090080f410001e028130806906002c3c286c0140400c480340c544002000eaa00404154041c0410b407000e5904800b4400700070a0800082502000500c00c01c00c2c180c189030b0241050240403800c0348603528010000310440085c0c031910400e414500070711751140e82859001d03802031000382da00300d0a12500070b00025103965a08070f512442d0080d8950b511550100b402414034195040c0c01c202e040d5000340308071a1581c1c42e0742c000c014640d5031514000c10440350b54200034009582d40607441420784000605200d1042e8010014807180d841 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 430760395 1250 430759145 430759151
    0x3070620090f031618060602030a0f180b0d020405030c0a030c06050a02030f0418150602060a0209061b03120901090b1810050403230301030f0b0c070516030204 70
    0x92400c1408200c15800c034180c1a1803000d10107150603003020a8010b00c20000601121011680c80350f84d0840d0090550002c61041c259080c8041c1c96152030107540000c00c0d00340021420a008241d0180408041d0152401000f580c0d244104045040346c2c0304100070001c0414583d596941c000c0c0d820080e40c058014207000e07108030802c000d040c1c1008a91201140c1c0c014401e0f030003a50030450121415070160404004502c070500c803a02e81c0600903001030004001c450050480904010311101c151400003100b681800c40c01e0108100341c54010810b1a44460310f07400050761125114000351003800744d40c2038030104043c0c21a1070b50307042d0030010041485025060707081100355141e07903025007615030905001700544808000300d40d40003060780c03102d02d1000f2004156500d083c000d030740c07020440e00c0444040d40000d0a00344240741d0480801d43c140018001e541d0294070355030654030341079001c0c450014011b040c40907882c0095540300410050b208210723030100070b45100c0c0e00b41b00c1180e040e603807940c041a442149 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 430761645 1250 430760395 430760411
    0x20406030b0901080a0b07140406020d201203090a0c0f0611070303020309130b09101e060e120f0304030f0b010b0403120305100b0c01050f07030c0203070f0503130305030706 76
    0x190982d16603040720b0108009042440e0b8945d14045035903806425038050109640361240b0b0381c11414050400380c061540240700000d04031500402144900b00031070004481214030070004800800c0f10410910b40c0c0707562540d40d88a1801c128604102214081d1000c0c2c0b42000200f800c2000201311811100705503102072200580c80c160548402087c4802000760b80104111840b6050112044002d4400110b00285040041c00450b0151900b152480080124060203011886d0640a009541c5000301e4403172540c14188480900705000170f0002e51310071158100e00102403042001103180644002c0103494036035949103002d606480f28007a0031140c1e103400c4400801c1900c4244156000c40b03402658203c00c52084403030640017410054010f94401c82c800c400800c2c03524060000704500c140c00000018030b850032621203030b403010014158004050070140102030181c4e001080e6070b03401d03420041c012150100b520b0311519512403c04180746030001c0500000c1402004000ba0003546c0c00740d8400c1c09840 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 430762895 1250 430761645 430761649
    0x20d0f090b122a0301090b0406030b070c02010f080610140c01060e070e010203091305130209010b09040501291b120c0d08010302011d12030705030c0d05160b06040902040c03020406030b 81
    0x1200703c050f040c0c0720400620041069550580040e160007001500025040d5241c0d01c0f44140114229407060200d81c00400180855078400d8000030307a02001d00d0000840d003131907000641c10144d8215010708008004403488c4148d5203110485031104019802000711907070305c90700a01c1812040b40c03000081044150081040e500110450326519001800c800107510032440e80700007840c002e801b2210001c8401004c0f00161a0040494040c107000600c1c1519000480100b00554205810000e48943e00c041030a05072501c1c18030444440c080d854800d506c402902e0350241c2480c2e001d1416554910a081c2c2402c0c2803808480181140071100041d25a42e0080b00800d0f115940203210003800981a1031402d861046103a401c070031030706401056450b035030195145843c80d5810075081902c1d00d8100148941e00c0c030f00200880310004145041c91403c2100000008030b40070340018000d0500c900710382c00514583e07a030b94054800a68001c004000850383d00c00020001d4000d4010403010925000070340180b4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 430764145 1250 430762895 430762951
    0xa150204060816020c03010c08060f04020702180402180f0403030c02030903281703090f0f06060d031e0909050705040f0b07031b110102120a020d0f090b12 68
    0x70392556114041d09440f0700b0200500c80d4495090b034821409159142407040d9400c1c01014a00b1903a940c81d41c241e410120100128441c203013280b5807080d84100507440050310752011a8036001038007201e055250f40e032030000c106040e05034040940314005200c1001040340038030020a0146000c0d560400c0904030007501070781d507481503030341055255010342059125582032440c4c0c940818040c1e00e9120714443d907990b40550b03c42c04500d94142c580008001c01400342d004000c040c0400c184140104410701c40072082c20344400003c1c11701c5020b0000e2510040901d4041d207212050072813400071007596040640c6008252407071394003500343ca2a050034003180c5464031540c03d8400f03590b213003031640403001e20781100e082d06c5600c5208202d051250075040600210716032480e034150903014240d07000150700080c00080c01d00708800724000343d0785010b00031034050036070015042400040c6420541c104461032801541c1031603050340906602c900015400b00240000c4da00980a151105001904541c2c8a06c101c404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 430765395 1250 430764145 430764149
    0xc030204050913080d020f09040e0d0f0c02041b0e010e012a050c03030f07140303100b03090705040507170609070c1e0602040b0403030806190501030e030f07050a150204 74
    0x1101c6102d5001c11660302010421200b01d501c10302c1319600e0000ca40071100300b44d0300840324092180c5404078804420f428a40036141d9001001805050101a01c403c054519407203442c2c0704d401c1042c1c180f5114115261903014a072080c40e565111100c00c00d0301c80e0020240510602e15500040712405a0074065004540440140f07809454804803a0300000402d050507008000a841034460400e071020151020b0000304515021641500d6540c03800d070506c030f40003802c601d2640e002e80d80200208500c0d600c2c0f61301c040040d240e58900c825a0f81e143d03422043c0c5010019002160701c036182c2001d10aa46810408907400012082c969065640e1260101f1030030780e8040302c1480c0440d1401030800c0028110704000d001400b141505e80640b20401d4560030100d8109411450700d840c00001c090060642010016a100c07004640341c24469241c100c41e00c04401e00351040a05160300d03a03c100d104508103005482d0450040000c10751551950f04003966103c0f400c0d1805c0d0b9800c1d200304560712606803240200c42c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 430766645 1250 430765395 430765399
    0x12010506090117010b150310140f061b061f0503060402060306060a1b030203030f0105060c0c040b040f0f020d0b06070507031101110f0115060309050a15090b07120c03020405 76
    0x1c03a880c04140080c1e8010615000c81c0c40d550311101000140e94070f000208000462500c2551a440c21443c4103119030b0b40c0341c01000d600e040007964068507a8500701d0580000034180c03003081e194010400e180d00000e00d00502802e07030740a840c00304400d0071002d03034020030030307448540010a010b5a28000e1507220103040e50003a4000340b040002600e503043c1840207103404400c070301d41942004001c1003800d2040045c20800c40c01a00b0000038070400b00340c0381000300e0240c1f0f421180203141000f444403c6564448400c40e46028603101d5000017415500c41e030003000c103141c2c2130364140f011019031403500c0000c1d0b02c2044402c1c078492800d407180c030303240c240b0340d0a0b40c0d62254408014805942192a10005003200c440042d040140c2d00a6030700c426030051040598620b12200003184c042ea40000e0003640351441d801c86010149480c18100105100140d008a41500039010806094242c0824006440080000360902e4003240c20b1102d11a4411561910010003140803c200c80c6031070300440580c0b05600c1055 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 430767895 1250 430766645 430766659
    0x14010903020418050706020a030905040c051e0c010c03060e0a0603020d1b0909080a020d050a050403140f120a02101a1e030610081207030203040b070c0b0d020912010506 74
    0x310050505502080c0f44414512840c2e4805010b60351310391500c60107070466070058100d0840c900c00c150f000402c25000d00300c12681130020001d000c070000d085001d10862803070f000d41c826400711840400f00003140c0b110307107540000f40100c0c2038001018002d00414441c054400d55080000f84002c40d251188409480e802400c40039010010b0300e40210a84031000803200700800d0b00000510000c10784507201105100e0603405842d041090700190501485189030424001c0402c02c41160301d07880401c039410360364865502c81901d036448600368030348079440c1200c2026202d01c010141e00030000402405c1d40302c14590880e14186403611482c019036070312840d2044150b00039401307074602d4a03051443c804a1021079050110700c076030500c000f925020701030352400b0301382d00d202d2014040c06174244060b41150302894400e600d80070302ca5400943d640304070300c0b5802003d1408204201000444142d910007002108489030700e509010032418029440075869a01c80d520709440c40c0d400407018080c4900c5118020191 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 430769145 1250 430767895 430767899
    0x601020a0f0302071d0603010c090b161403030915070e010f0302090f0a03060f200d0c2304090b10210b03010e010603050c18150d1416140109 62
    0x100188807403110214190f001c0c41d20080340e40300006820040302c2800c00c01682c1117043c140705150071140824084400c020300302d441802294201400c1396a00340c2c92142c02d03910300400e070030040010741416217050242e0000205008a203c800544a070721b041c8100c20000c040d46607030005403000f8020688080c0800c105481ca5070500d8003a6010740382d00c190203003510840c0d6802c08001a0364001a400c2102c00f50ba0f9010b000f084281c2c60b03c18480407900d5420b2aa881c0781c10013400d0550350142c1c100080f0b03030580300c040c42c040142c440c4800c200035015a4600c0d024030003005042d04130710380040c014464038034a005400d819a1034065610301407602592254141c1c001000035100b104510007400d03142540d151154114692424845c0d6411000d0704400042c1c01421072030710343d0030a88102501c1d8401d220a00c401a07280910401494000c0c51902c1d44484a00d0f121021030100d00b400c24000d0112425600d030484143c2000ca0240351161021000030a441d03254007040c0444241d485500740010007110003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 430770395 1250 430769145 430769153
    0x10020703030204091e0c02070e06131409030c1618050a06080d030b100908060f130210080f012c09120403151a0f010c0c080f240601020a 60
    0x40044034064039016203840d0311648400141d03220811280c0c1c42c010040d803402d000503490312405000e00d10303a10103414054904002250030725406402c03a0311a2100710303280c0c1c450012a1307100d008251141e1074841002e141885000391a60070030341c2c00000ca4069022016008448120000140c0e5907a081f0302804c103400000607001000c0050068492598951022403509400c2100c844101c0c1140d0340810354072140000e22a030078148008207030500206031414020740902182166005040b02040c0540d680d91085100c46c902c032451000c2d4200f4038502c0007062990344074440780d2003501800d01070340e0300766690b104007100c20781c210845600101d11400d000210040d0300c145290030081d064207c84d060fa0114007403001030b0b40036a1044581811201c0d030f203006500c4601030208110410a000c1d41c441540c50003090084c3c80001c203960412001071202000c21210710482c00140a1000403501082c90320601c0c6036480e50207074840b2060244901000e4041150f1000180c400da5060b4060410407466030f072 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 430771645 1250 430770395 430770397
    0xd06050a181d071509082e0f090b04032007090b0109090608010c12020a020c270a0c032901140c060a050103030f020f0601170a08030a05060a050d051002 67
    0x442104000c21040e4a1030420510002d000341c84120091110520f07130150801076580c3c0403900981005e02c404a284210f0912850101486c980e0321040304a002e01200062001a44c80880750f4a07151203c01070003c01165684540d110b03868611100c510b0400c1582c40181c00d0811703e00540c803100e030600281605801c290010740d0103041c012104e9448020420503250310350440e1946c2d0f9940c1d4514403550740c0c032031190340c8910131b00c8408514011440070020340310b124004185000d0071121150808a000d403608005d0440b1418822841c207040030010b4801030103110940d00700013800c12444070701c1d0090840078550031100a0000c455003607405001074a4506c082c12050b200d60005104111000e03d00b130000c1d80c4502c81c86500090329605626010705520300800d402c00455001c06c009085900e8002103036410342e5109423074810060b0344d440c1c51034680321000000808800001c400d010914a903a0066409003c0c1102c1c505500b503125001d0012000c40b0141c0505144d0060216101c2641164 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 430772895 1250 430771645 430771661
    0x40305013305151c02030a050f0c0403030e0a2301030b0f030613020d020a090e070e191a0a0303020a11060c070608190c120501060311040311130507050d06050a18 71
    0x10344030341006046810044d80d03c0264080104842c0c0010402840358201d1103040d900c80c51040103002e0909044e4943c07480d034091408003c051108203140d041c06a62002c1e4040c00414000c9410b02091210000c213000381c01f1191785440c0881c0c1896860b94440c507012411104052000d0000c0c60280e0350720381d10503840300c01c040040c1d8000103d005a000942c480006031409855500c10100395403000c0300e1010f1a02a990307200865180f4002c040c4210082c62800722500194040004114140114690504643c0d110441a80320346052000001c240c1c0101d4091106402105007560084401007442414810800304891381d82100c5402e00c03000e4020100f95410008034811703140c001150880c42001c60380c00148840204001540e07c0322610254040d09000d00082d1030244403010b200151a103da0249020050140448010a620f261200300540d141e48410b00d90600560400e22409003040c0d0001c0c030650751007418401d000c21141841c5441d0002c03100000c1c00901c41c03011690a1000400f105 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 430774145 1250 430772895 430772929
    0x10e06150f04090e03030103050c04110d09110406080120130303120b0402040603021210050913080c0d030c0207060503010803040e04063c11090123040305013305 71
    0x140404aa18880d5104c3d11020090f404010340d541e50550609929240003020064412400c1007000b8ac0c40c5a40742e02aa0410a403551000c40c000c00e0620740b9070091a103d40010303400620b00a80000e00c210305402c00a04001d013001c41000445840c1c02e0031030300348a141010900703551001410000688078491200051000035400960b992802c0001420390344103600100002e500410508800d18182003400c1d040020780080302c0200d460240401c2803480010b00502034084c203803d00380103000fa001c08603901908104103071861120b5440340540100201d9041400520600c64007242c220f002d00b040b80d040e111220025802c05203070112810303580d00000e00c2111550340311007000012620121600f461050440d242c100041030070981191076205040100c01201c2c286401782c030120790380d2812101c901c5e20a1805c00d0340c25108125000031501d0003040d11040000c00a0000240007041d44140303623040070200c4060811800d5159171710840c106164508000e00f11079802c00c00c41c074124000905440c40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 430775395 1250 430774145 430774147
    0xc120a0f1e140c01020f1206010810030605070c0501020408010501170d120911060d0c0305160509060702190e1b0901020618190b04020f03010c050a0e01021c02030a0206010e06150f 79
    0x64403e03150980e04400c4484c8988500402d9078442e45441d10110380d4060070a203025243ca14000320320255032007040c48007508a6a40300046042103110b916204d25441d008002036603526170303504620380200700c00d01c103401d8030301ca8942e1380c0c03081d4071400701e42c0c83e000540e1541c80c008409418100d00008081c0e1103800c8580c640c4142c2001019191000644040c041c903400008020300300043c05415258001d01070342c00c0151a084110482c2c0d00312042d20040c040c00d6500c10f03200e04840c40410005030b10480d0043d440c0001c0600050100f00009215109501c00c54691030302c81e200700019520b600810100901580040001446c80b51940048001c25402d007070840b100c5010300348840140401c03a0b4019101d0001d900100700643c108807200002c2c149003078000300441c1c103003803400a246000700340c1c40c203040204509407110749130320030040c047c0205421803030080302d0b10030700e0000b9580342e0200e0b800074007500a480001590401c27007000c0c81d1060402421600103820043c010304050b510078084450a044 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 430776645 1250 430775395 430775407
    0xd021c0905090126070506040303050717040b04080c030a020d020904030918022d090910031e021e0a1208042402060108010209130c03020c120a0f1e14 66
    0x280b000d103818002d0100e071070740300d515403100560b83d9004065006901465803021000700034a0f102c0100700c40c112501480d00c247c80b0881391070070f40d1a07001c20b000d40d49001140404e0111309050104020400c6031101c07003c4881c241e50580901d43c0350b0107851406035002c041540c24002600b0196880e641c00b92007454038400d610340703ca0000185000070540d0381107495000c55505107422540000440001042c041d803029181c5c240c40091162040c055803d0281d03503013001040d00d8150840070b07913019560000400d0520000f50905500680014000381d22a030780304800140c0b2406c904d01030b0069814003a00a0400c982441a03130000d2048804003111000070401000601040c078a80e0001c140c40d40261840004030350220080ca4104c0603040305803964810401108a40e540d1100c2910400c5084404035680460f001e00344c0003030082d06440f001c1c601404d610740a43d120560001cbc00803040d1a110420354621100301102c40303004079030702640b103540683c12411040d40200c4100c1c1c0b1a50409c640289040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 430777895 1250 430776645 430776649
    0x6030e030c0a030e01110a0c17100507120b060903070e10030b010312090807081b0a05061b01270605060a0315052203020c10120204170d020d021c0905 66
    0x118048000d400003150200144015a4030150384106c4200c02001072180380c00075102c40342006101c1c801c0000c12030101c04205030940d400d1060300141e081e0300d070781040980703069074000e0b1100e907140c2c500060292a048480c0c1040ca419000d07917003241c502900400e100c50928800240e1440c1c007400310701e015441c0c0340d00007000030045040070f4042c5100e15030300e0808070b224000161240215401c60101e54120003420f105a4000044034010040b16400a100c4480d44071b010501110b00c5810040d0002000640a07060220b5014002c410300000790082007a151007100c003101c4e81d030503482c18a83c0002c02d070f4100c03004140e094022a4000400403c5410701d1540c942c0e9800701141890f59021000d51a00704005101c0761100c0803410010020b26810403000716aa0000e440780842684c05201d84424000304071440d11400b41c002d00300e81c4440045588949407008519540f000000b038031003603c10a4070746c3c005103201040b070f12403030002d98000b1328083e41842e0b8500d1065100351419002c0060308003000a0707503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 430779145 1250 430777895 430777903
    0x50a0c11150f0915071e0305121302030714100309110402071b14060304081b030d0f050c0a09210b040303020712090605030106050c070504060e010f0611060106030e030c 74
    0x1011540b40e0055a42040303405102200c66508200f03c0b845030144082008a0b0030030042c10103c04041001d4010390303039030381740039a490301500c0d05d4544081d1034030003001070b4010015000a80c40e4021030031611841d95425019162110008013560071481d28882460713040e000703400210543e4400c413248000c44054402007422a00211003e03180070164641909034180700316030350005400701803500510740d01d554005c2080344c4405003008040b000000b440020101000d0302c0351012a0410701501d07620142c042d00100504400410340e440545004041200200140e00712041b010b001d40794400620f140074507500d035440030100c0304480c172840300c50381d200040c904083d500c0c4600c0c803e840050329005142020742e42d00e03a0403501c1c3e00902c13144000c2480f1071a0003500b542c0c116185442c1459072455203110050030300c0226449507800a050038404502c0c10044100b9905940300d00c02020a8140d030750301c00315a00c41c00c28400e001e10760030000c01400300d1482070f00420390402d400401c0f03d01d8482e0001c81d01e460 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 430780395 1250 430779145 430779157
    0xc030e03060915010b0705060705030405010b0d05030301301101090803120a0f090b0f0a0921080f041e06020403080c0f0601151e0c0506040b010510050a0c1115 70
    0x6030b60404000d10201c01070040f200c0d80074000e140b8516007802c455645950741d854016108500b4400048009010000250045a0134060243c182424a411440e02c82e44d01d4100303000c1e50b646004019054103481030b400c010806403800052402d07490101030b03240c4064060500707920034104040c4e0780b00450019400c00c000d002c0ca0610b00e451100c60700e04101c80400300c0301d840000c00d80c49400c1c1100c0f03e020031300d03418143d50426992031211000751603032078100c40201a0680000c0c91b85040c0020152660402c030102036208202d600c40010036500d1402219000d041150000d14a90040501c81c1c0070240f0506601683ca203d4240145444d4498071049101d07000f10064103100d07402848000000442481170500500c3c0715000c2d0040480005009050404030009440070740880e00100110540308240000720190028140d4607141071900703046140341802d00443c0d00844031000d0440c0803038402d0045441400d600ea07140c4031488615a07888002d41c1a0709074a503405001d40750301003417103000e0300020070b1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 430781645 1250 430780395 430780411
    0x1809030d0b15070605091c050304050c0a05061231051501181812051207081303120b030d02030d140103260c010c0f1e0207060c030e0306 60
    0x188a4484100c95000d84205040041c040c2070100c40345900710084509a8002e16400300c404101c84d41d8507a5081e1500e800c00b1603078495250910160b144036504000118001c41c051829100040030b1803042c409000c125200d01600800b041150351466450740110701c0d000401d0078070f0010301e442c80d40c04443c1742401a035400b05007084d5010f007800c20420100846030074840380300214070080d8507020304d000d58800d5080a4554007503d80046545031a080107007918110b03072089030140c001018030b000070540c3d0071003550348103184500d502180d940b5000c1d220321807040100404200880446070360460b84800e00d54030031610b9076140c42d403010b6140e03403e001c078001c07030b010f10360003513881d003031423000d800c05458a580354880d80c1d01d00100140040362500200320341d200d0940010b0180c00c90341d11400d05841c0301300304121265510b400094900305900881c46010504169940807e01401600903020228000f0512001d43d100e00c1080214500944402c00300700d0190138072144000d9241e01007030070050304845443c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 430782895 1250 430781645 430781647
    0x30e0708030301120c0519170d0e010e0103090b0a060e0a02070f080c16083a080c1c09020a090b010c0b07021204090b031207030503010302090c04050d110405240f180903 74
    0x1000003080a500c181c0c41c8d00183c0c00a02c081c0041160290141408103e00d60400901214080f8664001e4101464960303101c000f02d001391030035009100040046015400b0980c00c0840425000c600e01d0003590880c9821042000c81001503a44880d8203601c071221845240c0180c00c000d04040c604000c000c0020b0080c01c3c00b500003808000c4605901080040600c200b061210b00c114920f42c2000c440e081c00c4045c6800c3c480302035222010080068059818503003200012043c9800e91100350750000354025201b5541c0120321a1600804010b6440e5058200d002440801d02d2101184051003042e4018520b401624280403400424001c42e038019000f401401ea21010f41529034281000301c2100d41d201c01415a080074900d5800400070f20041c48080d12800c401d0000c60980310748ad108440040c0381c01409402d0003c158641912180008031300a807181d8a0701c4001a000700d403014106035803d2401d034500781444848010010545800417003035401001075017008038179102800b041400b60040a0081d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 430784145 1250 430782895 430782899
    0x608010c020f0f0106350f0a20060702090c0417030403020f010c170913060905070210020c150c160c08070801061d0624040303030e0708030301120c0519 67
    0x8620340801c0c1e00f00003000da071400e44100300010005104800c005c00392004000811035652100780c0c0c1001c8601202c2060292500001405000046080301c40344502d50f24445030f41e00c0340102c900c031858000f000d81c000201300f000400510b44541a90790289640b50b00e582000d468007901c0c4101501035011810a501c00101441503150000300002d1036a024a0f0882800c0301c0d96944504000b040d606400d01114045240c0f90300c0c0e62494481484400185020001c03a40d40708030703142c090310094500030301600461a044201020074021107a9101800b001494581c5400342d0445903940300500c6600242d0081c4003000c1c544254600242c001404ac4000408047c244944103080440d15407240041e6858940100301602c06a00c440158640c005129140b0b550750501181c480c15101102c0703604002d581c00c020041000810250054034084c2d5400c110b088160341010b0742d10b80103801107140b0382d4400c0c8010084140b0215410440621400d4007201141d52840429131100004179001d0320b81d4080f18007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 430785395 1250 430784145 430784173
    0x10090305060c041a0304020d140a02090c0307080709080d182402060f1e04020d0210020303010911090d060b1c05010b120c2209080408100b06040f090902040608010c02 73
    0x4c41e064880d6099001840e40c00c040d03000500d403c9841ca001080c8603060340c92456080e10901c98000d0182c1c0241a01107546008170803a40668000c440710004a2000404100385505c0f9444150583d0005c1005000b200c1d002c030010b44110310160110503100701c80390804516000008100c208883c401411501c2c1c14004007406828400010120100200520104600103a480803012003914099030070311140d4032030780045050000e90150194100d02510414510503900000460481d0300c2c1d4582041022145a034082e1607103d4911910f50250ba80c408250201d0f10a510007005098001d200d004004819440c0705041c401c64041234a5503590307a1152000c0d82007160a090110301004043d02075411850b0005400c010b039a15003000c0708481030546001d15915903c0038a00c1c5801104950f16990b5980c8a641c0e545540000305003440d040c244501d450781402c00c141c4040e1400310444000c010309110208000b1704031810203907402615648000742015080c484c413558003000d90b0103030000d080300b101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 430786645 1250 430785395 430785419
    0x90f0608070e100b1806031501030605030309030601090209010207030f030e030c010c020d030e030f0a050106031e03120b03121c060e0c0a0311070c0b03040308090111040510090305060c04 82
    0x700c092141010b200800440c160040300010903101c5104510343c1718641a0b03e602c81700c800c0700e150941c00c6200001404280b182e4091307032800c4200e0036a428812142c4030400d141d100e0080c42038558142d88401c0050099882940103424580c2062045420380e580d039445907040050503040503804901880444100c03820103001d1590f03200400c0c201508511903942c04250010a40c84c4040d080080d01c03004004156428400d100b0380508110841d445000e45007071403802400d06101c1200c102400940711040c0c2c9100302c042001c140d801da22002e000066035010305000c3d15900480c10382c180a02d20011b4a440c00c404050494403852211402960301c450410b0021030315107070401d80c001c00b031403010410001c040300c045600c407112500c3c000c0b4040d4002070203490135000d101070007070202c0752082000c80c02d01645806103110b90f0099031045c800361242d600c500d00700d400c101699544050100028419800d0100c0402000e400524040000c1c0d03640340c44d00b40c184141610030480b100e000041c01c03c02620000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 430787895 1250 430786645 430786649
    0x507050603010f0306150e0c09130b1c0305210702060a092f041a01172203021e010606090f0b1803031b030d0c0305040b0718090f060807 60
    0x26403024519414440420039081007032200418080c0c580303406144254895031044c00038001d1180292250828503000c5c1a01c2e0010503110b40a1100030460f1020f8903003a0058203107414000d070280c2d10b007541c40280c124000c80160342c00c0c0c0c14004108015111f00c0c10720602c1e0340304c0307a000b40b400203058101200001d003800d4000d4507003c00c880c10800008040b41e052442c00f0950318a0103c1d0190101c800902c1e000200c00010540383c1c02031904410580340300c2e4404801400346000da03105049040504451072001d0410744505104424171450024000c1881c5e070440c14090180c012110584130401c050090081a000b071280c040e511400d04004254000c028003018091000c041c05245050180064040c016610981c1c00500f00f2010641a501c0074030440d02c02c6403c40700d847e01801400124640e0341d0b80724841642d101840c1c03e451050307091003449010b02999205006170806d0b1a603c400303c4000c03803540b0790100101c61080001030a40400e103e885c3c2e450343d03146000728040745030818040c1001a29 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 430789145 1250 430787895 430787899
    0x150501030221060f090a0c12020102012003060d24060302090901060305030f130b07050105071e05031302010509043801050403120509150c070b09030309010e030c03060f04050705 78
    0x181c4442100c0c8400483c00c1e07503010142044a0f819a5101c0a12070f24154860b03070042c03c00c1c0d2001c900400e42c903507854001c41e9614000e800a0004c013000720034401c210262100310008004007400070071200d15118a204450070302032403511044c0760040a215410198642541094942d83d000c10011410134900c086d138003649950007000043d00e1626401d440b881126110b0710307420380c00190400c411114035140c101074010082c040da21800d4500d0300c10700a000958500340490003440000031040d00e540c2c210071520101d03549032030840e2075807e05466651200c0204a041c400c0c2440541206d0700c0700d102c0c59006000042e11890714048040415007180c05004803041035a200b0100507005913080300899048030750041c54541c0030030343e4600490f242d01420600c03640c401021842185106100c3e0060a14032040034283c50609568801d418882d02c10746d100b5030b8258105001c213030b83d50340c003c000e0a00300803030242c02d82d0055a01d06001a0803c0821541c0740880d84043c000c0c4824002c08014803c050541 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 430790395 1250 430789145 430789189
    0x91501050402180d1b080d0201060b090a0e0612030c0a0b060612040311100f1a0a030201020c150c0303010305251a0703031b0302090103150308070204181505010302 72
    0xe00400d40e483c49250480c54042c07114200c0c0003040142c82004014100820b1480340c83c500d85590309070352160103507280600150708042c004100740180c1d0b422540c0004d801012600d000c0e1070241c1619032114010400c0da807081c0000082321503410b007403009000100c0040044c2800b8280740c50008488038001d0b2646025003402c0c40700c4001510900121074000340c00d418a4008000c10f0a02e81e0f2500c00303180d102c521403d0410384c0c0084014000e40107a400000300034510300001e01c4140a009450216100c06401a4403010b1281441d090100780d1540f0a01c0f64046103240c0024210482e2841e0303c2a0720458582d802152100070310011482490506d038050306004020600e40450300c0da0740301c0f16221607125054001521410140070ba803202c000211201c150b540e100c40a8000540250007000000340403e0802c40150307440c81244100201381c2ea40070025a042403126001e0100601d201101c2c0c0c0ca54400fa403012030082640d55403060254000038001085940c190710500c0b2201030028407100e03549507 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 430791645 1250 430790395 430790407
    0x6090503030909060316030b0610081b0901031119030608061e0709120f050f0c031b03070807090605130b0603070c03140d0f140415050703090209091501050402 70
    0x5808001c0b00e403000380442d411000c0e5226040028180051000380c0c007150541c0900c00800c000b500341c0254030645086601412500b0340c4607042d100740b201100c00310706d131104070003e25400d5020180500072594061400040320810f4180f00f264aa01c2049240c070300700041c00703220b04170a916014070b002400d608000361201c2c2c2031010910060310700c0c6039030003081e10311046e0014181c43d01c6a00b07104000c0000d502c01070a98034032418298141101e0f0a02900c3c180601c0d500415903400c00940c040b40648050020000c00041c1c001c00075460f90342e0380329560300d400340f1480015400c00402221000c0c25038a0000038445141c0010480c001c00b100328030082841c1029810012650765a003540c1e44000c440c2003262280041d86000c8509014528006c0206500800c0c4411456010390144946084401c42000650380002c820800284201ca0003451111841c0c01010050700c0c6810290b0010560b040204000ca03103079000911480040701c5100c8c05600075601c00c00c5407501d42041c5030041905550461800d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 430792895 1250 430791645 430791649
    0x471524030402010e0a06050c0c01020102160311032802010f0507090e1306020c03310b1b011d1005071e0c0f030c0209010b2d0c0f030310060905 63
    0x201448040910804084006025039008040e0189480c500401049015072200700c00303021600040c030b101c00f41d44500404060554014400c80d80480071107941c00e070460300c840d0f904a0b000200d2150f100d00c98042440038110403c81060790302d0740c0c1c0c80702041580d00c801300098002d0843d040d070305007040030505010500c03040781d820a40490650b580b07008100210b90700d0b0082c4403010010301038010441d03031000440740348070000480a085401d41c9440307401c00114800b00b01c5540c84110891841c01001c590004100000c0540e00a0250941c0c480d01203000c05078441040b0308540d103111030045500f454242007400408140302400e10310381c0d10002084a03081248000f00b840d030310780c200300e01061521a0f10042490180d002c111205910100b54000d21a107850002c04d14000341c0012400340da0284000b160103c41e40b02034881c8000860282d09640200030305a00b0300360700040817074814a0042011300b103109814070a160740d41c07102c0c4008640da23040021445001c41080d03804070b8204000c03030340c1c140456 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 430794145 1250 430792895 430792939
    0x17040c061d1302040f05030304050303030a091401050403091a0a02101d030d0605100c0305090103020307030e15090c0319060e0c06040915060c4715 65
    0x500c0141c03605103290014403031500c03100c9828401595001d94089110b02c03195280e038006009864141c245000351544d144203040d60780c0910f000361a0305d6002440042c5403101940d0000101d103014510440c025801c0d1000c032421a601680e080c0c00059101c601480340d074090b840c4c2004c2100e802c10301245001d0f0300a000a4899502a4403121003548440711202d26081d0b824400390504404006c1e00d070744040100e40b400082c81c040c42014020400c1c0c41e0682c005074068980d51103401d825403140385c03a020b900c0740118025800240f6040c203140e650143e80c1424503003045559102400c80d0001d0a0340c0c00c06038400c92411040d070142d94400e902941001d140581d030181c944500550001f008a903040d4030102090414021140803900a64003107070000e101c010b60781003d1401c03203803d0050003882d17459142c21a520f40c0c000c00b010b402c508448404e49100980c1016804040c40054400c40c80602c2400409040c0d42100890368001c000900600110031804841c001600104036108075042900d00851101 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 430795395 1250 430794145 430794149
    0x30e1504051008060303190302031f03052808071202010f06062c04050403020a030e030a08040b070f020618040608030406021f0216060c391113090317040c 68
    0x81282080104e8003a0300d0030400d0300c62550500e04600e40c02e9204003001002504101d916544640b0b0203c640074402c030800c80d001e800d036600038015003440c0303040c81c2d02c01c490520305c0c504400100c0b19500c0c3c1040800c504a000d0856107100d4100000a8400d00f24001e007910710074541825200d00e850000c22141e0b400c007488045c0401c003a8140c0582d0100780158190100d66140c0380398005042008000030594045021070500f4031945515003090058010700d5130b20901c4800c000c0484c00104030500009003043d000d007070718500c1105130742c1c528002036004c40d1141c1c12070500b4403c2059800f0b04800c00e0700e007074068103000d41850b0000390700341803904000035035039510780b26007140440c646c184949080d0200c1e011203002102c0d415560500b1502c074501743c0003d20248101200080c05040c014040030920003a040c0214002d054141c8142e40c04520b072800c040c1d20f030710112420145005203100d44c0d01c1d19030000007031001e1280d0000d4070903444e04024001c1804000750341c440c41d0300303d410480000d02044039442 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 430796645 1250 430795395 430795397
    0x41b060e1207150e010314093307030207020d061509060501080421020a1209180e0c01030506180a060302010f0c0c0311010c050f06071b05060f040204060b07030e15040510 75
    0x31340a1042e4005070f000380b440c281c000320b101318900d081007201e11000901000d8503109090300c0380c45200c60389803d035070b40b401c80c0c114505448040000c144454800d0f00901a5180000c280308100100745d0f64a4048038203c07810700c940342c0d0320b2400400c00c0d085a44503a50003004282000b4625144c5035030385580e003c00001419200400c441001001c036403081001c04804d95005010111001c000c40e0b000d48514203902c00c1100400e040980c40c46140c416004044030f03002d0f000c00410103020601d0064019003001884c0903008002042c0e5020341505400c0340500840c00e40c50002038190950000505441004807103038140b000c81c0c08000d0010b01c400710b03814100c0760002c004024040340000121002400c001c0040c02a2080c1003884564100100b0308500420441e151a0b0070032003544002c460b8041c0f685005001c50b000800040c299515002000394090720003800000d0560319441c03200b00d90780000b0b02c1a0002958000024504c0c10719006c44014401c03410340450500f4074100020310030304800b0403004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 430797895 1250 430796645 430796657
    0x20703080f0c07050901090f0506010c03081801020d180b09121c0204270e1c0302090f060c1501140607030c0f060f0b03060a02040605090603041b060e120715 69
    0x31016405110b108060726000b40302c0c1d02a56034803400f48003d0b280f03403061641d41c0c909e0b02000c00e40c0780d0301445850003013542c107445800c0c02d030380d400311031201c01030319110140c00a54081203c18000c2c0b12078480e02c0e0901c7c0084682c03101131141424004141680101100055408801030001118a20782520280f0401d8985a106207455a1001c0b010703000c1d81d03014000070b03c03c0b4940240d0710700e07000008071110000150108150400d1185060745c0300c0d400420012100644654000e6031031003600102000a8050860440703094010042801584042a43c000a80040109812010345460141c0c014180d454841d0040300050001603128810742800a0603c6000501041004003c111810156401403003c022010380503400c0000340c0414176030b4600c00d000d200300248608075140300f80d805944550790748034203000348402402003a9001520680d6404140407103040d05901c4e101400340a0305059855145003003951040c0928400081c0d00505190007026051101b412689446000c2901c0d52410b1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 430799145 1250 430797895 430797907
    0xa110c09010b0c0a0602030450070f03050327060f0a0c020a0b0307090b030907050409020a0909050319050a0f0807030902030601030b040b061e2205090616020703080f 73
    0x800d1a21301032001c002c140ca40080304100070301294000b4a04102986400b01c503c1050858203515030100180c1900d152030042006000c0c0782a0107004140c201d407810040780d00c040d0b11003c03025035940940d80101e440d03500004900390030710054024002030f4540121154001845d4100140b200d0080b0f540803102400081500712425200b006903101094015060155080e220f044c074100c4ca030720485440b0049920000002078195003201224460911100681500b82c100400c0002412040708140c0c0d09c401c03400c034041080c400c140304042c00c030b502c21401199074071210405104c920001c0341c0b9140502005000d402c41e015009104101400d101d0328040e0344c545e9583c0c40940080c10b840304081d42502c510b074000300030020481c440c05c1c007860140c04075480d10350b9690100890420b1203aa070074183c1301c1074404540c1c4c0c1c1c10b1880200c030a490b820402c202d080343c01302c07101030202d0760300312520112a4001020b00c12200d58240d0305500d20200c91019003800760031070b03d501d83c0511820340303902c0b01c02c3c50008903 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 430800395 1250 430799145 430799167
    0x11010906020d0525050703050c0307050d060c0e03030a08010305071d0406270b09060109050c04090e03070f030804020118060e090c0915030a0506030c090a050a0e120a110c09010b 78
    0x1950460210281c91300110071407800d2690f030346e0b03516000440701ca20030304501d17101d00d10700003420f001144c2e401080c1c19100c10f440d0b5610000703030102c0c01101090200008020382c845d81c050001e044d00e030120b96543c0b0460740c91414020b00c0e0408a510186040104032500d244a40c501c100d1152710940200001c0f640280f00062028040312003400100c1c4691941010b00070000380f00362507805442c5280071641c2590321a5620b104580058400001402c82003204204404035031300f02440005480f0140d908000b21078407648000b980304c1b0300c1100064080d0b010007045681040440102d025510004c0760700a007008000f400001ca002036041c4a441c1000004518006030003c5465899016160a00700b6055941180c032640081d034a4060290804000815508000801342c81c204c5000b1328100844e1240c603000307030080c10090002441640c890f5401c030502c2600b00481d10a031000602e03683c1c1d40304070b03070301c0001d1201e680054484490b4010300c02c002500e039a0302076200d040d5001d801c01e00b80d84141c5144 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 430801645 1250 430800395 430800427
    0xf060509130f020909030d14011202150f03100929010c14010c09050109090b0f09041a18010e0f0604141608010603020a09021c05090a0c030f11010906020d05 69
    0xb000940c040910700401c00c18100c00b001038150307281d40207403d0000c0c072000705504002245c05d008810b102c500501d021405482c0c52480c0f9400800201c0503039190240b5600e46000c0d80d4801c03219088180704600e020800d220f1144621144550300400c4041c000314207031290364401f05200c2c200c50400c803250780755009006030624180d4105034180020071a422040e60040c01d9902d491143c680810400751001070103c10601912844000040400310107039400002c010807180041c0090314000d500040c04180301c1006000640203440c038400d0001c80d03500d179280003400d60745403140c00c1c0b410ba0898803004203050350000d0b840d0703009540429050310b28004011300c0d0f46014500c030750f0b49408111449002039419010750016023504c0c000e6816228442d150030b2a00107074418101c1420f085842d05006011242c01e581c00b141e0004116010746074903804035140c0b0054203d058000303940380c0707500c034840408200003051034800c08002800e000340c20702c0ca0114043c0d01c43c49520044402d00a0000320500403045900c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 430802895 1250 430801645 430801673
    0x50d0f24180b0708040b0a02030c0f07140709060e040803090114160221310602011d0c01120f021e07030908030306030c15070b010611010f06050913 65
    0x11508100400420300041c0020001080540e414103481001c40c031060303c502c1050707100f160020004c80362a182e443d900300013580014540408400f007403200c1500e202140e8010404140298014200d040e11241602e09080c3c2c160322499185140600420021810681281d801034200c4041c60300e80c0c1d41c500c0c4031405051031501c91406596000d04005074900c60000880281c0c100d9804c03a030b0607100f0703000b2403120f0041c1142c940b5001d580a2281c00c41181c4075980074030001025a490301c051031603001504458040340e03040000980d4507241000d01c0a1055241c0601c0700400c0380c0149031401d04900041c0800c08444401d10117180c0b5040034803400c08043d0101d80c90001804002044d242e0b000f0000b500c0c6401245080340062014003000500c204e0000507030340511801001350444000c44020800706140c400c52420b104e850901c0764502055811350b0781c5009112548400031990b24402801d42141c20640d80d207501c81346085400d0180d521038644069202141100e091034150941c200355a11150301 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 430804145 1250 430802895 430802963
    0xf06030c070b1003060b011409240a030b0306060f0901120f080a0e01080f0609060d0c0b1b0f0d0c20030715030b030f060a0908040f03060b0109050d0f 66
    0x12020320842c0c0040314564000c5a00178034017040f100d1031032401168010b206a841149440091102001e02d291008180001b84880c1246440c0249605110304181c5c1000a41e03034046540c600800d001401c040c8500741c0c1c4120110f40440c51202520001040064180140c40d60001c100300c0210030000d20400d00d40f80741c1c3e006116583c880072034545c01003580100081c1580011100004200f103031f5100f40c0494010200100510010b503160320502034802c8410400b507400440103a000144101498001d101d1031242c1a0842040d882d07020046103000540c4203944201d6010708521118981d12160315080c5950101c80d402d0701c1c4100d034190000300c05c055542c40c1d600d4001c50b9030029140300302004a0013404800e8800b03021b0161154101a02c62004800949481c0c1011000445c03903689a03100700344440c82101c440c2d04254541041d040218402d410032102140c0e2917034540500d60700840c00301c0c0146001c58003103025186030303614644046a482d50083c05c003203103c1031441e1200c90740c02c00c10707000c4202 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 430805395 1250 430804145 430804163
    0x61209071d011404020304050a11040f0501120c08060c0306040b13020a0f0305090a0309030f0305210604050109020313031202220e0a060e0c070203150112120e0f06030c07 75
    0x50710010301d003941c10a2091807411480300540340010b00702402581d2040d6009000b8008165103512a440003891020301b20f0f51207650f440130101c890846108490280c01c0c3c0c0c840d00c0720b100c0764900c0c0c40b01545944d41c100d426242c1c0700d9820422030440309002c03640d00071015200440c000c4610804501284000c444501c2061b0020411000055004c0d92a00800b00c007a84c0c24041d985494074a00c0d01c03502c0d16000074000901a51090010a403441d04000306544a4600342d8608094880ba83e4a642c0210300e5500c0f070300070308009020311031a090003528090803200c50110301d10b041c4188840071650302054000c007440a007100c8201d954a01d6410b8a61100f0181c8401c40c10050080c100f244204060107100b0343d450032034010411a04052040708103a070360400b003c4d5000d031100400392101d5000490101e03414821111550150318406510074024880c8040c0001241418500f020b90011255800c10403c0002d05101c0310545c0d800701d40f1042c1c1c00d01500c9050f41c907160040720002c00d100e104000703030030300301c07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 430806645 1250 430805395 430805429
    0x601140a0302130b0109090e0a03200303090a052b180e18150106090b03090a0c0b210709050613050402071a0f100311040b04050901020405040c020a0206120907 70
    0x2200384c00c120403501007603035900d90a94035440d1341c404441075007241da80150300035866400000d000303030002a01344109150300003540034000c80e8280f031030340103e4604a454204800050811008004072102c400f00f4050155895031000c402c45950440c00400c3d0013000244440c18241d52a001070900107443c020508040381d107460b1544111401041828142034820203105035036055039040c03001d050f260b16030b440340e00941c9010006c140b5a0130291005120f4003d44151b080001e800d150100e00a1040340042c2d40c40d80d400c1c0c92514081f000160006004181038020401303800d510130061f20643d0005c1300d5154a0b4120b403803001242c40c040c1d400403500a44001240003c0c82407035a9122106240d81c01007000a0b40ea100800c9241c0400340e030480f00720f41c45114180009071110b450718440c0785c0050300014a1810700b0300080c0075500c064400800d265400542806541440d018801c0c811402d07000500080482d80d000c03883e584591815451080142d0021030041c201c14403003030001380428640108240 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 430807895 1250 430806645 430806679
    0x414060f0106020c090903030f04020105040b040312030605040c020c04110c0a050304080111040602060615070209070e0f04060617040c051224131218080304030b0906090601140a0302 80
    0x24030300703004281c094464040c0100305480c0c03442c0400d1180b124000a5820f41e1a6203603030000301003001d0001c9061000130300c0b0204844451801610085006460300340c04110054000340464800d45c220318065402c014643d0714903900054546908181900c0c0011350210610034100e031405507075050700f21405a19210300a00000001800035142c0d03500081009501440c0044a940300b588112009a0480000240b086c900404101000341c104c06020b0320b09041d42c1c3c0044c0e5403400c12541240400d03c00560b51600b41040c415882140005507010814103040410141c024988040ca61303820a01400000b4108a001d01071f0740000c22014051001403101803540030f1721412140c03143c6007030360311341c1200083c41041c00009600072205000e5003041c160a079202c0c4100350358000703540ba06103e101132114020503d240d1780b010040400c00084c548032030451410b9a01841d000d07207600c6c2564885401d00c00b2240020450604546004950342e80360741c0488041a6000400d41c8041c0d0302440c0b24840b0310b42c2e1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 430809145 1250 430807895 430807921
    0x32a030d022703060c16080406110c03030a020c0f030a141f050c0403060f0b030304060f080f07051603030b090a1a010903080a180315020903160b0a0503041406 70
    0x1240801508070b0711104014140148a0015010941d16501080105014080000040c5490380d440305c0c1d91b42150600b40c99004250340301e503000b400051411407046110b01000e02080001c03141c2280510300e802005a0020369412040c502c4034410010901000c0850741c6c10808215401d80c4800b07c1200c080031004041e86541301e0040e48203002110003007000b86240c0c10701c901481741c141c101c01581418195200c01000b0100d10400b96060703079613a042410b199408101400c001c0169503104044a14034000003407400720050300c80c10301c0100040c240018160054182c41141d4030b011401d086504c541d0808601501140106540150880703081c8281901282c202c5000c101080d11144960241b25004581c0c540c40e038030000e0015601130144403403017403040359a100b090708203040d1912002e80303079100c21603074410361780741c80c003c0303543c00140060b07241028042407010021050031050042d180c603001010610691000c0b200300100040003500300b00ca81c94021030000c0804c1c4c212985445e01115005030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 430810395 1250 430809145 430809157
    0x4090c03031b080d02090d0b09250b030604110d02160b010608280608030d090c15120f020f031005010908010c1b031112031605040305032a030d02 64
    0x100c1e880c4070380e40001c0380b03904038894499200355128500001200148005e4014a03249a80440301c041d08101244c0c0e100c0c07045018540c2c00000d04100c1c45626989e5a03820f0701c40d0240e00d154001c5031401c20612009000340c950ac05c00035600811143c0d113000c5030f01d803180302c0c1c0c945c4071a04a102180d420039034065603810241080c400c050a522030390300c0d000c09844c070300d00494080c0000d010013010316041d4448245480f0b45211000c10104a01c2d40f03076000341c0c2c15600500100103115075152240c00038009040e00b08401030000d0444904501b884000040c1f0003030042c8020489140c588002145030f090030740c110b8071140d0404502c251a81001d40c1c015035412a10721035140050030701e44c07012980417018030130080c0161191722400c0c0703410a07140316509802c8102000740e050161441c040b12031031405000302e034420010200b5040d07403442e00345040d0040445498689081050911003800010000012188604d41150000d40301c2c100300c02030101ea110810401030f03841e00001c10b8801800000c3e401400f0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 430811645 1250 430810395 430810397
    0x318070b070320032205030f0c0405060d02030709110d0204090c020d0201020f1b12070302060f0c07150b1504090903030609020315060307050721121103010501030e0c04090c0303 78
    0x16111840682c50400810f48241c041194000b04284001c1100103001591580f20410100683c20b60380c2001134140090720804c1c10503500810b0941c003551516100d580e078031420446880801c1c903155004a50354034a180200441d80b0f56503040b103010580394006a80c4100030186056603580e0b115003440c80581120000a009440385403046c0300b6083c0107000341c600152601c42e50a0924010020b400d44404088980c1d540b1800303034a1034081c581c40640d00901016020390000c160b1420000038504d02000024500b00107680144038180002e01c06020082c1c120602190124031100104e0019441c0c207010301440604030800580041e15900e40c0d00000e19079030207504c08000090f9202106400c0c0e102c102c6085420b1271440400c0c4480c1d2509601560308000703980b408900f060901d079240902d4070515407031201300382240368119040c03d0380b2400d0500c51040006050001d2030b50034004000900040c01a1410300d07444840e501030b20b400810040c0c802100c01001030021083c0c9081032840d5202d00e0100358 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 430812895 1250 430811645 430811657
    0x101a03060915190b1018090903020c0603090c0901080618070b0a0503040f06050109021803161403030d0f06140114090d02010903060c03050108060709080703080318070b0703 76
    0x251141c48042203150303000200c2c0140c1074450b61108035040c6440444101c01d1022540c81c50340c8a501d49480e0b40340100d4a406489000c4450300300250700c1c1c2c0d140e400e41c0c40140716a080c00000e40001e5400305141d10403803c00d44120307450b516030121907400d1110b92103c0c40d412040807000022007410000f2400d0044900030002556080005d00450319200280180340200b8820090f40c48030340c0c4580e0040d80d11034003078009080d19440076503410702034650030f9000103522a0082802294040c00081000664404070020716226590203000e40c0948154443c14642c0e034802010384000d502d0510450328034860115040040e880c814195800900e058000e100c1100040f041108455010f4000c0380c1071400c1032950076013481c112904001c90510050001ca0402c001c1c0000000010b445025402c0c015507251001b15280d810030b292185422002446017003048041e8000304401d01c0041b4003082540d40040c41259290707a41d4012068010b07036050641040c0c80341250004140e240341000d80301c0a442070342c0301 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 430814145 1250 430812895 430812901
    0x6040b0307060e0904030e0a06090317030112141c050c120405061b01090f0302030702130501182703180906150f02010b120c011205090d0c0302101a0306 67
    0xc1a03940040b0300861002c55a6018607500714580038202560203886890101412000400850524800d40d40100d002c940d440005208200443c80710b107013858207005c410b5095601d48512440c100c00f2001d0058080800c0d10310b008508803092003c5001c900071084808105074036a5801406da5000810042d214001e06202801216a004c00c0350200d50004000034141181455612038084000c0c25141c919076030b07020304d00b00003525101000c103806e00940146880310013a0040c40880c1e09006003a0003101d01e86001402076062000001902440b0018001009982080e60a511143d40c1c01c0c42d0b0748003001458a0800c2540c003080c00c18002118000e16100c0340e03950100c000a50383c02d4000d000a10003c20002c10600d44210ba5544010b6845d20001c2410140360001c1980c50031202e042d01e4054000941e021069600951145000e420781c10741001140782c4032400a454803050081d20381084044440c0100303152080040340390701000714000300b1240215421450042d000368440502174020302c000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 430815395 1250 430814145 430814149
    0x61404050607021504151b1808031614010b03120403050606030c101803020a0915080a05062d0c03090106050607150b120105010b092707080705071509052109150705010e0606040b 78
    0x281e0745e06480ea020201d01016140c0d684999030601c0c133100800700c4d0340c0c03500e04c41d002d50360400c00850903815040401c1e64450540c10098140080117107190300a86c850034201002d5150481009110b01d02450034024040700700d44c0001040c01c00c1d034000b942c41000082c002c122400342d540881d500c1922410521a81c41d9030b400d19a49070b46130707440d0240403504010001440c00c1c0540c5080810148406845014000180641440c504068800000310b000c00f104200701e0150910841c0090802118401c4c06c207061684d03441020600034a07102e00c9291100305200b230302c0d11814048000005080000e104a44c0c4503619043c0d25040030704a10311852440c0750700000c0001051038043ca5402c807541c4440150307076611068451900c045c0c03003041044070811070fa9012400070704902040c0540003502140b8280720b806c00c1c0d481c0440c01340b8100302d02400d0440c107134a010301600403159400d20079070303000148030802400d00c0094003c80101804550030074104e12040d070300c0820750f140302c1d42c0b049404008a14003601 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 430816645 1250 430815395 430815397
    0x2041221090f050603071205090d02010b0312030411010302090a030503070507120b0601031a0406030b1603022a0a0602191710091107061404050607021504151b180803 73
    0x10800320055090b035020300039030914100030b50388200c0d17604124510801807020b000885000b10307180495904076044402c0c0155081c00740e0520b0060480c02003504110740c0d41c0d4404144000340c0003c1945030391400a080f140d000c1d8064807144600104a400515a282849912580201000c50b4140070b01480418010f40f0900c118002e0342d00403c41420030340d5103100544c0181111800c0091800d200c0704401c0055039507020307079000303148640075142070340c00c10144001d00450140c01c20f105150050000c6a1000320080702409031082c0300c892135151700c403111500c9062010900c0013804090001800400b98040e05c5003100050b400d55a43c880c1c05003980090310840350040e5044c01c000070503201d00f000064040e030094801040081100c030300d440659619801142c2d0103c1498180c0381840e02040280103090103555840061070001c2c1540c2e10904600411400e0020002041d10000e9403404021101540c04003a03890501052000d0340d508030344015100c1a41008010045411100d01040c00704000c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 430817895 1250 430816645 430816649
    0x40614030c0412050c040204090905010605030f0a1709030d080f10030c1e0e040b0105011101230a140a0e0f0c09060d0222231303080a0204122109 64
    0x1c08440c241400e00e02e0701400d4070310180b01130301c0c2440ba039080400c0554903840104000c00d6200310000e01460309180c010300f51151a8011403190700001e04519010b40081204840d41d0382c06160f0788407400c1202c030301c0b60060054a541d5034051081141c081c2e201c1c0c0e007040406014000d07445901030543d640000408181c0d903a030000900203d40800c1c104038602c0d40d55140b0441d0300b02503100302c0d00240c0360700400d042420221400c4d9030705000807004000958000c20f4800021540d0300c001c0c0001001011003031038200d015030344540c5c0c2d80742004c00180b9160140e440502138404240c114600e9080c294075980c00340c200c07900440054020b400780100889400521140d50700310240201c0c003150341d88010000b28031600324051381c021810b80ca003054208140c440d80c5842c40030320385000034a5441881c800600c1c2c0a5180105c0c610500401400b160030798040c1548040e5a2501d0303d00350a5446129940281c000c640c008000000e111500748200070110034210708404589100c4007040000f0f24013119840e11038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 430819145 1250 430817895 430817911
    0x19090f050d1a13020613030b0f04170913020c0c030c06130b071704030c03060615080f092d010c03020f04090c18140f03032a120301080304061403 64
    0x8044102d00c207165441015600010002911084442580100d681ca43c000080d144480007050018030411400321a415008520034001c2031180c82c059841e142011a00004101c0681003c83e000c040c9565a124101d00c1020601055440d00703080e0b281c440d6201c13134102d00c042c4607000740c05600c90310303041038000d40b0421903080310307100d041901d08214142d4940c0301d80e10030b40e00f407030584030000071100c220001840154491034020010a2131405d1140803a001074200307540c1200304401d04060300394050704d50f0350000304005032601d071511a2202d4918000d0302400680c040c03c0e03201c00000b000d00c2c2d0b0903c10105800c10100038083d15071072140860482c8146821000c00390810f00c814071202c0b4840c0d011060903860b600f44000384142500d848a4280c16a03408100700c0c09950074500700c20700f0405011144007030309400660510604100000e14101000052005a05090680e10003d00c0412140601c04400201d6680d42d58403264415183d0740203004542c04a4040681c00b080400c924045a101d02c0030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 430820395 1250 430819145 430819163
    0x20d05011e020f0901080c04050301060308031b0909060112093306050901030b0a091502180118060302460806030303160509031b040c0302072619090f050d 68
    0x2968010358107030030082c0407c038501c6018840403540380c60034443c00010b18021009641c6a151540000d03a09900400961404000901206017a85c480500c4d40b508090242031824981031030002d030000600500e07901400d90600c00e600341e18500460040e07000700c0103251107580c07000282d26600b070054650500c0b4650b0001c0c419401013000c146841d580781d4200700300a801248540c16034903000081c41e001c8502c8402254009203000c461078000d440c0703c0a0381c0c428201091048004501000c034540c0c1c43c440c0d803040c96000101100403034280c0150018408a0345006541d6100c0f2980d159a0058503c5103d14260010703132035440c1c01c0d07005081881c81a40d004000314070315a240482040b0003e00001034109119050045012640d4140300c0c654a048111b944401e0b840050400c002c141d50b510403003034084c58410492200030500c0622450419070050f0401c0d401c025000118a009206106010341d8119866000d10442a800010700040303603045030210303498039101c0040000c107200c013207801044400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 430821645 1250 430820395 430820407
    0xf06080115050f0103050601050c0f06060111240703090206120a06080a0c03030302070201170f090d2111130e090c0a06020a0209060a1e03120c02101209020d05011e020f 74
    0x205c26000342c4c1c1d20400c10b2400c0c0d420460b564a00d2450704e0501c82caa582d06402820421609580c00354070140c00b801c006008002102c61786a00c600503d0040e02820312000c48280043c054900a41242541d1680501401e40d5440b082c0c41c00c0c1c40c0303030b241a1550810941400c10005d284000042c00802007904410007880061030b41d60190000c0d80241d07412418484003600010f26440d00070f410601c2343c0003000e580c10842c80c02842c014142080d01258100380308141c440c00350030481403501d0b502c800414200004a0100303150070307250113008202034104034224085002c1030034080c524880b4090020b00c0116001c8180000c2008441c0c2c6443c00341100582c0b003074007680050b1511074041034010502806441206407100351000100d07102c000205020b00364004104204a05103001d01006c1049260404110100c1c2c0d00080c000c03007a041101003000704001e8580d0b0b09280aa101d007001c50b60051010160414030f00d0a98064200740e803544421101101d10700b0482c8025000f01d9101c0704224240515083c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 430822895 1250 430821645 430821647
    0x6090903020714011808032a0a02010c0812090304091107020618190b09011d063007111504021f0c02130203010e090c010f031d010f06080115050f01 65
    0x103d80e0a031118100154080400b10840300c1000c83e03400742c03d044015560303e00f00b213403d00c0b15004040f20022a1081d080590b20441823011916007045982441c041b660f444250800d000742e4000ea103150f095240804007480075240c00000208121a0495001d100322041403100d01145d008520000c0d422400410011541407840d40c03c5000c0c201008140c201256000c1e444446100d8494004100c1050002a80d500e190782019006003400d07a9520507412180818010030324a004900102020f4034801281041c040154200d00c106400580c07030801640c0b5003607030001c0c8504404022203119014030199002c4144081d40468401c03034020f0040d0a0950080382e2450009203840842b10070050340d42c000d0001030f51042c1c1c0c1246003031012034000d170300c95040a83c1203c16a4014126040381c0d8041c2c07451340c031980d80000c651398180e0114100020300c5d12244004034a44000021700da09a9440c010002900b146a9800401a211214001c010014228142d808c0030009030160540c481201c40c2c000c40d00d5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 430824145 1250 430822895 430822919
    0x60f0702070b0c010f0905011e02040f09022521030b031c0309050316020a080607020c0906040e10050106110309010e060717040e070806090f0412051608030a060909030207 75
    0x215040b030000124020049450800c82d8246d040494990751a5000503d10902d102c2d5001c100008002c0118501031420700000e41da0fa00a00c100740c030140c0c002c038190303003424040000380040700341210400803804140e01c1e00f00740381c16001c0c0b0752034810242421000e01c1d1074800e1041209000010340100300c002c0003600e5000c1c2626003600020205034554101d100000d07401e10181110440b903100d0150701001034070400450b001a6000b00c64980d125804000940c1d50000ba142c80c05e40c0141c45d0604240c444202240c00741845200814803403060702c150b002840a00c0d400396040320f91655800011458840c034480e11781c802c600075140062901231b201c10340c030b1600764014018107109203210300108000b10111070160704a5401160021511010030801c1500000c00c0c0b80d00810454030100145403168088440c4603000d000a4048008921540304060107001202d40c4242c4003080304145183d10f280940e510390080b61000c0280b810207070002031004050061101c0355034543c020706000e1f814104003141c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 430825395 1250 430824145 430824157
    0x10c0b0c041802040302030f0303090d0804050a02090c0904050a050c0f030c19021c0c0f0807020a0530060103051e0a0c06030905061f1403120408010e060f0702070b 72
    0x2038904104400640710500080d42c109600c004600542c403a840d50040508168250442078100c1d0000c0041207041640803410b020030360380d14288061aa01e40341030041c600755502000030741001812050244c41034504e0701406492200304c0e0103200306e50350400c0d40002d036001641c1e52050410103200f2910038100240256138000c80d400b0407681401094000e0008a081c54858200035030001203d0b80f541c03030010282d4400180c0305050007640740c00966034178440e1b002c0c3c0d0f020182ca441d402081c10740031941c55448100050a0082c01901804246007802082c1c40260f41100c3c602d2501003c4200c8041d00494203070704030398009025042c014910488842481003540100c0c0c098010448034000003141c41980c1c40c0548410364002071400490b1405034645a4040c1070107140c90342402d03040b01480180541c0030281c90092035400c103a1020390f0082031400c4c00168a14000380c0011a000c501c3c03010552280c94240c82503001c0341e180d07454010040170341ca0000d440300d000507009034000740641244c140082c24 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 430826645 1250 430825395 430825411
    0x9020a051c090b22020a0308070b0a150902090d051203090115030503091903050d03150b0306130c030b0d050c01140a02032d0c011b170114010c05030304060f0f0605010c0b 75
    0x2000744d81e60343c005112000c581e0000c482c00702010a00c0c8061118000c5001d41c41201c1400c02c0100480011040034180403510680700c803283c0005a00380c45464148143d9140c5600c6400c0700d00c035802c941c00799699a08201d0f280300945d07280101c030544504194594100312a0818003039803610070f82c0342c24454282280004c8a81c0041c0d0303208000005201004289500b40550340e00003a00043d060103404003804540c800c0c00c40420a2090110b00d5417403d0162102c000c1356100062000038401d002e802418140d402264004414008102400300c0890441c4a80070300341d81702c1c3c0d032250b4440e4006400e802500400b000607401407024086031200310a5800d0924844d40c8001e00030300481d4030070f0300107074866000d01e002651100300320881e200440461101240e8541070000300300e51010324851702c241e0140700d00100d00048800480d03103a40122441c070340d01601b010540750343c1d160a041c204060103da0300c0540035a4545005a480e4007418450401500c505070764680000002c1e485000340c0100c0685980 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 430827895 1250 430826645 430826701
    0x909060a08120a0906030603080a120e0106030c0905060901030b0c0a1407031832040b04020a0f260f18010e0106050f090f06060d0609020a051c090b 65
    0x4560302504010000010820040c1c2560f01c1919180c0184595480d902400034181801304c14000941000241c134021000381c900b045410241c05500409030605011854a0717500c0c1c41408018004031585420541c0c6200038284050303200e000a00800c01001d03c00500304828440109076441d0501e0020182c00034185081103200001030340c0b203695940405021408104080c0d4030f00444504106081300a24041a4015802d20100c4810564001320032506050882c800c00000c90759039141d00c8506403400141045490f0f40d090300000e4944820b4800a6000c03c40c1c8415084818510100c5141402c94229941c6059215940c00c032864010190140070007592015607100c04407400d110301d00c101200a000415000e140000340714041d00e00400b4140141071080800105503500103500c1e4005c003055918a0b6240004505100100442e80140424600004515480a5020000c0e001003003103800041ca80454032400f40c01110f00848004015002c8100021103101c40e4141d544801000f10140c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 430829145 1250 430827895 430827899
    0x50103061e0b0c01060f06080a05060a050102120c1c050a180f1205010207060f0f110f04050f010c0501090308060f010c051506012d020105060901030308010e0a1415030c01050a050909060a 82
    0x4032031081c203a1f00304400040c00c03c02000701c0c010790340c06100e4020809482081200c5d06100c0002d4455080e6070307100008110020351207803090010010158042c0c0b201c42c0307a030707400031807444024a80e40c0b0142116000842107006144910000d40381d080443d07818081c2103040f81c0c03a050055100300721040064849540c00c3c001440800e69601030030f206030411080000b0221018103426044601012400603900c10038402c1008140c5004100d400ba20000c6550350851030790000102c0350070a12031b1000f803807542081801c00c201500051900c0c01744808440d550580350181d0011591181000e0001d03113154422a0240c915150496549070014010700d03110031850600c9252403124001e100700034201c2c0c680c0800203175600c0e40c2072245a401420448040c03403070303501d035440040101070180101103030b194808000c034040c40180d6010144110184181c410140b0b4800d48011000e00b02013190b900034040d903100c0c03588940c13140e001c071145400240c5680b030400003ca024031500d41c00051210782c000722041d0300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 430830395 1250 430829145 430829159
    0x20c2101150f0b09060915040315140c09060a031508120c1504020307090b1c03022508030409050408070c15090801020a12092307050103061e0b0c0106 66
    0x50311201d2251400300d240841c900103011807a02d5080d4402c50702c01109002443e0581d855100301c4000c40703012904505119010103403480c89208640c002401400402c14840c0c40c1f2881c0c2d008464501c0d0030407011095070b990a80305007000c0c455210b4180c6d12140801c803002409000c0c2e4400b0b202480a402c150026070740718002c251516001d540f4004610740702044800644008121007509440c40d124007030b0300f506059011031750b6520709019a410a5440d210382c16880e44940003c4401d0400c0e407a00b00c3c8504086c1d05010b921079241d402e102c3e40d445140102002080d903d460b4040860308054000d40c6007914004901d0000c0c01c020740101c2e8214070410240000c03400002c464406486140b0002000400d2001d018004210903440804940d005004101d0419041000e44420140307045012501a04074a00800740d41c0440184c61070a4103050342c141040c0000103540d8069441c01e072020052261515200d807e100b02e030384504012441e42000c00e008800300360b400b820922030544004a00d040c1c0700c0704 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 430831645 1250 430830395 430830401
    0x501140712050603010b030a021210090c0509060405160c0804050306070e0307090b0310090f050a030f020f01021e0903120a080703060b0913050c0409050a0b040c0906020c2101 77
    0x56440001110410342612080651080b95009041140200125044a0b0109480750444440030f841080030342114414402c3c00d0201c00054840d050040200620724078024175207103014001d0ba80100382200c0021700c1030910340314141c020320224240e54003040d1484421905401c001100310703640341041c00009966203040040790f01521080c3c5682055004100901d4a884100e034030032060941032407500d088c50746020a1340743c0e00c214402008961032000b0300704218641b4003c00c00600ca441000702107818141d102072000040d44156003643c09400b6030210084c20b038003901180d046d20101d20754000c5003014002008064002d400f500381c0e4406c034036415040b03200350803074142030020484030801c000003160305200d8400070708840580542426180c4020610324541c1c0428550031903596004103070300d01780100650b0000c001a0105000c9441d02c0755405000e0300382200c03214000c6050114955400d80100b100000355482c41e07009007e4150590100610003100751380c40d0b01880d09600704070b04181d030280 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 430832895 1250 430831645 430831651
    0x60f14130b12060405090312150f0d03030b0406120203030d020a020c0904060506090f0114130b120a17030f0708041b080d02070905010f060302130915140103050601080c07050114 78
    0x181d01469500d02031040c4019202c006000c1c1b10300341c00030805d200411015800064124245444600120b40c5c03c00102d00350210300300032540d02142c900049410943c4c1358000001000d0159000d210503559908074012440081d0b400a5054109001000d00d00e00d1a130701415181c1c2c21441100e541444000106010170000e417401c0c1c46041c0c85100b004020f08103000c441c0d030041e2404400c46000d62500e210310303500603130481a15200e6010882805101c03a04e41d04034001d0004020a01c1c400200c014200c503503039401c800421950f00d07a409503c020748115001c1a80c1c80b40d005202c0400d481d5480507802c0310389200090044441080a41d08000027032002a4000c000d0000c0d40010001103540c000702a242002c5a4002e1803e5030070200140010b0b1841d941ca54115405400c001d038840c913180e091084121031307a4200300075803850a50402405449001070750110303040e4000c560245104803004409441040b1a59404150399101084405280000a00d010b6001c2d01c000181400c0545c4c1c503040e800415 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 430834145 1250 430832895 430832917
    0x7020a081b010c080405010809120316200c21010920121e011d06041406070203070b1e0a0236090403140408070f060f14130b 55
    0x90400c1c07118148060980c020788600f402d0400800d60030342d50b840040d01c5180101410040d03d940400c28222080203801314007030449090030303201d01d04800059807040f504c2004400041c40c400040044401d1190610214101e56001c0e040108044040c0300070000400c0c2ca00c00c11545d91803180c040d8032070030711424000b140320720004001781e10380e01442c1c0305c00540000d00394440e659084a00d00d00c5600010031940107404000c03100c84614401c0002030041224400c0302c40b40c0c00c0f2242c50091540008150076105030300c81c0012261140103d10255a13902003290114096030080000a0101d48000e2550f90301c1511150000300066091000d020340c11802c0e100c01c0c03d1160003090318080802c000440c4016803c078101d0340f2040d8004a80d203c840c00d18010b00560054409401103000c0c188110507140103101d2022215503034580e81c440745680ca0800744100040384c40c00c2c0101007481e900c0f40800721142c640b555690031031102c504031274400036032100490141e20700c501c140015240b00d0300b001402420002e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 430835395 1250 430834145 430834153
    0x7080705040f02030621010f0f05040c08031c110706091209150c080f090a1205060f060f0103150510080a0c050405090403050904060f080d032004120807020a08 70
    0x5468240000d9900d000c003401111070040c130400005880b000d0143c0d50241e40c0f05068084e01c280152954010045401c1541c030503070a01550130640c0c0215004140102d110f6000d444405980b01441d64a90140150786241c031034aa00345450900f01d0740c1c01051019080e00c542500e0300a99580303100c01c503651a81c086800e81045c0c80401055a00010341c103009240c0e500c140c15803140400c4008011800300c00008100240c04504221152103c1e015644028006007013944519202c5030508498454414112100c0c480d8030002403180680020705800345c1c10250a07154900c044900641c0940354908100380c1d03806001100048550302c4402610003920300d0713191003059042218000050b01d000c0002d51041c010104010801501c0301d80c103199006070146012600c1e4540d5400042c09800076030302412003d60b0219010030762140110f200365901209450030800e5510a1244500031505003624038852201440100400403212190325070880c4250202494040c1e194005900ca40031a00448583d0340 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 430836645 1250 430835395 430835399
    0xf032106031406060609061c06270e030a3203010b1b0307080906130e0a0209030f0705010207061d06072418020d05031902060a060f0f1401020f070807 66
    0x3030244183e42e00308001703459242c504003100002c11035620070003800c0e80805401a4440c00002d55079840540504000707458a040201502001c50002051055520300785203825038110f0040000012108040c0c285e840e0114158245030140e480058500303200c40f5401c451095a0600c0600c090065018203011007005442e002454000740c0c0d10140080200c3c1d065104008440100b1944819604000411262265121038150541e0440e5165038400e005030b0340b4500c18054201030a40141440b820b0a404480000000f2541650380707040314031400e40541c02c003a0f4140035852052080d510100815007100b4401c1030100701044855216000644500d0b03a6103030304104100162550400350980c0102c00c1c01191040c20345801201c4103844024862405d010365401004014401e90303030700d1107011a0b03040310502e45a101a44404080b114180e102d841c01002254200c10300410000740c8500b44030006803e401c21041d6600e120301e254001e41584a140d420000b558800c1000318060080c20020300710440c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 430837895 1250 430836645 430836683
    0x301033804050f070603090512160b04050703111f0807020c1c020a06050c1c0c0515040b01050307030f1202010b100201090b0106030605030a0615120506040215070f03210603 76
    0xb20035400c40070405087c9031080003c101d0004600e5992400224030569030b0340c14000940b45055002001880401e5200c100010b00c80003140d82d8049a0042e004403028420700d1081241d0513030540c110480340c18105150054681c82500c0c2c0700c0d480701c400d00499610300b080c680050000c440d0f50b90840c207580403a602c0d080444c104102c000e0000c2a09003021404c2a2542c81200d031994009444018004494000900304c140f040740410203158120007905d91544c4c40e04172546d11014100c1d4140d40903000100002100d050000f02d840899803c1440c03500c00134425541c0220341c9005202c11001c664840210845550300c000800406a900c0d03000050058131b42d140100c84900164480024145044420845620003052800c1c006a00400014000044241c802d050b00d481d9040036515403c14407003081003200c001001f0b401180200c0b101c07070b240c0410010000540c4504080180032490385004000080c0c0100024514124803104010016a4042c95101282c1844c0d0013a40c5102c8050302031034042c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 430839145 1250 430837895 430837903
    0x909140f0304030506070c02010519050c010e070f0302040902150a0f080105150901050d0e0d0302120f010501091802070f080909130305031b091503100b0301033804050f 74
    0x80c03004000510305240c81d5480303068070350000401d83c07010b1000e40c0021104580c03184080b00d02580b8030041c0300007a01c140310801032468201c980020030540c84c0401e410503801e00001e26008a403404002c201113a4110303424000503004041d01280c001e440e0004a100502c10f48024003d000c2d49a036486e0f0300701c1010034004102110690190340548082034444c0580315810b0212003552600703081880d650701e2041d401100610a100010fa414050450207482c1d01f94103030000c0084800d100d0707915809450303031669125400c0d001e100d003501044104104101800701c241c100a03810052090040c2010000c2d01c4020360b840d5450001c44180c500060065024a413601c61182c1250407004c142d9904040b42d5009411440042e190306c4d840103036020f4519a01450408842e020000504204549a441800301c88140c03c191103019080008500120703401c0010b20540e03040700d0f04001001c0201c2e0010b00d020f8250700740072240d55844050000d8045090790642c42c06401140305034010000114002e00140c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 430840395 1250 430839145 430839163
    0x904050403080403200a111315080f06012409081006260d080a231005090c0d1509090c0608060d0201080115020a12170606040509070e0a090914 63
    0xb00176030055022402080029448811652010a040030300401900007460075150400c1040d01d036081404a0142c420340103462422102d41c08100c2c0c04401c5131403071140d120f85090241d01004213030340990f402074220340301002011003900d0038410119030b00c91242908040280307900141190316000300b0040c44540c00080444010450502070054500c4189640c0b10110091007104004400005c900903004542c0070062030440c004940702480841d810320f100d0b19a04445040035031a5400380081c1c9420582c1e519846100495601894030203401a20380c0145450144100e030780d42c081002182101c0d143c451115440d0194a002007100d01d0301e10010107414004000382e008543c491408001030342c0003043d0505440541c4602031045290f0f4104910786000b0410181c42842c2200400400d01d0304001c0e4010491200b00b010041a41d4490504c070040c40395100e0150888202d400149105214150002e05008014070b640c001d1a600c400041c02d4400d40d09081d11002e10300c4c2c01c0d50300041010031903484 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 430841645 1250 430840395 430840427
    0x503030901021312081206030c0a090b10021917090a170c0613050d05010e0303070c2904030e0411040801020a03050a112d040e041e110f0102030904050403080403 71
    0x1142d000c40c0c0d900d00006000b0724030301e2040c240b0351502180380c0c0c8e43e051195000d0744401500002101c0c1c4d0300e4400d0000341488a04080c0505102c45d403580813284041a4004208a15101076150815550f10720030451051003251076004024071981d229562502c1d8898010110b120059988580c42620ba504003221444400c0c80f03140c081002c3c00b07482c002c0610346c000b1240c0031260034480c1d00702400c11a024045210203410503001c0007007001100380c0c0000d20201c03914001e840ea01084408462041b2a8850b00b00c05000300d083c0c00e00000d0006407081024440e0b00c440900045500340c490646400d5036001500580400d940103c0d80010182d4107204040e880225503200b031181c036840002200041c0718500c0c842062001c070310340b11030b4048030b0b202c00284280c102d00440b55031160707200443e04a107001a82e045030700c08000c0d0341d500c4005107840008100c1d1a000300107801d03044000c00410183d880c0080301541540402c0c00790501a55503881043e22640c002c0d01c44000524262600401d103a80540a140d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 430842895 1250 430841645 430841669
    0x3080618100603020a1803141009110922060606120605060403080306031608010911030a0201090e100807170f07060906080c1c1407050703021b0d05030309010213 71
    0x1041030494146108202c80341800e0040c0c0d5101109001c58840c0c4410405807030454003100000104090b81145584003c0040141d421100308501c000e8207490700408082d162502c180820211032401300b01c1103030843e810f401c0d08a910920607981c83d9103902c3c00c40003660410780c3d031322003045030702e800400f6489010303800078040020505281c0050014021400041c280d03c0020000410a8404011241e902c42d0f90f00002000d00350350b411003074060604401d04850200701c05070304001c2810000790307030340407103505840d1040c1513800c00200001c01c81c802003182d00441c052a000280e07000301440124054603d0b480a90306245541c3c400d42c0c5002e814500103032080c1e00c40c0c4004c000701c543c00045c0300180c50744c600e8451030946850020f120a4010510000c4043e010324603050040c0075154041e0b000842541124402a44c0700748003510a4010458040d0158026080100303c803c86000c1030400c00000601c05007840816448042c55500119808400c903907002520300b40b82048550448020f004207801d50b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 430844145 1250 430842895 430842901
    0x1209051c0e01020f0a060507030b0904050c030d1d09190f1506080702070612021b0a0228091e0207120e030105150103020702030f19060614210307020d03080618 70
    0x985c0d2100c0f84070014050303503034407030108054034070030303049455038800080000c4c065050606100d502d40307010340c009522900c1402407280a2a000d005c1800c03484411040b445d1951000c4020b1200d520230041074116003614880910040e1511031042c0381e280d0248480000750f41142024501c041d4a190300903d040c088148100841c0e550700003203a1041c0c621514144840d0071110741101301a004490040038030842e606200d0403040000101601138a008a0341e0030b41c0c00140c480340c207050b42c3e00100081090030450a0070b00180c210354006100d081441c180030690036028506400480e000581c044614050070060501e65941c841811082440100c0c000c1110381410403203400203000c45031b030840c14581c01040e01000d641d000d102c0c040701c0100347e0040d0780140c1014100510100c1c94070808440f00c500e404408203601c8801f000f220300c4600301800100c4010501d0503400310303010f288040074619204c10402d100042e150700052984062194036500f1003402d0101c204001107a852030407606040440c070030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 430845395 1250 430844145 430844173
    0xf040518010b0a200304032411090126010b0909070e0105030f0c07020901080304150302210c0d0608060f090a1a070309140703110a03030c031209051c0e0102 69
    0x849901030201d09013880b0340f41c80444200c4069001507158143c1e0b001c0440e000040c0170251140c45601c0303080c01401010305040050072011980007407480f5070407a50601101040303500404c001c030303010600399506130301c0c0c20320264014550402c260026084107001141124080c182065025003040d5039081c80b0031200740e821700080040c00020808105001000c0201c0c0002d600c1500700d410131034000c2c01514407503845146640d6640d22610a0085034030200c244124018424800c0d41c40014104010086401c130218000c0e08288000c0c28107a403215080151005400017489010010940c40b00a4005464038526515060b200240540c0d0550405414807000a541504141440101c064608031580324001c04034000e0210b130f680217011800c400c1b491a090000015100c0c22a485a1114505001003a00b4041503202a2200030701060450400e07000007401005240112a003064000411140a407105440e001d80302400c1d22020b82c2088040d400e065002e25001030040003030005141103841e82007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 430846645 1250 430845395 430845397
    0x2120a0c0b0a09020603090703140c0108010e0601020f16050f060415030903200c15040e18100203040609030905060c07030627120f031b0c020112020f040518010b 71
    0xc01454100762100048040280341c0c020f4618640240807240c40b032505160441e0380b4007160009844246030000c200c1402c0d0b00010748852442c106a4951805034681055102c0010f40549120f055016503000050901000c001f8a0600000f90020020b07107883c2a0178000e000c007075044068040d9000300030910141070814183d160350512440c00043c0280c15050440b001494800c1c50402542c0c9809200d142010024448402e110111038140a41c01e0030750341e02105100f23500c15080308044040002d9285044c40003d005481c0500040c0d6402904040240080f0307442110100c803015910b0104506040e842031030400a06000d8034500e141c402e8040286a0320369141c800104216102c080b402e42489440900b45603140c10460104801021031810814007001490b09200040340c004219101510a000300703040503000c00744807904040720844c01c4403e5410310000741e0500210010851580c440c61004020702d01700440d007241c030b5508007c20042ca03a60020a1024036480c2c6800620041080c90 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 430847895 1250 430846645 430846667
    0x604060e060d06180614100e0918011e051e1605090307090b0310140705030901150e01051305100b07050709020a170105190302121e0102090102120a 65
    0x1c03007041d201c0c1c0c1d94610b0240600320540004022801d07100340e0403003980c0e49402a400369808080c42c407242d6904e07035050206040e411b02284c00098501d0556002a0501c018120f82020000e00c040c14418001d0040d0350945000c4030208601c41c0340310800d8030010049201d03182d00303d1100307504040018002c03840750901c0e00003e80030100318013081580d1a82c0301d008100701c03a58144040c1c2502e071521340e01d900c08001020901015402400f400d02c0401211741980301c0d441c2d00e4411703140c144029854105c0111070603000108100e00940d40c2d03850740c1a4800711403408000602245a80c801690b04010034400c3e441c100d4480a52118140030612500c50400394440042c0c4042d14101070311400b95042c140e15120056004c40c41da0347c03002503000c0e03625034009240d1101c80da00c010282d00c0381c1d90314001c5c05101c90701c2c0c1001551015910301c0130300041c0b0f010341007001c445002c03c1c00c440e1801d82090f0440050070b0242c0012903c5e82d800a0032004958050100140c001000d406050902c1c5c20101d020300300100301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 430849145 1250 430847895 430847899
    0xa020d080603150117030d140f07110d03020708120a05060a1d010e09070b0a03022701170a02041e090e03030115030c1707110106170c1309081201060306050604060e 72
    0x4171000d41c941c504201303032240c0e01d03c02042881130b11424041514a50020340d0072400752440c03400004c4445001d0040d171251030740440010701040864500490094200e0b1504464440b41000507916140d02031000a000c0c454071200000c450805100704040840f05a000d0801d1001c0c40104000c40740030a42c6071811a0100080380c4000d07510509494104203c03a049104214000320f0780000c007a9256000c0e101c41d40c03000e565034104240e1510cc0c0c5002051110b103241c00243c01680c40313031403407618002090304141413000143c01c15850f50f4000b42c0161400c0200480d4125400e402c20008206000f10f481030942c61000e14a1941403103030f9030b0105194036403440c09141c0ca52040d0301c1568402c072480c001103000340d100d0102c0780c1400b40e0003c02c0811007032178046040d800d00c0381c04035a074501640341c6d0920a40150040103440c520303d06004100c82214414110b40d0394402a0f0004101004010b14804007461122101503041481c080c0403191260041401450103000501c4825000f40f02d202400c10300f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 430850395 1250 430849145 430849169
    0x2120a0501090b0d0f020321040e0c04030b0105010e01030b040c02011e09020901210515150306070e15090901060309051006050d021320180f0904020909030f0a020d0806031501 77
    0x1800800c0c23500c141714140f241100b5005900b5203014480d503002d0b2080c1c41e0240c4428006072200c04007451140a940009045942e42400404c0558081c1ea0314084240c418107010401c01210400102100ca0a100000260351550041c1c00d038001c0403000e1164441010030100b00403405034001c03840c03144050054200d4403527981c0d40c03d0359120030001c0b01d4550f65440012604031089910260103441d009070b400000101500c141450325280200755a07205070081d603900721f004007819041003642041200305c560285810408810184c45071110a4060070160b1000b1410752810314189107001080e083c10071480b4a07005050040d55508443c5400c0e07a601201c2200703404180c0765002d030051001c400d0046003070041923409100010070b0005803e070a03c280c2e8004907c00f1303950007840103514600311038541c8460b00800250042c03030407008194002080c42c0c22242402580031000c0410361019a01c00003590002d2030700309029a00c00641c03070348000141e010701340c2141e000000480c200c3c41805880000c0c40c17 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 430851645 1250 430850395 430850423
    0x6090b0a0509010c05190c06080417090402040302040e0102120c0310030f14011806050702010b06070f14070b0c01150b1602121e06010608070207030f031202120a0501090b0d 76
    0x2c45213004000380364002c4152131056280941110228141ca0411a007900c5e2400740094918040c0c01080c0c03007036410003203080c0d018080414020b0f9960140c1205a406907082c072010015071a280b040c02c240520000006988403148000d0f645144001480c54103032940800410114020b10503c14045950064a80d42030010602d0134001560040c001080c0940ca04181c42600040980d8a00484c500035001000740e40c80d4101c04909132280803416541001e0b04012120000d01c0e000100c407243c0d400380300341101948a041d280d908000c5070740e01174842d81c10045818500a03800b8410349076144088809909200d02d002140c1a06000c0d1009005e0f058203d69030602c01e640354071421040d0140031100380c1c5c1651000c07074a070704410400942d071603103240b0880c0004100d0501413081107014410310340042c40f1451541d6259044400b03626002c030104450b000380c103407142d0880e001810712058240c2c0d8001c0c5624040e00c401040f00c405034007070350402c1c0c2003141013801a1543c42e220408a42c02010f20500c40c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 430852895 1250 430851645 430851647
    0x8100b011211030414011a150d05130507090c0f1107090203180f0109081605010b040228020a0b06040906060803030a0203070f080712020d0e0d110706090b0a050901 72
    0x111030700390250500c5040419650740c0c40c007901d006511451050440051030b0249215003802c0326408120120f00c03d10f000281c4043e4500703020080c070200344062003a0700d801d0b0b181c17013082c068400c180c50a040e4170489e20440c1040090510511028100c003030000c02c1a500c1c0c441c1c0040020701100708000a1003008503a80758402c00a01c0414003800130f2150541d0380e41044a00c00c03480c2a065007804a0794041c004491032100e034180101e0541a4001c4101d904120480ca1180890054404111000d40d602c040c0d020b040d848900241c0000201060019041248400000044044280d4080c01c540104d0304241c00604041010342d00900d05071030000c3c15101c507140c160010a86500b1508051001208122003520550002d52040c0010b035520849a0340d018825124108160740e2140030840b03c890060148600764094001c645e9000d10104002c0b00c00d0382e88034103007032405044400103111003c085208070803c1000400404e00b600e0001c510030301c0d2400500d080e0084032443c03410040c000031515516 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 430854145 1250 430852895 430852907
    0x618100504080c1c0908060c040302010e060c06010602060103030f0e10050c0c0418060e06151c02060c0a060c0914040903020a0215030402010e150306010e0307150206150a08100b01 79
    0x41c0c0303c40c03080300e229002c3d0f541c40d050360345549684a00018448000401c0d02c840c0412030764050119403003d2428503042d0303401541d240c1d00c80807856812410901000340c1402d02086418020403040c0c002c0c090550660a00801050540c8003180a001c140310040301c05481d15802a1000036442c030b0140e480f0000680082e0605d80708126142d407160414008042d561501880008824840d2100b0000f041d5924a031035107030241160110308005604480843c24207004044005800882e4802480003606a0010b007054101c02c2007004a0792084c160b0034102316107032140c0b0f60840c0c483d0400014007460503000564800c1001142c03402143c81d91904404c160082080e9001c0740e50081c9200300d110030204565103590011a0103074000b0b4191540400309040030101c50691181034080c0d10b142d940e4502c01520510510301007240c2501c9082c100160200d0700c200c0310140003a9580c0640943c2c1401100805248002150640315004c0481d04201c002d400150b4401010390b556004200504a4001602c0f9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 430855395 1250 430854145 430854157
    0x190608030406021e19080d02121314070506160c090501120312060b0d150801110403030e150307080a0b0d1202061803160f02030f0f061810050408 64
    0x6038031001c5008607400ba004200c052008070240301c80c02980a103407059965580d1316a401c10b0848035602e44200201c0d00030001410f0340342000d100503292180581503041001004c80d5004c403c000c1101d0820100000481d844070880c00001c014001c45003043c00003042807040324002480f44510501c0002000000e2038140010804032800704070f990303550502d62111098000080700007504510900c12246c45a00c01d0f4001d641c2007100d1141040d0400360008020040724034017214520b0f21420005190109010308905004203101e015250f61070341c50003038541050500000d00c20719040000040b640070140580ea4401c00c680703003c11b401c0c1c85452440d00103000b141e0303005070050500c203d50800d1010088004012800319422100305984040760700410520070300b80c80f410307030704108601e0f0030390b88081155480c1207020b5100381494141c2640064a8100c00080026484d080010104804003051004562005245410f001009000000b42d03031140c4034052410344640e900d0005c01c0c10b0044131130559070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 430856645 1250 430855395 430855409
    0xf050106091806180b1f20010509060c0702010c0f200d0203120a0201020d020d1d0313032904050609061e06040f20030115090e1906 58
    0x100a503125030000389594498010508519a034014a0b451000944a01c4086440b6600c1d901460703840069403401929003845181c0d44039484080070383c0010b580000c1c25007000d0254440840e00c10507603000c5280030700458024202da901d00b40c204000800c1c00308a0780c3c0d22261030301b0303410340d00c03180d13480161100c1006820140c61442c00440c594100a8251680d5100142048540003481c1002041100c4c10008a43c000e41541040f90204000002440030b013811a07850b0001504200b0126601002c0341c012901031800142c4540c03402e00d100c12911014066040980091454451800500a20450284002400b2116020100c84002005000e00710b507000002181440741c142414000e40d254001e4030007038405c1c014080407502100b404200d0150071691107920341c01e90b5484104000080565014078459291100305002c0d242e10080c83d40210007480030301254803541004c140003004400a84d00e00c0a100a899060191a0401d01c000342d00003071100400d8031405030712008a014101301d0344141d03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 430857895 1250 430856645 430856651
    0x160602040305031b0712030f03090c050607030302040906080a1a06040f0c0c02040b120706080a09021503150616020d0201020c040c02010e0f24151c0605060d0305040501120f 76
    0x2d01e204d8000e00107116010300d144101c1e0b0b041d82d00d5524101c0445242440217010032030700448111030724002c0d002803005070301440725200415a40c0003c03890640c4180c49c2200000d40c009414080d440c1d89116203009000c0c203000a044001050340d0301103552a210082d801c110740c0304070000300144ea07503130842c10100800310070078000032441400c0903003092440348040f80b265040c01034a4000b4100480144020a8814018182e0030310703115003946c0940b00a800c0b03130030680d12041007001603210002c40000b4280d011109554918003004810b1014000b80040ca00c52841007000448040c3d41c000d0100d03c2d40c1d0101e5107001c0542040c4010b0749002032035442190002d0a100200c86810b030194070a03401e4941d0a0300345c8866482ca4410301b40c5400c804041c640603d010703003018580e25032145000035440001e403d01668110694000075518100448121000e8034004a00c40c0401505008090b0811015244c8c00c40581c2544c3d001360450145001d282c0c100040f410800d004ca07115604044010300c8141410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 430859145 1250 430857895 430857907
    0x90703021e19080d032c0a290a020403080f0f0d091b0503010902090112080f0c0d1e0e0f060d050a0e250b03072a0c1a16060204030503 59
    0xc0d41c02040b54414000c032030041901104007240207018800e140000c207001c01007002445100051102104801c0030030303a02c2031140b1200003801c800744a00c007400e405441a0f0060555042c0c090a84e04010010b580b9940103110030800103018034251040910340c040003d454181d48000f5848501030710150320042c0e828034000700300380001d00229055015800a41d500c101e9150310070b040c03e85486170b2000f07400c003884000400078a84504c04c0b88554601c2502014500b9510b0580c40039540c05c5078020803406e42203030030131359103068201500c02c4000d4008902251500400e040282221140e440d2282c000d00b05000c00700c4440d519031040394007003081c000080211341460459400180301d0400900000c2c4030f154425403a14420300c42d0000f0900441c10407541c420700b04580a001504040e00803030900022000c0400448101801c0c40c210000400741888800c8903400d11b1020b07040c060f48a14545032400200350020400c81c4100e4880000c00c030000d4400f201c01c0c0c41e082c07009105a41c00076080340000706003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 430860395 1250 430859145 430859179
    0x20304121803080a1e090509070e0d080c01021204030519090b121906030302030301031a06101d0405070c1a071b080705030301030302070e0a02030105090610230918090703021e 77
    0x86d54240c030000c1d10081c646648204c0144c80402c1e28504070340e8004440c02458001420b00801821000010400503040c41c1c44d0305800d0100000c140c400310003007030380403404407241c49046900741c8145840740740c5103400301e241c205048114803409501d9100d0000110018a0303001c440b911800b0001d0509a0420900350341c0e0400a40300e81080c0000c9a0300600403014244581410b00703100d0150000800e0441d0009541205030b4689100501941029003d06c4045080b80d46621616214003007030b07104c1d120415a10b182180003000810760f40058400c0c007406120041e603100546071720086140319040c031040d00c0d44c10403031003900a19000404034400000044101903010891108440050300d00c00525162000040305a000074041e942c0c0103400c1c0c4001480c50b25240030f0f071b425801081e0400310100f800031b14080b081d400410803410080f100020700c281c010700300a048280120f14082c0c034400705041299105444102620000c0e1042c991031044d23004a000c2407144d03091b2440f00806490200c640800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 430861645 1250 430860395 430860407
    0x9010908190905030f030a080a111c0c0c0b0a0c090807090204080d0507050a030c0312060e011707080c0907021006080703020a05040c08061c0203030c01020304121803080a1e 76
    0x6078001242c8100004803818002412800e01504002860030328611145c02c0b40c6c0700340010040f0742080d4440c1e140480114104c0b004040180c040c6980003070010722903140da42a12310285001c1e041000403541d86011501d558025030304140ca0030004102e03d4161042101c90081a40240f01580a0b12100103804030a03980240f04031096001644c0d0b101c16002026030b424002c0402c00b5003a5004044100c002912540c00f84840d14400c0c280031819100c0c80c081841150b01540101b201c12406400521120744650407641041108500130b140b01410a000c05885228490150740100c00038001302d038040b4001d000800c40445c000300d0400c101903603044090f40d00c00c65484143d0007403100800104007401c0a00820008120585420702d0980f00c580c02d01c14120500c0880008801980c415400140d41c20b00040c204081c03000d0025841e0704003401c0020750403021282040c14081020361003007420070b0150031a421290032840441d105e201ca118252551480429881e00516669028890362a0001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 430862895 1250 430861645 430861687
    0xa0903090b04030503040b0901090b07050604050c22020f091008071205040305031306020c2505030f0706050a0327030906020303060120010209100804051504120809010908 75
    0xc0ea40d03031a1030340d6070500100240725500001d0800e0308200130501110100900802c0b95810600d440300c01c2d29940c0d84407103c41e03009110120b40c2c079000641804244101005042558901140e9042c3c08085500340c614129580300340800e0115000706080b4204040c0c00c1c01c4d03685164010b080980c1c40b00c261440202200811a2100c0c041500c260910769451000d200d560b10555040e16400c0ca107807101000c5400d1a07698840466100303030200804640d084052000154108512081e407003101d54128444800d15000d400c03542c040da0064100e100794000000d5542e0460701141003982d614006520203d0140c03444000500d0301c050b140400c0c0a0584070900840b511030300a645154030380b51074140480c0c0340e20003566a41c1c00a0825940124048098820901015142c0e80010b182900444c00704034090300114080021404071000c1000f404000d200e18002400b500d4141075aa20b4260703285018034841c070320401d04000c61100010407102c02544002141030b04640758580300c9031140706090ba554460 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 430864145 1250 430862895 430862897
    0x4030c090c0503071205041410061802090a1e0e0c0301030303180b190e011505131e24082a0f09070216030c05040629090d06050a0903 59
    0x8010008a0300c66800e03240500025a6103001117440d40a2090162074080d01c240c074529100c608000e4030030802c1040e8150b0900300352012440c5d034500740002200001e59200c00207507034010810b03a101071340c2ea640700d4425035440c06000151a1407208e8021011f042c942c02c0840c112900401303101d0701d018007038065130403288a90340074007031340f00c4402003206000c2d201030000300ba00c800c0502140c2034a28801403150b1030110217000280c5181c0c0c9019190030f4a0350b28180c04d0700d40100190a12090520341e4580b03005961a40c800d1010405a0821001750302000d010045042d0b03a0744408001c001d240280440440700010440d01460344a00c2030903114154190650904440c07407140040c2018181c0080b0144d210090112600e40c400505011003d04024402021405012064034000030140b4404010394054040c0c0c80b0003505200a010446000c2c3d048150b580d0451422902d200d0103000c030b9518003546507090385460364050008200300030180100140700c203090108010442d0002e500c125002030003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 430865395 1250 430864145 430864151
    0x1030b0a1406010320070c0608010e011a090114030f010509060411030c160c060903060501061103091201060515090910030f112b0b090102090f040f0f0204030c09 71
    0x442042004981c0c044061640050442001034129070195101003000c3c206032400940c142100304000200764420742c012140d02986800500046d580044554003510311841e0001055041c4241d40c81c0d030300306200c07003036038050340c001051912648200e4549a0302080140c009450b81440104166030981c240a45805000e00100089492034180100d42420071a00c1582d480c50b240c14003800403542c4451284841c446082280c80c0016880070105070040c19507503100031543d0f04603c1c10b01e09440e1f040c1e000f44100000c4640d50740320210044112040d8510889152031180828980c483c05003519902466009490628851800020b08001c00b50103600f00c51050180d903501031120007803401e90001400312254000b100c4c2c002200110090701c00d210050a9550760745032141100304c540550400c1a100071015203005080110310100c01d03800040820082d0b00300040c1a010400000204a80510072038503410310344080da00310742c080c00442c5c66118081d5680ca48908000684c98401d100e49100d1500e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 430866645 1250 430865395 430865401
    0x516080306121605010509120703030507050f06040b01050d0f0b0c070201030b15030c03090c030d0f021c080703020f0408070b090a080102030c04090f1e1a03060906070813140601030b 80
    0x8042425100b15a07900810302240b41403c0044031ba540100058681050b103400d00343c15601c40c104044802503120f5555a941c4002510f0b2403070401000c440054590350100040c00001492032100340e040d00c20940350742c0340301c0c00603003400c44283c0e5016001900000e51030b4240724030075101c1030040c601c0c18000e890070f000c211500014041c0c054285c03c49030070a04400e0002c00d59052101004542040c0351a04031480025460b002a060200340885040403d010b5407500d10b003190113114060421005210584c0b4007001440302801d0b0000084c40b003000c0650000319007040c502c10006036405812058100e580701503c413680c92000c1e030300070300d1224414034070f9000000381c00c981402203e10440540030042d040901d8031034000c0181060072403980c0d901da00c1e140c0428040d100c0b0362000300307038036580540419101550390300c840c498a0681c1000d03000360003200802c8680a000a1810b030844082d28121407999070306c1c4003d400e01c848014008120a4400c03900701001300d80091214141c078010b02218949403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 430867895 1250 430866645 430866679
    0xb18090702062d18100f0c0806120601050118081902041b02030715230a151202090709260c0d03022e0e070e061503040609030516080306 60
    0x602d003007034030301080c000c088000f4040b0b1300403030360880d0b01403260b070101c0301404100e907001015550380030803c8040030780c0d5030120207101c1c0c2c0c404c0001e900404250342018010300a420442d4031250140901d905000324640105800581140048003c0404c507081d03500c0d48500c0f032001e50000858003021f81c0308504200c8800d20400c90390b031074003140342140d0300110701e407107095a504102c2d000b00001c9078964540d40d102c561812030707000981449490654003c13503418680044210100e9980140c01d803070803580c0042c144910000c541c20801f20340c0d0101c0d06000240d413013410031030300c40d01070f03401880810704442803042400c4e09c1719040029100229042d503100c0f160007030030f00c07031006c0e54030304041d00590101c0303d2006036001c202c500e03a100085a800d541141c5e820742d0203280907100420344a0200d0b9002850030010b100381e214402da0800c070100e404503003515071051050154000504050255030340c0320f40603070800d0300460803551410b0030080808400306031420440c0c035640007100d506000381c852400c0c01ea010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 430869145 1250 430867895 430867951
    0x31a220c0513150302041508090d1b02010c0809060406050c01050603060f0f070207050a081509010218120a05060a05013312020c0312040512070c0b1809070206 70
    0x18090500c091648901d0f294030141c89092800b80300c014141d003000081012000010704207102c0426440e4103629040240d402803904032003100d1081000040c0c09032000003050400c2d40c4e003100d40c091034420a13140190403d02c00611524500070341c0840c001800041c0741c0d400c9000383c4404403500008010703075510b139400e141d25002e0031102c400c0c1ca0030500300060107207502401398a4005613684110352146440d040410300d003260742d07001200c80313a010720b03400b10340e80c81c02e1140d8680c8598000000c0d0309151200503080e00449035068420b11545202000514801007005030501140c1c02200700ca0f04e9080c40c5864030000e000a004903001540e03a2030f5010031282e080d110b801d03054800ea444100c1003401020084030081280c1e40c0200c04542c0801001d2503548042000c0c101460f50340c0c14001030760820380740c07042c0b50a45070107840107041c00601c10200803807203181240c001c8a030a641010b550300364030b000740130f03010b448443c20a0f80000300c02c0500000729400112188070f0142a80b450703410b03c00d107003101e02d28 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 430870395 1250 430869145 430869157
    0x160b0615040509010302041e0911040e0106150f120c050306040e010903140d150f0f06020607020304051909090c050a0801020f18030c06041d0604020703020a0201031a220c05 76
    0x5000f600410060801d40d01904c200040c083c01c500b080b010ba00d00d050281c841966040e9624000700920400740e2820b4072a101102d210700b0000c100482c40d01c8031030101300318603104c1c00050000c541d50121f00313103010710b1842c0103142c00f01108101002005c0c0b03001d00300c1d8105890440c09540b400405050040052058a52090705615500c1301c5819201c1c0650527030b03105c1010740e111152904100c6205040d5558814050324030003990490581c200202c580700c4804e55804002194043d0082c40390681d0003001b124182c0728141c074020020054001a00c0d801a05644184155440c04032800180329140198205481e01203c5980210303582e019214240c0c041c0d4100f1510f1154108100811055844405518240b000d000c5d03406840381d0400240803608561300156001602340100151043c5051226500540c02c450031800e007045518001d50b1440c07809402818980c4d19503402d0613000b000c40161030217800041820b4801600b18040100c2c00b8191f0034018221804d02c0c0f90440f80070300610035241 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 430871645 1250 430870395 430870399
    0x60b0301140409080c0a0302150a060e0a02070503090d06020a0905040c0e091312090303020105090307030c0303020913060f090f0218101e030902100f0e0607030302160b06150405 78
    0x6446241d20801000300044141128005800c200001060790140302500303280d4069005446100c418103054040b03480010064005103180c200c0a0090741250340415802c180300d0880181c442c181443c03e685544103010342240c0c046860760b0050100031180e0000c100d100c0e0350380e4a04114a642c0c00c180f109498804203d4008a041520889500d003006c102440d404954003c614644081c1500e809032124030000800c1c0c0082c039400c1c000c0c003d0540900400c1c0e046188280154a0542c0302d840083c03148a12500003801c043c0c0005645050790b4502c4e101c8103031000108010441680e032904038444400d654414501d015061004083c51042c0342e01c2910004d5212000e5a411680c0000030001044454a81001071006c0c03140428087c80080e205ea5000030f50b03035100094010f1282c01000342148480c8100c01c00c000303403100d0380071b02290301481903001500c0a8803100d03110301c03842c030381a07010303002c0d0103440c8407000c0f2884545014844e03034040790b03401504162a4a00030110001c081d040610407805883e03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 430872895 1250 430871645 430871669
    0xb061902071a0415082a07080a050316050301030f020d03200105010801061a09040b03070e041a0f07020a03030e0309120706080124050703090b03070309050f030c07050f03150a090303060b0301 84
    0x403500d00000c1075400e4080c5c4241b0410785062074565644000780c110a81200c0003d00100802800052a44c001d40c546411814000e0541d0314546d40c1d110051407040c802406600441c1d282410580218108803201c86c50074201218007841c0071509008190074442d8040943c02e207803001034008440c40d02c440c919a03c1109452801c801c01d0b041c00003401508480d150148078103040080c004203098081401980300f05054003280d00b40085043d03400c5405030814170b4889610082c0030056070005041140c16a2608003c61140400c140703d40c2140901103110b40c0001e62801511102d6802003900400e4a80301d403541e034000d0f40c9541d90519040e807203041c0c0850f100441d20503400340c14080c50191803228840e1800b01c081b540c4412510015401c280d4030113010070b0700c800018041010901120301004500d0b002541020f000014841d0b0303d02040c8280d90158904161084598900b800012669052000c80300003905045660307000a1200e1541a00020705d0f080c0302165441121080340d048494403042c1c2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 430874145 1250 430872895 430872931
    0x301050d0503090d0f05010c170a0f02160602040e010e090307140703240501210f020409080a180602010c050406110a02032a040b061902071a041508 65
    0x1100c040004044292030318842031080707001c03e076654401601c0c094030899258424100d246032803420b40b00c400402a041c020b01c501842d88105c805a03040d0383c000420170f404658400313414040d40080c80f441245401c5141c0d884030201c2407240740e4004108540445c1e203a100d16a0341ca01440c40002d4045c1e40f14030058008003d0540480e00b000d10389250f85500d8030646924581c0da640f00121002690303a00c0720020100700d050701c5070311f405208450040024440421110301614008459040d81c40740082080c50100075003425511680d012031481644080c03a20350b202c0c20f184015002c1fa81403c42c0340c03005074101401091641c03041c000c1285090711a11001c1c14181441816604080000c20b00c1710b0382d20a080428000d66000c2180c034440380003c0c080244480c0382e42c1095801c8018000e000b6000342c0c02e1403c00101c5490f45001c803000110115940402290351200490500c40c1d140d012092036500c10b8032010b0080d09400c0100100c1e06810f0f11603c0905100038152203071030040341d03001414450a400303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 430875395 1250 430874145 430874149
    0x31a011214011e06060809060105010207150e04050c030105090a0b0d0308040f1505061302120705070c080a0b01090507110a021504031704061103040b0405040f020403330908030105 79
    0x1000040072120000401d030100841c0c041c0e03070003c0c10242880450360321243c4c10001603030010b210b0fa401c00e280c000039142d91341c10f00740041d542e1030291040e04031710000d04205400640c4540e03558100711744010814001820600c40b51480e40d0001c4c05094030401412012030360114140c8502c00c02501c015003000f16020344e41d00d0582da81e0b000200706452170454120700034001444c49160345541030390908001420300301941030028400e242111100d6841c070400c41300c001071510f4004140c0c4402a490826610f1000b03161111503080705502403c0e41c0d204401e810700030800c4d0060514161180c01074100442c0d03440d02070459035412140c00e2034615800509800000d41003040756440d0f00031124551034940b542d01d07a139540054880c00c40040d00d412003c5818000540d1100603220403481da080118201800c0c21042c000920951043c18444c036a40c24010181d5500c0360141c03001503402500711214618000c0f07030009900d1914001c003001450400c84103906007410710801ea031158108002504580c03e1a003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 430876645 1250 430875395 430875413
    0x30f060f060907120e100606110a26160302010b09010509070e0609191a030c0d020a12050903071703011a031305061e010e070c030e0103060b040b04031a0112 69
    0x80300304585440e140c04180442e008417001000c0e1180104400310b41118000121181078000d4010040002c06880b404440050140e10f05900107412002c2030310f040130544410030740042d03040d07031012010540803192501084800011030017500240007a02e200c1040200d03d0740b0074021540c1c41407118000c6002c01d88103840346409041f000d0040c0b441c14403228001030f440c0c01c07820203501c0802003280d0207000c184500c400c811aa0520309140e542107050130f245c80010750007002c401518160b03004c1420303440c0c144140c5a6100100c0341c00010001800d003503110075101d51003504207a80a402c030340d03046408401108100c034100e5030741c1c00c25607000d00c0038281c2c1034504c0ea00c00f07014890038420301051034001c01c0042c840715000d0142c0c50049483c041d00703148040c01c9000d059006c1400369111034100b021071a0031848030801e03c1d03818945113020a1406005900514054020030070350440420080740343c600706d02c01801070b40c0c0034445c030740009101d5110b200707007004007401081d0710304e200349402c0740006003099 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 430877895 1250 430876645 430876651
    0x30f061b0917010603060203090d021509061305030403020907110d090803030105011d0901060306170115050907030e072309090307020d230a020406090507021c0909090c05030f060f0609 81
    0x3013000350380c0341c841a00340d800c10707a018069034010150107101103404025005103038a2000c90720009142158089448040c02003000001070120b1200300100a000d0044a02545d801015031420307007400303640100031018011005815120f00b200789084d0324058001c0d40c00300c4441a00030743c0f80d0380c00c007001100c180c0504c0b803118140c810b02003461880c80d40d84070b282c54040c0000c0e0340c0000300c1614041400302d0078001c45074601000d900d020703030b07030035404400082e01001c0c1c51043d1869403250300c40c9002200205a003940344d8406000d0f45202041400e030000780d0320303030b030003044000404c1c84030401d01042900309003a5117040141c0d10400200300141030101621910303038018040c001015501380541e0440345100c030780c1c5c0d00303280d04059038501c1145424410342014042c0300900300903e182542011b0350b180c14602c0c8180303003101c600001008079441317480400d016254039081070000090514089000301a00d0007024030900662007407814001c4e0000d92184504000c031544003c540303078801401481000a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 430879145 1250 430877895 430877939
    0x2010204030804151808030a0525030c0201110f0c0d030e06030403020102090a090c0503070e0a0f06020c0916050409091e11091602030d020d060f030f061b09 69
    0x30311001021402c40c9000d04028540c4040112829a405600425202e61702e411150f000030a04030a008260000007075490710710b0b5a04010b5560040310a481030301410240991000300d07160400c1100701a80b116200da07506200703032030f000c10444910742560f0329a40d45910b081c449a1200b241241c1d10320706180d2214905000e4101080b50124200c0820200c0d8812101900503030740006120841d03080c15010380d40101003e00f0100440c680140c402442844003400c602d0400c404d105244810781d80781036642c00100381103009841025902c0001a40fa01e14280700341b84101b0503000082c030021180220082c1920032a03551038039084c14100100000c0a002c00140d8407140400da080c1300d0a031445880501c0e40d4050745220103c40c02400400000b45401400c130441c0c070f4004c1d00c055001c0390f000016281a20b02d01900561511200c84e0210300030403203503100d03004800c100140042481004030000c151b043c006c002c140072850400b0b0100f007050346400107500010b10351100401541294075203520034480c0b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 430880395 1250 430879145 430879147
    0x306012709060e0f07030b0105030f10092c0303090604080c12030c270102060a0902040e0a0305030402010914130c11060411030d030612060c0c210311070b0c0a020102 73
    0x1100c41c00400c880b01500b0100f004580b040500407400c0c80c81c080d05500422078541408400075a90000f44a03010141c800c9041084040c0443c101c0329090411202901c41c3d104100410825404401104d0802c901c28800c102c00c801703c0c2c1130070410040122807013110014010aa1030711a5070307079807445a001e200455003038000c140b04c003000245088000d600820388030400d030351142d5100e0b025000207407844802c42c1d52031003881c0020f8880e0b6008240c2542c0301ca070420f000103c0001c1800420302410140e02d0704100c50040784404410141c00c0740245000e28005c0c0e8520400c0340e1900581c2d00118140900e159004905031415280c803001d61300220000c1d146450301010002007007a040c0e240100c16181228000c416039210710b45400c3c20800000c4201880c40c0500100c5d1034500900d80310030011401030f004d0b175120381d0404191350149551240a85d80300c1000d0140c14011450505d414202d05501e00c0041e00f08445c1308100481c81d07040d290116045000d62101e51190740560702645c0c003003000b20040d550 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 430881645 1250 430880395 430880399
    0x60c0528110102030a2f0a120e0d0b0a0504030c0b04030809060a02090d1509020a060e0a0f030210080601021603031206050303131401050d021803010b010503060127 72
    0x9028003480d80180284154100c00d091074800c090940d18080035045500c103000e901043d0b03034040500c3d40c181d403068080c54855800c04040602a00110f07800c41610b118000080c0d0400441164080c900e65840d079800c99100001006c006c20002042c4000e8400320401c40800d04084c1c3d1030740078980261080c109a60010213507a00e4a030300040072a03069010603408001c00010358070600c15190300c01c20407031045107850902000076003524886000034001c5948505508050003980e404a9500d5800400003650650303200c000034800445180000d001c0c50f40d60800140701c180c0c0b03000b030b002170340e41c001c0c078000b021514101c0c2100c3c01c490042c0142e0440c8a414060242d040c50300e00c40c13402442c003035075035081c03c0403240b0542e509660480d88124040d81c4100020040710502403d400213030317500300c2680900e0008030700041fa098001d03d05080280341c800266941d80c0b004412802002580660091245c508441c0054865000880d0780b00e021034041c8c0c005240c4d81140005c10030700b40c04102111007000d5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 430882895 1250 430881645 430881673
    0x30f03040911190c020310020307090618210309090207020f0405040213020408150f01060207050907050c030d0b010e0301060612020d09061103040515010308040b03090c1201020301210804060c05 85
    0x143c00302c51818040381d02201c654003036013402d00461201001034070080d440c5060808004103e81d0480c4241c5c000c0100c1e000d4070448a000c00c480e0500141044a031114600d28130034545440e44480010803800700340e4201001803054518005e8522541d0000c00703011015200c4024000904001001281d100b02100c00035040380f0854130280c80984414802070142004104010405e54030280030380b100f20b88180010004507500040220a40d44203030f440329100e03140c3d00c4040d180e0340281d690946560001190840f070845065201e03a014040c240d98403040890750000f85400c9840ca4010200060301c401c2ccc000203d09032a800501d10064008800200d205c1c03140c40388002c44141c51381036030101000005101c140401008014150036490344284901d5255a9441e040c902c168401c4401480c004000030784081410f0003400e40401016103c041c0c810300380e40c0d629000358000d01980312110011f00280300c00300e03a406c1d45070f003a5660090445160500700380c4140c0341003908480c00c40b40c1d4820086601000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 430884145 1250 430882895 430882927
    0x1802070b01060201050a0e030909130311071401031109010c03260c0405040501270b31110408070e13140610050f090402090402010e06180f030f03040911 67
    0x9242e55800000e55081c021281d605035600318a00794030560080c40b00d04034690b03e69441540011402d001e00c01c008140385410784506c803d010341e0003007030700581ca40014441c4842c150041c020100760303420480260701c07088200ca54007134548568000f40d500e07090640068051401c000e5800341002c0802d20a08200f4044129620100e444526189011400304980d050901590780980300380880c008514060008070701983c250a00c0700003c46864100840c001c0c0c031400b00c00702d42c4030503940b4206004001c080c0180c09100001c4205002030f85020344404c101d682d40010761341550042c01c0038002040c41c107900c174408903030040c0007011454000c1424900050540e85480c00d0707c0c0d0483c015000a141c41140d050a03070344203a11150044d02a02298005a910041002d078400c0d81214001c07059241d9000498031807900ba0405900500d00013840e420b00000c01000407901c0d103080b00e0200c46803a2900c141030b120381035450007200940c0203010621400c8001e4000c0007a19240132034803810a00c500d80c0704098 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 430885395 1250 430884145 430884149
    0x10050c03220228140f010212070c1508041b08070b0319050709031101020106120f1a0a020c070510050304081b070b09190305070b09030a0b010801050906070801030803011802070b01 79
    0x150308104001180c050204e1a120b450119110811214500000703034507010001614001030340002000020850480d82030302c0a04080c40710008000b51408001c0c01030780f020303541aa94241c81f403018081c140c0f60f02c2c5a65060301d01e4070000d400d641d07250010321441034002a25602c114070203610740e01c002030042c0c82200d20030207056449404e414510300b40b0049054100c0712045c110390401000707000701100d510105e0030041e0300011940381e100203424038041d400c0c181106241240101810b02040c040190050003c0c4848036046d2071030341c0d989104202d1403061412101e0003040042c0001004036039440d0107064110000200d0031405000760800c58200340450f00200540b81c1e0100c1c03104581d00b4607200b1459003045058908842c2c1d41107403a44c55031428540b080704c000460001700c0c0c1c081c42c0c40c180200c0f10400e511001e4440c1a503180c001c0719000c1d02c001c48003c1036070320446001079035a9120f000302d14100c9401940c058596420801031510b0110b203007000c44810380d020080c0e5070001714020b2200c3c0c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 430886645 1250 430885395 430885459
    0x50111010b0d051e030f0703121e050603010e03120705030601091a0a11030711100e09010e04061b0c060b0609130b030c0301020f03270d0210050c032202 67
    0x1c0d040760948454419507130482070558980d00500c0400d41c10354114084951641e014100007460703800141d141c0e4003a010126444d12001c40c1c541c03140c0d0315000c65412842c00f5183c101c00900404c0f5080d503e00e40e40e0302940c0081810301c02d620000c1051940580000d40e040981031400b40c248644a04100c04920451441a4124400092006943d07680000d01001700341c8503c01641c58801142c54030002c00940006c0c1511036444030142080f018000c2c440c000d881c1001404d00c40c0d0310741e9260310b0002082021181902c1044c1410040e45061038211840707642c01290343c94000124029858210042421220841e0130001c01c020089480d40d5800b0109280e4860304008942140380c081414103000041c206640641c0c0140070703088407a42000c081c0c030342c050400c00512280101e41c0700e8541850301843c003a981c0d036000359407a9141107540810006400c070341d08034040c00682c0b00c0e001c0c00015031200b01d5a98460200c8181003e04c014601c04ca50000c0c14001002a10b0340b10f9180d95440d4803d1101030004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 430887895 1250 430886645 430886653
    0xc022d010b09190c2615040c020f0d0e090a0507140f0705010c080c18030115030804060806010c0f0201260a0905210a0c030908060c0307110f07050111010b0d05 70
    0x3c1c030083d040e40249801c110082c034241d5903100c2849101800400311036014840d0800401c0040c0c1c1c0c0702c06801d50440c1c8590300a00c24003020071050b401030f49585004440d500507000300525190640e000d07421440302d0a202511090960b2341e040c00c054000c1401a25600030407a0b00c2c20b0001d0000d0050010b407804010064007955214000d2800d82d00315620031640e1001c6c00519070400917078110100940e848561411031990440060600003401041e00400d2800c20080c0058003105121182010f00251801d50300c1d181580d440b080d00540780c242c401c0600401b40d0100c00c2540e001948100d44103010002c100c040454104001d040020442c0e808480c0034908994480034030080c404200845001445504001417140c40140380190442c800d900e1b000d014050000c4081081501c03404004000b000f290040d10381074206401c062606038400e4803e840003d021080c140c400b07000124402014240c000014440c8038606801542e184c51012a0381c1215582c0d0071440b440d944a0341a0300511a102e08054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 430889145 1250 430887895 430887931
    0xb0a0f05040c080405250e090607080a060302060f0f07021e010207091401060e0a090903092d050f010903050f01060801180308060105070f14100c022d010b09 69
    0x1000459016402d000d0800000b03d040c4400b003940030420f015082000c3d50345c4105010f50300c0c0c001c00900c5880c0e0181142e80e5041040044c1c012020600d0f9005640555400500e52a160140f20035190240406507100c2c40401440980c600c0010080c06072100c0300041c1070a08940d600004c6004240c0420800344813102d42d800740b599179051100780041d0007040c03410407c0c0c1d40c501951903a1500140030300c41c00e0081010780d522603551070540710341c01404000c0c02030281154500d00208180780901c039000c3c1d9030f084004200f02040201d40b100c0a08540303800310410151070031040008608400800c5418000303902d5011001c500140076412401c55140c001040d418548016242114900c2c007045503160703090141800020341c8609a603400c0142440c085850300013a0810b200d4000042c4c10040c1000915141540400c030041586046158000d0f020428403c84c10820b90302c440d19007510401c10100703140714004035007140c0800a542d0600100000f0790802280101e4101c0b10262075400c5050321032050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 430890395 1250 430889145 430889149
    0x100813060605100c171809060607080c0106080106061106070f0915020615090f0403080a0b0406031a01060518011103040e070504030b01050604050109090c1701120b09120307050d0b0a0f05 82
    0xc0e030140c3c5d080042c60070346085402e646811682003101c51851044901c2c50100e00700e40e076540103031041c1540110032165550302100001c1d0081115104030440c3d0750802c81d0000e042c40c010030803425140f0390302e4080d104903620319400711010300c044120103040c004d006101041500d080c00005043c10101d400501c41c5040c90400ca880a100c154105840b44004404000030748203800d50560b000f03941030501e9202030b12101031003000350518079001c0e50450724155000003441440d842c4110589035100600306940d032204400c8400e807084c80d5203181404050700400c030042d446102927003c44038207001540d061507180c030350006072401c05566800001320b003c1020720501115004840c0142401c4034064030309490000041c00d45c00051080d48503207955541c91100e00e5000700001c4c0c1840f0b496050141c0950f071074200401d40305c040c800094580848000000320302c1c41000403d07030031201d401c0300e015003590707540d803011122680710420320350702c0c142c0765240079150b1346030302540101402c10b40c2c002d00c20490900c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 430891645 1250 430890395 430890413
    0xa0803090708070e0411011b06110a1227020d05030a05041a040503060c030a0f1104141219050f011401090b0d200f030f0d0e100813060605100c 63
    0x31039200c044c0300041c40000b40040343c2e500b12030b9100b8281010041102c3c0d0240300002505c11014000f9414103a4410381d8036804c02c01004605d44580b80e16a5101c0148815411a100248030003100c00c110002c04800c104d505e1202e510b45031000f0840740c1c1003007040da81e0f1402c6810214908000c9a804101804803298103031040503280000c1004c0e0b4242454070700003a50300c82c0c02506074072440740c000010428440d119000203020705140301c018070540b00c4500481c051548580705040101400c500c0800b154175090195064070481c62008040004a21070703400700750811160122201e00ca00010050218000e0190303c1c0803180540388016a0741c5007403011001c0ea0f60b80d420046c03140740401d05210000e16000c15404802d500c0a0071503054860020224040d40715444c40380f50f0500c01c40e020b80c448540300040300c0240380038581d504a1000d40d00c006100300f080c60f403115540464450310001c2e0041c61401420131000f4003070100407030407a90701c01c0440c0130741c82d41041c0b030340006001c4600070043c031504030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 430892895 1250 430891645 430891649
    0xf0d030e060403050d020a0302041502391c140a02031608031e0d020c210c0a080a05070c0303050a0914030a031b1a151e01030e0a080309070807 63
    0x14280602e0a03541c000c0c081d100d42e42c0d4100400360701190320098148264184c40152184104091034240d84800c060350300d48440b40e84034110301c104811084660f4071017403c4011460003840b801440d410b180b003081100c005590429030f00420740502c1a01003030b401100c005214282a02030030814603240141400e2110800503074070490000403003044001c40000481c1c0c0c1070074000d45030042101d580355589900d03110b40428030420f00c2c00418611b078014404140e8101c400241d10346c5c1d10354641c0500c84136001d0300130351400000b250040840040410340360300045c01c007000701d03150441c13510360169180c0345510350701e40064000841c00300b0340d507810079041400c07040609030f4000d02142131001c040000c0d0303841a8800c0024104a00c81c040d02210311b40d0b015110108650014451240031281c0601c0c12451008403410090451803142408190601405000810008840055000074540010340c060941309040d02e89074490104030f1404504e214014601800a690140607618070b01300c0e5041c5040201c3d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 430894145 1250 430892895 430892921
    0x2e0326030c031b0a120b0307030605070201021b1b090403030204030b0106050715062303031c0c020712050c120c03010603081305090603030403020118080601090906050108150c090607050f0d03 84
    0xc2218003281600085c14105030240c07050045a82100c0c90086402c1108030b82c0b0003040c10f0300b414180450550190054510421083d1108945c44e89039944d1654443d0907500402140c1c0304c7c8100a01e20b0b090a84545900c80c0c0a42809480c1075a20ba4400c195500260f00034000a02c0c0411940b0800409030340e61554844003000074031000d03040c12010001c0002001102e9000c0410701103409140d101401550521070010100c0c2c603000290000000203013120014110050049040108544148038043c401003a00500182203801c0700d90280b22221480028000b400e01c0f45114054a540d0240910000785208406980c0c4030807035070100301013520070b0307420441c801d000c00810441c2648000056504032502480c0c404007600d0002800c0302d0600a541007080c8a019603000415404060f4201d401801d109881c200201d0380e851040948441c1c40c0300901811402c541c0101e155548080040c200c3c04c400104810301c1c19419903542440c240c50460506001d0b000714940b0300c55290175100c0da500760107030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 430895395 1250 430894145 430894147
    0x60f0606030f0a02030901180507050306010b0c0718090203030703030b09060a0501050d050402180f0603070b030702030d0e071e05100503040b130f0c0306052e0326030c031b 76
    0xb030342500c80d1400c4000d2031003110590100008904e41d809420020350045501100491540e060030b101b91940268000c55000f0322806000050b01c000040850301107079901400303040041c5c1840b0300c0104100720545150034890f1907610000240c2e601388014030403248a81c4002071018800021300c1203082c3c000300071600c03403d031298003080566000b03c00ca034080070100600140741c2c1c0d902d00c000340d103410b00380da0000d842c8080e4200700201c5000c000781036802000102d044440d001c1d0f44084981c0e045c40102e50550058009004c03c80e917004a0b42c000a0a48496070140c4440d80d4070750000c0200b54011000300c90419111510420080c1000c24250340640d80c0c0c0c1ca030062a625007500c65100c4902e01a05144118048400e01c005220b02146000380c02540000e0051000d660b170b04200c8040c1000f900c40b9903441149640c140800342d5259801c003135504d685000d00306c500340b82d91251b8440d0504003e001d54108003055902030043e800d00f0045100d6980e92042544034280310000121080c0d0b0b4a113030400e44a0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 430896645 1250 430895395 430895401
    0x15080711120f0d06030507081506150a0309060c020705010314070801031b030b010617060a030314071110020a03020706260910110a0f08040b04080a0c05030408060f060603 75
    0x1240841c00800c441d803031280c2e18012101000598070940f0b000820403403a024010082180c00300301801110408011100c007015408500c0c61640001c2c0e0380968840d56040c0c025900030344c110b000d0083c6112500740000c034481d058852009a40640d010100140c0000f8000e101c0303580c043c0710308000001401c1c9003400b1881d0904000c1c20b0b907103040c000035060000c0c0b4500034080603403461983c000756070710840954a950b980c84000d4003c01034a941c0071803e0940100103449401c106584d40101d079003651314842a440314464100c0d990f88010026207085c1da14500f01d800d55102d007040803040003103d80c010400c400341418028105503464100c0010420060754968101907590280194464151218070450320340303814440c83d1268096a601840782070444d1590943e10210140421210b80c0d29080700042491108407400c9500301d5000b01100d03081c0b80400d01040c110700c00740410a45505282c682014140c54a0349550400d0340b10820b29030000003004914030300e007464603401440c01d980460a40c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 430897895 1250 430896645 430896677
    0x2010b280801140106032a05072001020604020f0a080a08040503010c0929070501090f020f060903031603030908040909030e0103021603080417040f0323031e040f150807 74
    0x43ca06104803010951110031107003003e135503500030400d1002e004512280c010190000605140c2162000b03031130303550607a060a80c01301d0104950418500059000e0216991143e0070840d14006039401c4a0708492500c80c007040c00d480c00c0008605041c010a54142ca46180034105800e540c803102901080024118040061035003600300291046040c206d0007209030500c90a0030620301900c00c0c090a1582404c2021090003400002c040100c0e0007a80c0354410882d001e402e22205128104900c7e402d50b00070400000036420781d1500d03105540c42840c000c40c01940589541c4965081500070041241e51406051304051b040745d40441c003540d0030708041d420007042d8241e8903081c6060754400360504ca4032000280410044070000c0d840340c619900a940c0b00d640300d00289500c82036500048908114200108010030740c16100e0340e5640000d40010b52904440354000b50210300000354450b6071303200600c00461040f1002e0500e10140c40d2520100004944243c1c005080f040054040c4003800742d000c1c2c0d04200c1c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 430899145 1250 430897895 430897931
    0x14060307060c03080c1905031501090803041a160335070f09180902090c030c0403020613031e03180524041208071704230102010b280801 60
    0x2e20f03010f007084034440e030720308003071060910481d8800700100c402082d150810540041c0a140104420400c0c035003602c1400300159903206503070246502503030091000b040f212140c3c2c1081d04515140009183c140a840b1076696281c3c8001d40048012030702c4600600400c0c0041101d400c107030260740b8581a204481c041f400a000c0c0000790800c1d0402c1403016180e442c00c0e0244150400914501088501800454016100401d00e4031170480c070515100c0c0200d24050b542c503003949e0055528000d142d140c103140d6402c004881d07101240c804e9a013003001200001040c02000c54540c402007031107204100c2c0030075250091100d0b0901001c022099140c900c2448030303032609013082c56555964402580110083d404808a0340a65440428103001140c001005c0000c0310010f0600c951103110985420a038040e410b0440f03004c1c0b070040c1c01c0c42c90b01d80780e24808407944a48a6841c0c0c040180000549032814102189a070000f103206501f04c0e070b144038089071048085041c2c0f072008150703880080041d0100c0300551111 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 430900395 1250 430899145 430899167
    0x17010b0f04020a0e090907090e0610050d1a01090501210b0a0203060406170a0303060501090b07030503270a0201020d03020a0909050627010609050109030f0605180106091406030706 79
    0x107640c0421118112800f032621000c001c44018072000303051514501031940e81d01d1900524420509100555083c20800128240079503c0350f1046081f250a00c400e1001c01c1091400c00d66550030030b00c1032503c1445010b10140d0181030903d00c007051540c1898400b88244540d585021450706103454428003041139a01d141c0e8014a242030050707940c0d103e050000d8050000c0740c01500d040b030840450304861030000194011114400c0e00c00344030701d640c0c07100107448041d100d20545a0082d01003080f08000b031b101d40c2c01154021303850415030043c0341450403181c203445600504491258403c064820a42d0b03010040f01c1c6150b0801d1505500c0d2030580c50340200581d80740e200b000d0300d55880d03401041c8103a940e11110340c5032480d01420842111100a20074a50340b50030300c80e010100b441d000010030194420750508003601d070842c81c3e08841d219184c2d02c00e00245401441c002c2040c01c9080d8104452000b801401d0041c403110a000c0754202e00d0480e0644038070b0000d0801413283c2d0010b0780802c9801c0e0821341c00382c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 430901645 1250 430900395 430900399
    0x16080603100e0304180207120c020603040f05160b13050604210507080313060f0206010f03032f0f1501080607081e01030b04210912050a080d0617010b0f 67
    0xb000d4074120320b46031030b41c0900d800114245402407481081e18903c3c1d80900300d0325019802c00781c200c43c2c680f07006072681c002460010350042410400980403881e00c8211841a80c4207200302e45000040c1040250407403078136000709546003400911003c5004015019034040e1000710b80b010b01d0726262490341e80c0243d548950040d403000c0c000a00d182449821b00c01000103100c1c150999688104d1003008126848080c018a00803d07030400d0126905840000c00d00d060301d4030840d414641c541192030035900074410726410a41042c0804011920a200051004000301c58500600c2c10b01e0134111100c2c1081340181d507014103141d240b00100b181c2c100000d15280c00c4551401c0071952a15040c030300300a180c500c11030455540f9039100000042140c84454280b0850042d58440c8003d0382102010200c0b00301000c42000287e00000107024414210100c150f0f40c1d44560220381030034070ba9540c0c1800940062404181c5140d481c4401c02c02c446240829404506541000b0007004155800054081150f00c6582d8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 430902895 1250 430901645 430901651
    0x6121203070e010507080406050909010f05060901030902030c100302030a0b010e1c02010c0f0c0501031404020109060f0207030c0306020a181802030a09051506041803080f0901110c061608060310 85
    0x100b0781e405071017150000ba81080a0603510394541801500c01e600c074440d9a13000d015035500010f001c1403442c04600c251203000303000c10310701307901e080044006c0e040b1840183d034180aa1a00450903a46140700e500d017040440d1400f6850340b600075800c2040f1510810582c1c140a43c0030080c038030303a9498000d00603a207101040c0d490f1844d4080e00049a4a4001e0000101603820300c0c1b86000502c03401d0f0a4510848009036424403c2c100020300341400c0100c2650000c1c04901007240c10300405000d122203180d21940c910440368a40c1d80c039102c1010070896a40161840e582c005144003540d64440c3c081c14006000b40c0d51050b01601d80102c050245000c2110941c0382580031010490101c4950004003c0d01e8111080310312203180e50100d4480140159442c6100781d152407004500c01c099400c00d515860b80546031034807241d542c41941801c0300402040c82d04c41c0d55803080703000361400d0b80f00c014009140d100002010a40340c4a642803045201414524091040c14010060300c1d43c4d0005912751030b80c0d0590008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 430904145 1250 430902895 430902917
    0xe06010519050306011206181a250903050705060903151b18010201060906180203090a050a03020a030f021501050609010c120201020d0f0c0f080910140612120307 71
    0xd0700c8404103580109925000d8440002018841d00304a916900c2c020642081482c00d820b28448403100c034010001d00c12610058102c0c05510480c200e01c1d400a24034400d07461070201781c0115641060400c00f0351000c6854044244240f00c410031141e0050001510090b1410b00710a0000e540c4181c011440c00160941c0c0700011400d01070b21021000b80c007a840c0019844103211140301001900226000e40190b00e0b20300e000901d414140240380807503025814120307040713442c1c6045a010b0740c00100381c211a403188001c0e28001450800c20a03170224000ea01a2900c0200d61900501b00740b08e540c1d8490856004048030600010002d1403207044800486115a64402c0140140c5402c000b4420140c10303010761a034130442468040d0014040003c0d8401d007000b40310718854011089502c1103a204002400440130040f030140030b04000758104288004595a0514044980040c1e8040c082903441c45080c280c01c1c051941005525844405808406004203c2c4400d00002c0f10340030080c1600e040008441403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 430905395 1250 430904145 430904179
    0x1060c05011503050c2710170601180c03060e01090605090c030910090201020f061f0801110a08040f120e010e01020102181018120c0506031003060f0e150405010b040e060105 76
    0x1c000600600c074180015524081c00c02a082a10912514a0001c482c09001408c1180426814142c9259000d0b40c01c580c4145582180104207140b1040300781503540c80007290410b01d8181c072600a00010f040411504d00741000e208160701c0c050600c0302141814001c0c454030b000c01203401e509100d0855400510202e0341d0004070f140c90031a90844180e4083d08003441a45186c085500e4181c0758400d42000044ad1f840c00f07564200c0c1c0328850b100101842c00d01501072580d100f0b441e5103401502440c450300301e60080e030301c0310301040081110310380100301c1003e9020703125604540500b03d410402d0008504102d1000700800c07042c608582620b100c0e51948090380c0c0756a00490941341d402c0300898134840410307181c020000c0007149900042c3c41d580742d0708400240d140380070340840f4410819841d02004091540d651440649071100942c01061f88400c03242c0d040c40c00401c00017444c1076200301201d06d9400c0c141400d900b11282008100d028500b800300d40d4525400006100d8111181602c0da840c038890b401d0702c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 430906645 1250 430905395 430905439
    0xd08040b070809040207030305090c0607050a11011107080d0207060e031903030e0a11150415080a021b010b01080109020412030804060f050124050306090606090d050601060c05011503050c 82
    0x5042e138042d102150b40307001d040e4960700c80b82c8a070243d141201d000021180c02c0085e203004065000f002d0380c3c440c007081000034070102054040650181484001c24000d0807400e030809403140c10074401f9a02c6129815103060341000f9080c0140360a00300400505030800c0400e460b26250700c1036001c50200c9110190030140f02c1c2d030000005014207015202c0540e038030701e801c06083c40c5014070188140d10b6071000d641d442004e00b084a01320b820f402c155881300c421403141603803810b400130403190f0410b070309011840c0c000180f800c40d826a140700307000006418109000141000c001a0040c0c0310300342c4140010b200100c4a11303200c41c01140c1504013042d041c0d032180761000141840c1c11804c01000c0c1420000141c024450407601404a41b100e8403031201c076140d00045400c0c0c0070403204181d0012100001c5140d078140785004050204010b4202d00e40b0400c0360f25268504002a407104001940810142c824400288240025000140700350f0380203510715201c4135507030700800029078800d8000d00c9450503900c80c449 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 430907895 1250 430906645 430906657
    0x61302073002101b0f090504050c030919050318040213080a1208150f060705070b040501020f0316240f09030306090e071502070f080304140d08040b0708 67
    0x150107008600851020008900d201088002610440c110074885075142d00504040070400001030705624501202100d124048403062000d011130300001082a44031030182c944250f0390717000d41c2d0340d603820305080051402004143d100b008000502c10700700040d0011044130b040c0f07003c003851410080e4441c00043c00070700c11110103d540e107078001c0001664000c0800c0c0c0c000542c0c01104003004100704070009455400080b10101e481c00d0800d000c0400707a14000c0d4607119920310141c00700342854440e6803010300e008200d402141c0005004a020015580c0c10400c0000304040703600036600b81102502189802400454002c040e1003034446482100c5072804080020340c00b01d108288030000c008140d4100030000c80301c041c0c0010341008170114260301d0b00c0c0920307103076061b241d4000c040c814075202201101d001032003010302c00c5005102000880074150341000025148070384c05035030b869150500424000304072070030560140c0900c02c1e83c83e002c00c442600340e60441d125880f2860380e4001e286810382d181d200b20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 430909145 1250 430907895 430907933
    0x100806013e0a022110090f120206010e071d120118060c081b090d06060f08031209060601020a060f110a030506040b0f030c1201060506041205011406130207 68
    0xd581c1c40d4a500d000500e8503040341c0280c3e41c15074402103d0300c9130000320b40400b210107180d5204050f80b03218041c1541c8420340d5039001c3e0f88549800c0c51165100b03c3c140400001110040e88080010b10181c1130309240140c1280d00c07030400d4500307030400700b8492111200085095100d1200351010403e50b07030080d000b01801c0710824500000174801443d282c40104110b250070000100355000189030303400d90701006801d00215081980c21300507400c1c1000784495484c0011140c15450724800a048401c0d903002801070b12915003d1501e640385d400d80d944c50800001d01c5520194418414498503036000704900d00c0701d64020030041aa941aa80c1381c1029004101c1881003000b0005001515282d25501050103010115014802041e1ba6010802c840d0f03034141002d50b15401480c0e03884481e00d0a409181d200c0401d001c00411181e9880c00040c49a810a40c400d174194212203540310208070003803046280560311007281e40485c1c00c00601191001c148080d2050b04150300040180c20b02446c00200c030100524 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 430910395 1250 430909145 430909247
    0x110c210609030a03111219060504050901090204050c120c0f0c07141305060901050f0f0423010e0c0412060e070303030e070602070b1602011b03050910080601 69
    0x803603030390380d82d482e40041c000c200081d25000140180011982c1121041c001940c40341c00c20762280c42c910811101070550401030203070354100006039916070340280d51003015642c0000801007101e005120a44d0001010717208040301c10030803445034072151a100c50304803440c2a00c16441da0b00420007081c89108201e860070482c81541800600003004c40c0151440c1c500035699503050014000341201a500c0680701140d00c941c070800140502e00f0025140182454001c0054050f82130640c04941124101080490085451034120000b0030220243c0782c010680311100306031a00e0311102e510307128000c0d40600c0c150100b032441a04103200c2160400100c00e00044180c81f0696568078015000742000481e28259004010000071401c1c00031a1490450304890303140351400301016424902104021002c0381880788100800d5141e41074450500403452103034603a00d03910040002000890a51030180908000501042100d640d0380318841104000495401104008929010586681900b08040c0b401c040c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 430911645 1250 430910395 430910401
    0x8090f06040c03030e04230703021209070303030e16030b060607120f27140103110d05061507151a030307050105010f0e010f060e0102031309020309010507110c2106 72
    0x1c2e9200056080fa4440e441d0001d11008100c280421703502e004001c02c40b020a280303c3c07506220a10042d4039484100c43c50300510300404039112000b901070542c2c140000341e1150109000b0150144074040030544490010005103000200400900b04035000c0140500000d078041081c0340c030707014155030b80702d58420b0b01c0c50050164070070028582d2001a15080008140c9a1160640750710030f698010364510a6442214603810640c002c03801d6002d40812604166546c407403140b1481464014015100074407001040c10f007401010081180c44902903ca0204030801c50003002030034800302003c0d102c64041c0086000000c80215200c00201014a603403d80000141e03841008410b501040c1030752502400110000c0d1680218210b45000f402110325602108805000c3c060103200e001108180510440c2d00d0013586020140c10684039a114041c40c44c0c0210034000080703400c2c09015442011440c0c8000e00060002c9280d84e00d07074200c030085004201e007408450a05052065030700c0020b40340412103006003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 430912895 1250 430911645 430911653
    0x6020a02010e100e09060d080424022805011506021e0c031e19150507080c040b090607140d1e021c0c050a0318060504051008090f0604 59
    0x28244100490010b001c03245401ca040c90b024650421042d4180d81d081402554001804000c00c0c2c0078059550050381800c0d0350001914440041c005895074010442484640040c24440d00700419200815904001e01c0042c900c14205000c6007614010840040280c00f40d00b0171900400300034407503444c180921000400d0a5030001400c200c03046e1028078207144070380800b0029440d40014403d240c0e060b0451460b0880f42404603101121026a0006640140e0f0b480026890181c0184c04e007207594544014851032195090700c100c50b8040d030107040030382d05440c01550118030381c42180a14001d001740450300d19241e44481c000d80e05d002d0b5004042011f201d0860f1000f6944403182e0706014006010b58001d18202c070008102541c8020468000302460340307030003507440300c480f0203140300408001700070369500003246003007210180c00750281d11100e0080000341623040007281c10750440c6041c8281000108102d4031060400320075400680f9000342c15031103050549003000c114001030a02845040103100c180 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 430914145 1250 430912895 430912903
    0x1090515040903050c300c0309040c17070f080a02090d2004020706091101050c03030c031824070201060303020709050601024e0304061a031e0d02070503030304030c0614010602 77
    0x100e906c10115038680c041b004401c450303500c038801c00080150000c0c1f051420500b400c0c0c005803204200c600f000303001c0342004041505010001c44546000440401d103d1120f1a00800c84d141c10a000380c60030344c40c0c030805c000414003c0c8042a4010005200000314840015010544522704940113105658861441c10300318007078000f000c005d940040700c020100c40d6a60144046030100c5076040b010710304541d00c0e0b05442500b80c1008101c456548001c910b41c2c0384106051100c1c0d1403481141640520402d0b45941306950100003e080c002560314180041c000301350005041011070301c1401e8081450398641004030704120407907014a8035030301040201e04018007404c04a404403845c200e500f9040201d0b52107540704142a405440107004800c001080120380c490700607200c0342c40c1001e039005807240d40c0400f10781b0f030030030701b441c401414000050940c0ba92035003803202558003400c6100403c011030410000a84910000d44020188042c101140080080315044440d8a020354100c1c4841583e480b14043c0d11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 430915395 1250 430914145 430914193
    0x1911090f01030603020a0b0c0a0212010e01050718090504050309030304060f0f08040c0e06030c130b0a080a02010203190e0312030727061d09090c0901090515040903050c 74
    0x8100024115108039510a11030942100e400030003000398240340c81090a43d40e4061140e040843c0540100381d03015844005944c0e41d1046000000603440f4514408a82103440207081c02040144c0c280308880c003040e04a2001c81507904005000541e919640b0f410391462003090715503901804082400030345113070442c03400501d00e00d181c0c84801220f110b02074211400c00c82101d00500100c420a01400286200e070612940448058100c0d20031441c1040001da18041840744800c089403204400042800c118075400024412000105405401540041e4a90154244041468002091481500c1d04c2007001d201038042c054150b6004981d130b450b25269076882254080089044850400c1101200003140851000c0e02c84501c1d04941c18030f201102c104014001e50004179034088143c40041d45d070104a640280241e00050035058104401e0000880059115914003803500c42000300789045603040d012968000c41d0300043c240140d00c0c040e00c80d4020803103162014899442c400c07500441380308144007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 430916645 1250 430915395 430915399
    0x4050c1b01060b250606031103010605031209100c0b070f1b0210051c0222150806010806010909091101140901020a0f0c08030d0519020313020108191109 67
    0x103408003500390024242c9446120b54621080d0030082100c0a240c02c440d03401c015034901c040141074113850b0b21140140c69180c0c0080d40d02002c2c403005a0890301d82441402c00070001a400341690f808020001591405050f6105000d080101d02104103603114400b41545c0301e80c060b00c400a14185110f00800d0343d40781e1030b1400003040c1d0041320301b0000381510300d420702d885500501e20151004645402c0b1440d40040101c0101070b12482160800c0000e81c0c00075203a07000c810044c812202846845070071121216a019a020144890041c164950710194040c0e00c58801c1c00c110b01c8984034000100c841e461180d0101c400b80e458101e0030420440c480c243c1c035081070400d0fa41c18074a00342e660001001c1c0c1c8a00507515001d644070f8000600000c003030b1a84400e1890141d03541c2c51040c1d540c0c08600b0b0455008000b00c000c620780c1d98003040b5000e074829040c18840403001c04114210f1038070300080d10b120310700400040d051001c00e60024020f458141410030980c444501c003031059820391061040f0315082000075034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 430917895 1250 430916645 430916677
    0x50c01090f031101110721020a090c0c0807020d02090702032a03071716032c060304020909012901020c03120307111006120209060d032a0204050c 64
    0x354801c0c00c0444a054a41048039800740001e140d0054030810420001e4103c1401400400920205a00171401c6494003900d00109070543c544100240003589400161601e40782141418140d0740c4070400c0100943e20607a45683c1c0d4420b40002448101c1c0c000c2d0080d40a0804010008410b9000c00a0448070904500d186105903080010040c0c283c2490100311040c1d00c1400030304003042036034072074018158206111901e0715a2000b0400001c4504c4403055011804001b004241c8501840b10818003040000541c4454820314001500a120140010b44120400c07404205a58029030042c8442d8006038012900e90718404050304245150030b031141e0250048541d140da10703084c040382c400b80700110804001d103941c3d82d6050170f590454502203121914821440038240c9034110344100000307060f65003103401041c440c0b031041282c0440010700c030500482c07051560780d0009030011400c2c2400107102c0000392480340c803117070380300d01290340e44002a500c1420300043c46012501500240078800041d9514 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 430919145 1250 430917895 430917899
    0x31212160f031d15041506081005060102030d09050d030f052203020f0a030201050105090711060a02030714040b0c0d09080a080f040b030a050601090f05010905040209030f0604050c0109 81
    0x8a200910a41400400d560050003207005200c0d5002400c80880104100c00844103011440c2c6000c40000018404406000a000500c07009886003200e1903031804043c480c29003880d00300782e19603000702070562080d515000030130120381c02442038030403000100100300101c40c1c050500558401154010001280c0b400e1001882c4460b1800341900c2150301511200044042410010f081c441d0002d040d421402205620300c1d000c0010f10900c4c20780c500a50021429504200c208195070801825840c18401d110304c03c0101800c0100f0b8156124982d6200161a030342c6002083d00c070701e00b02481303d54a0b203000240200e080001e64014000d1000720380103c60b16100301c40029940c08203580140c07081580804150400110780900400c003a02d4000e10031804c050383c0780c42503244e81d0030640f050030801c0e40711000c20510b5603200f4540380081c4007506902d0aa14507000002e040e4524602034980201e40005110210351020030482418894003401c80700a407400c1e00340203031030701304810311749000036085200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 430920395 1250 430919145 430919161
    0x10060f06030216150207080c070602280b06031207060203090c01090515030703020904020301030b16021b0402070501061208130b0403080a0e12120a08010e2203090302031212 76
    0x3d035078050900440302c41e4140c100b900c0d01e4000b1148005421580d075000c0084100045515005c4d000740341d0483c1c0180606410208003905011300d034013000e94908070429881a101a03240c0d0350296a641100c00c419207900d50601107070420300015581d440f456000110202041001d600a62041032200251042000188011175101c46c4e1071203000e0b44440d0303400200500c54040d40017181c00244900300145000078120200301a60026801950b001c0002c0c400c110680c1d0701ca0280d81d01500d03151000c3c0103041003a854a456071000c40c030040740901c1d400b09a900c20030100b540994090450040b00c0050f920103443d110783c0310b1b8499401d00c0340600c40c4610000310700524134207940560342e1101d03200c0c0c100001c1403c201c0e0145601c04440394004500c1031007184071201031040f071090f40d54825089582d40c00000700508200c074181d00181c06100501c3c10014100d03095595408060364009405024005c0b9003401c45900102d42c1000e54140103068410f00010f004800402c203030750754540c0c50107441d40c070048 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 430921645 1250 430920395 430920397
    0xe07050703021b010c080d021303110f0405160c020112020c1e070e0c0a051306030b0f060705060c0306060706050a02090a05010e090a0f02070c0905060306090a17130810060f060302 79
    0x4480f42c081201607110500103003031103002c7c040c501c5034450f0060030000041c1480e84082e41c039500aa80c01d4035045019041400d02070410b20b00074005540074003040c20302080704005d00000e24184400c2040d10031101007160f101308034604202c120703140255283d041c00f0040c2500c034a4a41d01d00401d0074082410010710100c0030a5010803a82c20048800140da101c007401306c3c081c5e002c494408104082040b0798021902440319041c0500450303a070000f00c082c0000244840e0800000d01d280c460081481224001900050402d512001c0650b4554680c1c0b02d05011500502481d500180360070300b060304004842040b0b42c0a00300b800403c8900820499482d001551a5003c910b9504d030007402c400005035042c619034100304807503401900018503001490b1613542c07410840760000303103c2e99120401c2c880e4606d820030403190801407840c00340010918a50b01c0b0124000101c03400340c040c03840456101d90303e1b50240c06000040900c60160307a10000600305820080a0074001c40420b0301e08610046490b61084c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 430922895 1250 430921645 430921693
    0x5061608061203030106051303121205061c02151903050f010611210904020a051308030901021c02010212090a20030c040908091503090c0621060102070e0705070302 72
    0x801844c916403c0003c101c2c0e02da4003044104070130030001e820020001c0c18040e56181c42c0d1160b940d03010905c5150751224800d0f281c1c082c003035502c100802e059104603030100f10340824109604861440c1c1c4401c14841c802c8040c0550700b4103901080fa800c400c04203d41d0036400c014410890f4164000709aa00c0c3d400c1a541012541007200300ca5101c038000f250404c100426601c000022004101c1c20111100c0000f0203036030059841000191303012521084000c4a02c1003c0d0240c14080051030601a403400001d41e10700070000c0c08245a042e908200b103215000703604450391410341908114251500900702d980c0c8655204041702d491915101c0c088856010101880305204018040d2020030010030402000c2e00c0c001c50300740c0b80403408101e404c1a031b030ba96800c041e08502030a00300c5c039281d16000d80040c6c00c001c1a414524000c450030072042c0f45001c0c0c840d100c140c0c00880d00c4140310fa151150300040340780c00ba654010102d0010350303005004803150424003601c0020f1085e03084440841100c000010985502 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 430924145 1250 430922895 430922929
    0x80709050103050613020301181505060a0f0509090a061706090616110d020d090b0a02070b0706150b1309060f0b0a050f0f090f04050f0f070203070506160806 69
    0x10400034080c0390300c0b0360051600b0100090003c0403405048803040d003280c2c02a4460001c0c000310312420900300907070b4000d45801c01c07481c1c0303a010b8890b0702e448049400741c41045510f008101c10b808040090764019429610791070006425a409450a4020b003801810540a6a00c01c83d005171605001000c2c001030b07a44c070a40c0084d010380302d692910001415024a003901003000d0000410780308503542402c0104150450640c0c1c0108403403d0303454800707046501c06400030700100340100700d082002900002c0c00c804655031076000903512591410700f00010003504009142c01e000200000510001210282c012982440151032000f652080c440c0100c9400d03119424101c801034600304801420745000d456141c803d0f00b0058a050175020440303040781e004101c02d0b0b601c02030204400c0c00c4e60614826010b00c801081d20100810b042408401b280500010001c165418000e00020142e610030300079284599401011612181090800002440b030300c030701c400000450030000200b0030f103000120074800c0301b01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 430925395 1250 430924145 430924157
    0x3030513061b2a06050915041a090604030e0d29040b0907030c050f01030b1203030103031806020309040c0e1306051f0c26030112050f030f0405120a1406010608070807 73
    0x419138400000c0d103001000725104c2c1c05810407040390702407254103040c131852107164922080d42104e0341d40110b421001d0b20380e0310182e218a0804c00001d0300002500c50394081142e040032180900d00c0c01207405080c0d010382100f090350080440e01e550740c503985002d001e240f0076526001e4566403c0350700307645c40c1c0300e520014040e09210740c401c00c044d003000c2c80c000680420602d00480d25040650201d48400c090040b980f400e030744004010028150700020b800b01c0e815043c2c00003140c01d450600002d55a00071800303007500c1142d44182c0400400c0c010075010034001009480b004001c0e4a461120004106c0f038490039000b8480000c5085a000c0340c1804880f044041341c85408808800342c48800f0240b110070400f698a800c0c901034800f01c40c9108024500a0046c80e040d0050340c3d90300d10300036050a01152042c012503205020440721030100c1d500340c0d415105c00307031580c016440003101224a415400360004d0300008080782c0704c502098000c01d10505841a42e00c5200281d01c444c0004c03103000ca0700711040000124 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 430926645 1250 430925395 430925477
    0xd0b10020a022205040803010e070201050f01050112061e09150b03190b060316030c0e0609060c010605040e0a030915050714010b1f14030c03010303030513061b 70
    0x5043c40403084148840e28032a070703286040c180c00ea4101c0b01c00751820f9a144502000401086001011040d80001c00744000e010b10b003802001c0140c2c0a04c107020703003070502c141544003041062440d44018000e0a5542c48140c000740d03800d165103580c40c401d000d45220903080c901d81c8040d0402000c940400c651b100c00b55146150b0303614026022032081031110054a9444410308000755440328091405030441c000000004600c00c200602220111920302c2d09000004242034525628101038980d004010345e03c04e641d0f148440d1a890051869400140e402480c103650041d0780040000c41c400b0982c86503c88005058503190b050114050013180d29000840401c51200040d41080000c0906076a01c000802e100030f110001425020040c0240400f03050038a8405060a80c0b14440d01e40080c604101280b40d81410a2140381e2840705001c040c00307040d10b40c40031580f5240450002038034150481001c00c00c429682080d5000c0c48040c440940000d16030710324070382c01c49000308071844086050820182d2025 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 430927895 1250 430926645 430926649
    0x902030c090403030c111b0f0a0807030b070909050702070303030e070815040203060f010f051c0b071e030608030f0a0e0d060c08010902090d0f0822080708030c191e03050d0b10020a02 80
    0x1235841d00d066045644500c00082220f401c114903806144504d10515852404460007062640d1980c01340f020035040c5402e02c08500c0e000b00b1064152134040c900400c101c1e6000d41c0c01484c010300c5911401651044101e0403c035080c40c7c555540c0503a04c21010b4688a4852202820030924213010301c080e210100d050800c0a8a0140d110800d04070007010105103011040e221403448040403074116020810006a0741d50140680c1d4100d80005205d0134200003c86c180f4040030790340c2c081c0030a504100705e8002200305555000b6107680d0004140108084000070703140c50040d0250100ca0703071100c08251800e0020440350300d00d00070b40d1b80300903020340b4945218240d038445d6006010380a200b550744440c02c0002001420600404010400504840003030300b0b0f2412a0f414580001988a11040d0300103100601b01340c1e0380400c000d0325100c01c0402d50b083e0120a401d0a184041420680c0030036030550303034084030400d03400c1000380421a10041c41003003040f4180703050140c55074501002c80016041814104018 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 430929145 1250 430927895 430927909
    0xc0201080c210123010203210a02040f0602030a08090718092a060905030123091033030819050705070905010509070e0307090902030c090403030c111b 66
    0x141d1002881d5441a14040d203080c110002c4c0c025406802a0218a404070101c04100a40080d420320041d0700c2c143d0803c094042e0040285aa40d45002280012801c1c641d182e8050b2406441d90004501c0071603030300c01c1c01a41e2070340800c1c0e0000104548000003102c0c2900800e04c502103425500d402c1c40010741c03200d8208000d10303150508490700c0d41c00340011341400700807102e01c0d89200c20802c016000d40e410728101401c01203944d8480ca10a80c1840040f15800017600d19200f03201e5a20b901e21881c90715040740032402c0c00b07540000c0306c03002c80c07404464003003c00e1504200c01301c01801d04107000c441a000d495809005a442c00040d000b000c040110080c03411410200b00312440c140c1c6482400c00740d4035551503003410b0007640040191078540006200d0b515200703d1258120b181810031052281d00a0042902d0349403a1140c0301945913690b002c3c0c0103640b428050070103000b40c01440d2a00624041c60060004c200c030000d58400072b10f6901014510000c00107040000d0008100c44a10320703041c1c9010001c0ca = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 430930395 1250 430929145 430929157
    0x144e030a050436180501051f09050108031b1005190e03191808071e0605040f05011206050612040507080102090d0b040f050a03020706140a050304060f020c0f0105160c0201080c 77
    0x20001c4c4941c640c0c0214030203102c0c1600801c44411900c0003040c0d4410509101000303501b10800d04d03403034007004201c2c0f045c000080368141202ca4104401981d0003020440c100310300042c43c0c072030380c500308020030210700c030001913401d01508007220400402da00b12400d25603a00072042c0b0342100f024181d4100d0113146c020700700032042d205008114010507480711482820301c00b003540b14a80c1404035990031083c44011010080180500e407801e54105850a031500807299054403a241c148000540755207900380b004e80041c8040c00c4c010b40003541c1e644641c0d40c10003054804075410b4a96005480002c19456418004c540c41c000009014400c064406e4564284000b8060704c201c8280d0030780101d04001510900c62002c00b1400707900030303100c0d0601c0e110b80544603447d101468100d600c030400c440030728a50040180da4005800a40000d0601e0f5480c1c40c4900034880c0032818480d82c0301c4e585a0194003a01504003038420b1140e40b01c0c01640b02c1d03882c4800d8889008490000780490029400a40002c004e00083d0030703 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 430931645 1250 430930395 430930421
    0x40b1803071a0711010f17190513031106130602090303190809061e150a090f06081608060708090c0604144e030a050436 53
    0x20740360742d4800401c0510300d502a2191034808000c41c0d000706000c12400110210802802c1070810b003040c80c81c0051114020080c0885015012008900603507000c42009800c4001c10400308018144802101c1d9043c03001182203000650341e42202d02c5a210114241e80070301c2400e090303640d51041070394803500070b0340100024070b806100070311010080d54203e40c1d400440c000b0503242c0e4019400d2800d00302d802d0010003405844c0c3c4544090f01c0b04c030703040640911268011050303880c50701503401000004012000a901408101d810000c2d182540f09082d0300c070300201c403601c40460b00c030700c5002500504564001c1c428034003190481d000003183c0c1c03409076400d10f50015031203043c0c900703142c400700000c2c501c0c3e007080e0001501c601040c182120281400d800c00d00010310840200c03207110764400381c01d003044180c50707016150403024100d052144510030b10214100e80c9080050303d45404c8a40001400ca81043c46001031400114a8141d00d1010b04003e090816800001c104251100100c1c0ba0010300410300c0508 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 430932895 1250 430931645 430931653
    0x5270c0d091203060f0909020d0305180a060801150c0c060c0c1706010f0e04050703020f0f030304030b151504060e0a032f0117160512011203020d05040b1803 69
    0x1400003298503000b240c600100342c900140d40b604000d1000805003007600052525482d02001d0b02c00342e81c60030220310800d070f890b2030001e0780c900403000c142102558034483d468004880b40c101082c0c081d000100207058602105036807000e0345420004807905045480007402c60840400d0034808684591002d04c0c2d1a401081001c03813061340c540d004c0340800b041001c401e00c141c200400600a45000705040c600030030311000d2240141c1003584503640c5a00c0c0c2440020b00c503200700004506103880b03840c41000d1440d40281660303121950303030400c448441d0048500c41c012000c1c101d400320f518500703c601244075a10245d1158207080c01d1400c161942c0318071407030080e070001002100000045442c2182c0e0391120310014140100c0c0c1b1141101c0c0c512a00c50444c8505020000b081e016048000c0802542d10031300844d882040650350b03081c2034580d4460102400410f0f0a160008a962604111030f21000c0b8070990844030101c0b000e400450b001e0089004d01401407000300860911804404003825810000400762 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 430934145 1250 430932895 430932911
    0x80f04080304032a030209061207080a110307061407170d020f12180307020609060f1306020f01060612050405010e340f030206030406090209070905270c0d 68
    0x351864000e40c0c0101e440b10304028109007114075081003000c1420070b014021a6950541c2d0000380d0b85203004184074000e0b04480d0002070140010005c45009150a00c103985241981d400e141400c0e001c8080340c2d0340688104030000851a1003058009113088080b88064100b071038aaa81a202411400d00104014420700c84d0503102d070414401060964040c075030859881110101d10604040300626842c5000c000c00c0d2400218603012040b40d40481d8100c81d0310355242c101c0000680503000720019441104000b08021a106044108440c15034240350211220f0040310600300c2d007070750070034080d4100041101100c604c5044441c1c01468106104600204a003004a03004c10300d13001c0740c0c000081c1d41e120042a08040300600c00d444011034100e91186c48003c2d400c080c00510042c0e03d0388002405124000000342c2031105507401540340950060070444103041508004081c4810b90050b288200c2c0558114203d5240310810b078a1411141014002150380e401c0c0d0110080c0c11000030780184c503449050f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 430935251 1106 430934145 430934159
    0x110306062209081318090c2106050a020310050d080307050f07060204030507090515010905210303090d0306082413050d030b040e0c0d080f04 62
    0x1031034800c1e07140d44250000424400b00d024207040c1003c11000c00c4200040031101c01c0f252030306907036071000c41510b858900710baa1441001b00720380a4400708004e242550a9000b0710030720f203407842c10780c803080d641c44100c1a980119122020b0585c000308001d40100c064000e0400307020103941c074101074815545c2e01c80041c030001d8100800e000c400728003040010340c40c8040390550f9502520941d12aa940d2900e59503c131240c1c029895000d09040010342c007102c4110000070718010581d580b00142d89850180300041d2400d1804184132500640c40591041d4200000d41c081c03140c2e03c0052042d407854440080856801e83c00c080b60740e805c01000450380341d4400d4258900011425020f104907120380401c3c2c2c12806400f40c008007140035510144a0194040d07001840110301a00c00b4044034805c100c00c00c2c0c503000e4000300290301002d1802a00081186100603200b485420a0031510705a20755034 = true := by decide +kernel

theorem cover : BRFrame.Cov 430755395 430935251 := by
  have h0 := BRFrame.cov_init 430755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 430755395 ≤ n) (h2 : n < 430935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
