-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2196
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:57:34.097924+00:00
-- url     : https://prove2.me/submissions/3f23d2c4-9d1f-4f4b-b9b4-56378bfbef2b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 394784172 ≤ n < 394964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 394785422 1250 394784172 394784177
    0x117012003100f0e01050a0b0c1c1116180c0e040911060a080a060e04050c01080a06050a03052d03160c05120a02130c051e1b0d0e0411040501 62
    0x40c02c0c40c140201050054401291641c0b01141e803024080389110082c01114452509024002046c03001102103405040340d98000d48890241c00d00b280c0085192a4028024401c2442c9a5860b082c0b050054080122406030803102e4681800c0c0c01001c0207209e0105901410300c0c1c85c500302d00700e40e007003e041e40d076840c3d0071a0b0200d03195031a440d080c0d1101406201040c1c03c00c4001c00d20440051b0400f0006101e104a41c4e81001072680e1511200100344082d50041d086400502c140c5545510803031425a001e10f034644041001695100807601c0c4402d6907009031703466000f43e0384c071219840724441c01c0350a0400c8030702000711580c90320050940324401c414114180303080c0b01c130340e2004010700340040c4401480300800081c2070048c0440d045840f000103280481c82040142d00e1000c2d0988070707204143d00241580c0c6ca0504102018000c07941000701d40f107039070300000ca0030701644549040701019030101090700d10140280c000300010290241e40d85840d00b6105c0c0e820185803c8000c070502c002d03a011a4003d2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 394786672 1250 394785422 394785427
    0x312030a060b0c0a050d020d080423120d15080c0108090c030102031905071706040c03090501020705070f1a0706020313050d0801080d08130809060d06060801170120 72
    0x2401014028401d0340d0090780014408240071802810201d05144d4084c01001070703c443c506450400c98640c8004030f0b21901147d02d40020401040d0000c030051030058601450302240300b0301441d42e034a800d50401030780b0554000050a00c0c2145070034020300102051100e8200305590401180d6511404104589410002c6540015214a000f00503141d20800040d000b1540c80c100b09025005040360801254180390410010404d46442031b00d4034510120010b207500165240e2008000c0501700c0b0718000c80815403920319900c0031410a1000b803a01c42c2c49040180000361070103c1c100f1141c5407030360045080d8001c2143c1401780c8685142180c1c807165003c0001a82c3e0741d241d450340c0104950528010b00948111200040c1e25500020b0b03843c142d407031042c120341544594a9045841980458080c102480f40d002d07071900055802001d411200f10003070020713007003403406400603040700e07081e5011500155040c0c0041110030302c04030281881e00359500c002e008080c5964107501d1210704155400b903c05500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 394787922 1250 394786672 394786681
    0x306080604021e18130c06050910030f020408240702070e06041d0624151b0304031a07080106050c15220303150603090210120603080c010c020d02010b031203 69
    0x2518075110074031000c1da00307003c0f60707040c01d03000490300c250b070340504652038801e81300f007c00c08901810a948000c0c40c001c01c01100c80f9a40c810440141002455442c0c0c001e07028440810440c1c8180400301080c42c0046030254150030308584c440004402400c2c20307095400c00e040a01c2004504c901c200d5100405072008503d00c210300392032030840c1c080700e00c08075060300484003803200801c030320500c41040c111106001d404501d0510704002110b0308107010460b004c08100035030b075407080b0174a8100082481420a4070b08060307a90322600e401c00052030780c14075046400c0080040b51358100e1032286c090304251034101d04000c0c00c8600d180c1e546840201424103443c0b0300000811800c020600800c000302819500c00f0601103a103030207800f400d1740c103c00020b200700310f00700450003511900c00d00400f40c1c0c00030070660813030100d0381e010384054900c2d100203078040d503e9075004004280a27400a02c04d18401d1000003d0106e20010002d05060310500f0701021a418500010000c0d83c0c0007031404480280344980c3c036540e444 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 394789172 1250 394787922 394787929
    0x5060a020906090a1409180a0314090907020a0303050109060e01091805030c03070b0105180c0c070306060b0306100923010507060c090e011e0e340306080604021e 71
    0x703101d04071503112440300404503481ca6180ba030010060016541c2c504240c9070716141d50f02c00001000c500070315a11462340000480e10a4603107101c0c07102c40481551034409103c0106100c20380880302d59001d60711508030001011b0b803602c9583c1c010280d826040001e182031400300b60b12448180f188024094a41695035007100700f0300c0d0440c000c1640007013140d1740c4a641c0d0041030f07107940110390159094440d48000165a08048421207980a04e400444465542c1c8805213051608001120b441c2445000400301c0001c086225001c00740c801c00c15099240d1810bc0200b2140c0e50516050604100c1d190b542000380901c1244441100c0ca101c086400c86500d12100482d40c502a8a00140c8650301342074011000c15040045202640c00c45585040e0981c0c0390b1a1680b40f00d00d85048800c01c1d00500241000201c1c01226441c2c0c00402e812008070420980c08104180035007011350380f0300c44000e10341c004050980c041c0707c0c1d540205000380107410103140c03c2d000148609451450004016060b4002003042d55 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 394790422 1250 394789172 394789177
    0x406020a021006090b1002070e040807050a0506090622150b06070b04080406090501050a0215040816050c030606030f07031502120408040602060a020301051c03110d110709050405060a020906 83
    0x10b0703040300c2000b40c00d644100d5040506213481000b4012944d00e030391500010301c0400d14400303a40c0c40305c5103903000d91516624852582d00c100700544040c0030303008400d80044c00074494640904041d1005102d42d003440405a01e21003c4004490380803200d03400301c07000003a26012401803c04110704c00040c561030110200302c0710701c00c20354001e0927030300034000700010080050064400c3e20b1032030359070018003910340005640b244980201940913a005442411001142410023030740140709240f00c1d030400350744850380d1400340e10010701214503800131040e540c41420304200340d9074088002c6004040c3c40400c0071031035807100781500010700400c60300d101d15040402c5580441e04542581d1103486914605400d00700f0160b00980a0400180195000b0500c05800780c001d5a0584000510068406075040d64055002c3d8800d40c0840520046d0407036100240000e12240701183d0850300c4060404902c080c3c0759060516a420400340c1614103c00d00000c16000074499030301c06464180183d49903581c0c40010310b03d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 394791672 1250 394790422 394790443
    0x6050d0807050709051909031419032f0d111b07060507110607170c15090106080d12020d29120c210a0b040302120306090406020a02 58
    0x44801850001004552401099624080c5094400c010f0311944d8080907510252405200f5540592220400504581c4400443c0d80310b414564503005207003205150603000024042c0c81006001108100300b40c05026461000e0511142510111400e980b0242082c1c40f1000b9580f41c84004502c410b0051001d074882289990b40c0a80e25485210340e2140302c000c102031645020039406800400520640a2800d0321141a40941d003ca001340025007031280f01d40203003509a41c071b6803040303480142d900b10800040600710300b041c0240080e00081551502c00100140210400b6232408004112013400816003581451452600010280c05040da28001e401007440c09000c081c540140c2c03245850101c0b5002e0461110a10300c1c003d114180c2041014211040030f0141158001e42810400c4d0715200362525184014500307401c0002114800003440c0031000d0b81c08880e0200d4042c203000500d6010031503910421981c400c805e1031840c00b0004140506400391009100301e4001c00c0d2048454000d0106841d00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 394792922 1250 394791672 394791679
    0xa18080d151d0417040b0406080712050a0506010318050606011b0c090218040c080103060527030406020c032109150c07150507030203041211030a0302030a120c081303030605 76
    0x41c0112110341090320715003640c0840c0d961401040800c13542070550203407000c4601d240941c81c10185803000076500c1090081c01207080000040100e200000c052042d68020104050b00085a02e4884000b40441c1e41e141e80a03041c5c040034042100009000146041d4450000c0c6450360303140c220350381a445031404072030000b05081d80c80d08010904042a07405025040348540a0f0701084030720b03106010485088424420020710160014800714003e60002600041150310010707003d2030b854404032501c40c0d151054421a0400141008a694104030b04041c1c02000c4014069052000440c028100b0140030311111200c40813031102000e0755500c41c100c415031105024250340f60106449240c8885487c080c060310a1150181c207113500f4410780982c1e01990385500118a090b0900480904e111001001100c40040302540380603a910213000500f18035100303400231625102d42d5440070302124400c1150a080034540351150120316070085c40c50341c1000b04c100e842014041d0360b08045004d807085411942c2c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 394794172 1250 394792922 394792949
    0x902040b060a020102180f03060417040f03080717030c0d0504020f0a080d110303070906080604060b07080a120903050412050c0909030d1406150c0c0d030302030a18080d15 75
    0x2d0250103400030540d02c24414100b000d04996001002210980c841c3c000ea0194090b900007000200501040005000c1c01014a814240e503003000b004d04065079041201c40f071401040c00000c202210310511a0110804011800d524149c40503404074040c80d800005440c0c1c595000c202135454405001c0d0340d0601c0500105c041a03101d020b5641e441c66000e440344000340c0d00b154041d03050b00c8084280c9000b4400c664030f4951035403600d00102d6202c3c0d00030b00350070384c032565648000070b03080c00320b0000302003140c401c1c41c84039212025000c01a2101a0780c2046520980c100101580040e03480012030303080c0c0309003407800580c3c01c0d01800e11358070342078032004181e0300030780c0200520201c82800400b608011800300001d0010701c1f68003040d0707144144180c0c1c40c6030b000420350184580c03011880300a0600b01c1011001c40390008207400c0061030800d10540d050340800e900200707004001c0407a0090402000b040d00901c80c07031141d5569403c18600c00c4400c0d044400d503036100d0344020030841124800042090200820 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 394795422 1250 394794172 394794187
    0x3070803072622020108070c032001051603020f0702310b0319051e101e1802090403030b150720090403020a03030c0905120d030b15030402040902040b06 67
    0x212030360b800f510940045452041d4051100a84004514410781d06941e440015120090140c554050009084081c4200d030701e060144c03000000850609010041d00119582c180300d0800c58910740d12540040805004100003445100c000c42201e0881d0703810f0f02c9045124007a0030880084200c20b0001001800c0e4507920642b03c41c0e003503003214440c1e070021403c0e510240d03d10b01c1c4880300b4402e44d100c0140039030400c0308403000700000c201d041c00d1114501d1054842034045002d52204070b03001c0f10b050300901c3c0d00b0424520300c40d807414403400000100c403c3e4203030104040c1ea0005100380c04011300040c00c0503180c1444140c140c0303584407500d00c01c0060300490740e00c03101c161802255050076a2000040040340c41d0718030b840341c036204518502854058020b4190844a40ca01714042d1441c844a0300078400d00d92400109600c0d4102c004d8881c0001c10064522400e20010007800d031071903041e00500c5040e0414551030440c03840802c490b0400d0f4100d40000e48805030748040380c044c1c01c4030303032507542e0100c4045102ca = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 394796672 1250 394795422 394795487
    0x240209040f0608060a15090504060207140d020c04020421020a080f011409030a1d030c0901030f030201060b040537030c0e06011b260d0603050c0906030307080307 71
    0x102c0c199194403082d250a5034031965203108540786000c4c81040c402000c4001c0158004a9004d55000707070041ca00503251007503640300c1c083c0108001d65400c108d41d00c8481c440c02030681c103100c400e000000481d13041d0710341483d104034244d15204000c2003140340814550f242086540b09030707c0c40010180141610039484104070400c4c000c10981000c40c2c4c00301e283d000001c0c808980401251003502e01501d80c3c442910400c1d1007103520001a41d00c1d41c1e0075100b1048190025035070650018001c601c00d0340b94072400030040c90000e096964550161001c1c030818402403000f03642c1c228154007030308c0713401c4d0fa4040b8804204980e200d827008940f901907686643e04801005200c00881100141c40c9001c0281410ba1600701c011207862445151042d244101450301a001a1400070702c0240341518a0550b00641383d14003407013840c6d0f800f80d44541d408940d1441e082040140c1401894910346007216800800d2030580037198491007031480080105d2800000100c045002e980a0407540e038071018012245900d51804 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 394797922 1250 394796672 394796681
    0x609191806050117010b15070b0c0715022a06010b07020d0803070302190203040f0b0f07020907030507030617060402060a09090c0306090f020a090506090109050603040c0501110a240209040f 83
    0x800c8038179403e1040000c00340c2000801d810740b0100114050340380030215100c9010b20300e0054445042503c003000460081440318141300a08400307100d0050b82c5003515410f40c03c090340755061030006128007181401441c04007048060454003400d000700c1d03850b12144000f89031440c1c5010000c0c40c91070040240011154540e0260103134103812920300c09120781c0488281d030790740181d1050713910b0340f13031095000d10840c6c040c003002d054002c580f1400d072400c1206550004203625402c460a9000035a140c040110065050090400a044101c28600c40d0390f1198980b176103a840003040640942800507181030383e18400c444120050100d40f40400900c000104018084e01d0700c0d106404446040840713038100407103036200f20740181030785403105d10501c0d190401784441a00003900017418072003001c1001446031030380d500451046100304801143d613810a00050540010f2400012550348070b41800000100c8020107054040074208501e40122641d40c2400d020388035000519400a06240309c080c29050590071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 394799172 1250 394797922 394797959
    0x1113020313021009080c010f030b0d050c1e0a1401170405100c0905030606040f0609140a1b320c0a060617030d051e0405030403060506091918060501 65
    0x20f440b160030525100440e0324036918040d003078903908290081713002903001e0301c0301420011140c01c0c0411030206400010303083c402681815221501305002800700c42c0307040000e10244529a00981c40304502000115100180500410980112645544c0183c0e0f001c0d025840d015409103440420628003490711503110052440a02d0783d080c1401ca0302e0007143c2c0114080400d072400500100708540c0c03810108400703480c00c0c5145070321080d038a440100d40040b8601600e0b44e01c0e50340740c5075100103040850101e0202c0b4069001f24003440c0c40e48810f00c2c00c10740e03c20340e0101c841325a940c20076890215a0714001085030302e81c10f0382103003150000e0381d0080030b00003150386142c460050408025072075480c42d158000741c0d40c900380031105030010400c00c842c00840c0d91025401040c0d10301d448001504c4103884039461941660246d485601c0480c081041000354000c59034012026141110542800310305480ba4465551f001400f65031034114025809043e1100c030310005820074418000d95940d0740c510601c05602e0300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 394800422 1250 394799172 394799179
    0x14010c02030a0810060c08030a1d07060e06040501081807050d0f02090a0606080a09031e090e07020304050a1a0918060f0312030106030b03030403080d020307080114030604111302031302 81
    0x90003d4010030130101310400721151a2600030304c02110f541c0d00c01c1103500c020f24034030800c1e590382e448201104071201c1200d15111110024040b013814200058404158001001e10465081100340416680294010382000c5811042402050001d0b41c40781082d40725040540c1144090240710b0a0004020250840703900170b90b0001802c0d2919500c2d0340c25600b441c0035107408200b961000c210122000e50010409500074500202103200c00c1803090000c40512441c0c0c400500104001c0c000c2c01c0c1c0401450340c000c0d034075000443ca018070700742c086103d14806100b02003401c80200110f00ea40030381801102c42d4072200400215526039116011008041e065039020700885074100c6411440c1000180f005048001e01d4595040da072800074100c001d40013501c5910f406000a101c00400100305a025140c6503100440140c0c403464810780c020400305d016841100047c00806004080da1400300c0c145070010f402098a0320030544240c003080310011f06081401001f0310000800000b810202c60f044c0d9424402c9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 394801672 1250 394800422 394800437
    0xf05060a1a01020a030e0301020405041b17010f120f02061215220e0c060309010903031b1209081b010e010c020109030518010207030c0b0a1808071214010c02030a 71
    0x1000d10428003079150501405603116020340d2010034090600c600821400030005894076880c0c0c00803505032035410300180d000781803011050340095085040c40248000784564a0610743c50018014009116480b8000c98080311103440801d005c000b80444600c10740103010207035100d80c0320b1506005110301301c03000348c0764141d25030a042503441d00320109140ca0b440e65003e40c0207000300b030010500800c0f0160a0880038851003418010f40d0312030101441c881c26842c2d00000b4000355509029040c1c03030005000403a502d500c0b01054180c250020800004030100b9100007540c0c1d51140303000c500ca40b203008803083c52085000225514004150003e1000c1c140c6400203001410041c0710903801e84c1c10404000b8081181030101c640030b12601450322041e00c1e014030440c1c0c592a940c1d07e807901c0e02c0c41640c000c1c042c40140062891000c540044240589070818507484442a250801c5651140000c0c01105070140c5400505001d201020101008081c00840204007100389000e01a68036800046000c010070000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 394802922 1250 394801672 394801691
    0x2108030c03270703020402030a0b0405131e170705070506030a15080a03080c0a0e06070818010810090c0e100905031203040203030306061612082a120709030f05060a 72
    0x90315200040b10440e401460020305650801019400003030400400319034800100e003040c0d443d4080c050044000fa9440031150096040c68a80031440300c0c80264840812152040001c1040300c0140070030040035032140c0c49600a181580c00c05080381d2003d54086004824407420001a81c0146242c40e40c5103815070056544425403a114a00120040d001c290038600142c10351060f2801000000407600d02701611030b94003000030303500b600004820344d00c541021034005e84502d2111220303900204c090800e00344e035103410b421000c200b2080d4000c400c049a01c5803200c40c1161b002d41c0c1c0412070140000d099089075414044000d007440418410340b80312b8829103008410018851003244d0050390040d01a62075940c5950034032030198000c0100c00900c100c13000a01d0003250b050081e22400700e40e1640d80c40300383d04040c9580401503103102c0a12301c0e800409107540450110392011202d1804110b055100c0660303643ca002e43e515500f60b8009024803000601400810001161143c42802101800c118640380c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 394804172 1250 394802922 394802971
    0x905100327080d091a010803070b06010f0c05030403050604030305010f0303170c1b0106050112020f120c0912012a0f03110f0705070e060409030206012108030c03 71
    0x11040840310300c09a403000081c00d100346410034600e11501a0341014684806081c8120440303000c401c041e10300c00300b01760000168410f0340d40c20313a0043c0301000045050548948070440780302d4020302a04d05000b101143d00350300d5401004800f00c100d82180030340741c407a80d503801c000351100c00441b02100041e241c6000810100503c2c1852010b5907056510708880e10905036a28030b6040c0c01400264038010700384890703a91940c03241c540c00001a03644002103196440d05001404050000341d903214510b00501003540c40300c1e100b4090b101004803492413501c40342c580c45010100383c0310340391516400c15018203001200c8001504510051052030082e44c85a4045d401948881040310015000141200090600303003842a0041c90f00b4904100885182030340d2556143d04a42c02004111295001008100a14101c00340c415038801404e940c10b03c211140795038000d4640070140640b1901c8014000c600a4884240b0181d10007940d0048442e5503a0411000c0c40e000d581089030848496407840c01070210f500c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 394805422 1250 394804172 394804181
    0xf0b1c0b011a0a03050720010b01111207170409181712070e0a051002210403020901051509090a0b0f040608120f070b13020901090213030303020d020702030d09051003 73
    0x11003408406003801d60361507048002c5d0801605100400003443c403041807421351200b4200000e01e045000090f415070b502c001524404a1a42d030700ca580e003084050304207118880341112040c540c8110041d03040d000d956100c0c482802281c01c289a010300e04461002e0591a40d060805010f014202550040700b001341d00c01010300ca8003011104192188001c5404070f40210980416007900625110708035032203070041a11142c2c6a8021001a4002d901410102088050284040c0758002c00e003032400d41190086440743e00184103860150a19617804d042743d400c21002e40795400801040c60f007043c28156048005482c4201100b489940c84c40380030140f074a01446090100c40507240540350780c1c90300300740e44900c6800c90f00720b1102001c000c00c203d0000803d02004c0603c5140480518000c207101c500500c00b02c82c00503000300303188600c104108150303810a4450001100d500d40b502695462800722220064024024020342500c90310400700c1201e9004200001580c1c4d06031501c0300402c007a20002c80a55 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 394806672 1250 394805422 394805459
    0x8070b040512040305152a0a090509060a03120903080d0203010311040e0a3503100f0b030c03060d060e0c090c12011518060806150901080601030f0b1c0b01 68
    0xd41c414403032407807500d404c41c1007154800d003c0c000d20300304804201e4582020421f8441229101140003504200d50b40e007100c1900f01621050320607071014609100402c9000384140409080f03d1200c0190701040d41c4544081c1000e0755004018039114180349035400041c0d002800115103100400c02d2900c8a0308092041c01080c0baa031304014075841c0c0060303c80440c200c00c00d0420240b04d11300311030307080f008084040240e81441d06446a507556441c2400100280315030b560017050f481822000c0800403240307000152a00304501e0214070307a072610388400040040510032402070050307041011015034074402181035009403a0558840311142d030740080740029131051408003e00701040b40018070945030460032070480c8482504010b03404e11650707413087c05c0441040c0d11200002c2c02e820b0401a640c109074000c94084103005c81114141240100040c1101d5001000c241c10150307501c83c2082c021009802c5400507440203000c03800c4a030701c103845158642c50301c00f40c152440d000a9000140074072403043c000300c0c603 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 394807922 1250 394806672 394806683
    0x70314012703092c0705191e02030403020604030b070516050307031706030a03030e120313112409031e031305090903040509041a01060806120c010504061202040308070b0405120403 79
    0x110812181105584002d4204803c02c40181302d44d00885d940ea50407d618104692a01e0341e015180000031308600789052082e00854100f40020001030300c0e41019a406d0f00d034030003400c6020b5601c50781e04503154000c042c101c1c4003030f040040f00b54040c8a404801842154000c0d602c5034910400c43c02122000007040d280a50103510003c4d00e840828440d07800b11722a17401c05025523070449242c1900c148550000d60b040e01c01071101c1e24007001081031411608103a040162114400042c0a010714030107000c00076000d025003e000104201144da041c4269a051022102c41c21140307051100031390707034035081940ca5105010300b91001240134582a103007140b2074904070000f90f2a060500c000e010f06400080d02c11940d0f640c15095a54081c0d04004045018005a640341d061034034000701040003a600403031090040342c000940f40901a42d214044805642c01130401802507000c8100c1c410080c07107142c2c0003811802c0041861300c02c00c41c1078407002c4e000307a000e00c0c2181e036800340c04403204109216900c001000b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 394809172 1250 394807922 394807979
    0x12140a08090c03010b100c05030f040f060906020105041104050c0706050405010204290304020f0a082a010f09170f0f01020310060212040909170d090c08010e07031401270309 76
    0x104901c6a03424107d40c42c45007042d241080f00042e0741502503082904109025101d40784284211030307000503a0802400a44000d00c03080c02c20380c03620300100d80302d000624040c81d1500b0000d0011788001c4219810151b0000c000c11040c0b419050050003074101d8001d07e54140982c144040c0c188500743d410321000c1d5007108489103185c4840e42000000f03a40b030703034900380c1010a0b454000390840b4203100701341c013405402a00486521012145c803524820540c481ca05000c20752843c1c06620364881410410303101c9001d064518458107049640c906851003102c0d032858410750440300075080064000e103008a82c6010080c0d0383d16158001a82c5404500302d502080820070b02003000341c41c0d5150080d04615001c0e040400c00403501540700c10030355010702c000c0e00029840702e03a04c00030040d01102c0000280107110082003080b803408000f80d10750b00244806000410b41c41400c20104900b9888814995903501c42c01445604402d901d208810b1050800d501043d948100003400e410500384080000f4140c40701c806 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 394810422 1250 394809172 394809199
    0x8030f03130f03030b01030f020f030f09101d0d090303140904060b030103110f040c0c06110c0106290313120e130e070902090d12140a08090c03010b 65
    0x2002504010080521914905680004168072000200c040c0d80659400304552070715600141c2541c54034403013101504e10401c07400c00b403a40d00a0640b0782112a1040100c0c0589803400e9040c607101c01001c0034000039241a80e51130030814107180100c0e0344036a542c26200004100807090f03403001e140c0e10bc0030f40800c42203d00425250000e03001402140e0005200054064843d211600b0540007608111422010194911000e117416407040c14080c20803201404032134021507008161040c035200040c1420740714800e01c4410041402a90f892075010382c001c0142680d00c100801154901e80081030500c0380d4001c00e0341811943ca02142c0c4140da030071500381843c800c40d40d00e04004940c80081d280030054107840f6240696126110300203541054140401d90f240b82011f030318101f540c0c0b51b1049550034810400000c443d120700809001081d00300002003840041c000b801e4404400c0d03000c8c44010140d0000780101c40b1a0011310080c0a42c0c0032401300e404c140c80f040103150032210051011540400c81c4803000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 394811672 1250 394810422 394810447
    0x120c0a1202090604022a0304030b040c08010e011a061804050f07080f010501020a030f0302190908010e2409120304060f050609100b0a05040503010614040c020d080a110403021306060807090803 84
    0x7000d680d4414041301e12301541c0b41c443c4100044291000c9610305155242080108403d0013400b6a1442c950002c02082444182c075018141c24800c40301d000e039001013400c4042c100119000f810549024005210525182004505650f000c88503540801c811001080a4401c1101c0a5040e5a030680042281c0744a03a10184c50b041403203c5100201502045140da00e03d01910910540b444030f900e44d6210039041400e414203540b03200d1070000c0103500c540030060810341e141410740400104955082c40d01c0d2a40e044041c02d00408030440140c20a000090004120569001c0500300c11180d0040005498140400c03030b900700d0540d03140d150b500c0552001e00050b1100002011500d03624208a850980c0d600d002c2400d4410540c08000203400361502c2c00c219080501500720b40000074405804103148031040a072001102412040c0d4295482e2013401e44040854100c0b8013541d001000c29408819102c0213a0150980b4020600000c000750301299505010b100100c0075a20300c0d4002e181005c2412006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 394812922 1250 394811672 394811737
    0x40209040207300201140a11130b030114120d030506060c01060e0a05100605031f030b130c06030501060c02040f11030414010606021605120c0a120209060402 69
    0x400d50069080140c407000400115901c1c80100d1945941c01010500001462454070805814000c0d07905003140780d4255101c44401c564040a01440020498081404109103008040c0c0701c00039000e030110b002c19038404e8400610b040354884014400301310380301c03000d00103200b4844046041a80c420494070b202c0034042d401c0250312140207008581840d1440800d1800c1d030304107074050380c4510000014825020300d40d0080c6c55003c0010242224240d20f001e80062040c80001c06040d0302c0d42d03410500300c010811041407040215080b03401540340341000c002034107441e44c60820454440d40402e80005144c0d00074003841e41202c0c0e040d21200300d068166000c0c030025080c080d00c07000310a0f80d168002507110402c10701650169004800e41c0381218007c02d401421960203822840a40d8402d090112404e40d80c1d200007420785000341e815181d4614205290fa10b08070f464095913500100c541c202161150841d512020b8042c001c5a800401d44c0710320f424001244142c00e602401c040340c0064820031500540daa = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 394814172 1250 394812922 394812937
    0xc02121801270305011401050108010b0d0906020f0a030b01030903021e071706061008090d1101181b051537080106110d0f0e0301060503030408012304110402 69
    0x500801ca680d084401490401e120b9424a03440303825044188184034003441402c4402c0d004a1400c0c4240d410000041c1510310144652080440c00280c811130103950364020085040d03010500b9900d0b030000106210041e081042c512000130700d00601441550f11a01400070b090f60140c014101e40e42840c003020184031141e00342da04003489851000240813401d01121032261060401400d402d041080070001440310780d081e003000304040d036428003801500100e02c00c003600d420790038640030700c410301c00c2d0740c5004d040301a01150940c48002c0d1100c00388010044000d04080c0b82640200203982c4450030008205c0c40c1c2039001c070410005010f034083d07030129a824511250302d255400e40e804003410910145410001090070002440000100400c0f50420156200082c545001c0d04400ba80b000004014442515407481004440d0340503284503203081d44001c0c05040080d003542d650b9600c41ca81d083c040c180028442c0901450000c1034100511400031880c010380d4003441810006a2010810003e500b0500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 394815422 1250 394814172 394814177
    0x901030902120106030c2907020109120b0405120f0708070302010e160f060f0f0e040b0315040506060a050112050912030f0a05060303191803060617010c02121801 71
    0x2900c0d440075a84064803032918904a400100340d85046140c121101040d9900c60443c01c6068008160304401c20111441041c10700d0120549401940c00100d40100d4030340e00840108429158000c240030740300500718411800b90b82210305001c490020b100b142e215441c035010001c50b05000c424005010a03004148540c0203200101d04d502581500303070300b0810703001d140303603000c400b0507004000f07030302924803036900420300ca080c8254850014036020704000c07503c0310030004000404c51003000b181e542d40d1100248080c0a0115001001075054000720342c20140e8080d1800d104003c00184185090038070701342912010f82d200c09000d48000c210f40040d0101910606c41d03802903556090100c4940320180d8800c1140001c1500c3e14140001040c0c102c43c40500a1070090704204021010341c104030b02c00200120711807404904d468600041444c1ca1506500000c1c04941060300000d0011513050641e166110203c2c02040428006001669a41c05101081c001c003c0c041c003480d01c06c50704141030021482c0060 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 394816672 1250 394815422 394815431
    0x2206060902040b22030317061206090309040e06040309170309030105151906050306130e121b1903030b030f010c02161205030904091a07080103171e090103 68
    0xa0404100740c0c1c010341c01800c07011001090481c07a40302c0b20002c0c6924900400d001e08845801e5482c000c000da40300c3d140c2481c101000d080400c0268883c0240300c00000c1000d010780d12a0300b0403d40e82c64a9034820340c141c911a50804401d0640444085540ca0142c0c1c0d154aa030000145405003480da07592035040304106502040c0a441c18548003070082c28400d441d024030796089247c480c010010401c4a5496500c105020184c081c841c03503800000310303600b000302100c59050b0741110640e00000b8259100807111a4012910000036041c0c1c01d0000c2c103c03608181090240e00d00c0c0007151181c0c2c0308507401c1e58084000c1003080b1070000c0b83c042d5100e0600c080002d07056501e100c4010404a0070f40b00701d01c41c02001a0b00c8603e403141950410000328014040d05980760b16140a2511455985d01076015128450342e5120300307580411401804000103800500d142032040d01c5c007000040e000007024401600c0b044440c01d18000b2222083d4101d0342c0014000c99100035600850a24900c01d8008402c0306062540c3d9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 394817922 1250 394816672 394816679
    0x40914061f0c1a010608070815040b13060b041d04030f03090215071b15120203070504030c0e060102060a0506031911131505061204030c020103060b0403031101050906220606 76
    0xd8041643d104401001d500401c2d450300c20300518910b001800001040301d100300380309540784420003904c203200302100c1c0030034031050050009442821304e002e184079131403512400145828640700074100725505551a45004841c1d0010050003c0007118010f00041c0988444801c82d0700075841080541d00280074050f100250100c00512903002c0e07141590482c200115a2408410740ca8031000039141d1101c5500b201442050041d150341d070491021301805401000251880d4404d009440095401a01c406090766648004100900d0300b665640e005000f11400200d03003030102d0240038000c1e00050000d188542d0106045259640b485a003180c0800c540c14048101d5030b103500301d0342d0451007440b600081c6007108000c0c12421810755171005014200c24002098103001c0807110660050309070a250110091510048004000d02d80080b018000081804002d165002800a47c00c55119008008503181c0501840c0d903050203c5104c50030040e40c42c40c01c02d40f0841c0c410326400e550301c160008140d40d0b84 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 394819172 1250 394817922 394817933
    0x20703150e0c060c0a05010b01020f0c060721050705070f060918141005010305130b0c0d020405030304030804030b0f040809150c0d020109030f0518010516050a030302040914061f0c 79
    0x4902c00c003011a60080c00017105000d028131801d01101c0d0f00b4001043d0200c0c00103d115100c035000480740e4810030f00403440000b4040403049000041e4400a1640c0d020000c03101e01030000d8124880584440c8185040402c040c140c03089510156415070302e41c082d03190b1801c0f5065103003458003004c010299440e00d802c40355100005440c203028001d2618001c2e001801c0800050171908002d01d1440c40d000815103000214989100c0650071800c2040c0e83c99880c08200001e4001e4801d40c5d01054040c40009400010b00c002c11024109880c840d48805103280c60348910020000c1007030b2000381c02c4503000c20001c10280303061408050504030300d502850402a4290080d030030080d007100e440e13003d80d4444a90104040d0311040c2e1103501c40345418080e0070310703403020341072220500054211414408001103002c0207a202c80381600c5895486011500c00000c41d10340240a50085e204e924400c6040079245402003000780c0c0c10502c1150b001c4c0006d07840f40d902141d21450884880012400d02c1140d0150380003084 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 394820422 1250 394819172 394819177
    0x9090809030a060203090f0604020603060d1406070206040c06022a0d02040207060209011704050c100c020d051614060d02031503030705010218092202060c0f060108070501020703150e0c06 82
    0x600440300103880307141c00101035062030b201d490f5207d5103801c48800c200050351100c0680c0d40040c800d03546112884c4192070039040035103d101d1841c9141c45603004124040d0380c00121076205a00c0380b41c420300d5056480700d040e682c40002000600c2100010081d0000010190b203020050303079001000a10154043d8005c601242e0100b04141c1d070a6400040300d081550f001518220300c1a5108440c205900d46034507410b480355012030085d0701c642070100c0c490000c144142e0380c0b0600320350000c180408102840c94050768887d400494250b4843d001e4000064500d803c640f014400940030740300ca854104c150300c0c03040081d840104004050450311810700100d8030104080c12803148200001a583c4003042c1c40c1e541c021807140c1c51148900d0100c02081321820301c07080d0803150005c0300c0d140d00180c442a40f000800394080c00f11080d80c14410f82420540c00c00340010018100d0b0382d840103917051503840c0c034012602d40d200b80c0000350090714080490002482158020304030242c01e10180d60605000800090059 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 394821672 1250 394820422 394820443
    0x31606061703030105012001060302040c0c170f04030314130e0f060603040c03020d150c170a09051c03020c06010308091c0c0b09010507020306011205071502070909080903 75
    0xa5540e8542401807400365481000044521001541507602d00f0700020000d41c41c0c640b4407a1240c07100019074610a000b50465006542e008009121892141c2002840800b07820402d0b10203034110781c2442500030500d4100c4100700a103441c2c0a04d02030854509a030b650407500300c0c0f0641264100300d883e11004034030f1034010242440c02340d00842c2d81409a21035031504d00c0a0901841030340d0402c14000020005903180b82260790540c2d2000c402080b034107000040d01c901050074401c03141065640d8825030b07404504505202000414410580c0707582c4014000c440340b01d98000c2160380214000c90800407000550460f008140c83e0151a091000380081c0c1014420f070b0044800fa00041902c40e80e038507000144186100d50094000b01c202d07000e469003403d4518602c86d46018060008690038240d1283c401c032505035401504507820b03565a62242d40c00c60746100707400d98284c010501c012500b401d210b6581e010000365a0b00405c042030400130310303100400d4890001c031000f070710030444104252130600a00801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 394822922 1250 394821672 394821683
    0x20306071e02070602210d0509060a0e060405060f1b0409021305010519030f090c080a02040e0d0804150f050a1e06050312030a060f0315180f02120316 66
    0x1542041d06011003a440304540754019034010103828000f6035800244c2c40411407003000d00c441d4540c18030281c500d10b4810592a010303441d060104105000300c0c0010403034040c0740c4074001002209400207800e920744005480081864012102090113041c0d61166036070454210342e8800c10030f03003510b2140400c0e039021340e03c040c0d03059030041046040011542e90840040c40c003070070a00d1402e0194944081e00110074000380060541d100030500c14400300780d1000040e00c0d403002c00d003110a41c031120642e80d140002d00040344140d0074152240001000410b14904c110741c0b945401d0034079205d642c0d4039080741800340c204d55609941e54000001c400d4a6000b00d50080054410021302c41c4090925548502240c0501108460400d1360030461a1400151403c1481c03c0110035500d03616201c2402d009004031794000404400c00c0d000200500c8451044085803015074082001428442e030708645a040329050058110140c40c0f07030000140c242400840002400301c4103a138034113600c039120301620211600041c0c81 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 394824172 1250 394822922 394822937
    0x2030918010807051002031c0b030307030207050901060e100807171f0603111c11030403050d0b03070506030a020307020f070612150506091002160905040b10060203160302070302030607 81
    0x1e4a0b05200030301c0030300403c4e0303940c13000031840a0000c3d5072880b030381c41c1c030141d40201e2010402ca01d042951203179405440090a6a82e0340d003060800a42e40c0da494000e40c0c1c404c103019000042d9080c01006882e005650281204000807541942035810580040900051089082400581c00f1440032424070443d80b8100b0844420f60000c014240d65069800c540141440d0103040d07400c01c44500c041e696500500c1000b00e901c2030b0008080005081d4260003809842d60200c140320030160440d000d0606031803e80810007441c080d42007019501c0c4004e00c540394000108201040b2058040d40003160310080c21700460340a072002c011880e02c0e00107103a0100d0001440c400d84250340340d03418041d0250710f05240e132481e6075103424400005c14030f104812901d8495444001c4108100e80280801c0c0344a0150400c0c4402c41030b80c0d940c0c1c0c04090030046508541507090b14000600d011440740c00300013a588183d000b1070a0500108403451200031900d415000c1d0703c40c0450000040e5020030041740310740e100355100403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 394825422 1250 394824172 394824179
    0x609020d0207050d08240102031603020c010210020702010e01120b0d060b0f0102030c0705010e0a1508010510030e06070806030106090f0207050f0a0305030a0c03021b0c10030b060702040c0203091801 87
    0x2c1c203000000c00d4040c200000d28080c401b04007101c0103200d900c01ea46d00715440720381080d00d0040c0e00e14800c06030222850883c210103182415001300d0090b440c00c1081c1c00740c40c6a20540b80350103080b44541e060090200c1e0b100d4407035044c21351090400300200000d01c0b000143c4d440940c80001c41c0c0024008040b6045901ca00542c4c1031802c04203a0711090003800e00056041070407030f4400c581c0755503070350042034100810044c280c080c3c0c0e500c6030040d00080101c03019100b00700c50030300b0000b00244001d010f12030144c032030303072100112061080c42274109420341940070300510384174460300701c03031007940a07000f0b40d4159294840410741e0780103441501032008a2407001070f50b5102c18640b15041c002c6074490808150000c100200c0420307000800c0b0303a4450343c1c10f003000414011007501a0024040d411b00c01c00a1440541c420104200000e245481080200c1e00180001d918210850a44d900003c6403504603a050001e5001820a500003050040c3c0d90f0041d86e0038500c00c00042192030074036124203280c4610590040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 394826672 1250 394825422 394825433
    0xc030712120e19050103110c07030210020a120c03090e070e0f27180c0616030c06090f02041d0d1101060312081509060117071110061a070c03020d060609020d0207 71
    0x1a4281c887c0c50750004d09004020651300d448100c1c610010f4056410604042c420328828000f2410b142c0d401110123035074180d118402003004454050840100d480f6100c0483d0450550803c18850415030b07550880c0d40c1a41424400c15000c0202e0550300541c00488803003444451a0300004400e54060003800746240c50401403040c508030403003c10440c1c010304480d561988482c03003114003a00c060050701985d100075107000c460030141c0300e40c081c01e6030b8030700f81c0203400700480c4048110302d071402102c0070302c0291003404141c020601003200b5010140d224000c50b2002d20f0190840500d042c00c500000603500d9646e80f204c5d040503040d00854000a0321400411804200103402503c800710705445101181c50101c0000e051030084441c2003911841c1080022803041c4100d140202c403900c098162180a2100000807000d42641d004a41c680303045203507150074121161041d42c0e48a500240c3c000003092854003440300b1300443d02800c0e41c0c1309450300801b0603903214034001000c0041c4007020040e628040c40c2040c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 394827922 1250 394826672 394826681
    0x10e0c0f040e0307030c0f0605040f0204150503061303030207080c0609070603020403080304030806030a0c0b0309070e4f060e010924020409050c0c0c030712120e19050103 75
    0x2039501c140c1c074290020484090000503111190351505204c85a45081e00b44000032214640c1700a000303909003000c1001300035801241594150ac29901441500301004034003138511054003403250183d20010014080c050005069158140130381801843c0c0b642d15182c0c0c05d02540324129000c6644d110805210020404210703280051841c0d1400b14105819540e0724003541c800600f014080280d0b080100d85281c2d400e02001007030300d6210110004035551031030007105c00c0e08226841c10060040b8480021205c0f486042e440c0303e07a040790030315070070600d082014184042900c001d41c800c850302c040a100491780420310b1074400844e0136a441c2c800d0303003061410030151101c42e00058810f90420200340005000305a098400200d140701d40c1ca060b110300d007000d9000b070040d54003e0129500305020b001e0100240001000c88220f05000d90303004042c0b42c3d0515903512a1480b443da25403090410f1980070030400c1c035091052046518083c2e0300302c44000005a409118100d0502215000c9039040060f90f825200c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 394829172 1250 394827922 394827949
    0x409021516061a0a0f08070b09040605120114010506070302061303031b08040b0a0c080601030b031204090603050c010c08030a020306031603030201050a0b011b03050d06050910060e030309060327010e0c 88
    0xc1e205c04440c02c1003032882c1c85032201d01c25280c0c260000300e0a80f5003070341d441d0000d8014002c003a00b604044085000780601824110302c05a0401c001d0400108030b46c02c1c40341c202e48102c1d4054004040e15169020120790b400c01c40b0300f09408066841080003820b04014264174001c4095942d007240504040c205051401000741c044610686011f0340f4880b00c9411410403a4019024240040d440300c1e120046400c11150348030b156101c190010f004101681e107640880141c03800b54003103504402003140195103030024040086c1290205000051582c0416002154000405420350328480c40c2c0c284008480e001580089015035114030401400c00c03010f1203203450410007441e1908481d000d100c0c82c4d0034040d8107820080c00700305000031000301016041e0018001040050711f44251850141d03030003090500a0f0103000009850441e10440c2454000700751411410011300385481c685801410219400040c02d801d40c222b03412030700401d00f000e028414034100e030b100c01014082801c0068100004591440d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 394830422 1250 394829172 394829189
    0x1b010204060914010c11010f030e0304080115080f030301051c08030c070b07030504030f18121202060a050103020f1e040e030933251209050409021516061a0a 69
    0x1410310b01065400001004186080c2008072380380058020882c05044000882d00e0035200009002602040542c40310914010b1403403103042c0c40d0749a2034087d071681c5840f00c410185a05c28001800f41c0c2c0f80c46501a03440303807095264000000301998510030940c10480320210300d0580400d1a10500c0007141074140c0c0701d281072404102c0c0b45030594000d4103071403c882d54031003004165000d0010300010100c415000e0b2844081e961401c6125142141400b07007080005401409036a020034802c242c68054203050f298000d0810910f0580b080602034054000450701002e0385001c8c81da0703103041c2c50354814201011000d801031030741c1d90402020312140c02480c0040c06031111544001c1158901070802c4c94042d01c020040180c2d580c8102c16421100f1107550b41090180c1c0b8040300c56000304994a21010440340807034846035201f69907071302044121041c0d444040d41003105a0700c44581510307040001e0080001d0306004211000003034450800301c0301c40350b0641c5521078440003812128a05844450021301c03601 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 394831672 1250 394830422 394830437
    0x50a0b0a020706140c1608150c04060311070206031305010b22150308030f0f0c030103210318051005010b161101050706021c0f021e1b01020406091401 66
    0xd040080da0b40304140b03c0c03042009030016035082404d5040341152a134246920403500307903015200400180c0d80d100d215041c0a8072505880404510418003c0382c071811010b1082800c0c1840c08000707901070303d082c8130912070240c010000705c1c0c0143e036506c0146001e071415440b8103032014a546009421541d854805070300c1135000140000c581d031400509031034141040342000c2582c4451040c0550740e10b10a0300014104900403041200c4801d034400c0700707032185441d1060350000b40c50381e0032103180b984020b010107002640302c003d200c1d0941d07005084070f6100a10701d203000205491440c0c100080d14035000c400700c40d0784e0803a881e62035201a90b070080c0e502428003025080d2a003681c00e41c000884140c0400024420342030012001070790ba0048042c1c40142d500f10000317640c1c480d2480c26204030900181007072a0803525090303d20f885043da81c82a00c0524a40041c0030404060b0a008083d0070341101c40301061856002a1003c02c24100780083c1004180380d40355003000b2410082d00c0d803040821088031a0411904 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 394832922 1250 394831672 394831687
    0x2010f0605030c0f1c060903051c05010308190207050303030a09111905100c05060a05042901060e12030a0906080a0e1b030309040905070501020d0c0b0105120a1a01050a0b 75
    0x103054084604400c211644200400900701c00c048405c45e201000d42807900d01512641419044002010741024179015800303411101980c010443d0401e0101400a643c24000c0b544e204020725a02c86001400e801110010b60351000060b00d036600c00c80b04641c0290311340e4a00700400c00f4240581e0800c0000b110105804842e80c1140300806119100f483d01c03c20078070f15000c030442d00584002604a401405aa01620300315036410b000d1b010a0ba000c80f844044c2a0001c0e0040c0031a500300c01c4005881c0381d20f003110341d107402d030304450185414200ea91f108450f068552a0500204014014034100c0d48925400c03901c1c00360b0240510400900c05824141002c40c1841c48842c041541c1c00300034407003074010b1210005030010034598060100f109070000d00e02480c200034850002000001c44c5c40c240d00700c5001c45101d201c01c03104d21165850082152540500512481c075000e5900c292644240080351b101e4010b58603082c0d4100a800c0c02c4c004040174850040c80340b8105050194080e080044c03c0c0c9152585 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 394834172 1250 394832922 394832929
    0x5040b060909072721290114010e0d0b1806091b06040317130306150e090a020d020d02150307030b10170a0507050f07030504080c09071d04110a02010f0605030c 70
    0x10607440c10f0f07902e40c0c040c00304008102200042480c95034000071b0b081d0103010840400001d2140a01900080c40750f11140e490036503200f044480d01c11400030b0048410316642d95039040001101a0240d1008888025a2180300d2070800015104090400081031200c552021420940303c0e2540c401b800707198200020700100326118031203680e2040307408102d43d4580031812030f11001d550580005040c42d0400100340b08920849050070700303554248141c4211922014861640c542e082d0000030740212828a80f840540b0300325941d242c006001070035442e440011054082d400d50f20440c0c1c2d82010036901d0004201340c0c01c0c0001100010f074076904001501004600c0c8510000c5402480000410b0310380c00060700403446403040c2c2e1030f85c04d4890b1420317480d55954900900785401c07601498007584a6880c1d1003195180100001d4050764617a11000c541d070320703074158100c4403528503d5415002515560b201810101c1c200092000c80e05640c0005008140d0509400c1510740e0386d8070441c805c0c0c0c49490490b00ca41e4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 394835422 1250 394834172 394834199
    0xc0d050303040605102715080f0607230d020d0905070e01050306041a100302030706050c060a0203010317030a0e0709060806070906020c10090806070201020a090f0f05040b0609090727 80
    0x10020381d140c00301c07002d411600f8001ba24203280e440e4003007e180e107400102e00500051007450440102e0541d07403142d944800460f200b0108444842042c15030f07400c1d000080b00c0c0c003402410101d008617800f610340740c103c2c0311010640d10705403011030703407540034403801c1194203403681115014007011405011181041d40740d403030550448404900208181d00007040200104d40002402580c3c042c09484403d6990803000d02150000311044040e0302a500003d07060344800c2c4201e078141c1c0d03809030b500b46244c2045595101c00e50002030481100a56035040040c420300100702c00700003010907a02c04100142400f03021400c0940142c440428490f0040c0107004007600821a40c84651050b80c80c6040c03480781142c121203002190f400061140148001c0c088241da06400910b11900d41e5112644101d40d101d42282000103141b15490f400500c0341c0303041c0124074040c4c000a0601d6402019281001600300004070018026943d0a002c9030350034000c03004031000007883e10700d0b0b110318009a40d64146045410201c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 394836672 1250 394835422 394835459
    0x1e0806091c0c021906030b04091a040510091118061311040b040806090d05040f03030507080909161805010e10021f0903121107140c0d05030304060510 66
    0x4680c101d9545515120301a25000d40b80c00038a90841000c50031190700005405000b07841c00281050038060403401e02d4050301c030f04150302c54100c050401a0500c4040601c1e0058001c8402c2e02800100002c1c40000b40a50f24125009804004080c1d900804110009111200e01d180500c0c0000c00c000e900d0756281c90032001001e01800c00b041d0500b407820030255510036078004008a11000c10085015080050700354801d041030422510f0700440041c1c151520f0140d441840c2043c06944414030000c1c0c81100a00101440703000c0280c104a10761001800c0000300300c4d42c1504483c003001c400f10905a01c00c04140b03c041c0d1500125043c5410000000c1040e403034160035a000c2c00c00711a01904c154801c02c1819990482024104007003816107465002030320003287c0590014038080e00e07411820303503c0d01c01c3c2e180c1c89403c10030207031512245580700d002c104414000c801c094000c0c0c8420030144c0d02c80c0d002c4a10390b2445203001d590341f0300e01858280c0c201c64018200304c104e900e0181c01480100044175100184 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 394837922 1250 394836672 394836703
    0x6070f23150609133002030403020f0a0305030d11070606030308060a09060812030c070605130c091116020d0602130618030302070512030c1f230a0b010c0506011e080609 74
    0x2105c1074514203207501d0200400492070760014203500361a00c0d808005401628800c03590651400344030f01c100300002646000150042d0030800024040000f547e100303622030000c001e5081c0c20202d603500c03941e0443d10180d0003900400d03040020400985000c2150102501c490f4030304100581c01c0500443c6d84128107621031045010000100b4a54100802038600386030340a4414080b0349401c00100d805a4070311041129200e41c1400e01042eaa845d5000d010b8100500d4002242460440ca8180c06d41300303501d500070707070f0019560324140300400c030140014810011403012016080d071402000030450220700c0c0908100064a00082c03002982c0815850f0031518111507803200300d00c4041c0350070f095105802c400a11031188074a14001d45c4005003c0451080d12a1020856030b80340c4075501415240300e4003405d524403c142c0c0040c10f048515030010107070903010b161160f030040c80b81d610140741c03010030381004ca542241c6001c0c8400804000800070058440d44018110305d0900040443d566010140c00107103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 394839172 1250 394837922 394837943
    0x40e0d0e0102070e0a02070210050a020a031407020d050304080f0102270111071d09191b0b0408030409110f0f07060f050a0507030e0c06070f2315060913 67
    0x180e07031080107010060400c041d5103106030308103017130321100940c40b00d00201d001d0140e5017491040680180203442481d02e41d030700a0036019039183e500f12b5a035114a000380f61026814082d01000d40c4540c822050601d02c254001d45d9600d042a00c102d10f48401c040c62908a0ba0041111000d032106500d000c6400007050181003050422140c01a01c4442c0200b8a044103480348010014480324280752000104100d250200700c3d54403507104054444010a000c208032400e400c1c81c503000514107c40c0108001340744500300c0d40c02500c3e695800c2c41c2e40c0c001da01015040e480440d0a01c00c3c2d26091140c003002c5414a0306e841d2810601e0700e8068900c2c0942c0ca0555035015011403000300384100354020498210f4115410010f92070301c64555401404240c030139070000b07450010301d08940071b40091010703a005401000103083c140113564034800282200d0741120900d54280c200041c1c8070803001400c141c0d0156038003030300700006d295040b4000070000504040c4110000410b00800e4802540c15410751a04080c000b00e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 394840422 1250 394839172 394839197
    0x5060d0c0e0a0204031202010b1519230705070806010e04050607081905070f110607020307060f1401030b07030c08011a0a02150a020702040e060402061909030206130e06040e0d 77
    0x80240500c2d440a000310380c6c5d4820381c04650790306601036078004404503812007080c070071120716050600801540c01c0c0c00442c0d032220340c032010307002e14142804c0500200c86c0442201d0300c034039080f000d80c203c000d044425a100c00014803c040c003e12080303001d4920350525845625298485a50702c56001e015481130110075804a14600c0000c4001e40c584440c02d4070500c40c906041c50028500300b17540002c10001a1400034030000840c01003222401440c00b0341c025810500d59458220052454a2070104810b0b038606401c9072408034403215034002e6003c1c608165545c40c0059001d0180c5100358000000c00828000500082210030016800303c0340e026496912094001c10070ba151060390b050b0f40d03080c1c1c0402020040b120101ea0024100184250b03000d1000124199105554a0040d9802540b00794144a081311030450701c80c2d86078411001e0300e0302551640d5070fa000303e100c0717907c5101c02038100b6030901c000303100d161220840c09400c10400c0d42c00b00200c0d8420a1229160004c01d002c28003045019044503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 394841672 1250 394840422 394840441
    0x910020c04060311040e010c0e2b0303051807051f23030117120904020c032107031a010206011512060909140703030903060506040f05090705010305060d0c0e 69
    0x240c00981001e00704114050301c0e030501c040001d6446108070710a070b081ca40300c4070401c10103016800705030324603840e248800d01c0d65100700281c0a103120f910300d480001020300389210451081d040d00c440b0b4065180080ca50400079442844110014083c1c00705602c0755004000e0350f00c8003001c401400c150301da1246030500580c00d0440d01d40d480c00f00d6041035858005001010715100a00035412541010060000100f004c0d912175111600100654203200c024440c00d1110304041c0c004044080c149402d50340f600140c0c515203014494100f1403d000c40c10420b003005042c0e60144035443c0380c1c400c0c0c0c0e42d54010030005031000035510341d014002e03d0044c00d4440c0110200a00895504e40102080b150a2107c103407921001401042c82c1e440036200c109841040d4200b42c1300c00711307844041d203030503139030703503da07150460b03d600020b0b2801800444d0087e41d100e00580e82240340e80f04660103414020f0143c460503103030000040c16075402410b142d00ca00d0072488010300103549034502d002280d0300030726400000ea07201441c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 394842922 1250 394841672 394841683
    0x3120c0f150510090c0909020a1b050a20030a0f0203010f0617070b0a05031812030c1b0c010c0320030309031321020d05100e0d02010608010b06091002 66
    0x2040001d801d030381c02100c80c1c0385801030780c4604120200f01000640d681204001c1d21400483c05000c1380340428140125507142e002010901320a040c880a42c1c5020f0084401184032240261820f402c4a803505040080c5104090403a1104a24044d03950710340303030300207038440d56401e0300140031745450043c0b48119103080d005681c0190b202c25003044190b61340c007801401f840740310076850341c3c0d4040c42c4030200d295288030095901828180d80c40d60b08554940e040401d850180d0300c0d851320140305a0b003d660207410b0100055114076500d10100f41c540c807020100e00c0400981120304c0c1400d8100000048480c0da200143c081150b406103001c00403801045502a4545484441e410060100008000ca501d2001008001140d1160407580d0f155a450b01001748906e1005a0403806034042c01c820000740c03500c0440c00701464050b4040d280983c004410b43c000301c1d1440030614040340c000441f60b0300307141d40a100d14001424213400078008450300800040103489442981c511074194a0180c5101ca40708103c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 394844172 1250 394842922 394842953
    0x18010807030e10020405120609190807050303011203030b030d080a0f02070804030b0f010e061822060606090501142a03030709090c0c0201171b040308030604060f03120c 74
    0x2514034110f0350304034010103503110f070080e180154181b88a172000090000381c018450b01c084400b41c03285240c003c0780780c007501d800d00205aa140e43c0038070201c0c01044080c8000c500804001c0425940d03121340d480c0142c181c0d20000a0144030f604520200b1280b40e0b0014000f43e4441000c407000540c401064151100a0060130400f030240c02d00031a01204201d00c0c034602a0050041c1802d510385603a850030b40002d01075007281c034290400030b580320088554070b0078034046030020041d4850281300b400400100001c0400400c007074814a490715003c20286810240e041c025250070b10f02148000004000603000b8030540c5002852014450801101c0d0381c1c0c1030002000100d05c080640b0703030b41c0c04c125400401540c0e2a0145010841c90208800308090180d140e01101c90303410f840d204441c95070b104400c9440440101000c8030060024918013001c0040401040a544282c4000792641007900c184400c4842c10703007008012122612092011401100344102c02c44160b143c0043c0c020300b1868440c178106602c84 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 394845422 1250 394844172 394844201
    0x6101103031611070602071211030a0f06050903040609050d080c03180301180302062e0f0801050106080c160804090203090d030c050a230c0d050c0606061801080703 72
    0x91003407a480803185540c0381105680c5100103442410314290711294540302d80d03005a44514402c001700441c015842c032007127004051400303c0c20300c2e040220b030821396881005c0f101103440c160900204491482001d4000c07140c400210b0a2900708040500320900d00c0c0140391245c0d0703042144004001e43d11040300c1c000d0642805494640d0003c0046048a0000d0428140710f9400d200f581030040a8014043e00800d405600900c0e5540780c010741401201840616409800301061a01c1000d440c210300b4503005001540f52508400e150047c001c2c00c4401c1a0040000c104c05041404020010901511405008950b400c1e245003e60318001c0b94610865110080813400401001040800402c40180440054500b4020410142c0080f40c0d680300e283e4070340d0081340c1c0784c001446c801a11908003c0c041054461240d1405440704103141c94169000b00000002d5070014a00390117030014000c10f500644261042da0821084180134500805078102c1c0a040180f508006603100b032103600610309100000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 394846672 1250 394845422 394845427
    0x313032f06010602210a05090d02100c060b090412050c070503010c0e040f05010e0112020a120b01050a0f0e04141c080105010207120507120f0c0807050a06030203040b06101103 77
    0x10409484007002d228100145c06005451020448280d003c0f445003511104210b14040c40b00805580c65041000726070341000102d58090300503220401c10307020b104001d40341c089402e070300d529100013a02d82d051600e901622408003400002071600c0c200840e48003050a060303403243c0e522071310300740792031410b9200581c59820703e403080b200d841d00010100383c101c00a070307004d2000c0c0c4070541c071640236201c0030f03c20351840808840042000c848042c205819591008100348000c5589808030840720358210002d80d0b881224100411481c90040d8050005103d503880c0e002c6002c0c542120114003520007000900702c04038411281e01e1a810501c007941d05c03911901407400450f01303006001071509209024403809803007070060102e049103201e0015402954458020141e490911024401804074000225034640c01d40d510080022070841a920207042d5000040c5461490f0404004400310a644117200b814810414000860100e490483d84401c040c3c2c1c2c848180d0100c030108403030544404c1e07038214460002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 394847922 1250 394846672 394846757
    0x4050a0c031b0902090f040b061201061806051305010e1c0b0a151202060307030b120106060306080705060d0c02121b07060807050703030506150a1106060a15120f0501060e0301050705031303 83
    0x600074100e4401c40c44642c0c2c2500c510060b83c090c401d0b04070300780c4208800502040b45620030a50410860409488403c0c0403120420030407035809a194200d9001601404001d07850600744075050403800140341465459107429024103020343d0b1030502a004220000010b180c05000750400005a5000b402c250b00c0c40c3d1035059814000c14841c0241d200103070515400055010000840c2400c0c1c890050200d49032106441030000103102d141c04a10541c06442601c1d558801008040c1a591090b034101501503a490060141402c84079088807080c400c240c814080c440c0e138840283e440066040c10002541e8454100188000148200d1100c61240c00581404030a6009002014441680040b21000e440f0070b020030040082901500c80c2081c4646070b4a52010b21032260f1003500c442c0b42074000381c411a04485070040d25800d030401c0300410101e050110080c1801d200392640411503213013003410b40c140004019070700060000d015003080400e840641d14152588108100d400101c1080c101e039445 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 394849172 1250 394847922 394847927
    0x61c05060a051008030f0c070b03090706121503020603270f060907030f120302040308130501020c0f0901090903051b06040b0108010c0509060304050a0c031b0902090f040b06120106 79
    0x10110744034401d96042c6008501914401c4002805032808000134604151410140c110342d07412039280c0500a00c2411400140b50007c0c0000b140100d00c1c0d032029148a5080c000003920340c00c00c0c289034100711072a05100400b1440203207881c000f5694112112a0351b070b101c00790b010402c0604010354098208038007806a0081d44006451003103c403041050b40d50360f540311480307103031a1130480c030015107050080502c0d500051310200f2a149103000c94100103042680340d455132a1160030601d07210203101400c40081c460740d07804220141b00c01004458040201c2081c0c0081808100c041c07140240d440c0d12030340d98404040c0510b00351000c0c214614540d6a6000d200c043c415518541035905642c1018440c3c00031070b440b43d060203a4480c8010030b40f10329180c10b40480901c071160380020000da406015031041c9000141072002040004c500401c1e94003403d020003c171041b95450381d54004a001d600c100015241d0340c0b100f880c0410240d8041314009170380c0c40e20a002c1155442149203500d00180c4010010860340d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 394850422 1250 394849172 394849183
    0x90705040c030f1d010c1d01030c021203010e010609150905040513080706020702040b18042907080601020f010204050f062208100b0103020901021c020f01060f0503150103030c0b061c05 81
    0x1207200c0000d20884c80300708419107c0c405060f03041003103c07500a4000c21594000e07080f1105440340ea01c1150b003464000e10f04c0707842d03030380003031b008030100d20058801080610350040c006000340c0700d20034506c041000000c10207841e000142c4205030055494900041000b80401e46d0848076642001d10030741e03541128580200258000c440032441507207441e0b401061402e00200460181c54690b29050700c139100c9403500141c280690706c61700e0145c0352405005031056560307034038980202c43c680c84080c00c034280000064180903110300910b666038411303c01005070780d4a03813103428610a8140c503000daa0700007400c0f0005038207810f00b0710702443e510742e824005641040020042a125074481081240200403001182030b17101d084419401a4480208500703440301305000c0c2626a4240e0040380e0742036201c4085542911201d5000c05145042ca10003044035060030700c85c3c0b6a6403007102507540019811540c000c1d080c01100350010741107840e88000100162a410340d05405048006c0c070700c090250301d51030901d1f82ca1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 394851672 1250 394850422 394850471
    0xb0906130b15071506030f060f0209060a0302030a0506090621070801020a020d02070f03170a0201140a141b03010b0705150411040f0902010e041107060c081806090705040c030f 77
    0x44c0e51040010088603464801d02050b20b42c000075024021b400c6444290242120381c1820760415800c0000e40c800350f850800400b1b0002079624003507101d21305080785208849008107494015079401c2d04100440e69541080c005440510f2412a00240e03440d050310f2904d100703904612910b610025005012940025805640d03542c10b60848481c1c9031200301030103c09016200003402d00c1e07100940c0c0c0c0440141e1f01c01810300603903984000110806110703814040400c0c20303281d00c2d407820f07031303840f401c80c440390b000e42550358800109200003146000070324041c4181d1105105180c20311038003084150412500340084a80d0040f05812081941090b0602581058070b00403524407852031b07d02c0280e05001180500582c5a4058583c0316403028101c0900014003110005250300550400001c1c000070900d10802c0f0f40d031000307a540c1201c24134003135180041c5003020b0304e91411194411010031083c1200003403c032095820035140801c01080031501131b000381c407a10f03229500890400603100d20030380b00015601c119 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 394852922 1250 394851672 394851683
    0x923120703110d0309080d0b18040b06031506060304020405040f0f060c080901090228170606090f150d021201021902070902090105030604110702030604120906030b0906130b1507 78
    0xf050320f40303402d07000c40d03a0380301d0002d040003424001d1500a1b52a03a001e02c0950038041d10140020300d490204240c8190222011a0300c101c8810900200d41001c008403280c0142c001c0103000700c0d08240000034000e006c0100024425600c030000141007104481c5a910b400c0d52040d0b007242031482514101002c0d2603138001d0b40340024100800240c18500500842d011550064500001c4072444504030407003408401000e000c142c100038000070340200c52005400c000c040c1e50007070461418404100b10308088060504103038410b20401303000c040d850895445122801c00c46407104d00300070303034400314003114680c1d11641c143d5440812103203412042d45200709449040369095514240c0c030340341c2510803400b4103120a40000d0060000680700c1c28150f202001701d500c550b0440781480f903564002454140e04907000c0300e820191010004400d034001541c9006080d50341007e00041d070200d00450308000009210f03e1066401e10381e11025010194002080d4180180041b490181104040c24071507000034400c40d00c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 394854172 1250 394852922 394852933
    0x3070503030a2f0d052706090c01050415030507020a120e0108060603190e01060305070602280f0b04031107060e031006150c1704090902030f01092312070311 69
    0xc580324110b1801c02d5814103502c3c258100180242e01c42d0040400501e0f0844c83c440c2540e8151b01b03600b140c5218000300c888800100030929000103040c0c109400b28001505021041c0000e01c000ca040310740001d081d020921340040c407640e45050803858000e1000d0040c0c081c2209112246100d6480300d4a200c10420a88801900351a450107000e0b0310302c001c0310450b56409220303400c18081005608a4040944050000702d280c907107981b01d45040000e0742d4448800350380601641c28402e020340c8a080d50700f00d6250541460480d180d12590100d0410138801400d61400c280000c0426024456080c040c0041500b124880b9072141c90113002c808121b007405202c4d100d1180143c6900303c460240000751161a8140110070201100030341d001c01c03610b24116905460150380c0f018a0380d0101c0500001c2c248100085802d40300713401810b0070180b141c41c03452020707410040004e0118100440c1811243c60aa44a5030b0f0422030011a50a100daa080041065240000c00001b032550181d1840d00345100700c029100d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 394855422 1250 394854172 394854221
    0x30b010206040203100c0203090306010803131d15010c0c06091e08210d0f0522050c0906040209040219020606330f0307091517061203070503030a 64
    0x2a5912401c40b8020342c182d0207400c0c2071a5180d01c42c2c0040c549495180100d03420450810002420400c0c26005a4140e80c0003083ca0f44070300703403000008801440c840000034100e608241700711000c484014038003403002c1c0c2c0707444083c0d442d030340305000c0040075030f0304482c6403060b4984810b001000d07400b0901c10801d0039403a86020810301e031344031004181140c0b2260000c121800700380408403035461568280b03100c10141400303271405c1d507400d900610279150a8400001000c0c6044850540440d04100d41c0d680c0c2d1090000ca00e1000600004030f5104c60503045480b400613644110009010f481500c0030b1075040b600104000741d00420324102c001842549070282c5025599034030603c0300d003030500d00203034561503400c641d115501c1e500024139010034843e850f502840c1005102884001d40c0c404d541000005601d040204848201400d961341403a0080c60030001c917133104812004685006010700b4800c2915440003d10350a04104560301c042e804010303071303031a45000d062900c0200074920045100c00c0d0340c4072058 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 394856672 1250 394855422 394855427
    0x309050607091202090903160b0718080c010e040f090b2e0315060314160b030601020706120605030106170c0103020922090212010207140c06091e1906030b01 69
    0x100c02d4881d20341d903844040410342c08000f44a01c0c050306c4408180410481d100407000b0340045119141c2c041c3e0030b030034213030b0502280050403240c0e40650f001c07508141400c1403140300400b0070b01002e61502407810342104540400081e0042120b030580d5042586040c1c0c100003000305420050b44a00714182040c114514441c0e102c1e0890100c0d400618040341e030300c4005000003880807a061000c41c0e1045000155a40c50b9903500382c003500c4a0520b0003807580803840c0060701741c10b4104000040c00e11000214114100100080c2d40c41034940070701003d000b0b41c040606040038041d4041002400024000d00c89599503644120b51039a41d5150907180b801804a80380f4503500a00888230080d45c0a00030008c01d2000c0d0314079070040045528034000141c0c440400e4400b61303407041018030080201200041c1c0d03400c55868401940c242070040204036400c040c1d08122260380e20016100c220301d0589069a03049400110944421031b10701c0442e511668007001c040d0711804091601d02902c070151000c01190344d1403c010b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 394857922 1250 394856672 394856687
    0x103061a030106080a0212131209050a050d140d1e02030a020705010318150e0705150301030303050705130f09141312091a03090606010503101a04150309050607 70
    0xd2030504041004104851240000075441450383c1d80040c100440307a516010004403d60f0f159102804454046d4207102d0b00308080e20240c4214103100708043d103014041540c1c5101c0f8031901c0e06c1940080d0340c0308184400464922410500c04099030000e0050403005019000d94010303445180300c00d222401c0756580000110b6903880b20b15001003090034a1300700110701030140400f4000070390502e954039000050038041803c00d4a5010b02c0c0109851616160680c0392424680c40a0b125003810a0b02c0809407121008480c10742e5010f180215159903011800e8500d40700712020151a10848030000500c014101101c1090340d07101c913824070101c810342c80d03d5065104d003907030508014206c2c0402e032000503003000102003207440c40c0d04041c00c070183d8440d8054098944450078142c600b400201304000c21405100440d03200000342085429030a01d821407030b907130301454092a08405546070b5216608903241095a0080022580040881c0a502c20003005040c2525003260148542ca001c1a5801d019404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 394859172 1250 394857922 394857959
    0x100509010b0d1e1a010806030118080901050403021e0907050c0d030b040e010204091d0f06150411031611030408100510120c08070801020a0f03090c0e15010306 70
    0xd03141414850000c00b030082a0055440c9030301241d94050329000c95140c001c000b5150581c682401c2821100c100150444c000204400e21a924200c50f2002041484040a107a46c2c0c0040c482600e03000781c0c900603111842107400281d8400e01940041c00c1d071800b140412074000b041941e1841581d11030300c00030b4500340150001803030507400901501601c240b19600910f055840148003041103c0c559121508980c45a00580901e50300c3d6040e00000f010000214043c0803511341c010100c1041e49030700a926124041d00b10741210041403881080c40c0d5990f0081c40018080d031107016500d0410301e890481d00003000c0003a030085405a8503a1050750000b100303079411146181e003d0005000001001002000010217601d00680340e0580840c90040800301248080e00c10318a0450007403c1c000e001780741545940c8000f01c0c07a80100410038106520800000310202c40b41404144800d461401c046100c410b5001100040304800030005458500440502a01020b07201001996200c103003a1124658485 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 394860422 1250 394859172 394859189
    0x1060b031501090e010b07020d0606170723060c030f04060f0e03060f010612061a040f0e04020d020907110a061b020c0a060807020f0d120b010503040f0204020a0e04020d0510050901 79
    0x4c01084080e00403070017090840d20040000b6103004d019500d000c2140d0701074004007640d001c0500781c04041082001040c000c0c043c4945074000b9072000101e65446448458050780c001c680c00300d000d50400c03400b00240e0703443e1092003a22984880c1c407a84000d2002c060300070000700280383d5032214801c505010841c580900c80b210548070060f0300f002001d41f0b41c0c1c03601c010500111551008005040386034410b140d00030702d0784410410380c0e50346440b034019491541500b02021289110043c03200599540720030410340380e41901c00300016a0f0b80078042d20b5035161400e6035200741c0203801c84401041840c0d030002d40b281c1c548041000508860712000c0b44c0d10588542010340260300000c051151901510060703612407040e00c1144c40e54110f1610f1103052481d035800340ca0110b07100d081c1086041e501c40c026152080c000b840c20301d04600c0c2580b103c00000704241e901900030741c2c8c001250020148100e0205010344030207041550b40e0007956007004005c3c202290b44ca0f0340a203c840000c40c40f4036103055024100c68207076 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 394861672 1250 394860422 394860449
    0x40c080408091908070510050a0206040336030506010b0a02031b0c0a030506041e0201120b061b030d0614060304110a03061409070b0a090e1801060b03150109 69
    0x1590749600580c003984441d940901d848a40c21035981e00c0c0351401e0003901441d00502510380c600310502084694032110103046c010140242d4044c40d5000402d42d44c015050b1508222929500301c1000781c00c400b50b141401040349010f05540c030900c07420300e80b40450748200d0407910141e030b071244441d8040c00345207552401a081082800b9000d02200c2c0141508805c0405465545219a001501e485195171081b0f44c150000001c10007403100c0300c500080720035a0202201080d21065000810403000e1040e80307131070b65a9842030000b0a844013001c0d110049107000c0391442e031007540040c0a03901d0700800720107803019040081c04030b8016002c0802180d100350252815003503444136512040b9010704c4001c00d40c0c0140003600000b005c030b62140108082070071140803404407805c0440e03810703003032001079001005404001c0110400490344040d4280c11644181c2c00b900803070f19500015040e035100302c603410b0803960074000b000ca0441548802540140e0352101200503a1408000644030b840d418854a02040c080 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 394862922 1250 394861672 394861681
    0x50106050f03061309030c05010f0507090b031b0a0c0605060a1410050f12041b06021e030c070b03011e0f030f0f0506100810020301031e0302210702010e040c08 70
    0x1ca8000d0b60f00414014035a02002c2440031403042222075226003a00015240b100748000c2c00001e202d43c3c0c81c48000458280324a10305081c024000071014810742d60700090010003d00d442441040c2c0f0300f03080c980c440036a5907a450355000140705480d51842540c2e40c500d041c02280a41c0b0300303000514100c400d40040e00d4801d50304901040003150351200b070030052000c204180d00c3c0c080480401800342c8080c282500c81541824101305500542122000f01c1011700080306010307968001503240f158464100c2245060016144e549043d0301603035214440d03d104190000c142601a04003440c140c0e148940c2543d00035101c50310340c25100601e88146c001c0d4914251050001c80c82c04002421000d005030000022028140e8a10b86005000c950f4a060f80c0f0b5440c4050104440501c00c21101c0340a0240c151f0855046840d10381100002d80d07801c1c1206c100302d46401041600070301000188520900281480d25405421990070f0352041504a00050864058080615040c411780c10030385000c0d030310499036648 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 394864172 1250 394862922 394862947
    0xa0e100e150412170c0703061406030303060f2704060204031103370b130210020d020601120f0c080f0601060c0f0312020c0d0203040915030f1212020a08071205010605 73
    0x13800340001c250441000820a1140308224480045200780400500755200e600c0002c80c2d110b000d00988e20070b40081041c0f0040c0d03074407506010300d141c0f02242d0101098032650340d4482d8405a03403201817003c4075000208070074480307254081c0003140d0103a40400440150302040684a905501d4203411800903030341605036202042d01001440f400c0c4541401c404641e40e01c1d40031060004550508585c1c400490200031800c00b03145100c80c151306800100301103880c40e00c0103502c404050192812042024804c5d00a20410f07000d500c00241c0c0040e01003100544a140803625810503944403105032060200024020307114041e45c0d03410542094488411a007107a0741100d40403038440c442c1400d180c0902091806030000d01508440314003d400440c1e8403490001444140c03100011250031020042004102040c400072080621f168416003442c0340a0048030300303880844030071962515051011400550361a00001e84900545c0507880d19050500c100305d03580142c646c00d01400e0300207201848004503400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 394865422 1250 394864172 394864193
    0x1a06122a1e030c04051b070f0206031003170a09090c03061503150509090c0904140a0c080f0703030f0516020310020901180605040b0a0e100e150412 65
    0x5a522000c081222500000401c80da6103004a541003040240081ca800d203010092000340d258103483c11310035454880c03c040990300d4485006c02441500041040410011000340b0144c41d90080c0000d80745e007400426101004400c1c00100c1c0c2c03004070034028200c4603102100381c4642444940e109082242040f0721030000e04807810101d01419210040400c0d040303038080121020380b015a40014a03c02c2c1521605e511140a511a034000c140420500504a001007071714404120705650110550b200c520f046048040b405d00070381035a0144d48184010440005c1890b421250064111100c0c041c10005a1b0346440c1c00744402004101e01100d8011184c1c080c01c050700d51000705603030b03a21010f052900801d0800600c030a82d4400390f030340011000e5156070414082c00004d484140781c954190309110010b40644a140107494083c00301207610307a8654803d100b421101c41020309003480716043c610300038028040300c0401901c54444400104090048102a2012a008400b00c1407040000361038004019 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 394866672 1250 394865422 394865473
    0x6101e0e030a120816080c1603050f04030503030a1109131a060c0610150203030402040203060a030812010312110604020609040e03030f0907062f0705030a1a0612 71
    0x41c002c1022030000708012a00c43d00c1040d00a031910b83d880c0c80c010320111108400100740d901448240000c0c029030100710400d903407002030754080c808840c05c918103081d54180900151410034900c0020044200030000c0041c501891f040c04091080c0b044204e040b50a40c042d0740401a0080010b00d0010f200480a400030b80405d8440b460700106006040042003042d8005940240746900440612500ba90040c490300020701048050f407a27490320104009441e8440075102030300c82c1c0d4002c00400c0c19644c0e21014480196400b4140b10355500242d00c1b81000c101c401d100540b05241d1484049418074001d00203000702c0001003003c0d020030350f60b070b07420030203290814446d40c0c1d04240e40302108a11031104100a50040502403201802ca2405c00501c51624020350004402c1184242095450811685a403000780141810141e0302c4c4041c0c513100b41c500301440d480b49901d0302c186000e407070a002061140f002241041400f84406640742c205110907a40d08600c07407081c84e40540c2c902c1c8480c13400c03100402c07a02c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 394867922 1250 394866672 394866679
    0xb09010806090a02090301020c0703120f0c03030e101a0103140907060503091204081b010903080f030a0e06010929010c031809050f061305010605031602100501030303020306101e0e 79
    0x288601017010a089070860f80500c0480e80c0000c809005005c81d040001040740d24900c0c2c62281190010b000600d0031003c040002c00f410303140e8402c505c2c40d04080c405980c00280171542000403a4401c441d200c1c8074550002e0060100349005045400e1308041c1a4103441100414014100c031841c004080701c044e030000305840b640380210302c001c03d207117903a01c0010001030045000800e802050010304039140d54050940506000005608000007607001056503c06000411445c1d102d070b49041148003d00500c0f05440d1141c001c141c00031a40340e8265200d4016014900724002d00031005264541080c4411803146002c07400380e03200c03d400241f11300b5441c4c00b140141c8000000007075540c0f107030205481c800d407211144907103500208042d03070902100b03240c005080280c007801107500d4400c001e4000d100c0074080810180000481c8808203000b00035a40c50702c034201c0d804100b02c0d0b96a041c01002500b00f40e0f42c0c107109035407220514400500c144a064415400d1a103803413a502800101030707502109411600380c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 394869172 1250 394867922 394867927
    0x3180102120316080c07020901121406160311120103060203040201090b04031104050916140102010618050a061208040905180f100501060c031b0615080102070506010b09010806090a02 80
    0x58a01d000c5001d035006801810740500c3c5401c5219019040080081c078021901c45c05000708405641d8038614a4115442e10150b010000c40f42c0c02c00680e04002903030002c03114030406060000030582a04081ca2a0f01255403c0103420070b407003182070243c80740e0303019036500681880050003c10a580d00441d007051050411120031560f03000120803c4c0c125500c00d80792001c0c03d4440d8681d900342402240d9104d0190300103001d40881e500c0a01025182c03a000d0300f20581119401c02d10140d0003584001c024060540030800800560303c24100505800c171445204907040c0780c03000462090110b40c0800e041d0380910068181800c005c0c03030a00500004140c0c51b40070081c0504480301c0c160034008c840314885240042d0800d05104010902984d01c180e024030100014000202d022a03808000004016034030f405049a00445041940150412100304140c16003003400005110748158001e00c01e4a210f0004e4a0942e03994503141c0d102400340702d54090100c0c90340c0c0e0000707c2c0d900c2c22141480e44119803c00050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 394870422 1250 394869172 394869193
    0x90f0209031002030915040209040b09120d1a10080114010e09090a06151401080901090c0f030309080705010e040f1e0b040f0b030d050c1f050a0f0b0303180102 70
    0x38604210b100c01c1d1040b495001043c0944940d041c8404a8600492000c400c01e80c01c0c03d50109141940090001c1c100e0000c0d5070100f0f0482505000d8480c0303070400c00c126181c884075080c2c0c1c400c0040100c0c240c1da45808560034116801424103100c003205004903601e13010156841c000441045c2d849413101c40d4100291240700035640d5075211286802060103000412603175100e0300d051011076170120901411200c115004200c41d5280482d0110703941030a00e003c0500c2e840c0d02030014090316462070000e00c192141c14004c240c2d010200c480c0c80c11280241d035581e0050355520780d0942c890409000341400550203003038146043c1000d40107180c01c0714484000140f4003010305445d040c6052209c0c2c0100300079445d405040e0561030300d40902458010b12003c200440291440000e90b51100e800b10041404408900d01040000c00e001d25a154040b0380d800c40c810450201500c0010702c4101c54a400080c901085500c6c41c805900c102c9100c008040c00951030441110100241c051070100442d04504c107464000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 394871672 1250 394870422 394870429
    0x423180601080919030302030a0e070b0904110c100504031403090d0c03020f010507030204050f09091e0a0c0602390105030a110f04050f1005040b090a050306180105130309090f0209 79
    0x70f131002c82c002d540046c0c49081161844061360711602c6a050194400542400030360326500896800403c2100c00042aa5181c224565240a010100c2c0141c0c040e03100600010007440d048148100d1090790b0f00c4051031800b14683c070150206844581d01c6a01800921140034043c0c4400f51340a4013070300484e26a04207411301d4030b00399401117900e600000d801041c200443d040c82c402c900c140310300032603291030306162006100c1c0d13448405420400101c901301940000c1d600050000a46064100348184003050306d810000c0c2d1746000e4016501401c40c80c201c41c01018030410aa5034010448903103801000400c8500111245d40020702203801403030780d48526082d0501d0700801020344180440718250bd452600f01001004961580350300e000300b04810380115015441030496050702c582c00c8949072145d03800c0f004a041a04e103908400d07058401c050900c08098410000c402410031200300903c1680e640d108840380c80e100200c002404203081100501034141e094001190500c404500181012070a0001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 394872922 1250 394871672 394871713
    0x3050303130303020c190308310305161a0121020907181403010606020c01120e01140103060b031209010f05030406150b0a0212090d02040902040b040204231806010809 73
    0x4a0b0807483d500c8241e81b080541200a080c0d120200b07202400c259544014081c00f41a6501180c03000c06101038401c4c020107003d08243c1c0c807046c3c40c680005041c00310310314004040441c000c4203201c07100b0b8054000221501c5001880300712051941e000310038161181c0c01d018a5180c09402c4fc01400a0307201d01c1160311a40c0c0076009c0081c0340042c0120a07016070b0100b8103007121001c0d04064119045805d0454031359030007801c07074a440b00802c075000580b00510003025004150780980d2080d038103071010000040c8007641e008448264401c500381d804200c0d8070444200c00d48284482140030441201e1509201800381002e0350b4058000c00e030101d07148552291400c026032030b94000c51510038000c243c03258031340e0f810042a1109500c580b0110700c0c0c0b001c1c01002545500900c48000e105644415541c0e0031515035070005e03054160054800c0d521562501d01c9484e56003000e455044070a0718002d00408507250225403590711040f134000d10407039622440e0044503202c00040641c08284600c400c50120500c0701c464 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 394874172 1250 394872922 394872943
    0xa0f0c0201061a0c06010e041a070906021e0c0d140613031706090609180703140d0302121614360907230c03030106090f03050303130303020c 62
    0x700350b41000c003046120140d45181d1607043d1418814113140201c0090340c20f041d02c4000f03410108954a9240c203086a0340b0010780c3c843c0208400040c000d85030342107400d0300e0035540c40da000c0d5006600020581400303001d0300003004510f60b10003004c1e1121030801c2203c003242503015001803d421074009074041e107028420f0380c9242140c42226440300a140d4006d640080040b0422420641420640c0c0021403060f00030b0220392081c007110021a04000c1200803480e02c9402d20780c03d85407904e960b0700302011f401c960705500c610755000f80c55035900500d12134400c65107024030340320701058507844034186d1070030f0300b1804c104080c00d002071001c0d54070303408031207001a050702c1c080c0003110301c0c0046a0840801d907000300d0aa21054440005021a02a03a143c0f210ba50f800b80051510907062060311412400f0309051340d081d0f1a1a080024660150b50700200c001e6058501648510242d655a000300c031442400500c400f07030940d0001e201250428140c0c400c82c10115009140160a2802d5034130f819040c0060b505 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 394875422 1250 394874172 394874177
    0x9072d2c04050609090705040228090303022107120315090e010b06030c190e0a0807080f0703050d12020405090a0905100e28050d020d08060a050a0302010302030a0f0c 73
    0xd1030101c1c90300c0e00810fa449041036840001070706010300001d5603900d9501515224a40100e142d901a41140310340482c611086101041215840701c00036000003000d0006030b0050184041f042e6060114200c5c200016401070030305450040f4036140d00b100c014680d09a0404c040d1900c1a00818040c03c0c1d0102018269207203000500f030a48080d01c0b421600441a5280030300000d1040000c1e400c560384c20f0321494074101c400300c0810102094211010b038000f44030700740d000204000202d11130500141c080150b410714411503c0040e1407031403165030740c00180310041c005e901c0091408880d034820112801f459540032009810319884400262045900310b4611440995a03080c4c0024810208600342d10745c17545010400401d0042d80203907454500d981c1a03158801481110480c003658041c88503018140c014081c2c030f401c10040301009442e052800d46020024201a02151140c5800b1082c1e4084030f00051a02241610b90350056000e07420060628096981c0c1390165032500039140a00c9070b44007d06e5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 394876672 1250 394875422 394875497
    0x6012708070f170703150f2d0b0d210e03010f0905060703110405120a0803070201021306090521010b0a06020106050a090902060714030f1809072d 64
    0x1811081c0001040b1050260681c0311440070808200858889032040e28103030404101e2605c100072401c0902a8400603403030107031038000b401036a402e0844c2c0440b11231001d940144202e9000e44104200d42c03240d088042c0200c01114001d50010441e4400001c9146150a00400600002c0002802c60f0700004404050079150345860b01000814031640303070b1000640c00c0c01c01c90b41040250043c844d01031400303941c4c01840380302040503d42e1010400e005006501084140d9207103800c0d48000c1c042d401c11840c400700c0c5180034401044d91406141028103465002c1c5c00c045450501140020020304001d14114040d50f8a994125050305da224911340544182c0c1c00104503035180005110700c0c42c1c02d69200c128460300e488070b114010f07683c030f60072a07044036041042083c500914101c0941148607907480e071600f04000143d100d0b0700740c2c1565610541071404803031408145c1d4407840c05841c00e514251004080d2843c3d2100c02c540223054100f02e1410f05401c0c500b010098000f205205400507168981c03600c0144031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 394877922 1250 394876672 394876679
    0x50a300b040308011d15040b060c061305060c04061403062215210206090f0603040f060609050702100908090406030503090f03030f0d0c12060b07050c0906012708070f 73
    0x340c02c4488070701303645107031400b0003850211549410400b006c400f01c0d10841c0c4030184101159100c0d003d0b1110200c181c01a41c0c01420900c402c44190760000008807401c0c0100d100241c2c014807400d040d00d08403130003512092070100300d01c112050345510003840300d5070000784010b034840e0019140001c8031148086100028080541900f411401c0100741e020b07e000d0200003a9040d44a0030203485184440c0c0e05590b82c40d16142e4640001d0481060303c00d1300d40d0459404030810040c07004500443c2d011a0081030b0802a058a0380c1c0c015042d01d40844845001d40e10881d03001d1401803090303102c5c4500a01401c02d040c140000c0d0800582902e2941d4015a00741c0d001154004080c9005000d003541c000d012401146400070401203a12a401100c6075a4a0a80d80d0801c00034004d0191946c001400683c03481040440e0f11448801000e41011109440380d2103a041d24564a0030400c50041c0070b824161a82904d164851100c075071809403002e403050114090180006540e0800c000f5080508a5030080c1200d0303604 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 394879172 1250 394877922 394877939
    0x90a0312080601031401050f090907170706090b27030f010c2303060d0b190213081005010b03012709030201050103050d0503010308040e04060b10050d06050a300b04030801 75
    0x586820703c00340501c42c5e400400450b13a500544090440c001d94102c2d4040e59031880b060705007101c61303010488280c4240150422030001084070000c1d01c03401d45648054070389800c9514120f0290221110004441011041c4550324280f807031941880c0040441d0440410304a0aa0070348804400000c0860010380c008440d4040d20700c00c185a040e0160038280c00c9d403500b1b5000440300400c1000143c802250321000c24001011792442281d88041407805541e11602602e04038081030351403255a966010350304020518081030702841e0b04882c2d031441d03440e046908208180d55403420550002412102921a250034800c0380c0c091224421b00940001880e9803641c2440f9040606800c4c0040400c40104018800100b4201c15501600e14504c41818980c0c0d4904d4203c000300007990900e6072084841d08601e43e610340c17080c01024541c1524806000c01a9228144180c50b0300c540580382da8004646080ca5505600240b02140113640380d581c400d01c3c402da500c588503c00000d4409800080341200140000c94 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 394880422 1250 394879172 394879181
    0x70f0906090e0c0f0d170a08060613060e010905041104030c060203070f030c1718010f090305150a09120207030308060a121b080313030618020a0902090a031208060103 73
    0x401c840041c0050380038240300d951100302d58204280700307008540c9074107140c4d151401c4111840d44c2c02810b19812441e035840300c4045420a0301b001001440d003800084a6040200c00c3d00c0c030f0707045072401c41101e20341000000d441c0000405003460411001c0c1c400055541e1703403409107282d81542c2c1341800c0e681c2da00b1410203d0000c2c03019002a01503600401101c1d00080503660107072a980d40514041403201308a10f0400440814403501c0344903180301045007500b81900b6580010100c409880d50100355006440903901400c0030310000d059600b16054014640d42520358959100c240014001007040c0f540da50546071100b207201d82e20040c0d100400a10030190001c0b0b219410840803120b00d89194544025040b1000041c1030040200f1160440c81d0201c01c40301480c000500000020340791541c0d11800c494010384143c0c44181ea04a08202c0300903201c030724400d04020f41c0340d0041c01100b00700f070920703030010084e60204e03524503048115044000085440810b12000e0031081d6916000542803007000101030301d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 394881672 1250 394880422 394880429
    0x1212270409080409020a2003090f0a06090603150819110901050d0602070f05071409010b0315010f12091a0603010b0f0d1a0f04020a090b220e070f0906 66
    0x11840c040014010502c44000e480031111404005a03a0f1594a01d08442c201d16601e001070450f20304011035490140044090314440307000350707003004500016200700261058148103107004100481b01c2400070620a421484940c031944007015042e9543d03007815032510802c00c040301c400607091107101c403c10103548150801c50304115182c4c40554181b0000070300d007030b107032075001861540d000490300200b181c05e0b0f2203a02c03002c1c1c01030f09844049584008501c069585070940921803020040041000002c80041d61b001d005a020305a9540c2880401941c051041c02c04000a00010f01452140c02c01e541c0148003045101e403030b0b07500768030a15008030007c0c480302030301c003911a0741003152800c0d541d01e80601d08a200700048517441014011800e000051001d0310320381141c82d5083c041040441c07980d10304040d020368800d4410b501840e5403a00404100c035541000c40740e1003d840411411710f03c0c1c400304880072003840c030100090841d070220394035031410490740d000b088c8024290400b00302c525014825130f00203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 394882922 1250 394881672 394881679
    0x10020706090b2b090213021803060c04090b010219060f1d1209040902090f0403080906010e1609150305041b0b0d02071109040b0a0b04090b06121227 65
    0x2c1141d00f20340c14145540d829198840e102d05000c1d0710b04401c1c0355402110016401134040d99041801c101c0d140041c0d4802c19801c690043c0d4070b0506040c0e4180007880700d1050156588e81420300d0b0500c14124041c101e02c42c0028110b20030301c43d0a17108d051103907101901303041c41410001092001c104005040e10284181c402c00b840c10904004a40213020459481600301101d040d130760351055100003401044584030103034101c0c5801d820407641202a0300da460060b0700039103980d00146c0d54585072030398440e024014031004110b4080429a0860744002c1c00c4040c4000e8202394000c07030b0322071846a5207080a0221040020b403600144010f102c038584140c880c02106030f2080c0303020790504004020521031104e00c421960fa001070204144416141c445040c82c0004020070080c4c101402e1400c03021805640813440f192410103002c0e0103160500c41e81c280161b01c051700d0402030361511708103c1040d00e801c601c22002c3c0110300c8000340000400000300440191804a14040c080034106405000c0340649003501 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 394884172 1250 394882922 394882927
    0x606060f0807120f1401030512030c0f0c010212040609020a090c0219080c0d09030611030411040f090b0c0d1a1c260c010506090c03070f03060510020706090b 69
    0x11065112081c180e0003412428180c070380c1c81c0b900c602403005007200340e4640c0c04c8031700d021003d543c444806210303503040300c2c001d104823101d0f54080b40a089030f0313100548220040c0300d001c000c210320340c1c940c0601800030b0040480006007042e0040315401c1d21007008540403906c8580e01c810f903008600c0c0aa001c0310160000c0c0c08200000011090040d541e500d90005403154190584000e104120322081110301000d42c0000b5146c000003040c80182003143c19002c12585682040c072080c0101c42c02d0400c2d07070701c55900081d001d02c140e86441d0520000f01140d42511008507180c49600b8003080103281224000c4000d0b109072681c41c40d41c16140c0045a10a82203065110b031096a140c0042d550348000150b02012042240308002e0303240342c8203c100c80746415003c101102d905139100010070070405011045480c9009104035560801000010202115013205100c3c0038004540441e102d0301d44000a070341700d403c0001c0c5194a038000a91500750425914005a10807581800b9042c0e002080800074900440110b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 394885422 1250 394884172 394884197
    0xd12110c011d060702041a030709020f071e0c03050d1b02090414100e0109020a0e040f0318080601090510060f050a1d0d0f060510030201080c0304060204170109060606 73
    0x3840e041a000c2180750441d102e401000c03a5a4a11044074500d03a402041001103215800d07078001011000b024682c828081d030280003441d0b08407030080b41c034084407d084a83c601182c2c3c0d5074015008161010348000101c2c0fa69001e03001440b041c601c580650300660080500310900e500c01041c6018240162022002d50100c1d20016200d0302503054025520140c2148118501d4030f100745054441f807400041941084a01c0e030301060103511040b480c2d402682c40c40c1000703468031501a0350340d805840c000c2035060140c294101292180c103404800c0c0902c441090111590f40800d1032030210281c0054200659640521801c003c2c6245030800034036460911403040b200d4080060098043da0340d00000384140b1040800c98803d03032280001d0550002810781000e444103003000b4103030300c0040c5000c0b644540751002280401103002c01c800c045a03416507880b2440d0765907404801060700301600885205070240700120300c00744070504001000148800004891205050400070354005500c08414000c0741072190 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 394886672 1250 394885422 394885427
    0x130f0327122907091401050c1009050f03042c07021e0120090102010c0e1318080f120a0603030804080901021e0a0515090309090709050d12110c01 64
    0x10303019600250310982100c001500c401e00c064039280244410010b40c41082001c9401c0b8150405640c2d1614418600a00075001503405d8491402911229030005070401812441508400419482036055900c5203500c3c0c442c041c9160032942108003100700e1404184074840d1009640d0f10066090030380414941031100029460316495076481e00c603440c0241d01603400e00d0382500181000b0f000c079000041908800004402c81da085601c81d2030040d4204044904030b00d2050802e40c4074040d0003171a448004100811500080410041c03590320008280c541c14045104c4001400480b076100c074100c1c4c0d403500403e9400010080003403101200314503141060011aa00001c2a039106500001c1c0c140e5440c00c500050b4505409c1020304400100b5040740c414000354003003030300c854961103142210019942640d184d9148031089400c41d08580c0280718420481c58203410306a004130083c280308120603181d401003007401070080402d440b50411a400401c403c1c2d40507000c3c901425483e07014180d0543c418000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 394887922 1250 394886672 394886699
    0x6060801030803130203030d020a021009030801150314070c3005070f05122205060904090305040e100e0a0c17060a0909050f0c0105030915130f0327 65
    0x9442d00c00040001100d07a481ca02e9000c05968000b01125184c0500350b20b6040a50b00400a4200602498604035900101c0c0d0040700e010303e515494004440c0c0c2084149401d80740601c0c00d520815031210861a4044003261105010b61515560310302c802d00c0d00c3c00d040a06030406c0340700c4500c080044002940d1640c0d241121456052985482c540d0780c9801c2c1000304520785a9200546103010f220906051000d540000b040030b0500010090000b40301006a08145416481001e40104080060000c541340a9000441c0c8a21030704105092688400c001c08210b281207031451180400548103011a079103990307550342d00150304a03081c010b90011210040c140c00f4600020301218281001080940c2da403c41e4080160146a8003046084203c1c24029610b10001c1400c1c4400d0140f0031072080c080d413040302103d124241d40001405100f09040d144e142111004140c411084002c02d0030000180148031100e103420300030350b00c442c45100403041c81c0400194280707000002c22442c034030400c018005104d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 394889172 1250 394887922 394887929
    0x1090501050301031220010c0e0111010903020304090b03011805070e0a0b012102041a070c080d02120703021501120506010b040f06181d071b02060405120a02031218030106060801 78
    0xc2c10b041200540d1b2000c0d1201001c4000000b1035403c10221351a200c1d8007040880454009a0b01c40400b100c1c0204860700b2030300401009001078208102c10301511390550400d0b980c0410243c000559030242034080c10050b010100c0460b8140c0084008104500c1c00d051019000307c26030340304000a8100c107001a2012250034480700c0d490803045202c01e5002c00580c1a1002402020301d6040080101c1c01e40000381d0b8041c18046440d107070400c1c40031a1440c07000405030103410083d002040c45000c802c40498940d0400001142144101d101e41103c500756076007c60b0003071200c01090070060801d8036005080c100c0c16000804843c4041c041005160540b03a00d001c2215200c2c1885c0c07400500c0d4065001100e020340d0032040c0d1950003481680c840c20421081284119942c1d0360b05e20b00c0b01820014541d00d880b5402c0065841002417005003d50324246d152200404086012200e003680550302007030520b80d580c160051920b801055940300b06941c036440665494040b0700801c401c600300440030301109410301 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 394890422 1250 394889172 394889177
    0x402040e0403080603010e030c030406020f0f031234030b010f021f110a1806030504030e0609061209061b07052107050115060324050405062d010905010503010312 71
    0x10f0125242d51001e41c083c015400d841030590360f40d0100c03035030760603560f9105200b00c40052295102c0304e0041003000ca0110032418038007010f103140c082c8502d48025032620140440180391581000c9140750030b05c41d141200c100e03040e84035039010308207070741d40150844601110b102c0c14400401e001060b001d03401f00d00b104200300d00c10800340440c00380600c0c450040010842010fa00030002416485003904600640740199922203443c0030107443e42800c400f96401030360000c01213107158603002d02c02d1400310b018104d080d40c040d080310b0034594851624400304506658800403038104805120f0390302441d544c2429101c00400d035162421100740c0d121035680d001304031070340d0743c00f000d661640780089030807011200004d42210080c05400441603152542030450300c035440119140c58103078115890303800400d400039200d8440481c00f00e0310380800d1201805e0000c0045610881260090b140542c0341e150900e0003d00030844c4c02209090280050303e6103a8a8024605102007400100005954803401d28843c1307030f41c0d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 394891672 1250 394890422 394890437
    0xc230a0509130b011d0c2b091208190608031606140108030a030c08010b0702011107120605060a05010203070816020118090e01060906080304141206090703110402040e0403 75
    0x92040810440b40b20010a080301120001031190104c2e0b40c0da1210710107040030818103071079181003a00c0c07610a640b41c1c0000745420000c0c075450b10001d85103c030310201c01110040f9004407076030b841d00c0c8038604500d0141c020400c8401400100000344200780800c81c06024100310088c142900a69030380501103062000c0214054080100315003600202803286895049501035611081e01540b0380c0c1158818000207891b050b0100c2c0c10b148207400d580d04a800d20f4500500e003440d1900111800e0000815074116441080300000741c0d01d01c21300d5410030507401004009200d0030705030200302100c100395118a0440d801441601e011642a1048900100302c802c0e06140306840c0c2d10060f0b403111045d902103940403803440b0001821145c990024201242d0303030300c0200116170b242c03000d40c01299101d008503d600d6100b480700380b0a40021010801a540c0010007100386071202180c51442c100f401c4600c1101a0806082002000b80d4480c00340c0b0080000c4905500b4a030400c440c0d0310007084020710107010840c0c07c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 394892922 1250 394891672 394891681
    0x111005070807060605060403051005090a0804060f300f05060109120f0213050103020111150a0b0102191217040809010c030e030d02060916031203050408040905040c230a0509 76
    0x8644c084002010050421915681d0300d042540e00c902000d00095400d03410100001c1640b600454045a0030ba80721564908050030300c001101c0002c1e0248818051020700d103c00162020220003002900c1000160740840602640000003680c01c514403040100c1e00705002d214144e030b000b8003113000307880e82010813844480c0c0780c0c01c10100f070300b0840c140a90440903900d5070300f10402a0380c0100e4140d038001c0e00c03441c004035074260302303590f441c48031100f08590300e840c140108519540c96000305070140c2d4144110740c80502c22549004c901306c8264002c40e05020a202e140948507040705030302e0307040c0000b00814103c2d0b16050b01e0b040024419005000d04000202100004043c095000c000360000d01408030b8001420044029554500070f42e10801b80d40f150b40304291803409094890b40507254005008159101301c0c07541500601409001140c000c6400d0002040e40d000e0b80c40b074144698080e8000c01e41542c984800740c030024803401f000002c49007181080c1806d50f1601034651046500684400c0c525544 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 394894172 1250 394892922 394892933
    0x604030c1e0b0402100203090d152d050c0c030a050307090b0705061005030d0e0f060c030a05030a0605010c1109040305041a090301050708070c171e07111005070807 72
    0x286080348204640007221480284031400000c07074070962090700c0c54045101404010381e620701446588a910a040210000007d17054007105e03031945002c1d81e004585860b2a00c0c0603613034072400c0158100340704c02904441710f01450a00455030080446400d8614103040c4101098481c821502c019041c450008003040286c0d11910900e402044112201c07a110f0340c040c9416501c4d010b05651a06d0740c5603003c40040358915003c9510980c080031034031785900c04010001404984852032200980c014414005020211424030003414501c5071a900e256491408408180c210381503070300002d040082400c03404002032a0040c6200d840c407030840b900c02c01aa0303a46011181d5204a82100c0e03840d203440521031400d80400700c080d107030401c400c4000b032040c0e0fa11178000302d445c07034001c54807070000a00820291000c60180c08800b81c80743c10708080b451402d000c000c051410901c0980000240040000785002444900d40c0b40540c40102202d0301c181c00d00921500402c64003618901802041b0002000800c111 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 394895422 1250 394894172 394894193
    0x28090b03090726060702060105180414150a20070b15041b030b12120705030705014b0209030309040509060609090307030503011a070b090601090608030c0604030c 71
    0x1210204450000b800c0d525401c3d900b0100e04040c41a440303410b0200b5100e600202d00f285c165078001c3c000c500141e00e0610000d0340070b81c3c0903206139078854012a180380034960a0051510110380b00e001402503007001004441140c1030006c90401c21450350030050817a1305110704441000350040d0121200d0f44500810310005150070010326803241ca000ca8030400d039103c0d000c26044a05040e10100300082065081c4000784030340c5003d07214107400c2031180c0b080010031134001c6c0a189024200300c13410000260b40f0942102c0403042446054000b5103514845440e003d141c003088000f0302c107030a94901459007003145000c1f5180504a4800380c010030b44030034941b010400d441003018020003c0c4a2414505501c54895a050b5002406010031030006184040d00200b241c18055242d0b450929580c41c14402c1e0f0302e800006c66681daa038400400c80c100200700ba40e00e825024400005c060812540340c00602c0c0c00311421030303006400540007448454040d40e000318038141e01a030035040804891540b49070012220 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 394896672 1250 394895422 394895429
    0x708030315040b210f010e0102130b070309120b01030c06020a05072601060902030603060705040f03080d1409060108060907030b040209060a030b0a021c0608030915090406080328090b030907 83
    0x1d00701142c00400c01d80045ca068581500030000c010700858070000500340e124040e4401c444c1c82c48807104001e590b440c84010001d0354000d250030140b00e034030b5460054100f80c2d0803d094a102c5000e03401401803100e58001c400041603940010000a54a640c800c0e485a0a0307110714104c000341711f058481501e440ca02240040412607008024040d01c81000c4802500142c030118000e210740c1000801d854011801c031002e40e0070044801344d540e85150b6a181140d4404015695041d48486da8000507486010b6220301072040100902007643c100955540b500310020a01062a8007884080000c5440c9248180e00150180c9404406913144000f0809203101c1d0360005003240f5006040001041c0190301600c24600200d0000c1d4805405207200c1090b44c015014003050f5800400c1104050710700200b106503280c0b020b688103030815000c1000502220956801140742d508001503c00815545201c180208600401c10003009040303104010102d9029000f0103c0c4071030004003142d4042d03010001d82008 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 394897922 1250 394896672 394896709
    0x1d0f0f03120a02060103050c0105030601081504090609030203070506060105130b160206190206010501030212070c061b0c030806040507090e04140d0c150b100c030e04020414030708030315040b 84
    0x850442c400c1c02580c902003444140d8090092a074520510361103481201e018a40580d1100700359115010000e0784000b41500c81580700c1d03518800e4000240c03490080b03c510500907006151285031a0510504001d0000c25460402104011b0603040425030004102960b48066039151101004403400b815a510714401030352265001c900e82c207480304103101184032490740d9801d13221541d90315070055040e80914488440c120001c0000101114812920102031034014540400c5a000050400860113015204400091042e000c904240340d00035801507044042628100039901e4140c800a02c0b04415001d50000d4840300000726040c407031404041200107104c0340648a103c1c00c40c2002030b00c681e000703080854100010f1030a00708425107500c644140c00c000901391b06200c43c00740d41c2c1251032218041048080c0000142a03030030300d844500c05080503000715910045600360360700c01c06203814195400100707260320400070401d03100200021540060020782d0041030581914001481a07150040300010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 394899172 1250 394897922 394897927
    0xf02010609050a0501081005040201020316030c0614060111120a0e0d0507180f0b010914040e0f0106031b03050d03050a0e01051303030c021207140c03030f07031d0f0f0312 75
    0x2d80c1d841d0f0703124a0480c0c2c084807c9801603410a000c03041078803003c650190244e0010312109108401443c3d0b00c80070b984c460b2400080c0c240066076606c0c22907a0200d20010010520b408015865811903064810038148000414402d4000e100d128500c3c452107100d001000301100c5103201c9030b00c0312400c10341107aa2200075655010344a0b9022155402d07034603500c0b00c1c954149024844017010910070301600c02c5040e9254030016003000040000c000700c0844131600150780301c4502d4607208080c410310315030304005000411a00c0c41d5084c030309100301c1155082609090030a200300000703003000403c02d14800440c10003181ca5602d01131020005d02411842048950825040002e684c024882c4008214400d0703c04200c0107606403422690f4041c44d01c0c1c5000b150804009490105003200308035403820040c2c10407500d10b200f04101081c110382200c1d02d00b129515020034903008254106a40f04e1708110500780104095450b4000141041400e00006000701b03004070114803152018410800700949035100e459 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 394900422 1250 394899172 394899181
    0x5070221090f060c0c1c05100509100c081b0a080106080703060b04030b07081f050105090a052211030f01060e030c220e01060e0c0a1b0f140c030d0f0201060905 70
    0xe440b202d50100c079500c280c036050002c14000c00e52404a00a46c0e0300714000f401c044030020396a5005140141031a0301e984960036801d42d683c0c0440c020400c0415181e6103090700303428000700d0900702101140b50101c2d222024808005001d9200300d1460440e0103a2500d10740907151200160014081e40d0443c0149850010780401030182a100160003a0081c4d610388103c0d80d24100368980181240504400409200004001c1988150b01800c0e00e050700070060400217640c0c078005410024001d54130020742c02e2004d0040b56900041c0301d80707280d40d0494140e0b2895490000c03455004e0711814080e52092107007221505c40da0b914104180b0000c200003800048004004c15040e07200c1860002921640604140c1c4800085906008030000c503440c0e0307551030a00703480369604001650040c0c0e43e180d040111286603c80500b15950f0640c02e264082d03400c02c4070000d020304100342c4840c00d040c00400650300c0701c800105140c4001501010300c0e5500c1c90710203c0c003080114203e024020350740c00203c9040c105030500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 394901672 1250 394900422 394900447
    0x31101020f0a1808030301090c030b0a0f08060906011d0a0f110408100603020a03030309021201050103080d06240f05090909010b0a05190509040f02030312010905070221090f06 77
    0x1018019081d450f80c00030740e10880148041038010b4092032050307420900041004001c180c000c0001c8403920b05001c21040ca001d80802c0600f00d480d03015820750380210700c0400a03494180300c0d003a001421600902030302c0d03040c10b4400304664a4519511074009a81000403000985988003041000b82150244403140100c1e11442045d000741c0515440c0b40100c41c100c40c000740c154440e40c1c0880f0360140c00d0071126455510b0503001421400000c1c0d800903070303442003189018401c1c46441d002c3c600c50412a07859414454000b01110031036044080030041558620043d200c10410101f407002642c0703010101100701080440301406508001c0d0780000360802848034a100c19000b8040c070381c90546004c00311503652400c114040540c1d41031901d10314203d03041482641030442c0065400ba006205601001400341d02080c51a07200308110240017140000500c50003046004181e0820041d10050840300302c11041c45070694210ba0b0111400200010005a6901c030070f0503456425400034189904c0d450f90301c0c180c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 394902922 1250 394901672 394901677
    0x4080d09061401050310060305190201031d07030b010509071e030e010903090509070807050301060f031103040803042f0904020d1a1602060106050a050a030906020318190f0b04031101020f 82
    0x40a1086c0101c1800c041e0103505445480204c2e40c000b00100b01001000d186a0841d941480e0107a04054650750794854040c0c0082d130315560342502100074500c1d00e2030b500b03002ca0a0901030300701d035128100348014044074951048141180c2401b00110f91072903072030390009900418030b54030308248135400e00100509040d0402c0710f040444030140ca901c20150b4034004100c80b054021580700c0041807082c401440b14610030080110500c10302d05000402d00680b101d01d10140d04121011200d029002080104201800c141c000c1c610309a440701c01141c0703180c0c2c903030400501b5107103400754040c4101c00c00286c150354400c16203208450304482c0c002c0b000c117641c509016017144200c0d80012558000390314011070910010b1581e048941641da61828041d090b4001c449030351011010b441016100d5103083c011903d1b600c011805041d1407440024403840c400303034050405101040340e1940541803140840441c90030409908695401841d41c00ca07a6110718040e201820001e02030303d071642c40411580a203c40e907000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 394904172 1250 394902922 394902929
    0xa1a0703140426070911030103031b0506010501050c0309150c06010e0f04061d010e0d0f03062603040e07020607080f09101e1a1c0b04080d09061401 65
    0x840746052516400e401ca250310a07071003008202150320740c0401e900d40c042104030450407907290070ba6a540d41c1d5100003505a40c035550703100d210038000200410030150040380c1800034210f120301121101c500fa417074681c0c50300014400d65060010000f4040c000c40c0c4180b048a51401c0010070141e00248000510b500c0d03500100103040e410300ca040000314030105000182403003016550a50202070f90b8664514000c2c05103440c0044644150013000c1c0710000f000e0090140c6d01c89508001c00c0a010003107c010482044805000700781441e00400f8030400380c10f504120002c946403040d03074455150940e0154074610a40d4004240d144040040c40800c075030101d08503000d80c442d5030b106022a160350040388000325091b1900b844c1a80440210000f041c419040440b441001585601c07d456000b0180f60640b5007001400c81081c2c001c2c2003840c80c03458881c903c814011240c00104062038440d60300e82072103210141002e089000c012521140c1504a0341001d2440383d4040414000d14515450000850b5020700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 394905422 1250 394904172 394904177
    0x807050c04060e0f040611090d0b06011e0903111909060306060e0708040f02010905120109060f051e040204020d0615021b0a061103040b0423100905010e0a1a0703 71
    0x8000070f501c003c004070b0b0b240070f000c60300559215a1595643d403401401c0c51100030310000d00602c01000305039190201e80304414001d00000d00c0ac0d150000004080300c803000b020342c4035440b0300d208840b001d645c0300440e41c091f0b0b580b02011303054248110300051014101e028003407030035011065010400702483c0d00031404030303417180c1c0f01406116212502203000c0d110072500303000002c000e100041e01180c02000d9280a0340d0041c101040c507640c07202d0110300c00342d48085403610969103403092401003104a11a0801b4005560010031490a02c41821540c00c10402a003e0380014100302140640d510f90341151100e4030b4418007004000e64800540c07000740760610030f007800341c085c014091410406401e4502d44000004042c03407400c50801c8400d403803c080c60041804144404c2c0008103030f81801c4070040c0f01520441103a140c00d41d0740900b106130040141d0482c51700a401ca249549400c58104000000350b40090030004a03502d42c0c08042101c51050b68010281c88090f070074105600e40c14200101403990003a13 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 394906672 1250 394905422 394905431
    0x40f0c0207082a061c02160302100905031209250305010b0a210303060312050c0d02030a09061b1a150609030606040504030c1a0717071710030807050c04 67
    0x141042107195030503484503668111540d085122501d08080103100c20b04400d5203e500c06000c00c00c285c07007203030070210031030402841c0c90000a040c035404011411051070030034024044407841c0d503601c648034000c1c464441691102c038004078032021010320580340741e8140c40ca00805101c0941040e280c400900b0b1000b50391552801c3d0400e011070810000d81420758948001d0b00780354160f152103013001d01240f1042902055521400800000c40d114071180844031681d42e46c0752a10181e803a8141041003030700e0b03100306540c070402c4080456034204101c1422101541000c4544201d81058580d4030b101c18032000340b403074690040000e84050b060001502502c1d1800081412032019024410780d4800ca00b5000c2d85a0f11000c0081c80c0c5150540049620611034602940315040b07c1da0f070314000340341a5070114400900401002440b5a0213090390440d850340201100e0359040829001c0c100e0207101e00060401400e01d030001c1c42031544002c07404021580a19081c2e41e40e08075041c55519407840340720081c4180e082 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 394907922 1250 394906672 394906693
    0x30906081314120715050903040311090411030d0f0806030a0f06020d09080c150c090904060504020a0f1e0f06270e070804051c0207050906040f0c020708 67
    0x58051a104112206000841d282a038645005019550480c00e00520807940304070780824107540a01065031040b480015045410b2100b8401e90758010000071442c2d005000801c0403484507018542080d800313485060b219140c0e030030320b44e083d032412031410741e0103110360003482c0a01d030344c4004840c0001c21550345280e00b0b5155a030400da1036101c019009001c0b40520f01c8240e001c25003e90042c001c0441000380010310513001c0e950280e040d0000043c0c0880c681000e82d034050b1200c00d240c402c582c019150741d043c901d0804040002075010501402c05040c9aa079240004c04545500700d03c503001d003070001c0c000c1c0300840c0e84036064100000c50401c801c660140f51b83d00050441d000400701c0c8143c0d20107032551881c4054007001222524401c103c01a10f083d4400000110001e50180541c011505070780c41c1402841c241c1070482c41c003200394041044042c0140d604070f41085d0b01080a406440341245d01d81d500d40c407080c00090181220f50314480c00189028030707295807a5000203400301140d54920645407241c070f4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 394909172 1250 394907922 394907927
    0x40b1b030718060e010f1809180b090303041e1a0c0403020103060509101a0904020f04081510050f01021203090a02030607020a081204051005041104060f1d101e03030906 74
    0x11091326143c04a44c0c00c3c00072250103802210b6245030380c010401040009903880002c9016680003e10000c400e6202c004824103010501c207001d42d100107100011351550030241e440d600e4880700c0c000e01101c0200180784000400a8207003590158a170710262003140390a090f1411100c941c000e210480c04603140c40303030008190404500c0a0300c03a01100c241c00802601d020600c0c0710030b80c0302100c5134041d86d80810010440380d0303a504c068254004101001c9403038a0401400170710300085095602e036440b661004001072545000715203419200141c590310202079000b00140d00e000c0b4500d01c41c00b01e0a8002c02003020446001a00c40c0d01140201d084900684407180203a0f01c502400c0400341018404100c0010805403180b01c680d0003d1281e022250280341328400c420031290207a804031081180c00e0103000f85072925001300405080018081d41070356140400380000744100d030b40382c0d0104142c0e81c00060243d581e140100c200501100305001492002040741a101c0e40c6180001c03008210210300c041400c2c0d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 394910422 1250 394909172 394909187
    0x633040903120f2c1c0305040308010b0c10020d090f0f02181302101709010f060501090501080a0507090e0412030c0f30060b09120f06040b1b03071806 66
    0x1088001c405216040201c1000d0102d1003803c882e885a5045100174003200d40b1400310505071036074001410705203403170001d01209060b80820304144007403062102c00c0d28081591110042011270050391800c0015015000c0c000f4624007410748488424000c0074040c0e14882252520710072180c804880407030300c4540c0f4101c0401e6035006142e401080c0d1b03500060814864818a03a281400c0980a000001040d01680340080703034060840d03515403207203003404156400740c08003612003402d0000c9180c2c02d0000003020081c0080c07031a1aa661035402007841c40f806601c0e41c9000e403801e03404d0807009107024209404040c03004600503000900c0c4c19a03405680d446501c03c50700344041940e51001c180030702031911004000002c260300d00d10704031031040740d0000e0803449244010881c5410440d1601d12040030407006042d60441e1694503004074001601d80707038010503010f0380142d1100d200c10b01c507260032401c0111160010368201c1282400014444aa84c0040c0010b24024141d4000061551a82800c40310356 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 394911672 1250 394910422 394910441
    0x8010e12031306110304060b0a08030f0d0f182103020906070803090c0a060c140f061303020102070c0603050f0603070e0112110d0b010302030601080633040903120f 72
    0x444140003180070b9000d0304129800c0140150408500d0251486445610368010355048030142c0c0d030f600480615081c2010090b0050400001450074031540503d484450311039642a0281150340780021400010703a40c0c07080080e5030303441c42c03417005046940c0303488903541c96400929050021100d66010906209000f1034240788006070402d4100340c00381d0341d40c0c0829040900f07941454002c0100d2145551110019900102032960758810303e182e00341003400c500002c40d159104aa008140d003000f00920014105400650070900381454160350704089009000311140106a00b010500c0000c071254550042405042690008012030300c49904041ea0340320244151880c803004e000042010084101142d08000c4c0101d408055004041c400184400c0301c0030011200140c3c03040c0140107508041000501402e1003c00421041c180510074076040d08800c2e440314800441c2c240c0c16210701e0110a100d80c1e905401078014024941145009040140c001021424440c0307850603282d40410540180b400c803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 394912922 1250 394911672 394911703
    0x7050d09090614060d14040606050109050105071a1e09060a11071110120216060e03040f0b0702010302040e070201050a1b1d061902010b01080f220c051908010e 70
    0x442d9881804d102e0b040c0c211040c400480c07950380d140d800c51a43c0808005105600c20440050800d0a00d0005041844281c00c45030401c081400303108006110681030f14a0201c5408a030341c074540e202101c20303215540d10460180b00880340000c1c8619510f001880c0c41c0140361206044c0700c0c10544500c6c4860303c3c0668403018201c04420480b02a89003080c8040758990041445d1480d89944a80150000e03644020600745075407420f81f07407070310a000091007021803c04d5404007451805240c4102c0b00000000f0b401102c0d140100011103000316806541124000c0001c000c1d9800341d8130b032000c2c02074020102222003244036070600e00061169640185188900310b02132306d450304142c605400c640c1060341103489982d0402010444805181d6103840345400711256a400480e1710401d290004000030005444000d00b8007140007446100d66000c0d81e083c1c00c0d11030001140036104035501b00760038000210382c001c41e08880c018980c0035054424003407040503600444004e119214130680e0050390303010300c424001076 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 394914172 1250 394912922 394912949
    0xc05030408190905120705030c24031302040e0a0308010510171806010b0703180509060409030e0a0602031201140109061209051615030605100e0d050307050d090906 72
    0xc640c4003000c0724800b119841d14500ba40d403600003080c54444500002c003696400f0b404200110f1400300011000d501042d601e034800c1c588656011621802c0220310880010b07404400524401000d5942207012600100184054000b44c1c0c0000d03121100d0000a0380012101d00000c0b80b9828280300e258124449661021003e0b68080e03641b401c1c8181c01340440020408100c0c400d100724800300000740c06080107106069544c54946005820400604403800921803143d030100040c1e0351364000f480d8030010641d008200e040103403908554402135000c034540c1c807803074008012442c0c40d800006862a49040b40c0c038220700e40d8070741d0400f0780c41e01c124009450000324242ca050010512480d020401c0084148010a9a40d12030303440c01d0800f08a180303000c80322100700c60100030107205460244e8022826007001c101860819011a4401c1d03422600c81050140354202d90009842c1c159040032083c0c2c04c8026603440d44a185002d641340c00d034051100000070240234002c02e044450b44078100072620080c1c503821 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 394915422 1250 394914172 394914187
    0x509030301230d03020136030c031106090f010e0109020d030509010207090536070302060306030f0f010218030f0a030807030b0306091e0a0b01030602030a0e0a14010c05030408 77
    0x641c95040b01000d00d0205069580b4490181c96030741c000c0085500c40d03000860400d4074101c49140c2e071fa49000310707080a40300e844658420080e016000c100709980610740340c110710030141416183d550001e00c0120581c450031080060b0752101188044221004030024044510401412802d0307c0782508043d5202080032000400280600700402101a0600580d4131459a43c0030400c216142124404038614502d402d0204080c184405407040ca01d1180c00ea4004c44130200e04160785641901000740209400004104603a40820032820340040b104100c0d001000d0041500b030107504003c05103119600c5040280250b86008684012084803075001400329200c1510203e034407000142241052550300d10500000d500c05000d06442040408010000315070500d1380b8151031407010003040c60341c2e00310200c5840017440355110307030f41100d0f0020030250301c0703441d000c0c0c4100c005c10b401e4480403078611852417041d00304042111019440030464000700550032400d03009403410703c0300321001850010100300f001d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 394916672 1250 394915422 394915439
    0x50f01121a04020f0604090b0a06082512090809130608190809040c0c170f16080d06120c060309080901032c0106080105090304030203030703120b040911040506040509030301 76
    0xa03030243c002400800b404c24281c01049841d0310607007011200c45c0d180d0b0b016070807600304407507514001c00305882c103200145043c2caa280242506001d03080d82440c4c420310001c0c1500d100e03007a269099a012402007055580328508100d0541c4081182030095000740f00070503009510340b04403022503010001601d081c0c1080030481c4140e83c0c06c0041110801d0b401c0c80440000d0302c46100c7c510581110340c580302a251114100348055034041e020300e0000100811400c3e1601c04808140c88803032004258101c3c1d4844117207007411041c000e9508881889141110005011400034203a40300280a1480020326036144e0101b1416a00c09000262811008202100030395100c1d6228045181c5409075904000c24980e20f00111481c2c901d400412503916400c041c018800d0a109094220540c04002c0d840c10f072a50b03000c0380c0c0b01d018004010302030041d04131140c43c54017010f8002948605008000300041005440c000d11411086022a40107503c0c02c0300107071190809104290107401124011401c6a20701000c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 394917922 1250 394916672 394916723
    0xf0703080711100c0e0a0602190510051518060d11030115030602190e03100e07080303270a151107021206011415040605131701050f0112 60
    0x2070810018a58203070002e0081c14410507400d2104080081280d40089000401088a00c108544102c1d10038030308002003900000c0307039004001c48140d4440402c200d400d250b8240b10841c207181280500300010056641e40c4242d070024025400c0f81c910400c00d1624008040c4560102c9500f030700125030b10025004203050800c90031a03100700500206024190b55001458403815900454540390046048442c80b40004107040b42c070000c034500740c0c0300400140000f92b650300e03d40448841140d52030300c1c4c010f41c0c1c420521541010b440c10404481d56402c0c844190401c00410f030180d406c0241c0e40c03440c0c1119000b40411140c189a070080e0002e010700c4455a5590003c041c810b204055150b0204541001a10340318000c240c0d5581c110050b21483d03242c01d2001080c681a441154801c058500086840440d50301c103442c2a2001e9180c40390311004070070b80813550034905801840300e01e41146100d0b4008101500000d01c10501070000140c40e980c0c40481c0c1e480007200c1c05004041c20081c0101e400282160300c030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 394919172 1250 394917922 394917931
    0x5010f08070b0a180321030612020d0b1302091503061b22271103040215030703090c09051504050c0906030924102301031a041506030608030f070308 65
    0x1850658945d01e691300307138480100704010a4001070a0350b6940341c054140c40303401c000b000044005c0c0c4030748507680c1c00500d03494602d01c0c0040038942c0039408101d1401c5032030050b9140315806002d01c81107081824007000d060550b011441d2191080f0390004180700c080031500c1c201545907015180c2030074800c4801c102d0141000c680e55041d8841540001000d800018400b20704400704038140c004820a882e0b400d0583c0d040d40070070001075804005100058072401d1442c0421f00322000600e803170303480b002021005015510005404443c0c0810003242180e02076201038018041038805c0034044a104051000703030754040340c400f502000244100312150400000039903000309440305651030030405040c001c070f059054450f07080040d412501007082c004e0b143c80401c4058a41545800026102081070143e24107010350207134101500c510010001642050200c4080500144203008010603c1081c0411502e130703100724000a4200310001822020200c1142c0a80482066451500c9034a07102039170007650152 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 394920422 1250 394919172 394919207
    0x30507051002131a070309060c050106051005190e151e0a0c03021006141e0405090c01090608091b060f04080114010b0313120c02060d05010f08070b0a 66
    0x194010341c040c44074401010616007100039204028103110250b0954002c40c50030300c499810800c01c00c8003094000344981e080703c0322817030080d406401915025001d40f082e40d200c00d410a00241c10000942d070070001821443e41c0701c505260b80c014000d10105e82e0100360301c1038150403000c01072004c803001020030004d0290580d611850301c20580ca0005030002944046c2a003130002d018900340301c0c201603040c0031b021000300390481c00340310090405000850b50003a130012a881100080b070400109810340761030140d0716000030803c11942c0341804402c3d03110840c8000441c00100c1619000c00c505004e8030029001704110401420641c5024514100d40302d220707034885510003810300c08807000710040030081c4050200b820011a0b98120722000100651041e0442c001000c4107000300f00d45244481e103540e8209030405d00d003d1600b803d400701940d0f450b00d401e03030203500803100043d40c01024029410040c100e84048a0b080812561141116181c0c02c0e1409103105903082005454141445084801f4040b05480b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 394921672 1250 394920422 394920433
    0x14090622020c070f061103031005040b0409060c091a040303140703110a0c030b0a020403020d0b060a0f030501052509060e1f021506010f020a03030f09020301050403170c040f0303050705 81
    0x19080c80d19108144d800341c82607028104003401202e522400c04031180110600a50642c00e09405605490b007203801414003550307560106042a40d5503800200c036458002d00208411040950010a10185d900980d6000f01c10004802003001c0f42c001203c2c101c03501036031850409001c580c000c100d29800802c0a404000d41d548002901c030005210789007105200f000e580c4c00061552824209000b002070000e000207106201c00c00250312402030955000798001400402680c80d01c0c00555016400e4000082c80009003201008100d415880b4600900c6154040003140342d2030229130800e03000c403901e0310300007030340030007040142c940206240f00a040c03009203060305003061010660142e02401100c03000590042c202100c980300c54042141e0415020b18008e05085040c141c040c1d40c0b0402d4500003810140d9070350008001d04000d078011526150300030001c2c022411b150400502c6450060280440315038140049041039200004890132a40c00884c45085146161419501178010f501c05843c0ca0095 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 394922922 1250 394921672 394921687
    0x1060902030c070c090c05030f10091508152719030323010608180304030503040e042907030902060909011e0509100504151802041409062202 62
    0x5500155202c0d440b84205251503001d03d003032902c0003202c0d070b60203061070b58500341e031040030154080c08403030b8171130000a200300c040d0b1900040302d14042d032a079002d0580702d4500605038401010303161440341198420400c44e0400700306c041658809a40950380d19020b4900d498189a604200c01803007042118000b00b510741c401d001580210225149040440010341c0e200c0018132030411030713032501f441e410714044c1c1120550f040410180030304402401c561b441c1014101041e105480030011140a140d00c081034a0b100e55443e0811070f13034075200303070b03001c0343e200307400c40c107104441c03d024030f502c00c283d403000d5091408079101e400050f0010944040160b8101c03104011248082e180d20a80500070110900340f01003500c020303041e020714040603801043c42000a54280101c030703024140f8040c187c4508682c00550782c2c005096200b0039055943c0303c491442c600545007106a24075501070011501c4110000c141c21038500708001c20b820741100c1603a400517103a513442a405035507034415005104010f00052400d0310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 394924172 1250 394922922 394922939
    0x307050105070e0406090c0f030203090c061b0d08130b060406032102010605060c030304350901230d151211120712170f0409020a091401020c0d050106 66
    0x49500402042c0f8039501110941030601c2004001c102c4c00f81c1c02c00ca408000040141000c0d91180b61604258000c004107a00100501c4645402d0000a02c5079548a1010213043c044a89404840420740501d500505440d4084c981e124443d1004010b540e905540b82c1d82e40075080710000e40400c2d0001e03a501c0c40400002c1301c0c0740d16030301d814950701398022810342d0b0f00c00001e003580d20310b8020758081c1c2d1b01800f601203550b000000707403078106510559143c54403c4480781e00703003c01a182020522140c107019400300c4000c03420001c0c9015603007130340d030000d102c070041c0c0c4160000004640c01c080d801400304400642c0881d10792118805900074007a0400d829a503050001b41c190b841201a0b40b0301a2110400320546060005100c1c12100790002d000c4151620101d038615120000018206224900c021143c4a04410450b0341140c139054240d42c480c3d07154503580e0029000200c001000c10540c0368040f0301044060b0a003100034105a00800c0e128108030144000c10021000c12289992120008243c201 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 394925422 1250 394924172 394924181
    0xb09160602010b1504060c021e04050f0403030e030901090311120102041e09050c0304141501090b011205040803071805090115090911030403030518060903090102100b0906011103070501 81
    0x140c0d800401d020f40303030004100d28400304210114102d6010881000041e4000e101172001540448138146400c0807580701c00391a0104429060b480b03880c0c5000c1017840039022030468011030003540d041003240003001e00e2540c2e038410060080e0124900c0078042001034400a0342140c0800003401560f40c0b030483c0341c0d181e030983c0c22940051a1250880400c00c0d0280e51500c0f1001c010404500c00b400f15040011007042c20344005000035141c02d0306690b00c0703403100704208440d072116140164210519a0b588111500500f5001100c0c4c2c0003540100c411910040726000d4036005680190031180b840d161000d0a03601e854203141e4641550b6002c03400019941d0b2856a0706000b0040c483d02400d001300c030b90400421000c5150800090b4a20300041c2c0106e0b2510181540e80c0242c5c5418002415241c0020416640c08590303998011840341d41e0800548001c08000351413040c400307808584948503841c0034942036402c1d8101081d0003902090000745650712079600c0c41c0804c41c000040e289891000d4482ca030130358 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 394926672 1250 394925422 394925429
    0x903080f09010e030a06061409131403040b0d060e0c0a090e07020f10020301080c060708030c07150f0905010c020f060408070c03120806150306030a021306121103011d0a0b0916 77
    0x8a07501c00f400c02184184230810310b5640011a5804161300c2c00304509805100c2d0684003820030782c01c1d40105c8102507410001c84028004899007144c88004460810010b04602c2c082e0080d948695404200007503001000d4400404281e01e40c04030075401d03c054a52400001005502144118103400b0881082485150341a19008001681d298101047e0501e40540d14401d9030041d17004200322404108410b040d0390300425085071080d62480a42071000c0722343d0750007509070f003141d00d0038030320100c03411181e84807c1e1600c0c450b80c000c0c09014654041a61105640c070140b00c00e90300010002400213100b07000a208082c850540c0344403050b105e885001e0b0000c10901c042003c5038240050000c0c42c41c0070041000800d8443e503242e41340d40b41c20740109032078080079400240a40d20000d0070f0380200545402901c0a0202c0c280c1485000c515802e0031190388090030030050103540780034000d41e142000380035214010b03141040100750b80c120959070310000d03040040045205000702c006e452403039002c031401d04004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 394927922 1250 394926672 394926683
    0x1c0506011b030c02310203090a08040603021c06080a110607060c0216090c091203030e101d0606030309060307050408151608010e0a0207110406031b060903080f09010e030a 75
    0x2502e00070700c10310002c4c1c0d941c5c4038000c241074017402c404441000c0d0b0200c0d002240c0e504400c0076840c0c0d182c48102900d4a04900c4004283d5440410041041d5a050b400f91000105220308900c0011102202e0401c90364a170188050740d4101c004000081200c994803108050006400603143c0340d0107403901000c4421240e81800180c010140f01700140c84580440005850361400800c08003e8688020f030404c18103129485c05078980400500900d0301a61010815000c1d5a081ea0511905803041c90700030310600030070195036250f02c19941080d00d000036000344079040180040d481c04070510100421a00024448020400c0030003000c0762000b42403001c0d40101d0006031705050340b801c040b41510240c022542c4100d041012060040154914112481c2d410282d40500160b4503800b80c14000c6458580d118819002030420000001300074610403582c4407855a00c0103400d419454180c1260844400c0c807000d00155018004044c000c645003004000c0d04c070050400d0751050100001003410b08555010a841 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 394929172 1250 394927922 394927937
    0x3090507180b011e1b0813030506010609080f2d0102040305150c070c05010e04020408030c030403030f02190b0c0d05090d02060a06030c090509031b03130603021c0506011b03 76
    0x159560090340c914078440c9035804d0ba048546124100900d44080601c0500c000014050b602082c401c2c0e00d0102c070481c01001e160020300c95104c0c140280e48810038840e0200058003180002070811010a0040350241010040c1442070740e511003240e11440d11103100b2605d40c0200d41c280108180906c010002036110300013403d2240ea41841e07040038071000030003a0042281c20001200051501070900040e1602404c00308040301109001c14002d0240d0380042125200024800c188400300001501c21a80b0031b41d2100400401001d0803031b00c5244c0c0200d60703038550107001c504800058112110039032050800c86d02900307100e25202c030541076a20503510074140d40c02c03610800d0906075051240a43c003070741c0e1203024807800b80703196170f00342142e4503038032a82c240f45580310301080004105004442d0860307043d9914040c600e072040e400a40fa9440b25030402303401598440001041030190013540d4400c1c00b00001c0c10920304503c00c1410240c0402010300d0704101a480102c0417038003042c41c410902e070780290b0721142c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 394930422 1250 394929172 394929191
    0xb0a0806100509181503010f140108120409110d24080303060d062a0801080114150f181003060b060c03070f060b0d12020105070e100309050718 63
    0x5550052840715010007004114100864591144600d40c0b040703098601c0e00980e4a6160001942c241418101e605500300040700c00c11200d284c200d43c901c540b1200340180166624024244c0e0340002046080c0940f60a000400c440510399020f010b1281101d0422032502190908080c219001c046480c1d400e00d8401412401d40110360b81e020002c3c02143e0021803840c00d0103c0000d0080d080e400000b0010b5850300c514441215050350503811411022207036004102241e00003400d505c0090003051030f151301c0e00902c03240c203004000e283c9002d00c460155000b11808550f0600141030010904c09410030604405601c0c6201d07943c18180c4140040043e65409c90308500e004015689a86600c900c42d803820b21001d10a94400700403039003040e03480175080e84140514030b000c1c00600b40f6004e0566128581410450a21425000021451000380e000f00500da071810030641c1e60100b40c40280382c00c5100000f0360340441d40070354080c484c081d004100f15910b59985034001200a50543c0d40012441d407540c0951 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 394931672 1250 394930422 394930429
    0x30804240204060e0d0c2702030a0615090303080f07021c03020d0b010c020f0d0f0804060e270402010f20030706060803040b031306060302040905010605120a0215130b0a0806 76
    0x44016032000c44034a40800459214400b040c1b20703a016018080d0580121145c100c01c2007003040c0c030004a2000159200d1408018200080240b44110048ce41304407021940c1c8a12407840700080d40d80c0341d200d00f0115210950005e6010390010024010342c03140c0000c50240e200310000c0d14088070901da03005030b40e5060201100095501842c0c026061001c40841c50005039140c402c69a4514400d42e1280406803041c28140c204808cd400090700c0b0460000e0081600395002c00318011419060f00e10454074142442c001207401c1408019509040d403140c08240150320415040801e540b2a00d4000c003601c0c0140114110400c0d030120f4840c0c01e07440005c201c0200300303007406040b005210400c0610b04107440e144071104948030060041d455a1a00030000c820445140d10020155802034420842595140f9003107000f400701c1c0c058036200da448140600c10311240003d0b0310039650b5018141c2a4031541c0781c18035449a40000c1c0b000008601401004103a82c07a83e080039100000556440e05410704242090 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 394932922 1250 394931672 394931687
    0x14070c03140a0302060a0e071805010504060e0603030a120b04060803041d01080709200d0905010e030a050f0c0c120307030e01020d090e090a0b090109031b050a03080424020406 77
    0x4280c9503402c0b255a04002c241c000c200c3d01c2d84070380815800700ba100c00440440b803c00c03500d500300750f2041c60760060f52080d44242e5403050381a188203507020041c0390380b81c0019850b480000c65200d030f45503100b0003400d1642442000b4020324070340138800100d1a42c800b100020180d80c2c50b0b41169403a5440842c04203c10605403280c00080c00307074803447c820a9410b22030010344948850080081c1e00d500c5000411188480031410300000d06000c2e1200e488240762002e1070040c0c00004002c0c2d8182d030a04620a901100c040211a81c1d002d99407a0903262906680c00c3c5152a00300c0f0b00c80d03c2281c020000011000c0d110b200001544903880400f41d9507030302c094038016200100380e441030f0341194002c8070207040c0e007a0054080b006035203802c101c014081d59074503005898440345400003846078141205009032000e05401c260142c034866110300e4100085d01c4203400352141c00c440701900c0c03940000768441c0464081e0f84c0d1140c1050144034a01070300c1120100c980c90301d00d804100140c0b510b070300040401920b58004030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 394934172 1250 394932922 394932953
    0x11090c0d18020a06050309030c030a09080c0901080c040f0e10021c05010302010504440c01050f031f08010e070f0e040507060503070219060b15120a0c14070c03 70
    0x14070598108541c001c54401d4406004540a101c0e000000c0340340d14000300b0541d024408190100c0383d030303a020200020580101882040507501c07076103000202e185409102c80707041c0e414083c01082040b40407404c11014010200e000e010311ba80d1003103504801e4200740110342d07000307403151030140c1c1c0e5480110450306080c03c0307260903006080c43d2500600041c2c0e4003074103c42c01c0f100c41c01c0c443d008201c1110002c0d40d00e42402e25442c3c0340100c80016100030854007414100402c810001947c250321003041c0151014400c129101c1c074800020800248810440c1c1c001584107002d5800e0b0904094403070341c10b5400c40c0e000e003440b070700c1d0355001c000200b1014441c0710a840c041d06405c05000d4060426948240c0e07180c6460242c0030504c0000300020310268030801860317008002c00d2015030301381103c9080c61802051810b4209005001d40c52080182ea01c48004403850318402800104580d41d0707441c00b030801001400000707001c101d00d500ca4402c0380520400942400b50013440d4903284146546010203131650b6210 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 394935422 1250 394934172 394934201
    0xf070810030c05060f16110a0902090a031515170d0f0f030f15060815010f0207140d0b012606061815030f1c09180911090c0d 55
    0x14800126441002d80444900b41c404a80300e4070200c00701c070030601824032149120441d80e105c540505c00741800c0c1d0410b8090a403003c010309034a4004580582c400d038481a5002882c600040000035a00400782d4118010b01d20b0001e00241100c0e82c00c0503106543d401304103c100709040a01c40500d0074424402c10054904041304800c3c400003014020011400300b00c0103040c2c0e50083c0c401004456080241c4c1c0b030242c081240062a241c0030701504140d016100c21410000200207a4601d50090705011419020f40c3c004002007840d04103421820704908a80580048414425900080e203641c070103800b902201c1780d0b864150b6144413103c0000c190704d0282040a40c040c0b0300340321507070300c8801000703541550440300c3d500b903552030b40c0e03184c42c0100c8843c20a60b0140310326089001d269074003140c48244050038884501b4429100301084540d18824010046444040003002081085503400f820a280c8111482c008841e40400014003078441142e0200c035600c8001290b00c10340810740301d000c80984290 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 394936672 1250 394935422 394935451
    0x703090602030316050d06030b07030c030f0b011b0c080714010e01021605040e030c060403050307090b03250c050a0b06030c04050f040209180307050a02090601020307150b12060f0708 80
    0x450145134441513130010403003800f03400140c40c04814984d81000303001e140c202044007181d05210500030002c004600003000080c0c80c14600540c60341c681e02602d0028030741690703078080c0741c0944000c0c42d58000860800710381c0310420f840700050000080c45204024035643c20b180c0380740b4031034000141c038180c3d00415190454108807201e101011160380003000342c804c00d51f00012900e601440262451140a00054441c440c40003003004261b400300c020751080d8045e94031840c1c1140e82d40c280e07000e6800f055810f84c4503da1082c4500e94016180500c2024180d01c601e0041b00030580c0e0b85866003803004109056518614000030001942020040010061410380e0704216518001d01030b03905201c03000d40000d101d03c0000e000b103040b25038813011400555442800b030340d95980c424500740740da81c0350105040340a00400300000c3d80d69070000c41924001504200104c021100c08104030004154190300d590b40424810003082c9144010010340348250380880c14640740b4200303414081c146500007422044841d001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 394937922 1250 394936672 394936681
    0x2040609050f01090218040906052203140a030908070c06090b07020d0204020903010b1f17060d061d030d0623010203121e090a02130515010c150203010b07030906020303 74
    0x540b05044405403003006844200300048102e2100081c040603502605051103002849040d501c014003492684181064900d04d89207100e603002050f0101901084081201702ca10204000c01002c03000c0e40ea00d40020b030301c029961005142c1d04004000c0e561600d188100340036072504240003c015051104641d8181a1380394000b800780c02c51080004e00803500410f052880e03450035002480d0400c401484400c13149111009a6000c50050550700c0000340d8000303040d01c0e2413600d0b501980c05180080e184141920440e10385a025181303d40c5044000395540350300c00700310402800030b030058946121002c0b0b5141e01d080344e0150140c181c00144086055520b0001240d40e80000807165151030304120103180340c0e21000b002110b260b60840b05c80101c0403410401598035030204070810f84910840700811584418203070002214002c03204043e0552000c506c0c0d000c990300801080700c030188a84032503c030303076a104a00d48e01a0f801c203034454906804089a000c0400d03411231031a0021780a00e100841c00c6140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 394939172 1250 394937922 394937941
    0xf0a020a05060f1017030421060c36230a0503030a050a08130507061707030e03090f040e0706021f05220212010516030e030f0304080a1106130204060905 67
    0x301e8445d000c00b401d00d0400c01c89241005205440c0200300000241104402031001001040c200301002c65503c4d1030504507c0d071803070154001204008044200100e00300040ea0101c0100c000c5221880c0c620741042c80c00240aa02c03100300c3c5070342090152213014010724403021300a0481036508658401e0300180180c2e445c50b50f010701514980007880c68540060303210740c030204100904084001e011400303051008100a0740101e40c01c000d0404002800301756640d020011403c46521915403203040d001001551036916000900a414810040002030704c3c040408000740340c034106a00c244050380280500b902501c00b8403c4040503006085414880c0f0b2520b15640e000b5a10142d040e20f0503d52400c01d4502591644104442000d030000020400707824002c069000d003e40c020f054100003070034402d54015052022007a0f405004040e0a11421034a990741d61001e00e800044104080240d0808201c007401800c000d03103030003482e550a4080020032a80140400e40320a60084444107041c0400c0c0702c00c0c501d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 394940422 1250 394939172 394939201
    0x2040c0512040c0914042a0308130303120c09060807030b0901030b0601080108150a09110301021209120702010c17120406090203060f0105180a020f042d06050f0f0f0a020a05060f 78
    0x2e80b10403121f41001a404240540c9000c0b41c1000d00020301c04034034001d4050344203200005590180c0c540009003460860402c0030703074558815410004080800c1003082c1400780c801a50000da030b500303002c60304079800004103c070420300341e00940d407040c01c41050180d556040345180f80500259070242510603031a107400141080c014040801e55030707072040400284191205c81e40a0421300900079962504000151040541c007680c00000034000d0515606000008604950341e5541c1a1a8031203040c5841d1106288120180410700c80d106040003640c81c1e420012070700c940700e144268130005088886005051810600a140c100b903c0c8041c4018841540c4584011100c042c0540c0413103100c0c0c0d00c0860103406030042c3d01d99504500000308020855502240f101c85100c440da2070f102e00c070342c044801d450b05003100c0c501c40c41d008070310108600040002d4040081401440e440303d91403400402ea103401c0019030105018030016005851090100f03c0144040364109414080c003020030308004c000b066591 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 394941672 1250 394940422 394940453
    0xb07080409140105011704020109032a05030708150a020403121e090f051c02060a1d0402030f1f0f090527030f0a0216080d200a02040c0512040c091404 66
    0x2c811106c001804c40e031085d40340c4805940c1c400101044011124499900c22554412818000c42068404030340341c14002906402c6441d1a0014a10345064484541d50280041e160740011034007000b0100c04100311182c11407a980c22565070b0400e08082d0300317050350130321442505882040f0303c2400030050340b0034002c140b50644e502203d02c11900780c84245580b040c161498802500b00c10003060003075800e900030292514215050322200b03407482c1494100800c900c0110398283d0b80205000100e070100c2c000c00b10225008200c882d02e041c00503181c07203841415991039884501216100d10802039850b1200d180e103944400404102c000300d00f03440c00c1c0113890380034040340203102050104070348072500c2c0308021074800005041b031115030441d20b43c2285500c0e610078410301030104418000d44031030f84e11080510b00101c04208090300c14a181d81d803c100243c5100f00c007260400c003050000180340b80303d100201e8040ea00c01d8500002c654501410301064a640240004203100d0380350070400030032911120482403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 394942922 1250 394941672 394941707
    0xa17070c1a04150e01021b0705030d03020f1605030403300c020117150a0312030b060c070605030c0403081b0705010c020105090613030b0406021809070203160501060b0708040914010501 81
    0x65641d04d002c0382c1c020f0141c1d07501103035034400500c005074450001250090583c2d009400b40c81500429107c103900782d1090381d810382094a820802100810f02008208000c0d07031103541a64501552074a40f00c20688045000782c101c104d032800600c10008000240280d202d030a8105410341c2c8019800207010b402050742503032010038440c4002100381d041d115111104460060000c2c4e800d130340b81d0600001c2031300c2e80704040e0003103850140651000c4c54550141c1d083c42403030340c004240075404c05400f00d90580001e0160403090b0814440800020031040180c182c5104001c0c82030081c4d058400c28a2421010703901140c180a0721a00383c00160364010100c4a000d0001d8842d1340d81d400f01d4011a17184c0e640c0562000c1c2020a084051000f00301141e002400d80b0203001105080c01c000b904100152603d043d5201c8015900c2007005080b006603007188000700c580a00000900c41d43d42c2c00d41c9426030350054008449038240003a042c00701e2902e52048a240188840500c80903604040c00a0f00482c074581c0102003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 394944172 1250 394942922 394942931
    0x6140102060a1e110304120c08030a02090d0b0a09020f09071b02030a02100f1409010f030c23090a08070501020307140f0316020301050f0412050a17070c1a0415 70
    0x2c815203a441000b00c4501140c0c041120240c5580c13003658980040d913003117400210060002409070f20175a1441007182c0c00402103450358540c0d4120500943c440010650020003541c1c9120215a030703c2d020a10990704844046602a142d104210307603246e603082c46c98400c6003418140540c4aa00c214032303450f0000c0f41c41c6410092003040c00001c2c6001c0160100a5100c0d484100700700f902903002d2425082c80e0401d8030781446803659454041c049006244400d0f001411051100e40124400c0d0010009508a0b0030403840180150015400b41d6032041c0d2040c2d105140061022403604150302100018001d10000e8040c00c0e0070100001d40300d06ca041800341a10802c2c201030081c615090110748030302881202166607419134000c1e040c3c414458072501343d00c0303946000c00151904c1109401144902d5104c0740d1103180c10384207041503840e500044070800400221403017a1540045030070015000700441d8603400d12015080c94122506001300d45811206281c50043c000012544c46501504d400444004903 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 394945422 1250 394944172 394944191
    0x60f01050c0106061701060e09160c20010215040f0b270d0e0607050705010311090303120a18120c2d1704060903080f120c0c0106140102060a 62
    0x3110390080c5214410305500e84140000c0d0290071001c01c955848590007505501d0303a0364503040c0e800201e1410140e801c0704c2001d000602e0000940028810190b01e400c0c040c2034410b00d5111591001c002011680d2132100c00340022000d50380410040c0340900720000300090300d10701a580c070212140010401880c00410802051500b07410000920580e000c0010010115201c64000d40c2d55156888801c80070070320080c02c0b80894108102111803450b0400000c0040341d28080044008100c82d540c480011752082c802c002d010380e8140001c094910307107100b0440309410590008402c44204102c2005c040d07802c03002040001d1058256030000c00a03508058050590600300b4031500016100085800f4001c0d80d109040c0d440d00490307074050b0034000e8980403801e42c0b6240043e149032089019840c04101d1240b02040080c10140080030702c1c18054109a003896031011882074007030310a84200003404804154481e07515024443c0d40000c215510301c113180d92480000203912540301074440c04815031100f01c0b06 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 394946672 1250 394945422 394945427
    0x1c020609040e030705070f05060708120a06050a03060518030304030c031107030c0b1b19081606020301030c080d02070b120709080d0f020c0d080f0c01061a0c190b060f01 74
    0xb42c51035050502600d0303940000d0b03d01261581030740e005110380440b40e1340000c075007410300c1001d40b00c5940c5d100244502c0d214009581d884406002425009429100e07500490540c640092030703002903104140c0490300e4107041000c44003210003080c60a1140d070051003080040392f400f0004144850301400c1c05a242c40c507280341c842c01c1149070780018010820400002450342c0c1400300030010301500c02d40040c001c000c80c02140b901e41406182401a801040760792001040c40040200361404402c03041c10950301440c1d8802042c0c1c0c0003640f0076102e9894003401084915400d0105400400b074a101501129043c00c034109200c1c060840d136a020f009142000031b003124050031520005c6c0c81c51408955040d48421070040c80744921654501c01030003401092415404c280155130f030599886101a420a0301c5124a0306094211001076881507480e8a00050244444400041132402d0710100303e03030703640c05034100b14a44042810540d40c80406503001e0404552480b003401d401281c110f13910b000205522004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 394947922 1250 394946672 394946681
    0x2191a07031209020a21050d0306080d0206010e0a0b06070213020a0f02061306020304051203041b06050324010203040305011a010e0102060403020a1128080c1c02060904 74
    0x8802080240200010960408009400c0180c440c0e0354410b00d00d01000c02c0c510a4912112000390403408034032042c00442168062050700408403016802a4881c64803428504481c004100002c07a41d1584140501c4006110706c460713200e940d000511036940b42003806140003d005100d202d50f10fa86d0030080402d9500c0b48d08032180d0a400406201d12050811010360081d84a8512100815000c0d0301c00350300c007400803c00c01d11450f04054001c450180d103072181e0000c0d46c0010800c488500817401f00387d4440390800302460142d4001e0350f80c100c202c180b44080d1b0100380e040b90001e00a201003802003120202e891000b4000101d072440d842a02a011000141d10354000c5810080207542403000c4500d803905c0b0002e0030800c1e034500340e840e101020340110040e6282d203429600540140c000c05c5405021404034800f0b600e99440c094188116020313000f1303001c0040c510410041d180f0b464010020030010701e08101c0c031059050308617041d00320304242c2d90b0445030001211a000f4055200482c0e40b14207039503140e12 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 394949172 1250 394947922 394947929
    0x5010e0a09150f09110301030803041412030108100e0d11011b05120c09090a0207030c0f03020604050d11030405040908040b040b0409050108010207020f040b0a23041b0c0219 76
    0x14401c40402c400740c0e000300019402034030100d40070f03c03000044240d200c0c05402c5094540340c980038078690841c0c036802e80903030009005480d801d04900e03031410f90b54810081800b0b00021000b1854507541048580340c20000c20500351020617003001c060460001d000b04141d0040c160b9414a0500f03095503d40803805480421250030800c2c206142c01d512454000c00180340d11841d217401070883ea50745003208030881c00350341209070300a00510700055020103194028504070780241840310b4030505540d1100c221040740401100140c011900b0301c01040010000303c5940b83c3c503418040003681800c840c2d0760f034a005600c1001d1085440307403406030900c20a00101c4c1c0140c010301020941d603a03210b8000200c036602c2031150707601c07076441e0100000b843d16040c802e45d020030390300801702d0b0b00d07012501c82000003414100e103c081d400058440700003800a040300801800d08260b06600c5400d203400420031046410b41d0b2888081283c2c6100c00713160b490707885443c2d40b0140f64121620020312400050307410f00742407245c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 394950422 1250 394949172 394949189
    0x4120e012010020c070501031103310f080c0c0a050913030e0a060c17040b030103061e0c030b01020c19271107200307150527011b05060105010e0a 64
    0x800c0b505401001c45c0d804151031003070b00c0c03c3c03088408450480c0c1c00c0b44021102d41c0c08403031190b10b03003013408210a01d081c000e0780b1907014068005401c5490b000c561aa481ca41150134030000148000800b40900c00c080c407151046170845042482c0001094a6041c010640710701f0280588040d4100360082408000303200c0003411454805468510140c1039620040e400e89140390400c1d407201080148008540955082d0030519055900c4e591350500500000307100d00115200600c0760781100c540f64840c25001400743e076808100c101001c0006418144c940321180d0245213001b12008500b441c0c0008042154569062403401d4402c11154181e1079080170036200f5003030f040502e440e861184540107081424090241000f00d02220030240e17141710420315070b141d0150400001040030a1801c2550106481c280c00c24900e06010078140c81e9980e042682d40954000365440b0310401e41d42e010031280c0c01c3e030345008266010010a51100d0b95034510502c0384a04220407110703015116129610444014a01c84 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 394951672 1250 394950422 394950427
    0x60c0406080c0915031008010603080d051b0403020103200307080a0c03180209090106150c12032d060513090c0501080f130302031204060b1f1b020607021804120e01201002 75
    0x91600450950050461040460404020070004020021040c0401e2068902940b8050c559401034001d015550508400310144c8100c00c02c400d41c851000f90f1041c8020368130082c0529000142100b01c07100b203120081050314003043c007403640c148500080441074048502402c2c640d2000780e81409064550040303d0400400150100c0303494000203030002a91181d4121a0901840071040301103030075000c050800c80c2c91314807201d02e192100704000404000e01110101e60b0984800c042600d9801c030b03125000348140c0c1d0705941014070140740d0b1580c000e000c0034a4161400d080c030b1180040043c4020340281c02c480f11211a040426000304215480100c1041c0351170030343c1c50b25041c440e0040c980703803650078002d01030120038084210301205403a0f41c0800035142c030090070300d20b50380c624000070003090b080340c001d41e0401c9102c0141c1e41e00c0c20010140719200e00800190301c3c0a10f005400c40c0720301e0480c8001e20403044102015a82c1250031844c003009100c5181000c1002404600d2070b00003d030a4a03020030307100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 394952922 1250 394951672 394951679
    0x51819140a0503071a15090a33180b0904080d0f0c031d161401020f120901180302090c07032001150501080f010501030914060c0406080c09150310080106 67
    0x1001e0340c01c043c1c0111741601c10b4141e072846450301d6841d140c4514660320950100c0020700c0303099940d00010780c210307041540034800c07801419200d240d2804c12204101e46020480c0401c2841d004444007199901800010700c21056078001140c2d400f44085d000038616000492007108181e00d50703002000d240f00025062061018a0602400500002d86000a8980c1c3c004002e000c00100041c0e0095601e940000100c24a1820030402c040c10511405541140100c071000041c00c227003088011050340041e00420360741c02160001400b80d00000b02c080306045c80b11001000541c2d02c0301d0b84590704c0010f0340c0c0d0b4686d03522290301d002c458250709440e0182c0d04450003509000e20700c0056104900e060803030740b9261a62038036030f00195010760085540e050300031040b10062140c0d5220750010004e1a200e2603445da06004c0301d825146c01c1800441c0c45550b01e020205080004660044566400407440f00c1907620f8841030501140e104008840710070490000040442d0200c0300700c400400042a03104000c1100c3e649 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 394954172 1250 394952922 394952933
    0x3040311010c290c031e07170108010203011e060207030213091407030c091806090807050d0e01030506060f22050307060809061e0f28051819140a050307 67
    0x39510b11007210032a00003d0750314213400c1c1201d015903162a08a04003000031600001e42d6900180310302e04005403407204540c401c480810041c0a000704900150300c03981446050100082c04101044036100d4181b4200520354000c00e40b10142c0350165860503008003115503140107440b00302002004541030402c002c0c14600040741120550344114100100ca41d0388107422000e80350042c0034420016940d0300800001015a80041c1c0003d01c039805c0c2608004468032218280250403d0402c080390389580300b1400e07507906200c0c0795441013085552a081001400100c000d0f07000e8408a4481c403500c03e00c441920f0003020b480741c401080010210b54909840d40c0f07008042d040207031030a1035240f14810102d031038920140c0c02d50460b14070f2010103080c641c0d9600e40b03400c1c421340301070002e0685220062114110402000d50780700c40c28403004000c03900f410001d0740310807105083c01105800d030b08036035442c60710000319101c114034154005d1100c0180b5140030500b241441e1a0140c0104944000180d6808004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 394955422 1250 394954172 394954223
    0x62304120b010e01050f0d110d0507151407060218040222050a050306070f0c060207060504020310111c0b0a0602070f0f080307031d090114030d020f03040311010c 71
    0x40c800c81144001c1d99030f40b411440803000a0040c19405841015001002e050800f8010300c0280101e074901d400b21800c3e000309807462142d000aa0b01d64022080c00c2c040440140c410302e22019680c586100c400c4040d1203e1031050180d0300000780704d503400180403020320150714040200c80c2c030020000c6686803030005202080f44442000e0f0034a0400301e050004551500b501c0304411107d015028100c142d40d140c5085580c07071110701502d0244042c010604001c1120380c400b6000b440d128010010741d40c1858010540344c140e04800001205042c03a03220042c3e400c405040d10458154035810703c612482000c04440540802d03007001c0d8025144c884001002c941c001001400c4511420400f403000d030b15141350307103c800c040e8010f80301c1d00c0c1c0c41081010000b80c8283c3c410101520a5114a610380550b84002031344500c0070703400300200028400d0301100d07500d01840240c403511020300081903100441000d094aa001c0c078070014000e001040848440d81c0d008010280314a40e10058150032800003a0707100140d003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 394956672 1250 394955422 394955459
    0x20d021807050c011d03090603060627010909290109050909030306041104230105121512010623010306080d050a02070e01033f021b01030510062304 65
    0x70f600b05401c13500344110b054101405d0001c600c002e1854000a070f01801005d80c4040d12068001320108400d000108401c00440703500c501e0300c00380b40d00f101500000181480b0741c580140c41401d180500030a040d210b01d10081c9850503550b001e056a2041d002c006a03903041d83e9500403604803002404001d040f8002100075481031104950410000c011075a852080d400b49001d8040240601c41c00c2540600800f0700800f2601c1c414900700349441840020786c06201d00c140d802c15015a40410220054a8590700000400c0088002080014546030811380c411103409041007280c0c416441360710150b442074021401034180842102d40950003440c00400c9580800100720041c06030a00104040c0c80718000541260341101020030050140034400b10003040c4142d13140076101c600d884544030b0131402ca088941c600d4460300508903030455602045149040d040c0d06a04143c6024200b104801d11000070f2804d464062809200003107a5030702820b54a48064614001c3c800e002c10009820002d80c1c1c2c804511 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 394957922 1250 394956672 394956697
    0x50304150e030c21030c030406022b0b1e06121e010303020708060903120a0b010c05070b04090501080d0f0f02010b03070b190206190209030a020927030f07020d02180705 74
    0x130300350b041810000d134002902c0c50301c0541c03810408103001c94203540150515400d0100d04c1c01117642c10183e403805c8034541d004034100c4186c6131031314020030b4030b421890f0000b50741c10807411800805035040000c02d07500c40c0101d00da4109c102180402c020007040903007200607241c1c1d030a008103c0c0d6128140690703528a031740b054a44c01d20400c07002440d004004015500c0c3c03c1700c900703030700c1016850f0f0240305806081d11100b11410045c58601e4800840c40c1000100001d010342d1411035aa282070502080555030142c0000d2082c1c0c0c00102c2640c0c045501c1a0f044a03000401d28184010b03c0d00414200d0150844c41c52041e0b2512480f040400c0505a00004000b14203200c4901c020b40140c0d10b00c180d0311024200e4420f1044400b4030f8590302044525002401041c6005040d40c03061103140c0d00246000c03009540f54200703004060400058568040442c42218801800850522500c096803007004d01c901040203014000c081440e204540780e030f204d1507001e910780b00410b05081ca04202e000705a5001007410034407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 394959172 1250 394957922 394957963
    0x206030124021c0c140105070e0307080a0b07030b06040e1e0708040308070509030a2f0105040305030a120603080313060b0f1302070c0e040f0302010506060a050304150e030c 76
    0x191800040c1054082a40076050550840c803030405403020140700d031045e0740308504102d8018a0703140a2190030b10440d002d8951022110070501414a80080f6400000f141d6021000c4c3c400400c184507035840d8400e42071320b40440c0760b4021030301080c81402140c1c0502203242c0204207105040350046103024140b4099000607400b903032205011510080c0039030700500440e4914010404041c822001000c820501030210368440c1003d070b130b43c001000d04400c4035400d01c041c15400f84000c0c20b0f5040d031050551200740b801d1030901c4e046886a40d00c134421300800e0f0007800740c5494240e2080c00d040d00001c00550700156529164505810707166860300d10384404440492400351441110310784094a424400800350252031101c000c0c0099000962004600356245c80d04090002a0444554003e91255104031030400e4503c01d0703881c003e0b0940348040c01c01441800144942488a5808002d3300d40c0a40c00c0041c04108203108140c000003000a40501c8821b03020000b41700300501800140011100c403904040c14 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 394960422 1250 394959172 394959239
    0x3020304051908030f0901021b06040212030c060a02030a0906060305010c0e102c0d14160b0904021803030f2203080703300903080609010605040b0d0902060301 70
    0x10b1807a031801d030000d100e050144045401c10411046180e480454540010b260810440c1840204561102010300c1035000004000c00c600704020b2165001281e01c0c001c1d800e100c032048155031039200003044bd0183c02d5020002a0300d400281c0c000703001858101e08100702c442e84a050450182100c1d0b0702c403e004c6810762036501190f0a00346104016100c00d40d80d84000c01d6000c142100074148d00020380b20801d05040491881c540e200610062410301c1138003076800c2041c040700603d044c0b040d0718904156480c070b078110802440083d202150b400700f00c2140c0044c1d441d0791101c4e01141b4184440103094041c400460008016051300d4000c4c0076090303003149240c000c28588544507600042c1d901000f0f24861051001d180003c2c0a13002046154400100690340703030b4904002e81c910194036a00601180d5241d4210200f4141c02c040d50740e8000a043c1d83c2d6503140c3d81481e00103002c4d48030f9440381c20391702e900002d940c0400c044598003200c0396940c001c151702e9603540d662410320100c03031200c80042844540d012203103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 394961672 1250 394960422 394960453
    0xc02090a0b1e0303040b0901051306020607120203040f02091f0608150405060a0302090c190507030f080402010c170d050a020705010e1b040b040e0115210503030a1113060302030405 79
    0xb07a01d1850040c0114a41418100b1040050300302d80138580c18080e080c48103038040402604604081c002943c0205101d103800c1d000240501500c09105108620400502010442e214041003080340c050311030054986170660314200010460b043e524161819000c041251640024403d0103402e10065542615a42108100c1140c9045e035280d07a110003129001c01c0182040140e20390300945c140707031450607c054028803850b01014144144002803002848104043d080600c2d0040d0303000301c0c90031100790324241e800079203900044503000e0b104c0361803c0c6282c00003039200400c885282c2104441440141030503080140a908024000c80d92542070a000d40c40c50000041c181d10078800d2400c0481c80240d4001c2032200a155048103503412131340701d01d405501c1d000d09015a140400103800340c2e0516626001007041c0114038110399241e010981c500744004240000300f62504280820000191a10001807c482c0da200d980d000b0820415540c000207400d035007680c003440c031440c01a41682c20490902544 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 394962922 1250 394961672 394961719
    0xf0601061103120406090209010f06090f0e13081b0309040501150f0f0203360405091b1f02030c19031b0201031416090b280c02090a0b 59
    0x15161642c41072244030307020031a02403c10b41060043e9070000380d07905182c001c58640d28090300034000c02969504100a070952050081004024034028125080c1c14185401407848016080800f0b14918509020a0100103002c03580c0c036112203451a6a840d41e42c0380132646a8000e440301c0d80c840c900d804000181c9a03981c08410702805503e03598807021120b4142d0560b075185c0c0c4882c0400c110720082c0001c946141000000c40031110301e20840401c3c031120120900840d103000b0032024000e41c106001d01440c044000340300b201c0c103800c00d0304083c0c034a14000081025403814a40441c102d050000074039442940120040c4814000388081d155611080d0020320440075900c1c40c01000515003a408043c08219405002081403052501244024004900f1102e00e5000d9442010f0b1b8400200a01c081a420250b14401010103010850402003004244d2485200401da80f90440301d0f1207140345c542c1440b030020300300c5081d402400c2c042d0310f050010b0104000c04400401c00e0191070402c02040040e0307810700c0e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 394964028 1106 394962922 394962947
    0x30c0b07050c0a03030e061c1b021009030804060e212502180603030c010c0503040c1707062010020901140f070206030403120203090f060106 62
    0x1d0003420000e4049001d485588036080070800a13401600c8826a1107003200d0194841700135100040701146058001c0380c12901e00300d0385410780f0054030780c1000f0180186d4211000b460203010300d01c0131100d50850150100b92501c00181c00100f150b080038164444039030540d0f0f40c01d442800840c0d40446130070f1644900d81c2c00842c8041141200b15882d1028140c0007200401c0d48040e0b4021448000b0250f20001454041c0d03c0001d8140d00d00700101c4a00842160080146042d040d0004100c0e8000351400c03038020055190000c3d00300d4080042048090600c009000030303d15101041d9031680ca040290b60080e0384a03d14038102c280d080c48024040c6000500140e500c422040004101c6103031980c040e0301c0340c2c07010b000d20307011040c1c40001e030b68516a05807151640ca4495040541c2c0710240d64220301390850000080100244001c00d03189244d52b50a0100c0700d003640c8860042e10846002d28 = true := by decide +kernel

theorem cover : BRFrame.Cov 394784172 394964028 := by
  have h0 := BRFrame.cov_init 394784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 394784172 ≤ n) (h2 : n < 394964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
