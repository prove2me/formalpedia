-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0993
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:42:15.701768+00:00
-- url     : https://prove2.me/submissions/3094dc3b-ad80-46ed-b70f-f23fc10d529c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 178417266 ≤ n < 178597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 178418516 1250 178417266 178417271
    0xa0c060b031603051f0501030c090e030d05190e030c07050909030c010e070f05040c05040504090614090718020304260705010c030605180106050a0509040908030109020307110703050a020607110a0810 87
    0x4103103608174291602480060030864540104200c03201698101106000d80c240940f840c011007001000221401500c445010038400c2c031525011034101e2003941a0f0f100d900c1d000318101040c0450307290742c40055005050050983c800820741c00e0108005440c0303030799480e030300911800102c50011955400c00303100380c2d5100404544002001d0800d4424160a41543d0b919076207400d040c5024480901044441107855a0351611000070100f901c0045501a00b02c810240031410300e0421210b1040d034043d150b403d0414410424400001c4030f0210341c804071000060300030300d80e100c100b5040000f80280680503000e542007400c02d11107268150310150594200303c4a0b180550404800c1e4114071409015040214900f0490940071034040c1c00907240c0100d001b0400b2800c40314a568418aa803c280c1c45809982c1e0003006014000d50080100c4011954100c018003004d403840d00d41c140d0700d041c098400b9000d8003001035180f0a100c100c04a0360b1034000040c1c05294a0f42c0d81d940c402d90344008000120b03d1051 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 178419766 1250 178418516 178418563
    0xc08010b040509010e06030c031b03010b0603060a050f011101140106140703090b03060424030b130b06060708090301051306051605030a0c03020c0a0303050402030c060a0c060b03160305 81
    0x4403030350159801d0740c0e400f074440f091581c00c0200c60440c00c0406004a40e040c0300d0010301001a541c108114000d81c0828032481c09034540f03200c141829a4500003909104980034402c01210f511a15024001c65070200d1390a8041c03042c0100684e00030108245000341542041e4403407035503c0718920341d02d040b2402a0340e120000c160b03640b15500c00b070051000c020f00042071204200182c3d4408406941c000380e00410004201c85100d0220072441450b000070070005035a0002002401a0004441d50281c240c1071701100b80b5009a039400740b0303c1801440702c2e2240601044c150103100480f0191400420301038020441c6080205d158510342400500032201035003440e001907403040380000132060340315054541c242141c0b01c4221003400f03080c4509030380d0304243e403e2084e201e02180420000041034001d4a00103401d003003600505040c51031389a003490191104104c5208001c0d400400241c04d6034004d40009100981400080e040c1400c2809000b81c0002030030005c01882800f1444074152034020780d500c000407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 178421016 1250 178419766 178419779
    0x30b0129070305030a05061f0206100515040902030a0b0a06020f0d020f0a080904090b1317040b0703030f0e011b030e0a0503071b0b0f0406030f06050901120c08010c030c0801 76
    0x2841000c1d401030000f6014404520181c2c3c2a41101d90085001010706240000600b6040b40c000c0c144076041e00103a00c40c100b40488407160780342c280040d0409032426210485454440403c070720441c894142d6480c1d0000000b042045c10b07900807014650020010791304559914402980c440c07582031900018001d038092441c105000089000e20743d20800003030941210b1907142d460780380d00700309595500705403620b0003080001d1009403c28441d082c003c60040c070903212030414a002c0903081c00780c40202c2e00200018041c0e03400b5442918485a414a070100b031820a060f010009401c000301115955803d01101c60303100c0c4a210300c4c003505030b42d060307804000300d61081e02011380d51b01e0403207406092a0030070001c1101082c90300090300920300c906000d1100081c0c2e0b034818810aa888240807154500d40032a040c02019810302070a40e801d40790605c1402450700b80030000788420f00c10b10402d011081d00c01060300810400c11500d030010400d21008008001c04220007030301030989200100001100c010000c10761 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 178422266 1250 178421016 178421099
    0x60901080c0d03020c0306010e040311030c1f180b19020708091c05060c070309080f0c0103020d110f131205030f031302060715110a02030f13030b01 65
    0x485420400030300154540c1c60900c203080005030429400c60041071650360a03a20704100b0203000709000e2441c003041c0d2815080c01820568680100916030704200700d08102060300258000d04080c4003c242c0c03180d04802e4059100410003086c20441d210b000900020030310050105242c03289104203000b82c859079101c44a00120b02c50150000e04222003800441180e0512000f150425513041c0b4442c9606040d5031102c81c075004044032003c0540100042c0d4100f01640801d03198010202031000340036051040c21915200c6402141c0ca904040d40401c1c50140c60001c1e400c4180102d802c080c00942d03e0135040140c1010b940005c29203003c0d003440180000d0212204000c0302c03030803034110010710b0418009400300c91050b071000e040d0040720040402958007580d1614010203005100c0d03040081c100420090307040907181314080d20b0a42103001d000080a407a0003100310350a0384804803003d66100740e0040c04a02c03140a41c0c00c09808001d0001c00442c1002d04807003c188002d124010b02144c065401200b8250f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 178423516 1250 178422266 178422269
    0x92705090102042702040509010305010605010e010f021c031104060c06110c0d1b020619030b03011509020c1c050a02060105090103020a0308032701141605070b10151205060901 77
    0x10413140c8005503a050440381c5210140e03100940054a8181d40d04001820448207030000d0314a40d43d6010304020340d40c1c00040c3c0341c902c0d1000b801d26410320845144043e450300740f80d65001d161190540c4076084041e01ca0340c80070000c0e45121110a131941d4440f40c000380031100d28401103030724a107415040025404a5400e8038090303039074000201013a560a80c002c84480038403980f1525002c405050250041c2e581101038a400b0a48145071803500600c0700008041c2c402000110b40070780d1401c040c00c25490080313035400c400d40b0703a038000159990a15118052400b880d004400340e800141003070081485501500401c4041815801c4500310398a940800c15400c00a01c002236001911290400005030b8402c05150b001000803000c0341d104280b820090003e14409510001c545d541e120b441c2a00d040c01c001031600004164913025640f070144c10050040c0c0b00780c10000d0690400e441c00200610001e600b0500541903c91a10f0742c0161240c10142242c02e00196402d00780c1d040c44006130300340c00c01d41031850 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 178424766 1250 178423516 178423529
    0x90112020a0f18032a05090703020d54240b010504090c02010f0c0e180c030a09021203040b1e090a05040f0b1c030206280b0109270509010204 62
    0x8a008102105141500329040c2c1c0c10304178001503000008030fa070743e29128a482001c07540c501607520b8046099100481e00f484a44000c928052801960b484244209a1418041c1c00d815008844907101c4090380c00810301600400302d103500c8114108001031603070050314865001107191070700e8006103880c000fa5686480e5041c005101480100034141d80c60700207202c0301c030b4640000a10b240c0d100320302000742c9000c100124086485101407510174244100401508901d291209410f030418800b030314000d11018002c1c00f40d554441e0031141c00e5545503031441103116140000c580d5165030340e80140000742c12400c8500407520000d070400a28051a008803a006200144502d42a5051008100081030114145410240d5900d9001c40d152100c0051900b4007031a101220504103180c5002440d04900401001002980c1c0150200507800c03010030a0302020140c801143c40101400101d0309000681c1c00003140c17400405540034620b4540c107103080d0100344000180000d030750700c90a00382030f80b19504c07858 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 178426016 1250 178424766 178424783
    0x30806090f072d02070501020706111213080d0c02030d08010b120a020f0c0a0b0105010924030906090602031006110d050f0f1c05130c03020105090112020a0f1803 71
    0x4682d070b4407690031842c07412041c041c500410741c0c90590700f15502604142c4000940d01614080c402581c042010710001c103510b203400f403c4c440030044900d44030a00044d0004000001240040e050307130309011110040c3c90b4040466490b07030000301d80245004200309060380640035120800d9021403207414000c1c140d0340304492607450714241544000c1e950f04001e00c404240743e400c1c40402e6020b00c1110081a86d10800d400420a00744076041100b4880e0b41030784030506001e43c8007020400c01407401c183d1002802078521903145e600c41d40d070301580a010340500c001c0029103000030710010800140d000e940540041c0c00c407184416160b24040e204031103000b1080c086603000d40030200304548140b00070200f09021600c21030600c1140380052106030001401e0320244151140340796080051403003400d50141d110480400e1744811380d103691010156500010f03040090010b00760703040743d005420394901c0c0c10380c002b02155030780b96010004103c2c88900c65034a00040303500f00344115507a040050034065a4014000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 178427266 1250 178426016 178426021
    0x1502070f0b1905090703030201050c0c0601030212031c140711060a0e070509090105070f05030c0406050c010213150f0311040e10170309091305100b010507060612030806090f 76
    0x102407181c800201082940300c541c20140b040c801032402091300036945040140308441c19803401a0a4802c0100310707603095541401801c0c80d503000002c81904613601982c1c004c00c200240d2085d0f50640c800d1800c081c00910001161045818103a0f105800b244040314003104243c07a003000c2280c0440c00d000309036800c0d80c8030300045840241c0d1a40300701341341c07503582041750011681c0e54003181c0d611303000311098022a550fa400304000e55030031585503000c0c03021900e456460361900b484d9800c50b0f80201d00800c001c2000100f01054280405d5045461412001e042007611503990452000c030440b003207804000059840c500d02800c40c1c01303030250001001c054100c16050604142d01d030048140000c11200003101c011000045540e030340a0903941a802a001442d03640340d0040502007026409032102008404c075070940300c003080010861503207502d440000414010388140040361240a098806404185040000640c40d460420444501e1303110341c030303450400e0303882a08008250008035210000d00700e08400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 178428516 1250 178427266 178427273
    0x206150111070608060a030b04060506040c0c0317040311011803020d020a020105090409061e0e0c1f140408120c011508061303210504020f030708031b0c06161502070f 73
    0x5070303501c500090901d500b91b03075403515140803a1a05540680f000d99803101481140d0901d8060b140381c0d100c2c40c2c200a103200700103580c000e0000d00c60304880313101181c0a50100301058401c004030151500018000e1100c1001c03103d00486009608004a01620a041d03580d030713104d07001007540b0303107185d4058440c682041e01c424148009020030610840d1340a51315210541500211039540d040c1d41101c00c000240c158018071180c0c6407421031403c191040a40821014503030300305540004c031180e4503183c269503410050603c0001c41c015038100c101203004412000814041950150001c019683d001f4040c40c016448410440900c1d40100d4a4580100c0c0000ba44d6005041c0d20240c581d100f483c04407424410308034031341450b0102414180e080358a4805110030f610741070340008241c55044019141c054076102d00680d0b00c0c411800c10301d509c243e80918910040105125642c441400900034030341d5440e0b81c60380b400c00c0107100e250858482039089801102b440b100d10a444c03e25a20120702c0f19189440d45 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 178429766 1250 178428516 178428527
    0x309010807021c11010e06130c05041a040905120a030f0609060f050603070e0a030b1509091b06120f010812070308010501030b060c0f2413020f030a05010c02061501110706 75
    0x841e14491356403120200f0a6154003080074510482038600c0191604080703107440c2c01c601341a50b01c8907204d9401c01884032031048107d2201c5500c80e1084800080c200b00354640281004510310801f2046d03040844d841c0d541d16050340050800c80c0d0208000c1200b9078440c00c2c058103d450358015503071190344180c801c1c0002e041440045410040c03e04084401c044454000f464200c802d0b0000c0720b0001c265005e200e42d10102920254155404a54004061030f08882d000c2d83c90000c0c0d0030820601c44002e6400209868607412038500b450449001400d034a0140f00c86040d244c070a109100d494410320090080100c4030006542c0300d154160303100302c0d469180200440281102581d1a81d00141c200104040040104075040007510500003403d4030000284a014106e01c80e8209084003a43c5034007000307100c03503540000303006650741100d0b09803001c00040003082c80d0130f598102c0200780e5868000030024803a00012068482e5100444010081080300700440701030921240102095029a905018150240 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 178431016 1250 178429766 178429787
    0x319060e100608010e180742120f060306110703021204030c03110a1503060608060f090a021b070f08070605250809030a031710080703080d060e090309010807021c 71
    0x1207088490058031104102221001c3c0402d207256008d07440036141c520405007000300d02070b2202110506403503032140340160441100605000555a0314418a86030700c80390b0384801c0145821040400c401c050310003c540321688040000d40141c41008a085641002e00c1d080301d09880e80b001420014924503551003003c0f01c0d050030718542c44074a40d80c012070100400b80c0151040d8089036804031382c85291000c0030b045000054003032400f440140301d070071171180c459803501ca40160b4a0400183d5483e010140308140c4140b10a0b0072030980103a0300e0018031040030151000030380306c414044c0c561095071804281c3d000d120380052441c4c1d22060004060b118142c6885c0c00c61464000c51843d80740036040b0740001d0a000d66918120040740c00100021414000b940b02158040100b001d110f880509115105640e200b0740c0c0f01c02400018001804c124541564204a0080541607440c2809040c0310060507200d4000c17007103c0d80064000d030000380c100c600c0058031005000685000088583e66014101c1e42400c41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 178432266 1250 178431016 178431061
    0x809010309120215010b0406051c061205150901090209071d2107140102120a11030a0f0e0901060806060a03060b0307050405031b0906060319060e100608010e 69
    0xa40242101040300b1503406640000319a020301011a00a042d020444006030403002280b60244411300c50035402c0b000725a8541c6910300f03011144082c1e00000d002424840d008841c040c41c0362070660081005c0018031310309a03011908110321a584607003036036081791380c03004000e50b002e034502001c0740117280240709490500d081810400183c540107008110000342c6480990140401c80c00c40d12001002400341c400074101e4003603400c0000300f58000003551035104400240d80b96030001119014180569601803c4c420030405032078680492190103021040b8040307507032001c01e90300e00354a1524503000300441c0c10798140c0d855500f102d488080502032140c0101c141c40c0705040e40e03410081500c01c1e02d60003a502c00c0d485e580c2d4580d55681000d09050500b80ba0101c100000b0300440020203156407410003190f4490780a0711013503102d07910900205030511400f001500311303600d450404903596111b4240c0c2c51140c44c0d0303050800303e240ea490800b250412070900c5450300042c04200030803c11a010107502c490b0000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 178433516 1250 178432266 178432271
    0xd0f020f010c12020c1c08010501020c0d050703081b0f1501051906030209040e0703050c10090303090608040f0618110612040204020d0212010f0807090e0c010e030f0d09050307150c08090103 83
    0xc0300c040b41c00b00546d1803102c200100349424010072003507904122901c074041060711585581c40c030641d03995644450501004140c242c02284c1c0103a1609612640c00c412034240007100d0510543ca00c955407102d8500d201ea03c00c1d024000d00109281c209804000041040700c801c07240d82d10300d000300880007504050303001a4815158100b0701c1048404010140203035009901070a50490410100a8103034600d1868100b440302055040000c00e03040400c5100312803090030030304000d030b80340d00c2c04081290f4000c0c001440c003460f00100c41d801000c25951500352500c6401002154411402000494050152100c006c2a11040090011304090b009802100703202000075080004018219483d42402d0304202100d40c03101c0400c0141110800021004040022040081c42281544651255054010700e07040c00301034004540151800c0006406412a4900351b841b64040500c0007070040d202445000e04c00d200b070260203c1c1c026a500b240407104501a154540e62101d00da441030300d19000080003905255 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 178434766 1250 178433516 178433533
    0x60703092a050406091a01020105040b0a0b0f040c080928060b040207050105070f020d05091e130203070e1302210a06240f08040b130c05030d0f020f010c12020c 70
    0x80300e03409000050840b981010480c0406c5080d0305d0302c59100c05680504581c100001d0001140b400e4000740e401074140b42002c500c2c40c85500100350701d0503403045000d405c00d02d01280143c01d90350144485000303110050030784401030280040f10003070040070b45041c2c10050340c0c8040c02000034040d038000c3c1c5a00c1d402800143c18100355442d0745c1d013181c1086030b00c0d4010030640c08032003900c1c0341e041c0400341491010303040541c20840302c2004104c850348260092140030b101509031800319070324003842645102c50414255928580502c0081c6001ca500300c506014016803050410305200d1402a151042010410107120a480e18081c2c00c2107072010303004900041d90f030b020100740c013071569080c01c08040700603107a4100000320002c000c00581244c0c00d00010003017400e042c80b0005007036800b030b41d40000e5035240030a000c2c03540e400c10400c2480c440e4062039041c403540c40c4041e071040e00011400c1010440b9025038841c01c1801a813107082e1030240c55420006506801110300348503250f4080c0c65110004412500c240 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 178436016 1250 178434766 178434769
    0x150321030e070603020a02061e060f0402070b0a230405030a2a0c230a050f01120603050609010c020607080406020a03060504022a030901120203040311060c0309060703092a05 76
    0x2c007540c00040001e40c0000380402050b070100324440e0024803821f00034004002d181d020f0b036241400503002e20b01c280c051410b141026607442d01902c0c462500303c0d03d80c044908003862000d0043c58030903600d1040202c4410b04003440b614030280e4074403a541000c040c500d04041003404803003034045003804141c0c1c40b40007440c0d1240b18090058803041140300e014420324090400b0310700c0040056040382d06544589202409003903896034003c0104030f500c240d60b0425030584010068a4000d480090001d07014903080c000414070a00040007406001400d00070020710340b08901c00c0740c688408541c00c00c00b2446d41008a8000350541d401011008014a400582c0c1c42c8c48000180503a845120403140035645282404240041500441c02010318140110718004280002925003088015414015a404070010f02414090015544008180001d40702d1615080e100c02009400c240d528070024441d0b0400100d80300e00a1246800040c0c02c481c22012000000c001c081041d000062940031040d120314000505 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 178437266 1250 178436016 178436023
    0xc060f07021002030f0f1e040312120e01090312180507060f141603090509060f09100b27031504300908010f060b0f0f040b120a150321030e 61
    0x2501000503040b6500c03102000480061781203000401c1f030b01c0004120401c000781c0000c1d010b140d403c0e80c90400d002c80f980d0b14841c4200400f040410706084d03500f48000d100c04c041d0b000096040880007100304000d22124040020100c090540c0010b00d144d000396424406107000d8100d440d9050b0803803070320035001c5514400180242e00301c3c5400c0308441072620300348000c250304883e070080500415140c0d44440e150034000960f20388980b038041802600444013007444060b24050583c043c000390110540c0e0340d020018008220401981382c8000032a04142504103443d01040c146014403144c141d0329071603211074445d00c240a01040300c917166041c6109881c3c07014002e0b4501d200a044071521601c40161409462030309440301400700e0380d81145441014485c41c0c56540a968048416065198480030214504425480b5941016103040c0010036246a400d0b001034226226104030401403084690302c51007044402034a000c014481010710684640c1e84030700c5819000a25600c0c900407500c2135280710510308 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 178438516 1250 178437266 178437277
    0x4080c070e0402130e06131a01030c03020a09050405100e0c12160819031103040305100b1201180b070201090c0815060a0b0f0703050702090f0106020c060f07021002030f 74
    0x20380440c031070204410352a04d22641100203503241c005200c2c280d031030b25a41e921880c00400300d45e52021200d40540a0180182072400b8a000f0b00c1610a120350b103a080003045d00256200c124415410f00da00401c0a5150b800340754000c4d68088021700003010907003000c43c0900032122038210b0500c6060319202460b40c55400500301c40e0081009891100141c2041842c2d98055070070694259001d03002c0d6444400310102040c07046901458a40c282440c0d23020038505501c11503101078118032802a45400480c01e5a103c104012422035404520403140e0040c2e038240c420092100d100c149442603283c0100d03414410660f8070903994800000e0800b01a40c0d8504c08603119003103000e0617070140030480d61036512901d981e80c00480450301c0d007282038035141c00075443d40300c2c2030004c850001000c90008101070092094480155009117803a0107803518806803040c1610900c42d05005100d240b031020880e00b080d008030b41c0700112183d605407615601c0d0b003e2202c100b440c1e00500e011444100041484000300002510b07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 178439766 1250 178438516 178438529
    0xb0306130f0509010b01020d090b13080f01020405010e09010605070311010605030f0319081605130504020a021c03020a05040b130812180102161503090c0603020c2b0804080c07 77
    0xc2d00742400300c180d03400c4132941c40995040d58040d80039103044603004110071040341c1000d48116641c031804450b40f0000280c90b03000b06418481c002c0156140d0300d064002d00140c900c20707a242440080e0b024100500e00500303210b450042041005401e001ca8421700802176040e04c98400400c0da50303540c40c003191500402d9200302006400200e503204480700032542c960140c01c00c500c1e050300a8240701d1040c142c000c07001c42a80c1e043c440300081c00c0c2a03011500580302c1c02020020f00c11500c13070503590304c0039407102c010700700c000550610010007960082c007a20030b076610b0a00d20303980c0c0c908090522403030a1060f07000590055011054041c0011541e80c10007441040348210300340c040c0c469002080c40c01440c02141c10841c195007003443c3d207184001812040c9002c440304400c0244910070b140d5004c0d402088011809005d0720554200400c0b030325095001030140401c030360103c031a12400149003082198600821040112086d0607284926124078400d41e080340c09142100d01e00b0144983e0585000072990040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 178441016 1250 178439766 178439771
    0x309080415030f0c020c010f0903050118050d1e120209030304060309140303070806040902010c0b070906090f050a06030902150705060f0105180105100203070f15180c0b0306130f 78
    0x600310b0303814060140000c03440501800311103107207074029490b0200f40209070304008034038040742402486101e4503002035070440020000300d40130080c9600c0700800400180c540384035441c161014a0300c201c40007014020000d0011b0200700d420740003180c1e03e106460318005010780a2100b148166028002440101090340780060340d003040d850b292100c03000104410b00b00c0d130404e20402501c9500150307070950080c41111f001890b02031510050300d041a900c40094030b01c403080020010066000720b10001500c1c0c254503100217031592021030f110018814000c55420040c0303c002000741e103021350048030310644010208402520005007800c0590440e03a0261101d40c089000d0281c41d1840a55490150500b903645915070300a0121003000c1d90310601c5628055615420b40341070291003032065403030040c0d00810f6448100c045003801620b00d010214850171013484d0001a642001c84402c140c15880e0f841002c2c404854640452440d86400c0101001d800010035034040b040070019200307030202e554951000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 178442266 1250 178441016 178441049
    0x1030809060f1c0e030403030f1b061a040e010b0102031c0b030a060b15030609040f050106080f060405010c0e031c050405040c0c0b0c131725080c0a0f0b0a03090804 72
    0x540081d40c00354003030113190750410001400070a900154946103403840b414810940e031024001100803501c0810081c0006103440f401c07400c1002111808214500c2c01c54050040880859446080320700d65200d050250303004120100030300c027540c82000920601c0c40da00140324011507000c41d0810000e83c1c01104c20a84c2c420f034400a5182203a48402e13115024294281149005008186040070181000d0300e11500c40400c0030070840700b500060041d092540a4912180c0c181a14030303070b40d0005540446065007000c2e50803260f0340c85000b031240600350050080c1111107230702a64100822900701e0306420401c0400c4007280c0da0702c5a01501c04600820360302c90051100e6410144604200945140303c40c0303904201a42415189101d01000d680926241d03020310802c1c010020300d0604407410845465500180305114000341c041c5010845207a0401d840140c2050000c02c0b25181a0f4081c02a070300f56580801d03c4000e20040240815071404e050006035886a42c03140f660a4129034803190036480e07100c51 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 178443516 1250 178442266 178442317
    0x2030903071722290a050d11040b040302030c0f010806011b0f0822030201120c03060e01080328020d031d010501090c0306120b2206060312141201030809060f 69
    0x110550345190300c1c20000041c1a10303000b21198417900c410717841040302c00b0400081540312503114920610502e130100340d0301c2e0f0713840c0d0740c0c001160414401a0310a0041c0588011581001420702d1000c120595800303d007a0b440034015181d010991282503c2400c8408454000034100000206250300134031002c0d489060241c80d1041d0044003544506074a5070030202040141d801c489003104e40c805400e0085001c8071140700c100c0041032030380d2000e02981441c500000b030f07851000c401048040500c03a000c0c44809007004044060034003e111030401030f0721071054046401d11a034843c0304006e130441106420503249108090039180300384c102141c070b5030303980e0b0348080d1a41d0944240d03402000c118058210b000210346800b50440c0300200000b22042640b49481008810050902841075010a08010850300d0781081942c102d60710704c800c00400d040300c0754000203065203010f8502e1161480c4200800c0da0856551021a07046200ca03207410100900c005441d01c450700001d803082014a440740098540d0170b54 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 178444766 1250 178443516 178443539
    0xc030309030d1b090b0d0e070306060503070506160b1312030510140607080c030c0d1205070804110d080c010c0206060a0510091202030304050a0e040b090102030903071722 75
    0x1052500020643ca407900085801030428022555031880d415260b450340503410010301000c0c6987c10141c050807001004010080e4419000c0d9070041c1c0844004035101c81c2403104070710984180c0e040081c0c030101074500142110f166154048030300755009070720114903038030300c40110090010300000c41d440d01c0400505c0c1d020503280c1b40007007010080c0001c07490725010103d4140c0c819103a000e00039203400102011000d03000c00c00c6400040d03200045a40341c0c0030380c0000618840c4820350301e03e6143d09000108030702600c00c0d01210301a58102c81614a4080000308000011442c8101101c80d41421310584850300800c3c42000c484400580240c0141d140c41c904106600c0314940010303120303c1a00864403561b07544460424240c4102a1102a81c9000340c00041c1c51401540c0c400b9034060007070301c00407443d40b82a80c883ea004074803480c1014101d0300c1d8071007224280e0004a40151095000b44000303400701d0301448010580110710125246842240010064550b00c8101400d0891006040c100081c21191 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 178446016 1250 178444766 178444781
    0x10c050417012d1a01051c180b04050106050f10050c250302010806120d110a02040501030c090b010f02031602011202040806180a0507052e020f010f020304150509030c030309030d 78
    0x4003131842d1151a0840064100d00038203109000d10300b0341344002600c0440d035601c01070b000644207480e08012940c9290030040f40100301c40c00c80f21542421400929418070910281d104e10b0000c040030801e11607041c085a85030002c002208842c0301d510b0200e000000015a00c410141c001d540302528107046000141003040007030a0140a4001c7c1903030020641001b10756030364841d800c1c0c5060010344594150741880c3c00c6d22110061b5000d450b110000003003140045001084858a070002d2080020250041da00d4550a0781141d0141e0004c10a0907501c12452109030801441410301c0414001c0d4603c481040360001d81103003055921600501c52213401031800c102d5140c20500084c1124420345d5907032519070690703206070b5000302c210095440c0360381090040c0414480680400b0349440c8450b03c0001c2d50380b1818480d800003546800c03a0301404004900841e445070750086084010112a00c60910090070028041006400140284114410f0501c001c50041d211700004580302e0310212080c104452a4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 178447266 1250 178446016 178446041
    0x904140c150901350709091b031103070c110a03080c010c080c070507060807030f091209090606140f0417010203011d0402101d0301060f080609010c050417012d 70
    0x40380c892054103d54540c280186138040c01c4840a8954800030358480456070050740246050021402d086242d0a00300000200150341c00d204080c400f00b9004103501c0103940c010000f420150b07080d00418001c115190381c01d40c003c1c009806a40e620344030b02e2380b0780d0000242410580d4560903158102a440744039541c01504000304c503440c20000c2e540e2295600c05601c109400d1141c20000100418001d40c00801a080200750a00c141b51091400111980c049001000804e0420700c020900c2c4040741b0451040c0c400d2500c0ea049218000b07013201c01c99801035000b140c4a114200004640c0d40c54000000010b048648005030b125410100300c440c03808000036072074504c01c01e40c40801002da941c60303045401d441071900b0034140350340030301c8521000e03190301c180c0e566019030814000007503035034101309058115403020007665496141d08890a0030b0700c0e08004030030300280c400d100510100240b0703a5401e507a0900c1c000001542d90742e140302882401041198005c07103501d008074038050941c5900507803d81243c2d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 178448516 1250 178447266 178447307
    0xc08010f0e0312060a05060318060a020310090e0708070602060a06090b130203100b0a0509130207020d02011116090605212814010203040311010b0904140c150901 71
    0x9014080e68034050550402024003c01c1c02003646920f44004c003501030400035041941d2450854071690b100c00c07110f880c1e000541300e8040061509179045c42a13a0080b80c2d220482d0109615005005001e802c03030704411034107405015030001d2192000c201080040c1803130b40240c0a2031910b9100001103440303950180b4959130030310740f034071203a41d407034279a05141e18035103150050716500d608020840a62803601b00c00444040054400308003900107025080d400e600f04c89a4080754001441c0c40c2c01d038011600e0003508a4030a50250005601424500000c0f00a40045078240f100c0e4160313841401006500201e2581d550300b80078042400c052000000108541e1181d150b02607041600b640d6802c1600e03c01c281860841d0300c0101c0c084040c04c0b6490203282c1049990001c904d09807a080c3c001d41c802e0f5812408a1586152400c14101c10301030b04201c06002801103c860340c0369110082e801d104030085450038080c1d02d0030f00780c565840703003101c03003400d200440c085469240c000000361140880a00300c1e80c1d40c10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 178449766 1250 178448516 178448531
    0x307020315070e0a08100c1b080322030305070f02010c0e01050a050714101515080709030204051303080912090d0305120c180d03120b120a0c08010f 65
    0x803000508042081008807940480340e0780e4941c2191180304010b140f50703002007582400681e800300000d06a112241701a02082000d2040340f003610340c0c038088040041c0141d80180ea00340803444072406580e006d5a80040c08409060720184400003c1130702c002100800d03075480034054002d51100c40e46080e4a4240002c003c10740c10f85c8005494400c28442e400d041010001d100310005108a081d5903807554400078441c80c0680003610103407540502c0c0040780c00396140595240220000e0141001100c242480390640c20107640030848030031100030800b800f840200c5500200503212481014440c40d91300512800484081c640144030b18405042e200b040e1b40018480c0d4881c100e800103d03003e030a42207c841c500d005c1180303000d5406000e069040022194000304201010100710001c0149510810403000400030103c01c02400808c0c11f1405070000b002d170a50319a05000c00d500244010400801d860300d01060588243d01d4114080c4044441c4c0880c0d68042140043c00d00500c9600344400f8014040c10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 178451016 1250 178449766 178449769
    0x607020402071b061205240f040221130c151b030c020f1e010503040c24110120031008071502060609060108070f030f0f061409040206040b0d0204080a06050603070602030702 76
    0x203040d0202021601407d01040700d070a584c84078240c2c2e00043c809401591034624100c1021301c08401000da000760360f03401e02e000545c448d5010310000301242d48a0000d6075007074102908a202d07841a000c000c000d04c00321071284005410840c1d03544601610175503a2900c4821644140003840540c00c014038050321064002500a005250f0b05501d21002071070072548030394030380c1810006040e480c1c0c070281d002c110341c024105081c80c031806001da5a102d50785031512500c0f0800c0c41242260354076540c14601c45000c5800940c443c00d194000c40d003090003d008003403102d440d0301c1c0540c10005a83c2c411b10508130741c880c0c1c0880700c6406224999004200f01e03103001d10761425074006041400014510000c1010004641d02600e000b13500585203078080000801ca07c0b1848401800140f85074041c9904a0610b04a1002c07a4600a07600500c200c1d80904001d04051400110105070b4220b142c1c00c03100150244004550310f582040b1610340140164800700b02400c3c5902890300700a02a0410340c1150010040755025 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 178452266 1250 178451016 178451041
    0x8010b030601030b1c0c08070b0f0301090b040b03070f06030b0307080a0602030705040f0f05212a040510050f100203180f030d030603050601060203070507050607020402071b061205 79
    0x1050080c00c0124940340d0350030000e14400d07240005821281205e07038400c2d052049800c200e00c1519000b00c00c0380c0b034a50b200c403891403040c080e50340954081e9504100501015200b6041080e10035006400801c294613038400084c10030750300ba0011909205a1642001a198035025480c98020290081d007001c9050544550300e40f0350b0031902801158000020a0605101d4402c442c000c04910f201545079a44991011000030028490b192180c0c00300007640c901202c0032600a05440410b500030000020320040c002c0101e054001c00040e44001e030310029540c0c1e21755000e00381c4107007010f06104181505040030003940c0300d8071044032170141300ca2182d80703451550004225044111000340c1c03241700100003000582c940c0e5240303114030740600400b8056132174076415401c004162442001900e400b030303807146130407a41e9000307a64003d00a644240d80802072401c000000784039144c0003030400343c544a09500d498023003508100d4650b06080000c00d08001180d0311565002802107242c6051246041c0342002d100e1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 178453516 1250 178452266 178452271
    0xe06220f020604030c0303080105031501080607181703030406061415160f03020a0302010b030f071a0409050907060201050705040315020d0609110d1b0804120903020402190f08010b03 80
    0x80d020011a401503558240660f0011a40501154100d50312031600409000b028820b41d406440344000c100006045a905181600c141c080107002c55036442c5400c4a511880550440380340095500c08901111070b500c01e21002407a86004640c3e82c10305250280c03c5814551200c1404590403404a600c1e9841c81c1e1100c81d6850700840b01a142d80d0b4032250351041102510004020804044200c0300700750700410651003060190f002049650980c205140c2c8655200810a1858005440074810254800070007114200241e40c040d00b415201c0340c80b201214001c0e80c10740101e42c0880c80400c800c036424016141e000607140360aa050500c0c540d502190103442e450041d82c0316401040c260301c0c12485502140c01084a10003e005440c08240c510809a0229038412401c60a00d00f4403010381c285441310301e8010b542940d501400b6603e40d140d00c81c8100303035a00c070316040215035000000540d886002030060302002606a88141c000114003818100c0d24001c060240880000104094181c0c14140c96 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 178454766 1250 178453516 178453523
    0x807390506130e18010f0506040509070f0b0a030905010c0e130218040e031c060504140411010309050a0c0605031009090510020309071805090606150a0e01090306020d0e0622 76
    0x7854031007200701040d56031451115184c96192072000b0031061b9143c0c00690040c0c1c1c3c02c1e54200040e4075074041958942c1440d000b480b0400c103806208000030300e07624004052a401902e00015000c1c3d0b40d83e00d00342515504550302c070000e00d4010300d41040c0d25000400d0540ea00d13659004500d03040b2086652008d001d06003082c0d502c9603075107803038140413041c050086030040300d0b00c8080c407500680c0300740c0100018a128020300e401107140000201c2603219204900340240d81002240002440c200c00450242c00c030804215410302a2010f0040001c85d1109888040c21050320382540303e01e0451030a003200d42540d4030a4920b141005003000121ba0007241c1c8d100303046240440075a4954554200c18035104856010f21400c00c084900c04880f401140c0c00140501045416507005480344410041d4540711402c400c0340940b8104020340c1128040d4002c0b04100c40107040101c4641d03034070b80712401282c0001c1040c40b401034035015402c4100606024117988107202040c0f070903001101c107645150820445c003004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 178456016 1250 178454766 178454789
    0x601031e080403080d050907060306030201091a12070e030c010e100804051603080d05060a0b0301120c0b031f24031109030a0c0608010b0412080739050613 68
    0x80c1840070950850b006540c2101c0c1d21595609a0302a581c001c08017161800103038010043c0100d80e0512a0107400201c80e01656050096410a0580ad69807244002d0050708820b0801480700e01708003554074540326602540fa21001001d0300d0b000e0505010307141d1421410008001800e580365918101c00c010595568039100c0e0301541c0c1c610b00300d890444007610800008801080010030060b80e01c00034050001c02403001c0c80543c40c0c0005024417084980145580600e080c00140000d0503082900c101c498083c224403040ca5070381c2d040c5010300d68001d850007007007d10024004036011044201c1c04004106000c08401e109008a540c4240c11105428510806460b065907490b80030400c001d070b50341420000c00707440030421246028855090b42e8456040461016000016046071910603181220030038a41c101c0c45443e180d032459425403040300d04441c17100b020b000b481001c41e1608041040025040c2070104100c078505a1030710900c0440c2d01951184804202205141d000b00840100301c0d100648403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 178457266 1250 178456016 178456073
    0x82110121401060f1a090619300c08070e0f0a031e0506130203120702060d0501090b0102070902090a17071706190e0604020f04020408030c0c12060103 66
    0x50003548000300380701e80c075824210041825a0f14007000411241240210300030210500d07200091401060001c80e80503100b8800f900700d9074001c0c070b0800e070105624903141d41e190f142d8440c0140c0d01c100014412461940c1e40340704940880e0305104040c1e038414282000c0c0e84e81c0c030702200010a50f10740700103040c1c002d503500c90103011180c40b1200c014002d50350141c00500ca1181d411611041000c1601050b640f038030035403021a00b04904820510300054000d0090000b001801429241962104c01c04a80040c0100b20881d1424200d109140c064401d0030000704075130a480d000289410031a41100d00c0d420320400681030710380d8502018108031400b200c1080300032401039444c04d04100c200e81c070007022134000c00c1e031600601e880411098440c040104601c42107800c84240c0d80100d5017145207254080c0c2c0440d012402518158808804941c070050015140503240c203851411600400414107071a03101c1000d864451070182e90700d0103001c0c0d0381e0004040e550b02d140c480540700f401e0f0078543d03002e01c0300c1c0000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 178458516 1250 178457266 178457273
    0xc0c0c0503161a090406080303040507050108070801030204021e0c010b0301050c1323030a0f0309120807032f0a060c050715090f120e090105030f0c0111011808211012 73
    0x2034824044c001032041040c00d580b101c4150300c1c0c0c6e004580854440c0a440d50215456002c0c260450040496030b84203d080d0f82540c1c00d10000f035100d10941030b1034010300d10780b2a6000481c507004025424400001092400c41d92003410b09403403015214400e124800e022600e1400c8815442c0d4046640b00c040108241c040d11241407400c001c100c8069405004520242c000d010880d4607200006109940305035800355190300b44490140d00c0e00340182401410042000071903c100082c16240618036400d56604404881c1d203c1c400d03020b00b406404903082107010401b44221841142002c402ca0b0900c1403900003565221864902c01100c02c0d2007860340c840c0c04005000b25003c40d1034015a02901c2d00318001050783d4007034500e0000d01c183c1071050b10b192002103a50305011901384103007841e5800800300000144015100011400c0c1228501c1d076943c00d100c1c5a081500e10000d01c928081e4000c241d503410904e21b607915250505410140c2c0c5001102131004401c0c003c261881110048600c00103d203540f0318 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 178459766 1250 178458516 178458569
    0x60c0315060d0f02030c070b070f0c030c020109051c0c0905042102030f070b040209063a06051609090b010c0b060d020a0f06030b03010b0906010e0a090c0c0c050316 72
    0x103420303c1003248003004014509211800901100340104600b60460f42c03055000c440d0030050041c040d0004a188440e01c0002e4000e99a1800140c4141018031005807a0004148042c5007805043e11070245440301c4418003144584050191007145024056880c00e901c0d0500e42201e04c030481904520b80e9003002d00c03050301c2030064500c04014045240c1c1d941d081c0c0c0c2041021440c01380d0701644034019000114800c0e2520156031110100045a902d009045c0d0340210041c205501d070307442d03000c1004031780a0b600049851081070310074001c1800c0d40c860034002c444024500240341d00700d0603103e0301c0d00c3c000f09260307a088048441c4450740400000c0c4150b4420000c40c480d4101c056000350040710806000c40c00601e01e604034015103141d6a010000c0c0016003040500380d038068800140c2000c4c102001c5100355204e110304140c007000c0078041c00101959801d02c03074120f4481001d80c000044030303c1240003c0214071031011001303000403001419000c8100192429070030092044c4090000460841c44030708507000f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 178461016 1250 178459766 178459781
    0xf0b0a120314040b0d060509090a15020f07050604060204080705100203030f0601050403080a090602010f0204120f170a0206091501060806090a06120c03020a0506031e0907050d030f02060c0315060d 86
    0x8000c5500d504c0c217580400054601d50040c14800c40c401c0d4006103e5480010358900a00d8122200410045180f03064000a50009a00004855080201c0e00c0854800c00000380503900c00c41d00180e41c1c0740383c024603030f042260f1500054400d07030300300f0b90181000c1d500000383da41002c5a00803521080e201c0701c0061b01d09114076800141001d10218054000e140c208600714200d4105800a102203030b40750301c1c0403089120354050002418890317036041010488541400c04164407030404152644c115000c140c002d03030040d030756400c0140d00c107400308944018180f00800681b1f115418283c055414010050000e000c001c00540c0148010760000d0000188c2e40c11034401803000b1400e45031040700d98205000d200e5043c0c04182c2c02005400d40000c0c9504041d4103c0c1e10410480903c05207042003541241e1140f08050b280c08003500c6201004921a074601c003240036094441e4a60208030540d5110283c10600c004001700078241e41403040080250001080c02d04a510803540b0981d504501780c00b5000408a2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 178462266 1250 178461016 178461029
    0x4090506150301140a021804150608060303130e07030c0507020a1502250504150b04061206090c080106030b010c05060705090d0c0e18071a09220f0b0a12031404 70
    0x70005000d1403440d0780d401012900d900d81f081c000c0c0c8000700020703c41503e2240080060750103024004001d05031080402d41d41000300101a02e16091a150044007079110f640c005207200d418003814046416054410220161090f040c5103040c21034540000d21211198442c481c0349401c40c1000301c0d2814424460402c0036450365140c2d5610820030031508414513414050680914640f903e428600d41300010550b044402c440d0506240c141000412030342400f2041e0604035954980c100401c403800e4034001d620080040d80c2d00e089041d80342c170800a042da090b51071030a05000100402d0400f041c0d0201710164003103400d0400c01c0e078034022440410580c5030440c0f00135000c034a204070082240385a00d00454015100f0f00008500c00c2c40002c5400e407182141d124007400700112003c82060040f501000e001d010000a000b8206038881c1540c403ca000c08261a90b0300407942d03004441000e0344a4426030b030b605e15040e9030000c242810311440a516440403c405818040350310030b04491124100308940c00b40c401c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 178463516 1250 178462266 178462301
    0xa0e1009020705031b1011030f0414032106040b0f030714010c0b0901060e0c0a05030106030c09080a0b040c121716050712060f0513060902040608070611070504090506150301 76
    0x83c1c0c05400e0301c4286c02d041900c94a410006a16012030606094a0049100640f004036586440e5201c40203050072645410003030006000b641c1490710010036001402e40640f810341094a0894204002c44000480d014411104103100304003030303100024140c06880842c00c0310000c1070442001610040c003000e80003010070402004200700c501040d04130b01c0c200c0b841c203258000d0035214192001d555005207443c14000900c01c3c0010000700380320790002e04443c101030418221242e00c41185500300404011b0a0700c401b03140740305210420019200480081c41d00200102e001c0c0c1c1103503161842100c0c803200440c0c0a00010405140c407802d0440344808643d4440111880680e0360100d01c107002c0f05410b003d03a005460000c1c504085075003402098070403045072a6a001031001c2c1e03950080180340152040c0e03002651440089504071040003204060500ca884240d0000440040c0c6172420840b074008a004900b00803460002800c0015695000941441c07001c00301020640401e00600c003100c0f45040a09 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 178464766 1250 178463516 178463557
    0x909050102070b06010203090603150a120b07020d020c060a0804060b0303070b010e0a050105010e01080a0e01050903130b040b07140c13020c0f0604050c0d030905030102070606050a0e100902070503 86
    0x105500500200d0311a0100f0780203913640340010382c0c41740944050513401c004100002482d94084440b100c8801c034004180710704103030b01d403660454100e144840c100d4030050300c0300074804015010000c001104003588020461071040c1c01c0426194002c03c0100000d0100d0480800c2c108401c503004500c00781e4000e4100ca440340c1311401e0034644000c0c284600e02380e0302101c0c4003241c00c1c00103600034903050342c1d010303112620740300300034001155030913001441007031950350701c51101703107111000c5c09594041c0840780015900d603541078110720120440d03035020301c043e080100001c022642c0b0860a0ba03003010340215100d0910303890340c0791450504402c40e21181d404107045011410010043e03001d08040d103940030403506000c0200d4102d60340c0340d10503980030b0115800180c0209082c03502c003032841c1d4414480c0c6030000030345507100301103400d86c1c000c00011541e29440342c130244a1030404807501c80042441e04030107849404e01030b454415101c000e0040040050300028a181030000c01c1044032000e4071a00030015820703 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 178466016 1250 178464766 178464773
    0xd0e01020f0c010501060807030b150a02010b09010609080d020f0d0c02060c1207030314060d080306060909041101260118060810090b0109021c0216020d05010603030305161211040909 80
    0x4c1c1000d00910000c0b41c3e1580204101620038420b1460f52400581080c0d0a15880e201c0500d03150004981f10046640310210003401e520382c102110b008100d80e032a8012801d080800302070030442018a01d00855100c00c0c0001c1e100f40001661180c05892818508e103500d000d4008982c8911a0008190440c07080038480c0c118014000b00420899000341d5041084101c0c01804104880d42038511903030014003000800e021801c084010741e00108000c08061078001181c020800c01d402c200e41c01c2e40c40707002e8148105910358010580c46a0303103041b450301210848040d10b004c460345006008084188800c0b0060301c03803554841c0d00140c080c003010303030407540c1c00d80e1440205009020181070854071201c60400000d19845240290f4000d071001403100c441d50f04483c1e14480080d007003481c00e0182e40c0500110240542c542030f05110f0704901941c0007080c00c904504003c2c050324800703404607404100080c1351024141e8000040c103501602d401d00031072140c0d0500b08030b0340389009a40000c02403d01e0840d445042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 178467266 1250 178466016 178466021
    0x2a120304061814032d07240201050402090414070e0901020901120615110307020a060525081c0605040203311a040c030803040f110a05060d0e01020f0c01 67
    0x1801c660b03040c1100751510f038442200620784212079003640c4240c94100c4200e0300248140c5c9800b008400361065910800042d0b481c0c862142d2016040c09031030391544180c00822012412070b01140d0000344480c0c2407603808200415001071020340302c0d061007030078009415002c0c84030400034030403161b007180d00d400d150910038007d621048079240030038684020066604014051001119003400080740c400409210550b04c611030340b00d40480740cbc00100b1906005075a411412000b40c1000c1c0c0c4c800d6142c1d11811a0218060200b0b03207840c400241c017a203500c0015004204036015070308143c0c680b178403601000000380040c201c5078016a50150002c01000035038030b010015032000c0007201020006010350070460300000030584c200500000142030003450700340240042142c00c684580c0714000010350b00e40f80c040054000b0365003141e100c200003150206200c160715600e4801c2a04964201060b850074001500c203220380c410704681c1540720441044460420760580707510110034005540e990018100e281e00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 178468516 1250 178467266 178467287
    0x3090c0a0609060e03074a07090b0f0a0f0201090501050114031011031807090204030605060405010902310b0d0203070f0203130308070f020d0f02030105092a12030406 73
    0x190700c040d0030003198600010814200c8100c1d140c1d4884801d82c2101c2e00f5030300d4081c07c00101620300e00c05000d50440403103403440c1c1c0c21145d000918038400d0608460041442c282c55018181c42502032104410703802c1c2501c21103060300e080b800d0201c10085040c0041e4003400150202500b25440c00c00002030f402001070030178682046c1207007900d81c5000f0521802088640103074802c4200e100078400155003e018400f05800c02600c2d00881c0d0702135995000c80010303070f030142c0c2040302d60b00d4940c001d0005074280380c0591405440b014a00303505003080f100d0800400f118a22100f03402c0b01c4448502c507513207044291400c000e02040d090499031486c512410401a510a0b075070080000c4c0000542d4814030700c00f100b87c0340d000c02140b4526a1003840c54446050039008001d0956100200444040040e50b07400507065050b40300322880d0380c05505a00406003120b02c001c10500c16500300701c1c0c025010340040c0008800b5042290009184005c16901242c0c109218105030300c00c81c40005400724106070450000744 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 178469766 1250 178468516 178468529
    0x1005100f030c090e0c07020a0b181807022109130203060906040612030c080f220602030406120f0209030a0b011e03021e010c02030d0504060e0d080f03090c0a0609 71
    0x34038452000200c4a540051084e007110020000c040340c4c404100c4002012018001840118940d481c0c00c1c213a8150303800410180c060308000c0c09003558509007003900308000400c10500c0c07815840e00d10740207500d4000498500240b400d074440c1c15034402c005507080d45c41030100540100000803200c04190025032099850030310032020740000421610785402500240d480c209000a003011140e0303010341c2c24a100c140d089542e10400d000448003108076101420520750300760306103c66604e140e0856850003449800690454100300001e11250341c00030314007010050240c800080000e030302d00e01e42000780641e60b0314507418007400803200c051200c4443c0d4141610003900240349480080c08140440c0c000c1c901c070094010902d00030040503251516000c1c01800d034107040604484e4007d17070000b400c1000130a01034010903008682440312070b030300a0a1000c60a000c0d118017050b41c0c016220002c180c01016510b040c440c00001c0000c1916030244241003848002034140d5a0349074640c0b80180103001c8a02418 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 178471016 1250 178469766 178469771
    0x609040603291311091503060c030a0e1b0d061808070507060206010e04060c180306020406090b030603120715020c0d03140712050c22050108010803040803030a02031005100f03 77
    0x14081c03d40024903440c2d003039444004100f41c2001c40c03051001c008401000e2240008411190f88820344007809682c7c032440010030301a41e05c0c07810410303010032101e40710b03020f92543d4020b1000c1441d1910258106020b601c1c101c0e5403240300102d07880d02c00054107401400582072a44000480e0030041c0301e601030543d42d0b125500f0740741c04549441c404c9981d26030074403031030303001c0000140480e02140046d400300035961042e1030000b41d04040e001200038074202640c003ca075416800101082410380c03000e018000340c080e400440e07255051520000e0756550401d544440e9001000842c04200698021038540c40c4068003029034440d1500c1c500240c40307194a0401d44046810321428402803400546250302c03030440717170b112702c069000e1865032840140307001043c40900700ae00700001010380501007980794185140da030a4030407030b03414140014403a1506a0001c0510761051009222400001c0140d81c4d0101c045200103072282d0b81d0300c1f41c45c0c4e01c081259001d242c0105600c0c2e542c01c415580501040303452481610705 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 178472266 1250 178471016 178471021
    0x7080a06181506050309070509060a0914040b100e180c10050a09060e1e04061e0518090601090213032f0913020609030f07081501060201050f06060904060329 69
    0x2500c1034807044031b242d2001c0d0882c06044c451440c1001c1001e80020028044034100d6803210454000c4070210748a4115040900080008101c0000300d1580e002c08a229079080765885e0070121040d828010303000c4a5491000461403007001c408020314070f40e003000209074a80d0014070304005440c540c090300c240000110086004104240202b0b40001c0901001e0311190400c4503101c050009a0200d901d010307442601d0f64000141c0c003000005810b0782446100d0b240700305510b040708000c4003d0070410303099861500001040803410f008120241128220300c1c002d42d9817495514030303040d002c1c4d042e08024a44980304e001d8007a0768820240c0c44030103045641440e00401400030800403071130400c8803800c51111045031041c0060030498064a662000581210785180e42c807002c1038105280c6801c603007441d500141e40240310404551170a0b00401d0a40005c000c141840c20384000d000710018001070007441e001800c03440c9500c85900c200019500001091011034690f101100e060400525034004942c43c17002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 178473516 1250 178472266 178472279
    0x1f0507030f140a0f020c061b060105090c03070c0507050603070801080f1b0f01020703060501030f0314031006030c1808030301090c1b030f0c050a080304032607080a061815 75
    0xa1015850101402c0702d401c048281c001140c206500201a1086008541042c401350b11801c0203400c0e00c0c1e000c6444181d0000042880ba1302d080b40582c41140b06510410512182c0b0700e03d181181c0e00715045251081e440106420124a80085580025080f1900000304009581d12403041d5041c1d0b1900d13401d40d103846e030b0031003a919522209600880803615280015010030700d0804102890003006005407841d8981e00d0300d859084603c00d900030b85a02018400c0c40f000c05030320500f0030320b00e007500d080120300710b0804c809000c0503019540540750505540d9003038241850300481c01c07501d05c4d42e040b186d010017103038444002e1901c0c0c1c6c0080c031a41c03140904108069407028040c03003640c1e915039890980200c0c5910207440464041d4001d0b1100014001c0104461000c03d4080c401ca0721401e01030342c0669500d003014940100300e00904010000300c005034002d0015044e010719a40e0b0381040c8a403422005540790402c10070003c00044c2d100d2144400c5140314054185015000720811a0100765200602c1da560b10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 178474766 1250 178473516 178473527
    0x60a05062106280608010c080601050a0c0f0204020c0307050f071202090a05151f02150f070f030f02040306050f070801300803010603050f09011503020108061f0507030f 74
    0x110079032115008000001c1100c0409811030030104424500d40f40e0b850000314005040f40e10b1038100528903512a034118103850b41100f00740d60031010a04c1c2441c42c10b550144000c20710b0701e040d84000c0c01e0350a041707012415075803181c0513241b0b031403003035000e481d0f59421034030f80190f81c0c0341444454401ca006a03400012100b0a100500340340c5034019020103034540e508480341c40140001404502443c3c20030303140035560348403007000c69800c41d5079400980000c1c1020401030f00c0c04494034020305080d11100b00b08048190b401140316006800b41c140700c18807031440341d0140c02402103282c0c03812441d131021400005101c0c40341c120500139030301c03170000c08416180c00301c0480340d0540c2402010304000a03d0100703403942c03281d007185c0d09805070065400300401140e1f64402050707500a03400440040c0d01c54080c8002c0c1c507031141005400c40b00040c02000002d8544408504270080d512010707040c86009030007d42641c4400903030318134000f1100a80480c400c00c0c4c00001e070240c2c000c014154001039030941005041c90048 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 178476016 1250 178474766 178474819
    0x40f06050112020c01091703070225030605090a02090a02040302090604270c0509010b0309060a090210050d150801020a02151b070201210501150302070c060c0f05060a0506 75
    0x60b5503041d8108412142c09003e940109502e501c0c0d5940e42d5420000b040102484070b0401102d00c90543d42c0341464503000f450300c049208083e0901000d203500b60040c5200e031b51f180040f690b000304041501c2e136036200d030b590800d044030b0b0010350000d44540400c00402550382c001c00076240708940c144541c7d2940d400b03210445004441e43d4010b889018182c0b008031076001c171241e40703640c42a00c40c3c0e0176160701c0e0030102c0d080103801c0e800341c481d0304404010312128010600065501c400e01000400c03140c4c00e15000140c0141e0310310241010b004000601103000c40f019007041c0b48828040c140c40f0380156035aa0b519000f0351200d05124014000c8203010b041031103a10f00c4190080f60b48080c40004405248000c0c00584d01543c2e08034140b15408410500d41c00c0d02c034403611074007036403854005401d62504c44c040c03101400d03110400003090b20400850001070098100c0300284e0341c09140003480c0c1082417520218403940c20034058214810031081020b01c81c8180c0110340302c0d18040d1152201030b442c00b1aa01d6a03510751 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 178477266 1250 178476016 178476019
    0xa1103130302090c16030512010b0720030a02060403141e062410020a0c08150f0601020c0303031003020a0e0105060d0504030201240312080709030f0203010920040f0605 74
    0xc0010400341c03070500200340c0c002d032100380624a090444503650703008400404040707010034004903100e20f600b1070700c3c1702d041d00400c004085545080182d03501c2c0346030b0070580c2d20607030943c415182c00c403a4551003c0201e2aa5a5400f509242c1e480c0d441e800c08801060b0340300100a440d2160048110700141c00c0018103c1102d5410014110303501c40c181d1079141402c0e01e07408002d03045070700b01c000d00c0a40e6820f42c1c501d0500e01150098022019903003000440c03000a034001d1800f40d48904000d006000742d800701c9941c4030003c20407001c43da48500c0f004034103041440c000280d0611020040c4203580110940940403681308032004548503a84240c20b0492540c24854207501504c18041c80000015940000703601c184603200010300c1c41d0801c0003404031514103407503010080d050400305000f00032030507203072031081181410003864502c0d04274030040c950211404010000120034813500c0031501c09400214410740d100d81c4030035990f03051510602e1000c119400403031055041c081c024100d40c03514821401a03d10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 178478516 1250 178477266 178477297
    0xc09030c1202060f040b09150306010215090a02060403050d0201061202130902040b03010c05090f030a17160b070503193804020301080606011706030a020409030201021c020a1103 78
    0x5484401c00102480e1507007a60046401c1141c082c44125480007000501103200881f40c86001d1380c0284005107c3c030302025030344c120080061001603a00090006850509154030708002e0303035080c0030141880c420f5030009400082c0800c02008001001c03d0800e079900d160b9008100e40384e6200d4410100c100321040194001847c40c2131a212000c0d5034009918541c0094804101d0b10041e001090031074101080a9000030340200e110f54003860460007045002c02300b01d000388868426521042010762040b40d140b0f1113040c1c0001d001d0b800e5545407039000201174100c110415a0b02e04000c018155038811140301a585207510105020050301d440350030042c070740d603905c05100ca018407000380081400e00c01012071541645030320101c04c7d81d100d00045028249110241180c0d0074220005810701e000540c1c40b02040c001c40040081a4400203107400306a88c04580106407882d0900302039009110362a030700070300c00541c0c16510a080070f0a800500464110356100c004045044c9c00707650f01ea0082c10820407030b03c80d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 178479766 1250 178478516 178478519
    0x60f010e0c0a0320251709031c02070e0108060907270906061d1513180b010608160e060f040f030c050306060a180e07080a050109060c09030c 62
    0x1c00e0704019000403003031400c001842c101406140e10b02d14140c0502001007001c0094444646061110f411109581c1c130003141201031000d0781d5240c546810307605150480c40c00452012a40d550402002404008030509460341a402040003501c80009005203001c00c140540005440d013000244d10344214843c00c0508066814900031400000180540c0d60b10b04080c5071b24240451418851420f800d4842d02c000196240303840d609500000c1688048180d0072020410420348155000400359485021290160581e49682c2a00020f0030540740b22807400e60054030803c00c004040414030b040e1011900c42184a03030300c45400a007151004208c100c001500f50780940303403030b080c903c010f4043d0748070307884200e03082513141c10005100342450707070041e40d40402e14101044203081c02e00905800003003d688005055040c00090b00f10084c00c54418054180d403070112070180601070048001904444050b55000c030301500b4424040c2a2582c0c055072024540b210424059009540420440b40d228554401e00c9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 178481016 1250 178479766 178479781
    0x70b1005040c0f050703031a03010f05150f130507050706020307050d14060a0605090a0305030307090317160308041a0a0f0b10020606010503040503120c0409151a0c010e010e0304050102060f010e 85
    0x9018810000c0840c234031010b10070182d03a50038000c1680108510100040500e840380340c0f002500140301400380107803005115000f42d500c8403000540700203610f0384003081780e0300d480311b04903070a10034030401900e041c0c0302100340014191710000509001c80c0c0c802c018031480e08814400c403050702083e20400c1e40700c5003200c2c1c10012030780604060081088000c21990038a5503a032501411588201d0f01c0c14005001d1000078010410b54500c4800480180c10b042030818500d5060000341003202807000d0240112100090100b003901e81c481360504c0442000701d05e09007400d8821401410440401180311410208052201e050000d6800c5035007a16a000f000030b1b031105001922158000750041c1c810340420484001c5104c54090200e0103070b4145030000360750740d01d800010300c204c030500701d0700341401d1254410802c1400c411100c80c0010011200519a40b01c5116030701c1c1703004081420299840d542010448001c414001c00030b002101d000381c00340c800c90b540f403400c88070b0070803001d0048030044400b2401040c040d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 178482266 1250 178481016 178481021
    0x501050f040e030c0f0703050d09062a02030703030806040608030f07022b050a020909010e12090420031501020f1f090f0c060e010207060e060c03070b1005040c0f05070303 75
    0x6809960a591030000d040e00c01340e0401a03802400c04a03588003640810400208000d65100c42c6040d24010780102c0c00c12800410203201d07401041d8008040441c0d0890006003a500c203c1645c0d030090407511b8090f1340f860060040c100803a010f80c031032454100d0006d01860080220354152040c107a07407501d44111030342007103007038001e51184400c24100c10195011807842c1e8004111258000c01c0141030002551041140c000307001801104145d0401c0c201d098404c00000f89108030317a850048540e114503000780498000c00c3c01d804001a1020368040380803c058441000714020701d1103500440e200e560700390059a4440d00d00090f04142e40c403000480b4075821548a180030b41ca00b529034013260403c083d880b003c10505c8401e02c10b80307002c2341982080080c16080a80f100440c1c40a0016142e04c600d40364015011042c0d00703d1141c006c2e030700000c19091102042c004c40706803542c009060706150030702852030700400c0740c28002c141c0a5880c2c062907191103801303000002c0d151201035503000c1c034242d030a0354224007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 178483516 1250 178482266 178482281
    0x9010f0c0909051f06020604200d120221030103021212030a0902040b04091a07020105072c04060b0703020c0301060f140a0e0c0d150b1b2107050c040501050f04 70
    0x20424008094400090024200030340101769980c001c000704e0805007041c500a1090701d03840041c05003840707100b00441d118003654450a640201d00482d1400180d00300b6030501c5010038407007000c4070716104100030003c0c040000d0350603a4000d50b41034114207201c041c02e982c1d80c50a407a1040c091101480028402000e54001208462002d0000f1811600c5400407405440e58404226500300f074401c66646c04107100c24126501400c548020700c014145041c1c0505940002c15190640314084403031004402c11a904207625941d0243c000c000c2203a5401079480f041d08810030403801070007024005955460305008190985240f40039503081c091034042e10100407492412541c2e003003000c0d0480028510140c2034201d00c40c0d00300d001c0980da200c1d0700701071000403140009810003200780b06d8403007440045111000c1d030303141d80507049610100071041643d591a252201c403c0780d00c10b0080d510707207148000040b0013502d440362080f030860b8a54607018003004191002402400d400c480c0f909072608113868103030084003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 178484766 1250 178483516 178483531
    0xa150911090910090f06050f150402090f0a0605031902040605040621090305210f070c1e03050703120b031b1903050105180a1208040201050c010c0809010f0c090905 72
    0x1c8201c02000110000c0e6068008290b0341c05034912212002c6c03042c14054980d000014a00701d40d018030741142040c1010034509005802030f0780c040760407149510780d12080d2960540043c42c00f509a951104024000c0d8401c80311082400c16402c20300ba01d4400c18000d450a54807207446039401d260030030b50b040354455075020054150b0200c040059042c0d000c244a8007a0755070080e42c1d41a40c030070710340b402048a80d122550b610f40d000024010000b80c255000301c6290003076024a0a03107080302e9a0b0800c9012960100d80c0d40080d50603229442080503004002001918881d0b22240c203400070b0070104100301d03070801d6103182e0541c2040031191002001000c00e991140d034001c001d004600000c4180240b00780298104035842e84d51036052001800254a0071400741d42c0c028010702000f00142c1d61000c0d14041c0840d00310502c50784a0200b000c682c0540c040c1d400060315200200310581c00042d000305400c20a4540382140d500e4101c2c559400215070062010a6440b0f40711542600d182007000c000800c0024020b2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 178486016 1250 178484766 178484773
    0xb0601080c0715090311120909090c030f030d050105010c08030a0c030608161e0b19020c0d0b0610090b041a0706020a050304060f060f05061b010e0a1509110909 70
    0xf00100510316075114002e5001420b001c4034503001d0700085035040004080d501514692000c01c03c0e10003182c02c10031042c1ca00c00781d2629030901c00c034602003034205034a07418020300030008003030b180004c00340c9034601c0e06803030070b01643c2d0341d80c0c00543c1c54051400018120304070400000d05000741a0b08400c154185070305d00002d21a540ba8102410155083d680203074420b86071008014140c2d0b001903038802e8968541440300d4113031400c0c07000d01041c0b181c0303a0b07410802030040c3e4026040710b00911a20224140c0034040c08034084907880c269002e110111901c80c800d03011540540052840703190824243c800b0045402e1805040c481c0154000707a01030101c00000340104402400102140046e0443d0006921172546909081c6803083c190380386012460318940c5800c10070060b502c10b80c00004200c41056440c03503a503503001003105040442201480b070041d82003c440c80e6418200281014004c0d028800e41d4005001807594203060324540341001c0d000520107401044945420040b003508400b00c0d9045 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 178487266 1250 178486016 178486027
    0x30806040b0a091a100905030717210c010204030308010824070309020f030a05060f13020a12030201180b07022e11040312020105070e010203090a0303050f04090908040501021204030b0601080c 84
    0x104100d6002c0c005c20002250540c01b00306a040403c20b0f4805800300001503600d0a610310380c0c2c2c943e2805102010003001a14922412003040c03180212102c1d0b041d41c01c000d540d160741380e0a01a0480c502841a010f1601c9100201d4802d040c00f040718060b0990228800d20664031042c0003200a08500a0280e070301120200341c40d2001da80802c424a0a180300700080c00325450b04800880105c0c000800703441c0d02d0000341201c000165603001c2c03488107862140465445a240504089004280c2d82c41c070082126400841c3c003051058a25506101d07c5155080b540280c4a040c5c1e10345001d01c01d001d0b40150400c1e5503c51183d5041076401201100c0c0400400d1801c0640d25100c4080454488080c2409030350f6604c240041140d000f4461030b007200c8280000d5241000000200d03420703a4181c40003408010300815048070100307800b800c0f50010152500c0912581c5414205201f00354070a01c2268090710800c1403c14003007074600e0940e0110f07504800d0a61143d03680300015200c0802c001d0640c14a010200706 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 178488516 1250 178487266 178487269
    0x10515090604181508030a0c030917100f020403150f09050d0801080706050309031909050d0605010504140f010605160b070e1003060803041406120112030806040b0a091a 74
    0x80c00c028201e1480300c5810034840740d103c3c03003126804192010800c91000044c414107100100305c860300211480c0030645951207040c101d034001030300d806c50034940c2e0450400f1890107000282c15948001c2581040100e155801c034150100d20031484014107802d584000300c01e500741c42d07034894550355003030b9080440e21036a40c0d6901810548091030041c0481c8a003030040c402440f040003103034090049410007a02c4c50030f010300403641d68016203130940d0712103040413404c0f82120f11034000a001444c0c082d108502c043c1240c601140900b078240920340c002c2d8907000c45a00f00c0b489072540e079070140317010340801d0b00750b40d0801000f107039164400c40120740003140b0096540c0000341c5d101e054074403483e002c0d542d120840c041401000f00a5020708440da0825080020510400c8808001c0f14200d58800c8800eaa00a4103034000c00d440740146490f201e1105805400082d06295910150b8841d61003076885540c03d03a15801007008030707014120201e40148003154140081d46040e440600600100e18a05d03103401c40d41780 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 178489766 1250 178488516 178488529
    0x708040b0708070c060c08030609060103090c1d0a050105010e19030f200904031b0f05060405011413080703081e04060b030c030a1709060f040906060906050306030601051509 76
    0x1442100c00000005900781404a6003980c4d0002d4005072030101144050f6480f0b503022800060111417103849920045501680a64480032800f035005148454456841c2c0114418070406074800141200c550000b5406003018803e442c10303140161100c848100056080c170620025441c800c80c500501400044081554100d02c0d40e03001c0d100391006d404075441c40b540c5149010200701001c1c000c00c0f03c5003d00000a8102150048940d4007840812591546050020040c1b500c0e0388042d010b4019401400180070041d004a9400c401c00e0f0780010b000e440710030740701aa0500124020b0f240300c0090001c100084c1c0305030303035090b0019068000388410443c18082010908001d0303034119003956480c01d05401d40d0a044c455000c0100d07080b0701174242c540107902c410400c01d42c3c82000c81c0f10140001002c400580d201c0301540d11002c00d1010050321252a01c401100070b0541d03000b8800030070340c3d844000840d180304000322440707014085c016000c1a441c01040c032400b8105800c0319070180000384080d426549a00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 178491016 1250 178489766 178489777
    0xf031107090c030f0902010e04020a170f06031e0304090218180609060f0a03170705030310030203060a0c051605030c01020c0a0204050901140103030f02150f0609070201060f0b0708040b 81
    0x1c0000a1030766401c2c080541100c0a080b4880301050610805034090307038000c020161074000540300580e031503414240455a183d05001103145411a80741070003000c10798426410b1280e0816401c40360114264012160302500c1c05000449560040205100700c012a1300a03000d400903003210040c8003680740001400011b1511200d80c5070304c20480c2004280e15040e498a50030007030075168500c00a1220003c1401d42c4010f02005e044168008031300b4041b05000c000b11449160410156a100e080040003504030f6422880184d110344a8400462050030ba40e21540e0780a0205894051421a0390030385180904000701040d07680e40001d20200d51000000c0c0000c000b00000c01c0e01030684000a84100011076074040d004c1d038050781c50900034020b480f4000545506403034050400250900707108030202e2030240710184000082900106002d4040d00d0041107501814085420052650315041c0490817244a44039041401003001d404101c00303c02180204203032402540b98900c3c0c0f580310249200c155118 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 178492266 1250 178491016 178491029
    0xb06030a02190e0f0415120804060f02010c0813150204090b010915020a2004060603050103030f0c020306070c0203030408030313031701030803011a120405030910110304030f031107 79
    0x26011007000d5102000780c81030303002ca0070708004043c426000f0541e130000e11141c903030180c0e80d10048600483c02056400c1d0081032076a01c44803d2104c0791401d00343c683c10034411140860511100782c88900e006000f07103081002569203822140d6a0040322410014200c1002e0301ca910114100051100a40c00140040c00759610040b4400102c0400100340a410b07600c500c4030f21104000388400b840c2c0c08078880452640010341d01e80505182c0f03034140841c0b0100006e26500070314243e40083c403d03405400c520304881c007035116151013a080c142c0a844180e0741c83d07002549034002600040d1000d0241c020541c6140c00901145e040a4403590801d155620a80f0315007a04c14070340040c1c0040550022003591014060b00ca070311100d51641e51f0f1180c00d8041800f4000648c40304020449039200710205a0309280c003103140c400c40d1414175061450700d036801045898014499510920901d1b4014041241082100d00055141c1469a10fa4101c0c418102ca421401c104501e0700c9030321004410030441e0041c010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 178493516 1250 178492266 178492271
    0x10c140106050f1c03050c10090606030c0603510321050a1b02030109030914150d02070f02030f0303071701080a11150a030b130605150702040b06030a 66
    0x400c41080f42d0000c8001d10b00307214400511040c0e404200c440c0702d01a0896040c1070454850348421443c5081c10315103890b1600003403400c42d03114280a9140c0010086a00030740c0c60481ea00d8803420210291910680107800d10250440080c040d0030015940e8107900c00c140c40c2644503002c0082055051042070b0034000c1c502a440e60090050001e44505c041644114001000000b0050b403809031071801034000403020300c0314084540b0340c03560b0144032000070640d006008101d22200c0e4500900b8031360713080c040d100045002403410a610f0400d144c0d0507409125510140341410500e44101c00130798401142142c61b8a0380396004001a01d040100c002e000e070195010319124500b0b0320004050100d4240c04d042c0003440c650040046120208900130510b40100c80030304400282c2002c0340f0501040b8031550007141c0c0005041000580c13540c404807078000200e51454050001911748401d0724054000d266101160301daa01d40701c00461001448150f01c00380c004200b1940860000710189c0080300c40c440480e8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 178494766 1250 178493516 178493519
    0x80405040e010f060b1c05060303040f080d08010803160b06060f04061116050a03030804021f0e0325060c06090602040b180d03080601030c021608030901080109140a020702010c140106 80
    0x4403a4013403880030306130403850a030411099412001c41030040e0602050b50542c0c8001280d071a84040c02290040e0500c0a0003100719603558140720703952646040340c5000104d2110000c6400d240100488007039100440610454503220380b00c0d502960f1016182c60783c401c00420030402c0140701c0030060001070880b07884d9408081e11980c22581040c1c3c19025804282c0340b402d0040c05141d90303010306481aa41c0600d006000c1d986d5610108201c1c02442a4900c0884170094007000700c1503200c101001440019001e8404400d00c01d900c4032400400e40705a41301c2d50010310b10501c512445034003120442405080017040303210080d01d5200403a40144c20101c209035001521540d842e2103200001155030b4155415042c10f00d079601c0041040401914590400da129044018078601c01c0180107141c840080c4d410703002c0d560351280c0700d5680d400701d0705050104042800000c1e402d0b1140c4107100e103c1210b080f84144aa80d20a0701d80700031f500c41c0d0000c80c144a4038449401c04940b14145400a44a4a000005119 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 178496016 1250 178494766 178494791
    0x1806080403120e0601090c050702030a0b1902070c09020309030f04030b0106090e06031507090e0c0a090b030c1603090806070822020315220b010f06031107030c080405040e01 76
    0x2d000d2107a6103060300f410980d80411082c1c0004c4d140f07046074041900000c032034004800c00c50301440f407568040d515100d100034480602c02500d606038010441c0541d440266000d144001c800c0e4011558080e004000b140000c2082d45121b400465025070395a00f62440c101c030702036484950f500150000c1d0380c158103800050003038136001840c80002c0d14004007101258540743c3d000a617200000070402020a9001c804a850300d07004042001c003038007501101258500e80b8001c001083d400950f12207000075600100054250106800c40780210303541c1c3c1015181880f40051480d00e03c1c002481201008140000010000c00501c1614000e007025640e030300d241d0400c81c0b401d51121840c81c20b401008085c005240c1c005903000107400d00341e4040d001c941000b0b07695103461100f070b030300c0d2241c592407a0f910b11014550401c0300482c455810707507592011060b6403927102c1c03804a0854000500340548100308111300b5000ca406820f101d40850300c14040c140c505a154000300e03045c0e503600300b01000242e4545511040a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 178497266 1250 178496016 178496027
    0x3030801080111041203140c07170c0a05030a03080627071d1e030a0507120b010806060a0902030907090c050903070e0601080613090b070519080402060a0e011806080403 74
    0x1140f12003000509003410b0a0149055081e0504000e00b848000209031156590000c01c6d25044a01d035401d0320050350fa124103500d92440e042c1c0703213024140240e5509038030502d009410901900c401400a00c2c84100310b0741c09440c841c3e0f0160002d940310703104180100c034844030301003415110000800c030070000782410000503208c030035881e068212484a408248007a5207a4034009203c044191100400d01154400841d0800942c080041c00c503000d41c13440071401141010700710801e184100c000c0686603aa90741419102c010580342e07140d00884440741004440303e187c020b507821a6055007036895840e51649010116010b03d001d00c000705101140b0300c05640b0301072024034000c1000e10001d90766490880c000908001b0010b165501c01c0c0e18a030084100102c090744640d54144d400000c0340740c0c5013401c00015003513030421400e0401c0110410b4020b641c640c0300340440350140398068500f82c03d20111101c2561703940104803041c4d041004001ca0340c0320b4000c51400440040c400354941d4500c600785410300406 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 178498516 1250 178497266 178497281
    0x151b0f12021c0f090b030a02040f1703070624170106060302131205030d0c03020702090105030d0e09070e060f0c0712050c0f180f0a0b15090d08070c030308010801 71
    0x2035400c05071400300c1c6015001d039001c0d0303410340a207080c0f6001c0151410658055006400001e8103800110800c0301c03901c0e81da4000e01c15034004000c5650040c0c0e444141d01c0e08142d400c030f070300806038000f4010b901c0020360581004055002404415841300101c1102c000403074032590180113100011008584852428424200a001e0a1500303601d80289114024200d40e0b0600c0307148103020300622090f09201c020f200703076103a00041781018402101e0404008001e50052101079224a42d00784c000140703860001840c1e80d0442c01d94507071040320700c1c5034010000151b000402e030038240102055100d996503140d10040c2814450386050580760040415034a1400b0596041040340300482c0c0440004240002900d0354100f000300c5110000012030341c089000341d00b03540c00442119160320140b148207a80c80019600c1444210810048542c00c1c2041101f42c001800588000e0f541c2004050484e040054256242c28058895540b4108055a54045004440d0320541c00030b400302e40103100404080c060342c003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 178499766 1250 178498516 178498553
    0x40506191209050a0b060d0506071d010c0209040f02120106060201050415060e16030209090c0912012d0902150a0f020304061e020708010f091b0f151b0f 67
    0x8501950f03581c00350398006103100940102c20700030001da50f5540e50f1910703c48070344c3d10009950060409071405080715602c00004026001c0c0600c203614554460f442115907150000d16042050f1943d44641103140c0e102c60060ba0403650008001d01482024040da400038002923000254601c3d0900708000c840c21146804906c841c01c020301089440c0c110240c450b0440028980e8031804c00d00807070160001c0c4141c801503500320718181d081200c20205d0700040c02c40070f44199a41070ba041812103203d0300b03c40030000c640f0b4541a408100b241420101ca03540314405d810044001003444541d0001000128071905d14904498001110103005500c0b081c0e05034503131607600081d07007003d00f882d4000d42412406010040084605a6058003c03442080000010001c02d0000c00044d80e900c114800980424030050321600241c0600303030130241d441d40d01e0740e00305d82480e00d5046006080c40003903110006904020020002c41d6071210202c4800b540049054911508990241054614010890001081c0d110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 178501016 1250 178499766 178499771
    0x10504020604030b0a02090a0e040210090807120c081009050f030906090108150a151805061909090f1a010f09150909020408030c01060b13090b060405061912 69
    0x440180c960406035416260b100c104c1d240c0076654029140000d0141740d415540c000300310710000605515118085000d580252802481c1c803095210944480d402c51088080301c0d07000b40e8040105500e00d03680049024030441c27680c2d40c0580e9a1018034680341e400803501c11004e984003c5001049020000727a60300b001d03540c02030740c04c10285000181d09409041d5009051091801c0043c0c100000101c0050319001c000b04503c1c0700300c0d25110700881091102c49043e010400d4955100c00c0d0038a5808034004880004000780c1c03608070403100d01d98614949070414000c0c072070780c1d11010034442154050342c0c4825540c1c1301c0000305102054400b408600510020340d0521030507128892a455004d128a01035610a2a891116402c8070f403080740c55425a030302000501d40b01050104264001100070002d40380030600901c441901d41e19294220b1140e01664540444035000800010403e5001150002c000030079072803c25581c0d60100c0e40c5c2ea449000f02c100c001480c4030180c00000e402c1201114504000c4004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 178502266 1250 178501016 178501021
    0x702030901030b0604080a060b01030506010c02131a0607110114040513090804051c1a060321090a090b031605030c0103050a1d07060906050a0807110c0402030c04030b06030105 77
    0x6926442140005410981c0310380316401107072100c1c0c04503801490444101c1e03030301d02040e0500390018008500030500190416001c10303420340c804e1146404841d002080c00000d03402001001c0d00428807221146424900c04e840109180d8418015290950003500110a40f4000900040c80195410f13250410345206010520179511048138003001030346078400c006128203407401c0103601744c0a160312061340500350180b1094850115a9200d444620980245400d060210300c07600d0060001c848ad90342561010342c03803c1101d8240d0a003400003d038040d06107440c012058002c40c42c00700050704145c0780c05032641400001d03800d04002e4030602e050140b80c80b040060520001035141c2c010354140904040d1124003091150340c6179800000741180720074942903034600031116151074910611548005c1090900c00082c2c10b0b010340b0403105080910764030980140d0380c82c401a59600758180788141c003442148088040c940355440114003c40c03c4c005a00d07119455481c0c1a4030801c80200664040e1341007106 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 178503516 1250 178502266 178502281
    0x14151b0406052b050a060905010b03011512140c030403020606010c0203120a090f0807031202010e0601090e0a1407050a060302070503090f1801150806040c0819110c0607020c0306 78
    0x382c845000d20f1060485481c0060302c4403003048448060221483c03443c01c800c2c40100c0e80d490380310300210740707600c07070240516a80c0309030007030460009200d2014040901d13104118603603c1044d200181c40300c90307032001418189405091920303450880300d514081d1070000c140300502d6010000c0035444403003440c0c10000c41c080c0368042600c07180321500b940036030302c00030616200c80ea002d4034201001d05022174a055511b5911030281e50303070740c000384400da40c24103840d103094203001d1041c000c04215004180c000e1084e0391074922040003d0410110030317002c40c000c036a01440080c4c400000408a0355514006040007410081085444a6140e0102d01414410014030b80080c0d0b011040c1e6140d100121480204624054003050740d2090356080c4450805c80381c4004079a03002c81e415241105062130f910700f40c507175441e0800e000c2250307c0b515030200031075444000140240648903a0901130019031202280f0750400e0f0a00b040351380c0006201c5507540d00706408115140e54108102540020708500500c06c40c10b00c0c91 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 178504766 1250 178503516 178503527
    0x110d03090e0c0909090a17031b0a0e100309020a0b16060203100513020d0b010305041a0405010f021b0d031509050604110408060f013014151b0406 64
    0x824040c1c40303003140d400a141c1c4107410058407503000000d00710020b00d1500e416900c2d1150060038040300c2100c42080c20b0030602ca81c0e1000c2d01d00c21500300e0080c0700c0c461641c111101054200c1d031003000400c208100008007644901d10f0340141d240890b10085540280b92040003429415a00011510401400a11240c902c9034001b071428582202c001a6603031940340840070030f8070040d000070b80c110841e41015010041580e0042c1002440e01e8030811071001140e00441c140e40099a01401408101d038610182000314800310342c1084c0320f00000103506d2150b600104c2030b40c00014503004005c040c0300740a200c001e01031140c0301e0244502d240800c8100380035102d000d0000c0d414056105a241d0350303800202292219803040088454001d00d16807100e50700d03440e00769215401c640404c0000f14003000025480447c82d9100c0c1d8107840e051800310401c41c8008014039030296450281c40300704d02100300c0940414140311083c06260040e81d4000c0c00d01e04004145407014281000c240900f17802c20041246a5101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 178506016 1250 178504766 178504769
    0xd0c080c0d0b0d0c060804060605030105010b040302011b21030f0902030303071407023c0303030c210708040b0903070b0705070614070305090d020309150c031204050604110d0309 78
    0x40000068004502c00442c08440850000416020616201198158002c04010310580c41007805009041d01c4005040c06ea800a01c2072150b000700c20300c0103100641c001c1070313025413441c4030a1000e60742d0380b80c5840d8001c101080e841c404225001a504505100c0d07814042c02170381c00102a02400b8180c02680829038030720000b089002005150b40c801c1010007121000c903072800f82c00400c014802e0100a90311411400c0d108107a0000401c103504507002000e0a8206e0502c0b060f0003006141199145812140107074028058482c9a140d00000c07400b600421078200e5010350b371696180440c92800b441c00207040c12000e4400340c050b9006101040001707400d50342d01580018640b6000f5100c20a51408a01130400080341c148140012130402001c0b43c0d042d4441c5104291440c1102e5a00302d0395181030b601c0c1c0c800c200d40260440304400c80407080f2404100107040c20340c540e404484c50a003200030309078058101a50b04541c9500003405110501c5080d100034003107884d00b284c1c001d04000283e6406000511117 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 178507266 1250 178506016 178506037
    0xa08030a0c02031c02030105090f060d1112010f020c01060e090606012318030d030e03190504050a12020a240c050c0a1202090f010510031509110d0c080c 67
    0x449844200d024070900035a00001400c1c1c44903040444c0d80e60342c1d000070b07401c2400703028001d641c0c800009041e4884c9900c0d043c00381741c0141044d404034619440340c1e0705404010242642082c654400e018600609104a0308054101000141c94912103a640ca0944169621000c0c4114411062046400000c21111b410800908001008070b196815649040c0f06142426880b002c010403003c0c1ea400200b40d1030305600340200c00f950030300c810030303007040e802c07107400c030010840310350043c0455900c5c0c0c021000e5081e01540c150510320b04007a41e440008413501140c5c2c00141001a40802910850401c03107040f0019200310715091200092907440260080e102e800c8040410029190718400c0c09400d111100442c0c0300078207400310494a0b10710100c046103010b80c040b40143e00704000100302c1c0c7d51004c0c01c0c9040c0c4800a02400119586200840291120b850458100041e01000048042041c0714040d00a1000c18441da00c031800c800340700003102d480c0181c00302800001c508103d020001c1c0b100b01d0300070142 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 178508516 1250 178507266 178507271
    0x320030307170702070b0c0105041713141c1a0112021318080c0a1b080705060c070906060906030f0e0d03020d090b07031e09080a110f01060f050109080a08030a 70
    0x75100f000300d141c0300b01540508509080058500b507900d4064001510450043c0b800d42d6850240740d0300b004443c403c0700203015640000050602610100110104c0d003480d00801142911300e6141022255421189081f5400d200c01d0f10302010480402410a00400b01c10911406d0174040e80c01161070440c00380310754800ea07581c030f0300c00d11011a502092001244d8028030303810784649056a032641e03500c16410b000e07a2444065800c4015002c0103004020a480300f817000b600341a45014140080398100410a07246401400400714003800184174500003810f1503a01c6070f0000740740c20b0000c0c044640345000b44040c0340c10444000d502520024401e03103540720f185801a42c40001030b070240020302c81c0500c000c0c091940c40c801d0017a80c6526801070f15404503a401301c070a1400d40d10340740034102c0300315060041401e88280030041002d0700445445001400900549440c9210402c6a5003100c40541140703141d1220500203111030350f8405010409804075100407e02841c86071101940741c00024a9410740030b4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 178509766 1250 178508516 178508521
    0xa061e1707021507080118053d2102040c02030708120106084614040311030c1903031410240909021b150f1e0703051b07032003030717 59
    0x191100001452690798441c407850351801180d149070601541c55403440101e15088000c209480ad00d400c140c590302814081a211003015424072002e08035201c40f940541c0028444e05011407005c030010b0980190580003c07200750304200d4040e100c040301030b01c500b03001c1e5040000c943c90460701d800ca008a41e805550540110a5034003503130880305905406e002c0e8102e00b0851203c10f0350680e004018041c6201e515544140c904905080d6a64018601305200c02d03400486c5001080d0210340700800b807240a442d01081c0103841d51180b00904000b0750f4007010403001020304124100102801d034265042c80e046c6c0492914a0340c9005054100e140202d4012035800148ca40d01d9400c074000d0551070f4683c020503a4800103503105840c0c50114110380b5200d003107228000080000804050091416814100c60445602c8015084000303150003040314400001c0c46019103509607d400181084600c250780b545025804c0d035101c4a0144110502040076030704c14401e202d00d0a4210a61065407000311071b0a110a5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 178511016 1250 178509766 178509781
    0xb030f22030e210f010b10030b030616030209041a03010c0e01091403100c0f020f0106030c060503090703080f071e02010923040216060b0a061e170702150708011805 72
    0x2a1400d00741801d2601c04c1c040110040c001c1900700d6000304008607502440383c00071140c00d4090b034200303642c095810b411000004100d82580d03d441d1807805c5492030014140f152500104044a0314100302c00d0031207010741607031015460240034000f0581d03c10b00c0c107510340e86041030000e00301003060b0003020008503002c5250801501c040080c0301030151450014854035134160f40143c410341d1040d5643d801809065022031401c04140903182c12a0b41c08000300c4901c074603091045805410280460b8518010380800101042080010b4961556001410340c1d48100c036103000c0e4500042c1c61800d05c0132490580030800985c3c0c1005105d800c0395020302a00d0a441c043e00c0101e0b5a200000e60714503402840460401d00340c2c0c4843ca01c022106100c0c6008004e00201030040080f000d10911855000a10244c10070a01486594400c140e0f41031900306101c84d0200d0740e5220b6080c0004851060050707100d0300510b45104140741c0150b8100441d800d01800b01e506110300b003859540c0c107100c1c04105c00d4540b000720750320 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 178512266 1250 178511016 178511059
    0x9020d051e061003030212030604020d110a26040b060d061a01090914010b0901111207050105010b0a05030a02030411090a09030806151806040b030f22030e 68
    0x111503000080d95003001e45600d0110081c0d26070300d060340340c6206540000344648500c054180c1a01d4160700240540d45810b607100540b81d10040100b90410703003c0c4207400c0e41003654000c084c18100b4152105031074042c0924014030344c00c00700c85400c4074046c00150500206811140980d0040d4204448003080d07a1404007041c4000b2400d5030040405240554400c00d8840580d05108a000c090381da040320242c2d01c1813600306540d2180040080005070b800104045111391004052840040c141042d00340690004c4504200050380d107800507810006a00c810480700303208032409081400e0009080c503070500300c004c202d4000240340244940e40000841c6c00e000392060f40e81d02c86000108000043d141810840001c1c20402500300d0100c1d200390042541854039011401c214016404244d017401044001c1c0703494000e503215000c0c3c10000400c804240d010200d0f00035881400346464130841030402e2007600440f1801c000d80203000d06e4940b85a0400a0fa210000403048041241c40881400b05440145107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 178513516 1250 178512266 178512289
    0x509091b040806010803071101081e0a23160503070503130807080412050d090b091905040510031e080702060702130e01060815091507110a06050610140307030902 71
    0x50b18840c0d100005030305600040240384d601d2081e20348403600d56044005640400c2d05403049a042144e01c204070001c00c2d0401c8100c3e501811446c00460300944036400810001141e100e14400032000ca03080145940590349450324480c1145869491441c0c041c82c0107009000250080c400c0b0714500c1e08403002e114241081d0750075140c0240409598555480100d0320203076810408407014000c620582840d1405001144102c6046441040c5032200202c1041b0810004001c1941c1c008900140030807551980d00ca90b0748103405c20110b6541c42415420550323590075001140c03026106190000800140061007520f43d007a034181d40c259103070301c175074030000d03031340c1101380c1a070700d0311a4a014205800b0a038150801e100702e42c405015250204120205400303440c0b0100d40442940d8030150703c0a560303110101040e0317444151854880ca61410080c00c442c14030140b0322003a5070558403542130103040e14020103840304e80c06050a06803208450448240c2c92400001d0951040c16950303140c42040d5102d1800758031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 178514766 1250 178513516 178513529
    0x30c070b1302090a09020a170109051213080c01050f07050c090406150501030605090f0417040b0d18050a110102190609060608030c061b070b04060501080c010509091b04 74
    0x8207203441a100022040e0049040c2d101d540c00c080071130b8615129214510086801805900ea41800c10901d104400ba40f080f40070099942d82c55428007282c02800f003841128201c0300c070301d0740e43c400004046131480103035003041816801400d501c0300b0a80c0c002c022034410f07105000500c0c0d114507484c01c256081202d0742c81c0e0785400070482810072080220aa00074003c1501c8100c1000c02c43c0d032190011000c94203d0f001d041e40100c01d03003011500c18484010b0031a03109110380304c2e0120200b45505400b12580065100402c400008142c481004195020300310980d581050b43c401d1502d0940c40d980d5071412481c07000342414040008043c00c90f4400e1007941ca2194502d49005020354031464440014884903c050f10f4492a02c1408900094003001b210190304841c8002c1c820758940c001002110b0040d00c1800480d03100420003540002c0c014a0685e20a138001c0c40f00154a40c94008540d00388040d54842c40c0c1004000c0103520215507814000a82010b288091445494407544940388540305681048 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 178516016 1250 178514766 178514783
    0x120905030a0207080d0c1106030919151a0d02150c01090c030c05090105010c060e1905060609060a0620030903031b0709090f0803042a050108090f060606030c07 70
    0x80d10041c2c0010307065045400300c2c0c0486200070070b00002110400c45010004000315861040c8110301c1c58804003450700310b810003055075003804c040c06140c07024600507901141e0b455110300d2070541400b04d07413050710307078440054165000c400c10b114000345ca25114008000c1c4680c8041031958213010900050f1032800711098005c208145043c10620002d0203940f0003200c070a41c1c66400802c6c1c609006541c0f5049600684800b50182c50725503030300d0301415140d08000c2640c4285645905001c000c1040b548900703010794003910260400c401400324a0034002c1140b801500e1440c010040d450340310440c6c11808101000f40c0d002d00ca40c0711156400d40c45070b01c82c03480e814800801c030319182e01500910403000f1449403044034541c0782e440b00301c0c2c0190340881d000640003202c0152040c0208005400440c0e002d8801c00405607090328a032040b0741d064880d0440010390042800f070038082541c21125194101300c0400081142008011081d981c1c0d03000205181d00400d404004902c1c101d03d201d040d100c01a41c0708418 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 178517266 1250 178516016 178516027
    0x506131e05280e0606100507020402030f0603010b01030b010f0e010c05030c15090705030c1309140303100b09030601030204150b0a02010c030b190302040203060d021c11190612090503 80
    0x480842c041d000c40329041d0300c000e000809074000c07450f2060003042c11000d00070b4150307070341c401c02003003480c030343c1c000e010010310004105140c01030380e8501c000c601c11352407080901d0443c240002414211041d401c603030350504d0b00c0c0c45201103141c0c0c1c200d11107a14010f0585031620514204000403100011250001050b500c400b09541450f600c020400084250368950101080e60b41c20740e01a90b6510f01d889800c0d0960803415000c401070030241841d1a032024000170101d4260341e0350b07989031046d84180882000c1600080103001c501c8001c003405030001c041511400e800c0480c0000000d03110728041c0710003407060342d880c0c0300d15082071001d0141000624609183c180c8401201c0000303400713800c65144040c00a0324006d4112540d103015440b5010103008440c106902c0c07070969003842b00131343c4041e1031a5400a1542e10500042e500c0b42e041912418240d4468400c0e0b400c41d2074180c4140480c1101c052285006403004142d6216008030340044501500c1c0910301204031041d03541c0208240b4001134a80e0100090 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 178518516 1250 178517266 178517281
    0x18060a2a0b0406020a020f0a03050406050d1407020a02130c0e0f030f0d050a0216120b190216021302041a18090906160809031c06051f030501090506131e05 68
    0x182c05d0985036a001c1e124110680c2c4544c544440c0d9201c4000d0104805210500c4005d00c580080e00d41c1d20911180010600c40e040004c0201d194101c8020b40184e00c184130b070400310704201c11041c01c4001d0040b000d0007007a03c0300e40080c01c80c800e8410203a006403008541512503a5081003212403204411094410640401000616691007140b0540251149403002c140d9820245d042c0301c101c0300340d454a10f04811059a03030b110818005031100e48070f0003090000003008000c030320003025050300d8081d00010709015441030010080301107503444c10003841800200111160080580340010444840698901440441841100c241001903030464440420001421000a441401042e0382c9012110703403106d014007100c0301441201d0140c0c40c0d4006100340702046250102d441803c50100324007140443e11080404c003c3e0300c010400401c2c0e261070303203025921030381c0601c41d5074003505410000740100d20741140810750285101945244540e40d030b410b070300008103e14200c4d0501c10348412052107541404607 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 178519766 1250 178518516 178518521
    0xe010f060605190816030203040f080343140409060e22020a0512070503010207111e09070e01050d09060c11011a0607050a060e010218060a2a0b0406 65
    0x143c034000980000c8408201c150040d141c0350300c9181000d80d90b030000e00081c90110040d400103030040322141c4c0d01c1c00c426400140c807080514480c04078021894000c030440200303622280d0000800351000540d81103030040c030000d1401d10b482c03110402c1c10b1040e1160020300c414065440365034041d50600b4984200458042a8800603a008900c0c000400024050000104801068140c0c0080d4440c032051810012400e0105036510614103002c180c0d05525070b0303180441d0a9a010041c00c07904950b21a0120b41709117041d90280d140d01818410301c02c1c04206110204cd0003e0300030b800b0500b44906696200003a0b8418004c0354214100e1000c00c0c02088600e2410070064158812964007141c600102aa8444414401c0722244007039405c409c602c03d0b0302c1c0c50500031664001d40007541da60140c400ea00001c00d600e80200c4080c8040035000507a82ca02c1c1d10350807045d5844000c580e0781304a904004540d5580d505c4000900c4880301101a40c00000741203083c0b5461490720480241905080c004020601403540d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 178521016 1250 178519766 178519777
    0x90f070b091002030a2106030501022808010308250204021201080714031b121902010e01050c061f05040c0903150908121012050a12080c0403060e010f060605 69
    0x340d5003110390340320b2000166181e000d004840c030002950b00d030102c0c55816880f82c10320003456000c440040c441c0c0d142d8480d2400da9100f403000d07000d481a00040462405589400d042c0d1103459440d0401e010350440e9200701d41441018100d05c000044030320803241d01460076000c020b040780c0c003c00840d035272088803a44200d284800d2041a1244c020904005000b0100b000b08941c1c6203001006030412054443c48020001c10095a2135003090108105030b412001c20420304884204600301c084840180e0b20006010307228200c60705040003000d0082c0c0c442d8800c0005c40f1500000d0b80c010082c560881c0522400300c0c2801540410390290600b440481d05a0704a40e5003000e80340a60042d0034902031184403242030364400302005000c10000c024100d01101d145854036004200d10060000580c0c1d02c020108415998103c2603c1a820801076501001541c064868030001142400203007490325000000043c082c502c80604215103c21025000304401c0d8071101c09440c494604000d01d0f500c03030754010015040b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 178522266 1250 178521016 178521019
    0xc010605100314240603090703020a081b0d0305070201030b150406030605040f0903020a080f0c0a0605010810050603071a12010f031203050105100c050102070c0e0702101401050603090f070b09 84
    0x8040100300b00d00b454420403202c600300c8a280032010300510003807205d19480107140c080c09020f407000100050b550301c03528500411005000b0105641c900c41d081f00c072105c115113141d01c202d240880c10800280c01c101902c0c080350302400c0002e6046240340c0032035002d620100303800381090800580032a2441e0150b1051342580da00751010021b421090745070302d08a41d4900b50140240c0d12003035104002400c0d0070020702c1d01450007000d0a00340381840107810718040307002c40210381d841d0b01e40c40107101c07900c41004500320000d0652024000b509101c40480c0e1544000e00540c03048101d03040030030007400100402c841c008030b04035070641d21546c0c0d03c10301c0304c00108550000700e65100c0003070482c8015074828000c01d4142c0c3c034000c00002000c0c902d09800d82d100608034004840c555000c4c811117010034244200600203181c002040030440c42d00c18402420040240d4490913420318001c0c01289602c044146213041d03d0003a50a19641e4882641051409203009400c007800d21807030344041014214240a1f00c1c01c00300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 178523516 1250 178522266 178522301
    0xe090a0515090603060a050702030c0a0606050f09061509011b0b01050f031209041d0604060906060b040f0506030604321e062803030305040507090b090c0c0106051003 73
    0x100200155120b06803407035941907001002107911504a03500642e00602c3d540101ca26000100120030f00301021741c0c00960b030310b940d40c90040103141485a000302401c1401c41d02d1101905c0c004000448942540041c81c0c12040049403d40b41640903d115130000141d07a440c4c00d0741c400503850040e414400034024640140d540940c0510681800590885800f00c4502c0d070904204002c000d10006044241c940c604001150b150504004410f10915010b51f004403804503040344981407403002c2e50b17070542c448180804d04200400030140d0074813600741030350811030320b00344c1d0b039110100050702415200a0750161181c03c4481e03e03041040d84400003c29024141d240c0c07441d0b0303a4150910840071501c28010304842908400500d803490140442c0f02c0d0a0500a520044107656142d84900300d80d058200f00c000ca6607460500061040801c1040300520b0782e12002d01c6461568004a00310f860b015005024066020440e9261a0f1003034103c40098500070301850030210030604002c0180903800e031000040103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 178524766 1250 178523516 178523551
    0x50406081c050f0315030a060207060e0601060203090a0b0d110c0601181b050c0106090c050a030b040b0315040f0501090809040b040c020319020705040606030e070b03070801090b010e090a05 83
    0x240a4003d48826543d103140460940d034a0340c803480100d8501071034065141c0a0f08210b040004e03c10f1000e84072290241000082484103034200030f2421806030410019580140800c04483c1d4400004006843c10400d0098981301424100d41c040c00f50340048008802010a01072200c03440065158100c8250040c0741c085174880011250444e00d00000d00c0c4038020f038184145c00507502441c010b016908001c0000504680d503050024121384814030301c0c000280c80018105400c5a00d405000360707101d000c54040101610407000a55240300100000b0021a5148005001c0c030200a08031301e101508540240141080d82c030b40002d40f68403c032201442140382480d0b245250602d80b19035160900c20360001c5282c2400c1800c6095442c5ca021f0300c55045106001010409440341d000e410018165920041b6000e010262541e040102d02d81010b500d1540910401c6852980468140d04580e85074a0000e00c185031000101d4450140f240004d411103401c100744845039400b0386c4842e114401c260301c2d03030b5040f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 178526016 1250 178524766 178524823
    0x10e040f03030506060c1005070e0102060f07181502060406111204030e0307050a1401091d041b03061406030f0a05060c0903070f0801050115050c1509010605040608 72
    0x15200502103403080455040080d000b548810341044000346000d0034414024000c5241c0402c00301020340c0390b51a40f00b0701422640241c0c10409161003400500b843d40f41030014107840400042c583c004010940b10300c0d0b10a0340ca42c0d48440054041144801c90b50074000c81c0180d541e49003502d04a0b05c0382d02c5c2c644580f4010f400d00042e1102000a0000a007098a8544080b51a00070303402c4001d5241c003030f00c80001070700d03a01c03a03491500401a040e2002d03544140c1e0000904074482c283c0c8152110071225030031740030103034683d40e6050784607038050020a2000c019000e000085249a080200810b18000400c0c880400220f1700c1480303050124112800402c0d2400d4003921007800c82401030030785e440341c004511020417041c05021900c60107400c9542840d030340d99164089aa50b0703403000103540d564400501000310044441030402a0b1828502e203044181540307265201c13604800826610324160200b00c41400a400150003030000070010701941352280300c1075480381c1c0d42081e240915240e21644a000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 178527266 1250 178526016 178526039
    0x6060a05060306040f020412030201140702150403050f070c0b19020c0a1701090c030b0f1501050912010f05180105010e011208030705090303030f01061d030601090209030102090607050d0801 83
    0x80d900058055401c607280c0605100142c02a15010b0240030f03000d20011544030400640302e407030107010358008181c8840d4045c075405102030103455030045411041c5195440485c48800c10340003036140c9081d65603a0b001e01f04c40200d034056940c2c001c14815035050000354200c4a403001d89200d0b900465020640e00d81504103130303514400314900355000201140201b001101c01c404243c006581100085000c09107540c42900c1c60100350012a0010b400398240681b4208810125070303c074008001403a2100c00c60000030302507010b0001c0c1148070b0b10900c180b424100b01d080d000307001d014100036010b22860500c41180e901d04074100c2012403040d860180009640a03804d01054100d580700440050058495240c54016901c01410a002e2000070000b00358503480410041d13108480703111401c1915414108001e190714400304105141c10700009540106507404250f250458009150040c0d0380c0310030b480402d000e4041c0020280d804403010800c0000d11201144481c211310305540c031401e5070b070303200c503000e010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 178528516 1250 178527266 178527269
    0x901030b01050103020a050906040e1f0b03060f010c060905210306060403061104030b13060c030b0315220b010f05032808160c030b070c15110405060307020f06060a 72
    0x8100114010020b550013540108281d4855141c21840d18a8036408542c890380700d81d02080300001c0c0842049440100301044024407032100c118105041d203841c44082c15400301a05043c89001c1c070313400041c02c1d6800b485074600c0c981d5008400303204007542400d05a844500303101140c8445038080720f00c801c160740d600003240d00c00c0d0320041c090b0b82040d00310707201d4000916060800d00c64902c002c001c044086024698200d02c0b0701c10560030407407140e84a20b004420b0f136441d0031007507060604241641c4a40d55011038003003208140d0f00910781c1f00d56149610481c100c0d162140440001c481640c0d40c3c07041c030414025280c117940d1446022440e00350f40d1014541e9407060a01000450714201c3c05152100340021070102c885070150742100e007007944000d40c52903101c1030312070f084600c040054800c0041003001c00b403c1c2d40c0704419040c86a440881916964002d109610314a00004d948032110900d010152040e10050131000d0303e05c58403032070142c001030340da01040a41c5240520845001610510301180200d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 178529766 1250 178528516 178528523
    0xc1e030201090317120c070201090f050607030e0609040f021317030d0911130207030201140114090604140915010b071a06010909020a0c0b060a140112092f090103 71
    0x20420710f5138941e0004800c8a108540005030100032030301d0401141c0c0c4085005c1c0c1c04500600740d40341d845100250401550f6805400c0c003196000040140359100029920a07030b42600b4407603003000071a03000844503c84c22000c1030b03105240245001d050f41c2150b01900000306001040c2c2502c82d1101503803403040300881440403a607072003013040524807202c5802c10758010341305143c440340c4103808000003041d10f013102c01b04000c4958041680300906609000d090b01c91941c3c04100d154550404500c00c003102144424540201034502c0030076844c0d00c0341d038819046e0b18030260210481c0d06040c440d880e19802d40c0050007001e4403c1030008103102000714100e581c0f856001114101c1d15a8144102c0d0103008000c04c4181803144424002581c030015000404480c1c481e5079031811242c107985005000f4100250481d809003809100601008040c1101741110440c2401c2c0340c1c0e1182c907030b215a14003509141100070b089440300d43c1032000300740d40c0302c0c0d07402d00240d0320040e580c981464860510541e640244000b6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 178531016 1250 178529766 178529777
    0x2070b01030305130515070303201b07031502030123031b0103140702011b0201050c04120f08190801050f0a0611030f03040c050a050a03050709270c1e030201 69
    0x400000f40100700a00c2d01e072560010f003011080e0b0f60400a6001200b0204643c60014005610010140d2511400920740b40110240202c0c843c100100c05150040514540c0103243c80600301c80041420802e1038011a44000c8180c204400d004520b00a90001c0c8549500861000703040713420020284600c0070019001f0380100720154140302c1c41400c4103900482c29050503968550000b50448181c0c040740310b62426000810740800b4588500c802e00c0780442014216450300b014002c1080d201000c4800321501040016028180d50400817003464007840e00410400002400c482d051481551511881e00c840c0c0310ba18450783e8400a00c000711501541c4581d03c20004039083c408903010b00c10b01212407000204036400d1404030024409a5401034900380c1d800108108c0c108214039100c8642c50140006860080c0b030240340d640d6455030741100340a011000780e20386c41503c0140c40c081c02c001500164101104621403802e04250f00d1aa026009503e200c1000300028560501c6040041003141da0681d50b9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 178532266 1250 178531016 178531019
    0x901020a1b082e05040c030b2509180e16060f170106050304021905031e0f0f0a060b0d021309020307050109050a3b090f0106060e0103090c1a071502070b01 68
    0x8000c000c1500030700c200c07140510a200071001c038a031006114810700b1200070110045c00084240c0c07040c901041741c03000402241020a110403402d011544146005020001c28003100c076402c01403d1090b0b0000e8480e20300e21a040010b001944240103068441160700c81c05082618580c0220400d00e04b4001c0e074011400c20000f00d801424001c1a121710f081d0f901e440b8624860722a40028140320f902501aa40c3d40e441302403500c200002880422403400b4258014070714445c041d068142c449807201c130043e083c80d94524181c80c45480380080700d01c406900a05a001c03500c00b000d0301e08010941501c09034001e214080c00440c03554042c0c000c070f030140d800041c5001800752401d6240708a484495940b000142c0c190030780209011180780e00c00c600d05c0354101d0f0040d4180740c41c002091074281042c0c0c0d0795005a0621400300300842c1c0014107110020030a10f070125010b45a81041c0d100010140e011000b2900004e1884c0310325a0303484040c003d070900c19040d100200001004c0c8909034015550302405501c0d0a100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 178533516 1250 178532266 178532353
    0x1401050702010918020c0606030604050c100201200a03050907260102071e1a041101030b0f0306090609010b0103090b07051e040605040905070c0f02060901020a1b08 72
    0x303001020310501d000c000141c1c88070000c90050044816003540030b0f8000c250360740e00c1032042c04030342d5125106030010070451030a52201c2d6541c0c0c0951000380e000340c041120040701c0c1c0740700f074103c8140b100d040e00200524026000c10b030b030301c0765000c00c0403000020320703200c0071807201c4001040100840d800c000d10f00c0c1c03a0201e000d25604011141111501d01c0e0340d820440080021107200030364440c0c050241c9084100102401c00116507441403c900d6803a08100d4104000203030345d40341d00100d060b070a12380050444000400304295203030f03040000c1e5151098008012140d40000344852003290200001d100305105040194155106480010030265a03403000800092140d0080d1034414203006c55040851140b0b40424016803140c0c010000056001400707000142590280c0c6420003441d1500303102004983c1c0b188810310b0100c54009208007400030744800d0503803003004000d140c03d8002c2ca66903130344d01c104038912607c024584103140b02c0303004220080c041c427460980300100f90302080880e60320351300348401e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 178534766 1250 178533516 178533527
    0x510020a03020c0105010305100c02030f04090903050d050916051503011509030f0c030209060105030108150417210a0c091202060f040602010504060f050c0409020c03160c0303030e06011401 83
    0x10000da0406509106942c007019090065500031402000a0100380c042203855800740e4160801c404250342c420000306421140b81000c0b9400c6510303003280000c3c00015407030102c50f00e10401d1250341946043c0401d0000c07104011440c002c00c128000d140e140d030340356a081801615a10104840c20b8698184010062000c9403402c2507041138292409100f819101d60350342c645030381c1180040d42d01030080f4000b4400c60522800841c0c006409080c01d506662401c81c80c00e59448201c0d44004410850b103010904000a01c200d1851941c41d03042c001d911800348107411480d610999500340182140c11000c2502096107228901000300203903141c04404e801c061400d80700c44901d40d0203d030402d10421546241e0302d01c05025002400741607001103614141800d21005440502c0706144003a40b4150034084050303680d03012201100c145104c00350f110444030003081e046004441991032111074142002c42040303840054071090f6407007500d0401c04060103205a0703585590901a400d9041540e0312035540540c086d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 178536016 1250 178534766 178534777
    0xa080322030f140c01021218040b1e090a050610080714040e0f070e091515030403030506130207030804020f210708011a1005031b04030503030a0c030504051002 70
    0xc200c1081a501d94501040e403222600542d600d00441ca40030011040074013100d00400824402400003005d0300c00c0a040c94030400b00491f041040d00c0360320349107035103070741d044001c941c400103000c01d00b85410030b00d003c0d030310110001840380718880309400149c0030409480341d240120f90180081e031407407140d0101981e128201030196810b216000e0b0400f1201d0000600510240111142074020390a14941e80b805800307016000034180491554080c44035218201c82c5503001c1c0e8200382001e800c103070f10000324103107142011804501880020403c403e0503003540007039002c2c1d00165161045441c0620140e0102d00440074010009000036011802514118140d0003844100030000312481c452a8140740d01600f038502445e2058100b02d504000418081c4600f40e43c00901c50340c88600141d000000500050b080310300c86007800070100203e03400c038003035200290000b081d04840655440d02c90a24555036001202c0c403034489410143d00142c010701c40d004403400741d54440020035000c141403402101a4110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 178537266 1250 178536016 178536067
    0x13061d0417070510090c030201080c031b03060f06070b040c0608040c1401120507020c0906030a03090509090106080a03020a171206010804021f050705010c0306150e1f1d0a0803 77
    0x15402d241c0c044c09864411140b440303100781420715407039180d88005441d0040080100400240501c100058048100d000303000b001c8000c206a40c1d81d030388400004500307812640c5840e810903c0030424000b00600c40c4412400360f80100d0b8241c0480c2d680302c1c0f00b203c03815421540100f034441030f0f030741c10405140104e000b4032038a00e050400144089035491081d048907811500d81c00180d00544203210f183c03d00315416a04001c00380c0240044020580703000d4031401032071140f5401208540000780380a4420f60044000d00500004c2e9003c1c201107040c000e44e140d108a01c1920071040500300c0364840c66182c2d0445451140920210103039a45010054400a8009000380d0b0002d500310b10102d0600300c1c0212401c030b41030f070584496440d0100f45c00c045007154147c00d80c82e41030518005c02407008454804034520512507514242c3c2c0d020040c0008a82c1c0c2e00d00d030004202404000640215403550410001c1c50018500a806072102d8900f40421004001c180b18201460f0010000118080940719841040790503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 178538516 1250 178537266 178537273
    0x7090b0f03151003060e030304060605010e011b0c08030316081e0a0b04060902040801020406020f010501050306040b0a0e10021908010b03130809030d0c0302070801061d1513061d04170705 82
    0x3131303a4840e036050344c1c88440c980b110380d0800010082080b1482c032901c0007410080c601100502503480010300606c1015481c00d6140e09812448000c0103c03400d10300c4003030726031301c070560b5181d00340010703070b00311034440d458110011940c0e010010314803640c0200c0c44030007001c2038040300e0902d44403a11000004d103210071003503801c203031035040208030b040d15800100001c240b03100006940e24034212000b0705040050303c0c0d4641d10f9041800400c4030395400201550080d4225040a0242c2c40c1c5401c20380040c134004124584030300446101003010402c59000e488044281ca120224400d080b0741304a42010090180c210620b4083c8007081c4441c00000040c030f03907240309040b068039041b42c4000203440c118031403500d00300048491610340c0c201941030103d08001c023082c1000740718641c01c10401c509058242509540c040740300b00000b900a10130745000f1800040301410320310403000551082d10203480940590840030019130480000b41420402c040d00c0740d504000406441070012503d28256805940e0a0f6050320 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 178539766 1250 178538516 178538519
    0x30a090e060d060603151a030d030b03030c071211031501090c020a0209010807031106030405060c07020402041d0601030c1404050f0a08030301090902030706210b01110a0507090b0f031510 82
    0x460750b01c21213001d1401050f010000c81850742101c415149113003015001d41e030b0040c200d00e009071000203007030740307103804904000c9003000d01e62010901c0c2d4002c40310211901e11520a0015581501a00c0c290101d402055101c52070580c500905940d01c140b030021483c1000500d004100085159000002d210101d105813640a200754001869054082c0c1002c40c07590800001082040348100c030918a28130160b62040c1145403c0e100c458072640700402c3c0c81980c8900244600443da11a4112405032182000d607840514441c040c014000c0e00854003d03000c01d24201f0074480880c040e0902c0108004080340c140e151078200000d105040104514441d00304420700804215841c043c00514084c158003c0300081085117401050f150480f0b0f580b04e078061008003154038803142051060610000c501810101d100801940101c80380a0615810700480c082c5400680400030f000c20302400300c64500c4024000400440c0401c0030500003003070000e40c594001070094040100100f0b0242d44203110040c4403c005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 178541016 1250 178539766 178539773
    0x40e0307030c050c190806091c050d0603080a03050601181413060803040e10050a050a0302060304110901060f02010f050732130810050c0313050f0d0e12030a090e060d 73
    0x1d05c4d000150321009448201c06101801e4108404c5a001c103110000380b40c0480c0b0030425200e40b00304c030b1000401f08140080d90202079162030b00002e00540d0f1100ca550340d1a5801c032801802041c05030764039070001d211500c00c8011880710004207000e48035450316049000e5288820030049210600c13800380039030384070700c000160150f040c0007610040c8480c006502c01c0f46007000400403ca143d54004504c2880b2048003070165494040d2500241d03903043d5511640c90700d860034006c070a5121401c88991001e51000045a4184e00c24060a0890f0042d0028810400d02c0034070941a0f400851b40240000c030380007280306042c500036042401041ea150240b120440301c11741081040e61011010500c48501c43c842005003590810440d22490a103020400071420841107100007484082c281101080d0068590028068140718240414003014111a0100c0c424180540044500c000f890300c607410000c15060301d61004000c8a1141905079203002d01a424031000b4024258054011608450920600c1001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 178542266 1250 178541016 178541029
    0xf060509010606021608060601080903090411040f0e04050a0f020d0b01080c5128050708070f0c080d021e010605030a0803040201020c060301031a06040e0307030c050c 73
    0x94080c4400841d586060a50281c40c18804e042050264220b8610801c6440742c003203074840d0465000d10348000c6684070000b68500d103010301a445a8800d1512060244290b504c00041049540450784050820b40d0382104c28408038044030082c01c50f03000b1101c0c102c00540b0b0340003c1c134a40c1e8401410740645d081c01e80c03240050080240c2112401da4040c0900807542d190811805d4800704000409400d4a90303001884140c50f00c00302103040e01c603046e240b240201c0031003035407080280380c89004500e52101d00051611036500c0704505a803c0a403087c1c018500b0051240044400084e08a400750307142c4031701c1d5960160041040d000a5030503100050000c18249002d0240c451140080c0c0e00400d006c15401c50521324a05070240000d03c0b580c0341c1903040021b510003250307107000b46c2d4000d1f10076900c96882d130006078100070b04a1070040d444174002001004102d042402e49010614008144069945000c07d2104030b417800304490751130768800e10825000070320910010b00894411001d403a542249680030414 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 178543516 1250 178542266 178542271
    0xf0305121e0a050402010219020303041509140d03020a11130603030315080105160302030a1401120c0b04030b0109020a0e0411121303081f1a0c010506150409090f0605 73
    0x303030079611001030300031298180c90594015401c00d03420095400d095002075960814010507400c0c1c601e1704580442599014026200202441075a82e4159051204010416942c0f4043d030300301000e02e00202151414440d030b030300e0b0f84a64150014014074619441e100024000718181507400700281e01c20030600070103802980015032081d02c000c42d001c4c0700204000860840d07134100301040ea14000801c514440c0fa0114115118580e0a0040c1e40c0d45500c070f284030107040c29040f0201022192000018510800c000040c40700d400384907000c03600b80d01c41003c02090f01c11444050b21400b0074900511410b9590350003404c038048107080c40c285040004d404201910b41c15001107040c2d04022503112510144c12009692015550b9214049158030b90790290080502070000042d640880700364040c01c514860b00500608040d848141e201000d03042001c02540c0910404042542018013003082400c00008003558200c00c007203583c1c20130b4200040701e0020b010400090ba47c416a8080c1103022426034801c00b030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 178544766 1250 178543516 178543531
    0x50c0f0d1b031406030c09220b010f1a030f040305090d0c180c05041206150e04080d11090d060f1107050303010801051609030b060d050d08011401050a0c0f030512 71
    0x540111103c00f201882000103000b14001d8200884102d903d80d0383e00f0380d1070340c052425251040148052101540c40010408d0700a280c5007403000040349032206030b6040e40854044421054580d0000905580b207800140c2d80581c91258100100d0b0000340030b40080c01510ba4060604419001c060312141c148442950103408219010458940400302c0c6014840802070380d41041490f0500e0404515100e00411001034251556141015030302200f0303111a000828007a0518407003411f15003843c41c519848038004c1e031282c038030341139404524110180039a40b041c100104415200303206600c40d44082c0440000002400b80d4410454a802c0300c0d4501034000c1c94001c4004540320360400214a08454014200f1500150710b6400d1902d480da0006594042d030b6848800720a0645a440c0400e60380050094000d1050240c030390440c1242c0d40c880c0404c0d040b5009009101e03450b070f008030010360f0310b44603404401c4009030505107441c0114180a01100e059403191400925245594045141c02c007410303100c15 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 178546016 1250 178544766 178544771
    0x3110d1e020102010e030a050301120212070806070e0a05100305070e0616050d08012301140c030a1d01050f2206050a020c040225030c05010f1e050c0f0d1b03 69
    0x303030555a091141305aa021514021840c0040303900c03020f0811b001c1441100510783d10300700d5040c110340f87d80342c0401c80800c0481c01c982c00991030302c032a541c03605801c039042c07000201150000c50081c41c000c0180f00403500d010301217040300711020000700d0160100030441d07000d001801c1c07003189031a11010300802000b55000314281c4803038604d103007085c14100411030110402c91084018007582c82040c3d81450030324410014400c103c1600c0d070050316003468400031007031040c2020540d800d080c0000703c020411002641e5500d208090b814441c869901800d00415000600510041c204144004010180e1940340e100400400d030403c82d071501c01c0301050b04854002203000c10080081c5404000c00350360114203c8055040141106030801c44051003105c020203141c14100d86c10915000d0070780c4c03455440d0020000c0c8078086000d21000702031300541e100b403401508402c01891000c0e1642c8141806996115001c6e883c6c1004608a40c01580100d6a0680c00304e56807002c07000c445c00701c00d1a1284001064401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 178547266 1250 178546016 178546073
    0x412081005120a051002120c1c0614120111090112090c090606090b0901021203130f0501020307110a2001050d05040317070e0108040308130605010b19050703020703110d 74
    0x45420303e0401d6084c800014018044485e1f2421880d07021540408030800c07403901d498a5200c5204a503c02c080070540680c41c1c04404604070842c21221410034900340d841d04200d0a0044055003241e00102c5043d10a440901006000e90f11906503040111282c1202240109842d01d441200901550040302000d9641e0403c01001d90401c11800003801641996814905c201001075142c0013000c121408580c00000012041510202041c5159812411b8146404010328005000f5401610b0388000300300d02901e101400040081c1c40b4401c0c591050506110050909200d850884030000b00c0d814400248400c80c401851072203110b11640c000c0e610000300c1c00e81c2c038a07011004034015001104002820a0810ba26600003041d01e8020b81d151800c02e06030b6070b4001d1000d030f1514912000424840c202800042c0b0b83c81210050051100402c118844945200c10180ea1718442c0031070042c0540c02c41a410004a0207003440c81d0880d1038060300c10804d414946e6605104607055007005400c21200300038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 178548516 1250 178547266 178547273
    0x215150f1c05160f1a0c011a04060f0506040905071b0b011a0712080a06080d0908060f06031509010f020a0201050702070b031515070b0f011802030412081005120a 71
    0x25030b01100083c011580d880c240590b54003000200d026009039041c09007002403e49440c40c00b00c8509090607402080400001c014002c1c1c00341d880c411071440b80c0e007884004900d0709500b8500e03004540008014038503040c07a0036551006844010100020310401d4140d118051130028400f550ac1c3d03102d8150f41d0300542c140510751043c5c151130300c1c84203851311090242900150380140e11510001003410101d005698001c440b5026282c00d404c816028010b5454400c00c16402003a2141031310180070a440955650106101c541c120440d02c8039070503809001030301000345601e40001d4000100b43c0021032030001c52505801642d004c8450900140e5580e0104900300e0740c10300048010700050b0703d0491450800b244c1c00800f0107241c4148038800c1d41900c0c000300c1542c01000c02c4440255001c2e506119500d081020980310b18000d1060510244516034501c1c0d00e100b07284212480740350302c2111103002152421080f41c040b540141143d100c190304281c0401e1a0396001c0c13050814054110040030382920345e00c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 178549766 1250 178548516 178548523
    0x50a050a081e03060d0206070f02130914010905030702091e010b09040c031406100504090608070e07053a06090501090c0203040f0b09010216060309060c0215150f1c05 73
    0x20201d150682e401d0041c02199500c41960800340c03601280c0c2c440e12061a810558204000c8140c021351181000310180e1105081d50400c1d070040740158901308105084c021013900303842c50b40c01d009142da00100240300061401841039608134965840b0003000a000c429420750860b0f0a800000c0c20405c0450007050320318150207140840c554615060105070503a060030802c0031000741100744101041208000f485110f4020703140103062680f0148241540c944145d44c40b05800c0c060300600c016900005594a03015400312107205925442c0c8070307070b041e0f03070f2030000101d206810720255007074030300d050304203000071020b020b9031010300a05d0000041c03551500c01074604548101240d50255002404200520744042c0300150071180f0480c0e0440d581e032a0180101d040814201c84811f125404550128025030716902c0401801d101d840100407280340e0700c8007aa034a8a05080444224a00c0400200440442644030581000192101012211342d07000101e900301c20b1a4080d560b0b0b8440d0f41140c0a00c2401c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 178551016 1250 178549766 178549807
    0xb04050901050d02012a0206070b0601030c0203070b0106030b0109090e0708010c030902030309130b0a03060504030801090635030a0309110a03050d0c0c03060507020c03012403030c050a050a08 84
    0x8441c410550103e503800a0b100540d021140384c80c0a1102614882e880d50041d000c1b00420b5008204950300c660525088440f148141e80c0c840c0080d02e400d0744590024000000ca85e0032942003a8483c02c2c1b40e19020041380070b055000041410020304541c00070b940c0405008800d8510740e120040c144560801e0407a03404c4a40c01d40f40c0008241c144620310001da20b000c000c0f942d10300d00c25038a03214030022034401d040291046005640d001720280b03100105000306a4030490265110382d454020030390b0303902e00300c5d82580c02500402e003100c851018207018402d00307508000100540f031040c100b03001c014400f8417410344d08400c2003000420344410402d81005070b0f085125510310b40464209004c1c9042d510390598812401c042c0c44140004006440c050000e68440c0720300542d48100c0c1400107162500000751210030b83e04090b0700940c02c20041500b60490b4043c1000c070100e81c002200001d501c1e6440032074801d40307560019a8075020f59500100412410700c6541f00c035600400b21a0f030f441c0000f001908150310750 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 178552266 1250 178551016 178551019
    0xa0b0f06030a0e010b010504050a031103070b03090304060207050402030c0301050405040201090b03070f08090f0304121704180e0c0f01050d110d0903120b010c03030203040212010614010207050d15091a010b0405090105 95
    0x30441802760703551b5040100280ea4025030082154041040822302d030460301d4002c000042070100c100010380b0000401801610403523400d442800ea52802440b00f41e00040d11703181c0da9102c041c0700500060030103030700040d41700c0d0052510f9010b2a56a218a03000c6900c1030702c0b100d000640244540c01c1840c0c000d200d20307801515010007485d110206c082e0050b100c0c012405400c0c0c81086540b2a5810f00c05000740d04030b01002e01040030b41c1c1d51643c0ea10750105d9a1403030749024001c1410858000c1c4940d8001c40e80024482014107040280d03c00351004507001e50280003449211947ca994110031410480c3c050144894800170008170680e85083c00390000e04421984000700d402c1001280c066640014003d56aa07494107000d030b06c94a5a200090710103500300b956040540c64500c0015007844640e0700304044040070303001da895141d00c400511003070309840d401c00b4088802940c0c0e6092a549503a110100c211302035552090300f11188903110715902800c3c1c0c007100502c58042002e022a107045640310380140750 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 178553516 1250 178552266 178552277
    0x90807050109030507090e16150f08041109061507061505151603030b030303070309061503020f090a0e0604030c1205190c0503090d0f1a0405060a0b0f06030a0e010b01 73
    0x1a56440d507617200118040c22244d2a1039031004110294100300c03a0160a06150b1380303291442c0c9420f006904118041350210001d44da8952000d002401507503168003a50300069500d010307581e400203000030580c0152416402001c7d00802c85070200c080ba01422005105030004512801122648048007000e13800140c40b5040a6034580300c006040c0040350100c4141709024a003490242c10113500a240d01040240c141c000003081200c1c00303034154403800d8030b2031158500b0410013868841c003014020060100a4021015047d200103e1400341c001d164001503003400494017240744407010b03081c080c1c103480490203d030813800e4040400a5031011001c8050161903c00c1c1401000805212890f40c00845a4103000c03d00306404140302051003114049507014250000c0c078611490302d003e00d07001d540015030301c8030400345100803a0308204d82d0860069421000510301900c0e4100b001000b000c1d58040603070702030314404c031002050b11000c020b180700c1e40000f0b50005800a0550350142561200d41c220b504124 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 178554766 1250 178553516 178553519
    0x10060f0816050f04080f0715050d0f020c0109050307060b010507170c1501080c010e0604080309060d0207020d081b0106030308010911120a0b12010506010e1002011803090807050109 79
    0x240e105a1140c0c0c00200c45580400e1401092030544280c4500b0311680c1c92910000380c04529904001280000407940c00d0845140540c1c82c814104038000360300307900001500c00c11644803204041d400820000d00401401890040c80401c16403c4a1140ca42141c40740c002240000034030400f84a20550180282040303440c0c8011780d0b844410908862a50501c00f000c007140400d10110100024600b034084d80d0406030032541c51b05a0280c1e20001c80280c44d000410b1480c50f032805091600c01d840498122100442c181030390030081108039007100c40c0311110a9030078040f4102607540e00c12450301460040c10445e9442401405036410800160a120001c0c0e0404104200203540b0603d410704507201d4210000c1c0100e001c94a82d98280b041c180c21501e0b03020010107020400540398400c41c5c010340f048501c51101c0072a030009500341c410441306207011800d01e2586169500384100045141521480005003101c0c2200f0310421100444030140c00060081009100402c000c01080e800341100b400c10b01c0706203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 178556016 1250 178554766 178554797
    0x403080307260106110c01050438120a2d051008070b0a020708060c0403110f0d0308010801110c100b0109051305040c210f0809040e061006 61
    0x14403018206008000110700b503100c0c002c07050981d808520808114818403035a41d414000d0800003407080800c841d01039810408031a42c01401128200c801e40c8040341100e11054504a4000150b944e030040310070440d005814410003010001d00c5480a10b0b0001156800c045a200088401a050300c1c00840038040503c000200500040028440100e40208090384c849007201d82d2948a94401e071210310980ca0085160b003013480c0608072403012030342141c1180e5035410046030342d10000d440d800c00004040005101056500320391204208000d0952061132120310007040c41454000c10603400035004000500c5511000e00442d00d64005404001d4140003081e010b03261100742c4a0900c0c0041507541900b0440341e40648089030050600070310a070110620300311030b54007501d4212001c907945000c0d900c003c0740703212010043e045400101020404995001d03038640d0030485805209a650700c0081c03024003183da665010b0000040d8054001e0f00d07a604084142d4550441203404c14800e2082110483c400c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 178557266 1250 178556016 178556033
    0x70f02060a0906020d0c0201021206010507200301021201081c03020307021e010b04020a0804030305160503041b08070b070302190305190507021005040501020f0c06030a02091c0506040b0109020403 86
    0xca0007940c400189081207141400080c403130136103200351150030200c503c2d40b015019400340429100c0041500300958a040044401d84125200100f100d100c00c11401140c424a42c212840d024025000600d424072000d1001407034102603000d50003651007003120622402c2001d411041a507641e003000e41c1541041c0e003019490343c2c1400440d501426020921644e142e809400400305042c0182c42150b031a03402807402045620100d130141d0200f1f040c480450b8581c40ca00520b0490350005903542410740d25030b40d540410002450f8490320560780c00c9500861080070034030216000b045a6210f07243c2d180c0c110f1a01900300340b09502c110061a107440c82d1840443c1d004002c072400c0103600491203154800c1103605a8060180f07807000b80d0000e13440005140b00b00c2d007103802042914026021500100242d0f0b000603070396a5645c0e00181c00903014804503103660011b40282c0103010005101c0d6140801c40c90020840215a08040d50759500050070f100501c956962000d024242c2c0c4182940741034219140c0128 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 178558516 1250 178557266 178557271
    0x311100e0105070812041a0907050a1809051203010810180221120405090c031510021504050102040e06090103050c013005070e01030e1b03120307080f070f0206 70
    0x6102e4005000002c214440c0215072140d40c11902030b0707550342440d00704000d104185050301d800c0c44c01c5200200704142800644c100840d40010250b80485050241e0045200c00c2502003084440d00ca556a4002880c103002c0205243c111102103626076140c0b0b0151031424050700e1704444500d1405469103030303810050304080d00c0e07a5016601c604914103011303d81c40c400c4103098507145043c0280e008404c01141c8810050080b82c0040303c0d107591549035500615903a10056a1600d00740d003031904050600d041040034018021864016079032007520800070400700c000c0440c0c003152640d41c0002d080c0400b10070b1191803030300702e01d080c2c44590342c540c11039944076914560100540d05000780c06800c50700b0184841030b101c00f401401c0d802520318030020f582100141609468070404100c2402c211011035210344210616118018000e04610024441c880110822205c2d101d4042c0a2580d05040b908941030056025004503952200e1500d0f141040700118040546820100305000d0801792800744d0026441d0b4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 178559766 1250 178558516 178558519
    0x50c0301052d04030c14030a030605040501080606040f0e19060c02060103020d0308190903050711040b0a03081309050702030c120a0807300c03060b0702031c0201240311100e 76
    0xb42039071102d090039a4a5801c03420010046400700101c6451380b00c010000e41030646458030140143c545a00403c41520390234007402d01194040c1e8000303400c518103504442ca0045400b100011001005089181800840700c00404241e1820010004002d041c4c0b251104c0521140b020340b0980d4115400144e1090340100081e0402021101203070300743c1d00341d1191024500c00e004d01044079101d2403602900e5900540c3d4162003260362140ba41540d4140781c000e00e05c003c07800070014070341c950942d41c0c0d204254000e032130071200d81001c81038003080c1c00b01544641342c001d00d1150010354031100c1580500e840e00c0f10808416540c0340051019418241c0c112100c0c40e0062030b030b800c1100032003c1c840f02c07501c0c20520851a80380d050700c80c44042440075205620880c1a0902550240700083d11505d4510a51003030004c02505544440b40d4a000c039480c200a11850314403903c0003054515000800e2429070540310740d441c0d1200d00c030000800810455444040042e00b00b500e10302c4580b900c0202c0900500021822113 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 178561016 1250 178559766 178559851
    0x14240a08030318070f26010516110c06040e09060c041d04030e0a03060608070806010312050703180305010c030c030b1e0f0306100807050a180c110a050c030105 70
    0x64034960001d010840103001d10040350800155104601c4505002200b9280f82c0306c42d44038441d5081c020180641880303a140c400070b50030300c0e05010720308071a40c1000c040c00c031030a4083c00031640300a9481200400080808009015060624225050901001504490320010100010019501c6070102c841c080380c040b4210441c03550b618142030b102d41c1600308086a00082e13000700070082000650001e010358543c5002c644503191504441603403401700780000340035a003e21030500714a034070920081c403a0714400d00d0700480001150162403082c1440360400c8403165101c0d40907a05a0380d00d0b118081d14000c4034a41808140c1202c0c0c0407410481e000d1142e5404843e48141040c07003521144058100b030040501120a40d01d01006401e400341070b140240c0782680200c12000502d40703040400e0500352000802c0c08100d604540700391030010240102c07400c1c148664650a40c02d001410300c55072103454007035000b40c81c9140a0b41d00701400c55400030190480000000a0b00d0682840d4940c260040c0ca00d05681 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 178562266 1250 178561016 178561051
    0x8010921120209180708070216050120010e030706090b06060715050612030c0709060e0106140d0b12010b0931050322031b03030503150414240a080303 66
    0x1043c1420b00c813070a0300075884101400d02c641540d0221380b03684604030070b50a40d140c40520b04220b0684400a2040303d0006a0045490b91903064500009081c0481c03031000080001408024908541000100342c0b1815074501f522814000c00511041c0e02c540700b00d032518131b8000ca07070380c4840a031000740605500450b80c0710001840d60f1129000c0803024a0744104817611000c60100c8183c0d40c91043c0142d42c0003500b17040001480d5038807007160358103950280e150307401d4964089a007a600358110051243c0700f551a42c1700c038001a160366001d652070305181400400c1411050040c800d1842019154040007030300f0f0300c0171024440c1d241ca0168020740c030402c400405255241405461401035079144203005042a01560144007400c0e503400032284100943c0d403070b4030090400040040c1c42884081c0101e04100001400005030840700740c00d43e00b009000041444515025130a050021102040003044c0c1030340d0721001c080784003804494450701302c500503c4141041075150716800003804400303e42400640 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 178563516 1250 178562266 178562269
    0x13080f030d110415320903100c1403091609090b18070506070204060504020d050414030307020c010804030507050a1103010f02070503090603040f1509060f0209030d080601031508010921120209 84
    0x30441e00300b00e10007620390b010081703220b590b0b9155011070103a1b0312911a02000408646040c0210110032400b6150b18400c0d450402c09402c20741e0000300402254000c0e42c0b4052204242811610040e001c06580000c4482c03d920708995180070241007984c1d0b403145001110311001c0b0002d04d00c400e0b01c506845007070b141c24203072020030080c190540103203a0180c00810303446d050b0b030000c0e0300651045c1e004080d0030755498003810140f41c9074813040c1c440b400144c01c5444081c0095008048841d0418424600355141c845c440d01d0f21800d1520520040351b9850100d0007000a6103000d00880e1100c002d052401c6240c45095511280d0342c0c8140704010340240c03004000642401186074805031f03c0c5801c1040c214020f4156503071100201840c4408991b02803405c061700c5003c4040784240e0301012000380c001c00c1c200801030070070365007180b00410705070403d503c580110440e003e041c6031400050903800008502e03a1100d140160230301d04440a145000802c0070940c25805030300020004603030920000040e83d5450140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 178564766 1250 178563516 178563557
    0x60f040512010b0f0604061205071403100807050a0501050717070c08010608010609020c030912010b06070b09120703021207020a030b01080a0c050307180213080f030d110415 76
    0x600c010303070000140390180090076064000950821040350042d003240010010440f5038000d174003903040080d0850010070300b20070385944081d07000b404504085160701490441c2e04400c0d401200e1140c0151111101008018010040c070005400101c60240741c80e410180001d005005060001d006001d0341c00c080d0305486c500000700e69009801515285500e43c40e070800d68007034591441179003455881c0c0000003c01c50100c0c801d44a54240210140d031800d48028100564000401e040c45620356803881c0b01c062598840c402400082d210740d0044c03000b403030070525550601c100d2070341c04d4044000800c40c04c0c00082d0b004c10004080c0f90410300d500d4644040f130000c182800300c2c5030401400e00007a2400400d90000001301080280e01c202002030004d521907050548406a501c202c1c44404030304007242d0101c0d90190003402c85400b40032400d401082c6d64880c540c0c502181140c50707540d5500700040805c200080c500510f00b01314443c03480d6500e070518040d8564861500f000b83e11041041c401032141c0d6000160 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 178566016 1250 178564766 178564769
    0x604090803011d07080402010c062316030f09031b0c05030601031109060109050306060f040f050a050405161d071e020705030c030a08040b03090304120503181905060f04 74
    0x101196140d40e11441803a00480352600040c2000c0d880f44001114240300d82c0b6114805c560607034440b00300d203150f60351706406071907802000b402211010207008407010010081c1845142d240d403030a81c14914482011b0125030304450107800c524144142000400d402a000001c1802054011a440e52403800e00b881e09040d40e4209540c5400386400000030f100a40301d4888202c10202c5103000d050703d884005440c8102e0394840c2d16010b421010029800f4603020765500c001d03c10241002c04d9503034071841c0c600d049820031120800210350316070920050013800c004c141c2030b800c01c4c24054405c1c1d41c2003954000c0000042d00c114107515585c1000124810310805001c1084401201034041885094001039210310160040600074030640d2800a443d160008400380720303a4000348424070b49818801e9000c0c040d8001080b80303c1c1c6100410000480308449690700102d80d0041c80a5038660440117003800415600303104540c403580100c44022824455160030104440301111520350300d172540603034280d0b0f07805136 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 178567266 1250 178566016 178566023
    0xc1509270a06050d0b01091d01140a05071b020d290414070e01050618060d0222051011190305090307060305190f1512110402030c0f03060409 62
    0x2405403030050051003201540a54000903040c0070b59912481400900704803e4000392411009000400419401d58006040952005100c2c1564603400319000d007590703050718411181820490400203981418414070740c0081041c90140c21080910003181d02c00e600c0b884021780706e40b42c007642a10402407206111101d00347c160b030340005104007803940c503804407000300d07070a50b0200c140ca2583c0a00c3e14003c00d80e081030301e4800403a07441603424041440750381d4100348800c40490192590003122540c07204040c1401008000c405a1354829101224a0b11031904040584164031184280803030307030b81e4490005d2a8100381c90b0000c0144045020345180108c3c1080000c01c4008008151091552080040444000a41c101c66407207980ea98218200c800456080e80101d060b0094443c034810300350050244101d19802c041400c1d0310529090300d240c0d10a0307001c807030000d41c1c0402d02010003011040c010303034a00044070b045041d403800100e040080d10070203e601e85050f000100050b081d40e0741d58846d8011a81 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 178568516 1250 178567266 178567309
    0x8070c060908030f0601050a0c11060f04170705010306050618130e010603031805091614030f01090c03090b13060e1e190201021f0e0109031d030c1509 66
    0x1d01d08210700300d5407043d0380c00034080940c2c2c0001411540107404862001c0d10390313601c1218524254542100308040100000e41c4901d080000031a1480f0420250020b0546400d0b0000e24164881c0c24509d0038100b940442d040c1800d00c201003102d540e90070196203a80ca02c000c00040c17400601d900281480503104d005030348241c0780124104490340c05500c00c2060ba4070944a000708946880c40101403030410b4864235500058100c0000e41c10130f122002d15010000c181400b61010708150006034850300201c61407640764102e5070041000480d180943d085100b401d0030304002c07401c450f884900341418020050491030306070a400c281000801c1c0c4c000c100e07007a648001d8075456900c1220039080c1c450125001d01841c07140d10030f04110030901071181d00c9103550507001498882e00c2620030504015074030303600c0e200b143d9565820030404d0b0400c1c003400c000d6500c00d5903400031000d03081c0c0d20701035080a00180d56010790300030342e100e40071074a6201101401201d0840116120110600058034601c00789010a50340d12 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 178569766 1250 178568516 178568531
    0xe0102071209060e01030203130f0515040b0415050f06060f09091509011a090d23070905091621080a050c01060b0703050703031505030304060c060c090f0608070c06 72
    0x2940006807030b0588281e83d40c1c155140803c07400440c16400140c80356403026100015032000600c1d00b4030783c0d96013288100280c40902a11035a02556680111000c0d1443c0160341c04020400c01c41298502400340c4c1400c0400c41410840d40d400c4159100408a034001e200015114101e1200c4100b5502c030008001c0407061a8980010054401e600b800c1d803407406080c01d5800803420b00c9a440d5250481010b400c141801c060204c070412084590b0301800b0b0754050703045078180c0b81890b0499003800254078068002c00c1072501d4400440101e40c4e0003817000c5016005844d0303600d10740e90364070046022222807030350000840035070445140342e02824000c020302e26134000070717140180c6412101030026410240000c000041d51011b1203040380c4184d03032000340051010030101c0c00007401f80d40b1000030341010a03100d0030040c1d203981c042890342c0c1c010380141e00032a8203036a5a204000c1d03507000742410001e40c0d00c5e01406003440c01c00d400011031460700410050181c5840060822803080b60031032401030b0080c0c0c0c14080c11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 178571016 1250 178569766 178569803
    0xf0a0602010b0a0504021e07030309080d0504021216050d051014010f150509090a060e1302040608010605060702010c03050f03070c03080702070b04050d0204020c0604030e100804080301090e010207 86
    0x9100064089003d6040210005510300c0c19100751034401c41401c2c0d00010030100c0032100d440c140d1100d6001c40905036100045c00c08142494040c1c213640310355840010f81070800c4d0042121903e1190600b9a4075481041c1e5000c031900340d404400d085400c1a291003d0b00c060b82e01c0c1c95400c100d0f4082c0020251407500359584103403100200f109040fa040d041803082c40315160852500d0030f00020a0490220b9010040e0755800e04040c40d11381d50150b40c5000018449841d070410360002c010580381081e150640c04080005d525091160200401c1001c008010701440d04000c10024080e401707001e07060000c0c2481da01d0501d409181100d21f4030300d41c040c0550703892a0001c400742201d52801e02c01c2e4001104040061030181c000611181901c60322034100307007840c1c07512080025a060088040b60059002e2021000500080140d01d015078469150448044001c40501c80e0502c0d1038002c90341000b005806200c0070031030590071130781929081c184c003280b0400d0b0030200c58064421143c0c02030111082c0494480d0740c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 178572266 1250 178571016 178571021
    0xc06050a030222180204060f0c03261b090a03110303040312120c1809110f04030c1d160f0c08120901050109061d07020705090103050106090f09080a0e0f0a060201 71
    0xd032941d051550a6581411398640128062800381c1d1000c0380601020490f003500441008116034401d240591718044040001119a010f40380f14140340c508010078001440000010105403640200c1d04500340011200010a4460a0f1001400c0d48100c03d2043c181c43e1818030441c0c000c0d507001031003608070402c519401041d0014821030b60360040e1916020052180c858802c00302d000280090921040f82081000c400a0522810b4405042820031103240c0e5606044050002180038018819250b0324018003d0308044940b9008850a10521300300546900c8054407100b4000440c605580031680850080d00c1600d01110043d004180218005d00c0006c0e1105034070340315079032030300007488581da0742e18503003040d0b80c5c0d14050405960006041c400b00e007102c0c0aa02d42d4171000341d1044440c0710baa50004103103d000b01380c00a94469440360402e0000d0700040c00380c50315442f051082000320072825113401000b4040e6184c0711f801c00071880c0640805d43c0d907000c2c0710300da100e078024907003000c8170b6540401030700 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 178573516 1250 178572266 178572269
    0x10e070509120a03030b0d20011e030609061d040f020609090103060e010c0f05040302010c0c0905010b12130c140414070c11031c080c0d0c0f18030c06050a030222 71
    0x242015000c1c0d06c1070414456001035542c1c00462401c0307100c05c9030302420844c8841ca02c0581000104960b40491201d0032200d1103c00c0d0031614001a0f50b420f02030640240c461a0b00216403800400c540070b1540b481c0c0d280480d85c02074104820038400030781f91002407641d100715182198011801d500220038492942e100714646a9544000c1080d08859041a6401000c0f614810003040c011311003080954040d000c4400120300c10f2025010b601e40701c41d04041111420717080b9001c0080c1c0401d0b0002c1442410104507040b201c0b41c492298038041540d101c26584505010b010319401002c0340c541c049850715000356500103040e60441003545803e5000400d00342034600142c2d101c0640340c0038503466040106600c900000303c11450b803081030a800c0c055920403c05040d002003100100181803c0052900c40d40d2840e030941e680c0e600310720640c0107000b80780c0c0c0020396071190420031580c07007003000505454a52045030080d0030314680b20300b56aa0190028010000702c2d800e0240410084070018084041840 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 178574766 1250 178573516 178573523
    0xd0305071205040503030106050c150c2703060a020702011101110d06060c0206160c0806041b090b0d02040f090c030c170f0613080d0f052d010e070509120a 68
    0x14422550140350301d040d100140c50107803481c1c2040005129080c807900042288505407022038180744820134521443d02c0d41140c21840d60301c00401c100080c4100b201c00040101450410000300f145041d0001c0c0c1c0320700d005000d1006041d400a81501164064035800118110740002003141000e500005105a840b283c81c1c000c070301e0719240f40803032414001c01c0d00016043e0003400060401003c02e4692811500007001902d40c400881000074182d1010012107214078070400c44030701501701c4500b0702010700246030400c03040681441c071565a41c0d00d42e040421030854044402151043d222000607005040c501405000c01032074031404000d014590010108490507072003103000c2407059540c40b940760045650030404582000c0d01185120007101c42c0c86c0032260245540e24a40f011983c032000860780b41640854909407110204a480c1002110110300c500104103414110340103500b10316145101405014029078004002c944000c0c803400540340304160140c074020085201c4404503a84d2030020340d046 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 178576016 1250 178574766 178574777
    0xe0411030f04030e04060b0403080c0a050d0c0b07141e0c0d020c03060a05071b06060e040b1b090105040b13030c0b07111c02040b011205070e090606030709260d030507 73
    0x40c3e8240c2046e11960085841c400d038118102820743d0f40303c0348640d00004a03400607204401c100400700320244068801c800c2c2507180c042a1849a00c0e000c400c0c10340c01802642805111080140388c43c9101c02152440c42c099401071240030369503911071401780142451562280f02d0781c0b180420301a0000f0b1038034005101201207581695400c4041d00942c1e200700e45100000750b5a81c485160b00503000c00c1400c1c505c1c41080c012840035101c04030416071a0717007282c003680e6001c10b4005000d006071103114410f480c0c0d4501400380d85014600000030300b09100328852004803c0000032070080c5a5492650000610742c054050070076203030b0390311500b03440340c00a582c19542d1000d41149000d06240c03c00c051603070070450380c4450103048040d408000007440044043d5060080f10b080e00c04100e400c502c00d0910541198507515110301c000014411b03200340061019010701410418440c255402100741400c840302c8a0040c80400a4910409226041c4810402d0300748901a40c1095094254100c40c0c4516210380e41c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 178577266 1250 178576016 178576037
    0x709060207090e190507030209040308041b03120f0201090206070f0506070e03070b0c03070f061a060309070306110c0a061a01180501230708091801080705010e0411030f0403 76
    0xc18048880d401403042c0c1c01c0c2d10905040b500040310700d240070703010b5000700c0c140c40e2a0307647c81c0c02041c50050110707021800201c074007080004015409080302001b960104d01c03140550704598400074040c03582003ca2060080c070400c09030405200350081a80c1d81d82c00b40c0415200c20180c50002c0203041480c0381120315005410006003514812000d140284500030014414a40307456580001036000155140540c0410801000450204c00310034000522a02c1d0000c1d00c04c0741c1805034907405081070700c9184030b080e081092020310b840c00194241a00d80003000090980154604d4001d24030071114581c00034001e2100300c0d003e01903075a0068040b451074400200e200d13404040119220f000e0300d07651807004c0c0c1442c581800554800c0849070300b42140b1303500144030300c40c031f20100340720503041500121680c4d00e000030100f132681007000e07440310640d010006400642d410200c0007501d07546a40941070420071420301800b001e65554110076040040c18280a03540e0601081c101001d0104030703416008039034031080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 178578516 1250 178577266 178577279
    0xc0c031401061a09030c150901083402010509010b010c12090503060a0e0601060906230f0c100b09010b04090903030b0402191701061704050c060f070303061a0304021c0501050709060207 81
    0x3c4204941f800000540c1c90b007400c10b401581c400002602505a5100071001c0c80200300082d8590001c9074035002c0f142203019802c4000a003542c0c40188460010b0b41000303034000715640c1000b0b0b00e400c00790780040100c1c520715002c0c40440344507040c1d40c00b0302c2c1e051080c81c003840005070b899404410b1015a032015104180e0b00c0d180180c907230031000c2c4680c800241c8101c42c1c08042721003444000942c22200d0300c45500c7d00d800340f041c1c1030440e0001006121903030000180c0102061840c403940c08131640580b120402c035031611b01d6410780c07802a4401c85070f00544030380c7c6200415120394440038860200030801c64840500d6041500c0e1400f0400c500c4c004240c80c2041515420305c2c90300054100c078032a987c0d0a13190040a4103950181c18040c100300c42078841d04100805982d00d00b005800c4608212080b01c1d15030580b414010705465583e80040c111100c5a200c6e6070b020120b00007120360141d0140c9403041d03141c54450400d9040d021124001e1b0840d4604424170907441c2d881240c440444102e58219580543c0760407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 178579766 1250 178578516 178578529
    0xe0105030309090a05090a0212100509010b010e010516020406030b0103050c090c0412151d1006030b0402042301060302090427112d100c0c031401061a09030c 69
    0x1c190390f03100301c0c03010014040744500e030821503000c0d44620a8809440c3d1039800300b10300300b481c1105907a05400c546079440c8081d004d4810700e03911070806402401168242d030300203003480c0585164541000000501c034802c01110030082e000040d8040d108010081d5603060000312400d00380003c88082c040d13410780b4101464070710003050282c1e00300d080b424681490b09280c0c030203031100008100c64050300e203c080d0600c4005403052021411118416100c4804000000f5007403000074207100a070a49846001d0001c04d41d900b81e42507001c4d034180c4002400c448582c40780388400d0842070380c41440d101048004180154150042c241c0078200740c0e8280451841180e03080080748200c00d06244901509a030b85001c100880c1e0201c1010130f0182c14580c00034103440e1903024503c1c3c12410358403c0c031086948076146050000210404425038030b0700c003001c41c02c65682c2d03290f40300140c4000b0341414a5a28203941404080d0300400040240641d512500003c024610a02e9005003000798405e01410398000d00e6401d019 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 178581016 1250 178579766 178579777
    0x20103050f071d010c060203130b1321050702030d0c0201020c04060e2413090308100b0a0e03031303050601050f100c0b09190f0506010b04080d0c061104030b010e01050303 75
    0x81d11445160344007240c1c000b020318610038406042103418103552000c00c6c401e00c0254010210380003400c0c00440720381041d00f94480301130140942c420300b180010011801d400d10081440a0710603050501d40c00886040307601e0301507804040d5241c01211144c00a440d0440d038004c0c82c1905c01c1e0266641c4401c040100000c80d1107a02c90128081000307000106c1c5810040f410300606100340403054140c81c0810003060300702401d00e102e02c00044da0f038450b0b0403c0c0340e00f00c020301d81c0c007101075403503d03160f50b0a08150500c14060101c0380d8040c4000c050801401d550240241c40960440b00741d14042c00e503a90902c180c0d208c8003840b031140140b15410100b180ca0030401803030800a02ca41d142c844171180e00d0b40d00d1001d4ac2d00010318034140d5029824080300c990079000c10b00c60782c050003008ac5400c03583c030a0401c5402c4c0705041c0d101c0c5203081820041013110345004100010f109015003407030b0210406a05045010385903d24003241079003400140401003110f980c484505a8440a40031003081c1e80302c0017850303660703c01c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 178582266 1250 178581016 178581031
    0xa0c18080d020d0305150105070c090e0a110904030903060b121b120a021c110301090f03030e010b0a05150403081207020d03091106070516080c100c150c0504120807020103050f 77
    0x80c46c041105940904000d007a454810304841c40c2c000c1e507556141003100d500f0100040b60740c12100705041848111000c40c01c8810007258410454206660050200a02440000d0000d5203e40400d40c0a5942900441b000c02d1100e050302c2404155440c0140c920300c88070036182c400c61180f070901c3c400300d100003010120580c2c00742001e40346c03020f84040e407962194070840c1206c4a00745842444040d4a003801040f00d282d00c51181c000130041c0500d4083c080c1c0b481055001800da151108100071070b540e40b80c2000480d10160b40030f01407451000c0000740c0c1d611443c2c0020300030315030004440200c91812410240f04207030950a031134440a0207070007107043c1c3d14044d1001d0080c0c4c40e41c3c050000145088030041405074421400c41c0c18045203906030440d001800c1d8001c003000e411158a050071420643e140c0c4503000b98600e09095240200c0e80c0e60b0304000303821890141e80b56964400c3d46c41141c00340e8203d80161411418403804003055281ca05035550020390100c1c00032703007401c01140e00c0910a081884c0103408 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 178583516 1250 178582266 178582291
    0x10080405070608420d0210110a02031504030806030d12020f0d0f0b01030f1512020d05060c0403020310050906060d020411040306050604050c0a080a0c18080d020d0305 73
    0x70b070210403a070101d400781050f0380040301030b11640d070b894060494003044074514500703a46402c003c0402074011815035150181c002c50b00c1d4821030300160380b00c1100104202550070004102609109100e103850b000c148020342511902d09000a481c580d8000745105911035075071030995076524003e064584030003608180105484030701000500001ea0040c040345408940150304040300744544809884644120132030140d56121128059681030194007503401c580350742800030394600c900c550b003081c800b40f0540821005401310b030000c40d1b89000000d05206c0c1c0100c115030290a05d10075000a580c0030b803004034420300c0703000181d017480040c0d40561403017907034490060704060391148141b1000402d10142241d0003541d41c205076891a5009001d000650300500c40014a8a804418007044490280814401107801e03c5502c010700e81c0000301e158428000c00c0081400800d0010990300c40700c0c0c3c48a60364480b110031101040b0044001540c00d49042300c1d41c02c4415220710b0300803d80468a0903118040d0041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 178584766 1250 178583516 178583519
    0x3020a05121306050103061e0605060d1508030a0801081635030a020c03010b06040b07030518030a060b011206080706111903020c0102060f1311040216111008040507 72
    0xa90841c0500c0d800a4011621241c07030455030356110031034501343c00807601c2666641d8617120414880d40501d842d0300810300c0820910f82000700003030640c00303a1103010140315110f0089000e405901b100c0b44000703212a07002c503030302c50811150203421101c0c240201c1009104612020b5012189600168211040e20182040c0d14003941906003405a010012640320307104110051200074041000303000380c0c2d525502520b1000111130801d030030740f00079040441c450b0400f44006d015000d181c0040714003440e0f1606081c0c0e03460002030f034640707103c0408401040e4035001d02840c00040c480781c2d801c41d2100e21400d0381d8075104140e400c0120003c4a45c7d40c0540d001c03a41c8003c4040c48107901074401041059825811260f90b03d404107108004011000000c13401a0449540c042842d41c04100280c1c0001c0d6800e920b212a240680c91031000200050000e0031410044002c1820b80c0c899074110742c04221007412100c040704c03190030b060209060b90328486001e9a2003002183c9018442c0d4400c90043e50300c0005402501d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 178586016 1250 178584766 178584787
    0x3022107080306060c0a060b0118080d030506030a0c0603050406050606180103051005030a0c0602070803030f0c0a030905010c03151d04110103060518070e06030411090405210d05010603020a05 84
    0xb600000c0003950000c204100c030850752402040850092480b800011800400c450300041601540c1480d0520404c10702200b845018008140e0940c6002b003494000383c81c1c0d41d40b50000b803810664980151011a40340c0000c5070040c0e168201501c03c0e40142d01c14486034a1f02d00c2404918411110107140381012040642e00741c1d8030a401407600b004d24102114400b076118000207041c485811401c481014402c0801c000190701413103040010f295181c05981585000b60480c3d00d00350004000e0183d0480c0050041c0000b8040e0f03010303401554000008001e18000c0c584054000d0525200d1034401c7c0740e0300d0130002051804050761240c02155003007500070a466555032006900420345881d41859101c050100c0d10b030300c5643c1005040c02c8140201c5d030a0f41442240030380300400100d42c480c06a00108100f10204400020700b20700303280c042d40e8078103855403541025400c0440300301080c11a90041d42c0304568900d8800c001e84032000510b2810020360340d03100c0c1c0c140d04030322484982e02c010540c18007402400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 178587266 1250 178586016 178586033
    0x10f120302060a0b13060e012102011407050313080d03140601020709050a0b030f031b15040305030405010e0304080c01020709020a17090307120512151e06040506040e0403022107 78
    0x807041c000e40b4048442c2c1080c001d4178143c4220350042215484001b004025090400c07181000414101480c0100002d264000820036500c244603040d0841000611384100b280c10022121005100c2200c901e075203456158060f01d42c1d82440c0d840c40003030b007058106603402058001250050105800a100c603511313007264000070b810001c3c003112a581d90380c21030f01d2032138134248649000024a40c02550380c420004051581c00c01490b100c031042984101005d000c1460041c40d4180c000f07400d03003400713603d0380d5403498502d0140a0302810002103001c00f180000303001100140000b00c0260036000e50343c003141c49059000c22070050030010710002d0b842c40c40c2e101244100c0d1001300d81102500d010703a46810425112844040200340e1158002940000d41c08c2c1c02400c1c0c400800d4000121180c00390f0420324100c00200e00c0380014103058485400190704080c0f541c2c0e090304a070300a1201810a40c0c440fa907598400c8891001210141c0141c02440c80c1224180d0345056008180c803111100503042c9406915160780 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 178588516 1250 178587266 178587281
    0x5090601060c0302010905070305031209030a0f08041e0c1d0c0921030f030109050c0a020d032c030a0e061c05060d1416080309030601032006070308010f120302060a 72
    0x21341d503031226804082070040c00240d000e5030142d801940e1360341c0c4a2480c51071010000b00400c07441c2c3c1060003c00041e035400030501c5151400c034038084420f5156401c002030b00c46040e0611007281c1d407032102a0000c01c5020b2591104403003100c1d0040c103800031080c240328040d01d030846003a109018200141030305413400000174143d0b0190102d43c184c248003c9004e86156030301c940003505105d80084010000400b19026040e4800f100741609070600100243c082d6560078026064414140c589000d420714541c52501d0102c1c02040450750345c041810112217039100d074888121000001e0080c0e44e00282d90030321100325088080b03c8000c0c5c20042c000985614024200030f46040c0d0b0000124012201180c40d0203070b440300a10340c903000f0700450781c0c0c1051a500c0c18107482d40304a03a907400c03d00070701c01195000708050f41102e410103215040401c0400c000b80c0c90303014803804075901240225014042c15889481c0c64160b8000210104041703072074031040c2c6150050701c4c10040040e4030260000d059a40603401103038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 178589766 1250 178588516 178588523
    0x201080112170a03060906140d0201121b05090306010e01080d05280201150f050f09060a03020607050d02060106020307120e011404090b03070e04051507050d1a031005090601060c 78
    0x1807540c220b203403100c6640040c042500083e2114002c1c481403a441c807910005200080b001c3c04600c1542d40801c0c9200d00d8580040d0501121504850440f801904400e07200c0013410700709a0048e8480802410541003988818020312841d00003143c191204041181a00c1c0400018420325002e1402200e90b80d0146824542c252a000c4a100c0314450341d2808070b00f488015000071806042034200e813141c4402e5a803040d07155143c0c0031303001c20603074031500351a00342c0d1a001d4403440e080d1340d1103002280403c1a16800250800d50008200041c460f01080d9401182d605500703607a0603981e160000c9030344c1d0240d00d40c003800e001403c00480301340e540156038070100d82c2410304003c401e0410107001030000b5081036100d18603070740d201c2143c0d400074501846980c000c1d0a000c01005024105078031001d9032090500240642c20700d5002c08200381c40d0141055400091203490140b242c5145140360b40d00b038400c0030f04014003e1280403c840b05001c41e0b03009152148c2c640800a0519a203491400c5404403003184003036 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 178591016 1250 178589766 178589783
    0x8280305090306011401021b0a2c010b0304050d08010b090607030e09190b190e0718081e15040b070903210207050111190c0510020d0f0c0201080112 65
    0x50982c5051000600070024408403480c2e41000c4000a41003041d000040122460f003195003044070394800340490103032000c521580200b080d22032682d600e074001d00089101d005039203400004480504031b000f10b20403032281090301e01e4031142d070100380d89a460a0041038240d0400740000ca00394100074010b0050f05000e440c04070a42007510003c610303a1882594190b9030f066004a03410001a0b0310f000b500d545000c1580e0750000b00701401d2164102003040c5c050314150506c124049000d843c802c1801d008c904404807100b80846a0398610545ea4101c6201c80090380030304e6400020650b08007280100e4861420364000c8003039526a41c0da40210074005144400784080940d011002c9920000800b51001d110382c0c1c10002079514107030103841c050079079102c3e50400076031008443c09032002003083d14080040201003140d00540d46801e0313291610301d800c0281c1054140c5a00610554000b0b1040800105034841c0d000c4000011021038039009c3c01c180c0680482c4031400100b0800715180d041407506d90242015 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 178592266 1250 178591016 178591027
    0xa1a0108011d220b0403091e050405070212030c130509190509010e12030411030303040c03080c010f0c020d0f052b020c0115030b0603071d04020a030203030d09060608280305 76
    0x102c2c4020320f5a02501c1c445064010003040640140102c80a41507101924007541025440701040c2e0050340102c5004a846101050301c03940204121540180e4407601181c8070b15203031414002c0740d00209989800c5404030003000403a4201501c0c0d81d801a442c55207141c1e40e4250340300d80d80029000282503620302d0341d600c80c07900b07110301002d0000503001c0010502c0540ea90400382441113110a5190001d07200c2e80081080c803000a003090120030850790310904030740d220b103c00340c9103d00403c0c90014210700c4909124160b002198003195415081c40103407141c1001c603040340000c0b00c2500868820101c41a59140079441c032104d00c01e050056400034600261030000b044a480742074404000d070744c0040740c02101f418800c0128406400f41d02680c05d40080090a141c2681c40d6541c0911540e409541d4040501107001c1d51510307521a00903607006030480380d0311400b401e5143c0c024150400281d4500e454000041140a0702141c0d140020b0410a41c0c60302070124012602d20302c00480500b1002c5c00b104008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 178593516 1250 178592266 178592311
    0x1120c050319060b0406080d0c05150f0115030e25090207060903080a05040b04030e190b090a0b090d0b061f020c12010b090708070207030b0a1a0108011d 67
    0x10312580400100c0c2d0464566503e160907420340d188100040e10075400c22601b4040c4441c006030313012025001740f40040003601c0300d082940c140a5590461031100c502c40b000c0000d580c00311013040d812503805400b045071038840a403040742120008000d000b101d40042c03040e00300000c01d510703002015468426a1203440307659940700310100d900c008011a9582d403502807880a05411806860348510101018401d81c90166222001c403800204000c05001c070140c00c6c10025103e41455149040d41d0b901112041030726030008100c65000944901c1c882c0c07207c480045003c0300e00c0b0050b601d880700c000d4454a00c0201603503d0b202070300e0300100038a0300014181021000031071228142d12070f20710550040c0004199800030301040c030500144444680e8100b00c000c115544955500b580e1020003894a0046500c0e41c010490604500c5e13400a08020266801c1c00a03800c07055104100034280944141c01d0004d01100540d054a801d215011040b02450340820284000545c4940d0018600280400c032414428 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 178594766 1250 178593516 178593523
    0x30215040f080d03140705031306090f05010e011a0303040905090102091305090d030506100e0114040f05100809070902090d020d0303020909010902090a210218040b0c030f01120c0503 80
    0x9002d2651039002c10f1641905036090b10a0b50700064131456482c0f100e1424840280c000e200103054490301c0711038804510284585c50b4024000198070030448500b1550328103249010304a1001e4200e260b501e0302e41f04581001c40c41d00d080c00800320260186040902d0310501c3e400502c00146441c24954080240000e03555401604e030007202d1020800282e5030910f4403401e468020802c010006262a01303007031090075544c0201d800b5100780310b80b0741596850740000040350000a4400c6803804000082008608000c01e1001d0a0a0350340070750f090491000d000c201114402000d40318110313036801500e07043c0308503100354004061198004c0c0c10703200620450780c04124100c12031841503002940c080340d03c0d0850b140800880f8014200c4000950400c0c1119001072640c601c1c80c401d02e0303c405001c2c1c0c14800340340d0324030b903114807299001040b000912003003409040400e8001c450031610046404001500780343c8000c196400342c0c05c8604081c40c140e00340b1000780c801c0d5441700b0040d64540c0343d000c4005256035040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 178596016 1250 178594766 178594769
    0x30c020307120b0a050109050705070b060d080412060b09060a050d03050c0d0908010506120606040903091a090907020f07030f021807120b03010902091506040b12041101020f0601030215040f 83
    0x105002540703413400303450343c2088817010b030041c0240606090600428070f03409001d86581d2508000046195100e140015030000c61250008000c900040b400145400c1072142c0c0c41013050082c5001d21605410b10100400044100d51541d4000d2500006000c03906100d03404140c0c80307120f414114a401024811240f4111030078841000045081e0018003c8070002c1c0205900720348140c031899182002808201e40380c0c0402404a4050b5139150900c0e41810320656450b4020102541d4185071410044440701c6a0341c041103031103001d024000c010a542610020b841544038241c500900b00c22410b680d5901018035800505a03408150103420184600ca5111618002c994075120f031444c101d1346c2c1c81d002094840ba1008503110380d1500004001503180c250000340c2c0007449401111a80100100041d101e0040b0740080040400114025804400800c4414001c034000c480c003c01c440101c2004980d980f1115201e641c090708540300420060030410908030b6200420541d00381801c0e00c400d507119890384203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 178597122 1106 178596016 178596023
    0xc050d0b152b170309030a0e0f040e0a0b06030307030909020306041503060b090f240f0d050303010911040803071401020f07060f1506020a030c02030712 67
    0x2c0d54890610940424007501080c0490710039001555072000080700d0344450f24580203228511002602e01c03600d180c50046242ca8007210303080b1840954044000d401603803107101c1003a2a502c40c0140c1240b10003420041c00403079401d00f4114120f071070140586000390030400c01f4101095000d21000300303a410050015135603440b680041401130440020741c0080c10003c030004030400444e50002d8003101d40860300303802c00d62500e1405001c1441c040c0c402403a680941c41d50701e010720003030003040c0c259103a00a0070141c1c003901420124103032411010080310203400010040c80041c50b1482512460141140c5107800d041c03c21854550b42e20590700e01410802020082140c20502501141c0c2c5509801c000e203038035504140307404005400e20051031245c0f60304120482d00744119100541d070407a1201c1c3d00800c2c44114070303102600e45503020102030303030140a443d502003180120300b880960010311 = true := by decide +kernel

theorem cover : BRFrame.Cov 178417266 178597122 := by
  have h0 := BRFrame.cov_init 178417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 178417266 ≤ n) (h2 : n < 178597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
