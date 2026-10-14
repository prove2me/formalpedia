-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1472
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:09:02.065646+00:00
-- url     : https://prove2.me/submissions/cdc01935-e2dd-430d-8144-117df7e3ed7f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 264568345 ≤ n < 264748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 264569595 1250 264568345 264568387
    0x204090c0f060206010b0a0906050c070e07030603050f070b0a1206030b2404050402031b01120629071e02010e090906150103060b0906130e04050a061b0f050d02 70
    0x3034015001c4140212641800781a004100300703c003550910040c41c801a100c0030450049400704000070550b40c4801400b08541c4c4014491410805110b04088a00170040d0160b404291061310840f9890508000000341840403640400744440c203092401d002218261880051201d00e2030319088040049200280080d01400600609641048400c040280f03504484a4060300c510301d4041000b0140c2c0f00841d1070841d0400e400740200016500c0710040c3e400c00c0f10351718031119207441d0850100c0c240d132211134410740d01d40d10b446401c2c9516289128151003807050000080c40202041c600419500c0c800c840355000d948141490006508031901081c0c3d108001c85a1242950100c0c0c1441103280c1d052010108116082c030381404014100507210f0118130581e000c0c03d00036800041d1500c071103010803101d01c01805540d007462050b03040c01e042840c1d55009030501950074600c1c0c21072000300b81c5006e1030b908082031240d880e6544000c0361a04240c5554014021100c7e030300f9003c010034000e505c10100303040e0b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 264570845 1250 264569595 264569609
    0x150108060604230c030c0c0106031a06030607172503141501020616030902060a030c0e0a03020d1202010b0a0e010e0705040e0a15090606050307030f1a010c0204090c 72
    0x200346070860802041d6000c2d0a80d10810000700640702c4401c100221626500240000c0307071543c1c80d00c0713094108109103e01540f010440d440c1000101c1040485c0e10103005060491031010035680714101015101c08081d5291000b10300715501020445241c070041aa010904200841043d122000308002850404060310b0000313644644108004055010454214160702c1880c20300c0c00c10080040d40e04e00c8003410140210845082040703806100e41c000c5408035501030035940c5c440c20226030140140004150300c0000c00c25001007083c903803c0074084002202d0700200b0034090b61550361502c0200084409280c0215502c844014085494000082008000910175481c903589007281811001d88050038901c108142044104010046a910240c0242d00d043c4001410f610000b000d20000f413890b40104821810250001101504034000d0352040140d6182402000e000020440440d1402c010465020202c03511510042d4801c00c0e44450262026000181824564079010b60f1054994810700d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 264572095 1250 264570845 264570853
    0x1506030f0f020405030d05030a09020333070f050a12020c0a140a081e0c070e0f0610020d0c11040509010c021002070b0601300b030c180703020c150108 66
    0x4103a220340303072003860300080352080c08504090520300001c1e150f1a0030055041040b601001290704121580d00c40e0341c07074943c0203080700c207603400d10070a000038210790304101c24100d0000e01500720000303c04100c11380324080964403501d4060701c02d83c0988542e003010541c0800c1094440c0001d81b48a06440180359005544006002d408020f103409c69415080702200a1290050030f940c10009a00e402a14219031034a01c802400c0d040d15a15481c45001e0001c0b43c040a00c1070010000b4402102d6250318082d660a20403815642c0e100000c0c030101107001f04078480160f006101101e112803040f05401e443c14428582c10210264200021302505d0055621840c0c5954807800f041c103054040000050140f49000194140603d5403969540380b02e0061510741400141c110168003007080e041c0000c81c0032107611500200125a00c1100c0080c0100442c40c0c0c020f119020f1420030500c0c159014050180d8130a4104400f41d80d5802e04501035000300603114590712558a4482403040002c6603513018100c200300034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 264573345 1250 264572095 264572111
    0x150d09060b10090f030b130807060603031b020d03180f0b04060e15040302010e0d0f03030506190b090609040905060703020909010909050606090402130603080909280b0103150603 78
    0x2a0008050b8031040910041e040b0410080c007200d02c0b2201101e410801d11015035445400a135a44540e5001c0104002d400150b05020000c885e800501a03a0003a660051aa10501800b048084042001a5100c9032840d8030300006841000303408880b46070b04101c1581c40b03984a0300c1980d25007d0b40c10210341c4200c0450705220f4650f02408041200324221102d140c1c00038549035004a03441140000781c10004100002c0585807601d001c2c440d09503a00c984407400ba4261030400074001c01058a07803502c51203155844500c401d0107150550701b42c501c901c030072034540b002d0203041068640c00031941a40090305c0358040b0000c40d00c00c1c0402480340045440c05a070716920380701004a507500580160403a0351500c0c82040108800058980e840402541c89000301e0b121030002890100407d0350780040c40d405e2880c044100194000981070030706056a80041580ba414a0059211580040c0c0714000000d0380c105024481d10f42c00c042c60020040c10006107540d14610542c001800d56084400400c1d120310351 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 264574595 1250 264573345 264573349
    0x3050106080c0f220204050a030f0b091c030e16060801140d0c0312030608030c01020702010315151b050312071d0f011425030f1d150d09060b 62
    0x7a440e10030b00c1c102c4408582510b02d0f400186100480c1031404242050180154a074102d03d50440700a0b0000070640c114050341d9152050b080350007920102e520410502c0030880c084000920080714803006414150360b00503940c0e048004102a441c640c02a10403001980301e070a89441c40240908001d54680c0c60740c0d8100080301061200e410342b454098490b00d035040000c21305420381078003039983c03005a031142d110408508501500c01d9401c0981c1078000080c844000410560007840c0a51003a2070500c840200300c49401d000ba0f900c0d10454801b491160440f0f041c491180f2074441849201c1018045000d0081c3c80d80c51650f08460300480050216600b0300400c1c5404c041041a40780c00d08840101e0140101c0c0440c0d060b082910300181403001c1e9000d1200c400c207080d82501d4040750318401d59055400752110780015030b145823100798080303611903004c81d6242d4800d07858408001c403e28a03100031840c000307040c400e01c4041d000c41c4031040030003849440c001c0c41d02d900070300704600d004600c00b003100880eaa013 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 264575845 1250 264574595 264574603
    0xd0201022a120a03141605070605091e03100e2a0114072a030605100918031d0d02040e060a0c1701120507031509050d050313060506030c03070305010608 67
    0xb01d000b02c50360000d0b03100340c0000d03805005480c0030034100c40e4680e00c4194100c0c149040010078100246680207590010800700e910801405094804441b0500540c40c01c010023804801010025034258002000100031520b440d04a00e4203440d050040319000100a8038400742080040408448981040d007a01201c0d80d0114441c081810b001c5601c40c48c00c0b0183da6441340050380342c1c19200c07105501050f4a00e4030800a881d0781c00035074010005000758500380f1900007c1d20400d006034000340345400047c18034228a004140011641621640c4944049161004581d504044043d03400301150000d4001a1124000d100e810510000100b480c0d0070064400301c1a540c44103055020011051034601142001e09001411241c09030091440250a030810344e00700400b541014280781c01c8203050110b00750b40c0b0750011407801c0c01641560720903509480111040d100c103441185294141c02c80c140c0c0800c50651240d500583d00900705c4401107004c41c00700b41040c201e68415502a59940000c2110070303810300c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 264577095 1250 264575845 264575869
    0x307081603080717150604170304081e1203040c09110a0e1002070b16051e10060608010905060316320901150905040f0b03010c020610050d0201022a 65
    0x42060340c910500c407a84c5142e501001080141042c050101c3c9800645480b01110003401280380c0300c10415218900e959a654001c0c4580c0d0f10a1045104202400c00c800c01702000b201c801c40c025280b45080202036009541000d40300380c030b0000c00490000358507035982c8164030404003040701c815200e407011007019201c1c012000b01580a0304818465404455011803503401356002c4201c402e44441000e030496511500a5100030054407842a080c22446030300d110401c1c00c17840b0082110702d91090201b041060340c00d603100306404650a800140300c0380030342c1c4d0069940084042e04841304403450328600c58107450b4035031046810500d00c0c440500c921030038103086031540ca5846141040a0403010100396502c02c14458060801c920040004540344103210003c01804010000d0000440d003001d040000c1100a14244c481c1d843d00260030030b540d0002c42c0e168490710300404e031842d10602d0f080500c0b40c4032080782d50880c110300490901d0000d003414880480e0b000d02044000480402280e028480c0f46c1940d9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 264578345 1250 264577095 264577097
    0x703120b040506060a231815040e0a0509030c0a0b150d050316020d2a06030c140a0504050a0308120c070b04080706090f0605090c04090206120903070816030807 70
    0x70100300c0305480341c5084545d001920f10b800f0614513900041c14610040d609461042d85e80700062843d0ba171140c1d40e43ca000321000c200c0d40500281004020344500c4e1040d03208180540e1412000030b1101a001e601c615070004008064a2038240155002390600605201c1101e0000f61241480341500c007541c5c102c0d85428003552040744044140d00c0b003170390f41d000b4800ca107442c039452041590219101c1c81040003070303150311421150101c00c200c60350003404100300b915414901900c0c3c3e00041c2c3c280c403034014803007420043d4540d1a4202015606004981c0c0032003448003c1c44010407001420741c40c1c61a0842c000c6004415407600e500a2808880c9074083c05042d5a2074060207001103004200d4011041c2d4200d070341306240700e41d903045610b0b0550203170004071006003842c9001c0300c01800340121780d0000c504c18017041c0140c501d21418242000100e5000550180d004102484000080040c600722250428107003000c480c1010f0042e582e8144030303440344500401e402001c0901c0382c101030f0401d40d0180c00101c1c1d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 264579595 1250 264578345 264578351
    0x2090a0e12090105041203140c010b090601030203060d0f02120d082509121b030b0405060105010201060812070c05151b010603031b020a080d0201060806090a12120b03030703120b04 79
    0x40c400028013a01850003003864212200100c1810035000b504943d004a030b03080201350301c560200707c680d40280700c000c01d91030103a075814002a803107620900c00c40b4800d28004140034490802c7d0b440f410000e042d4408226000301015405081c040e104100607010a2440e039680310043c5803e0000c42c21841440401c4404202c124000c98000713500460300d00b09a0710748000080d0741070040d050501d0482c10b020b2008104400e440d6003c000d01c014280058840c0e8003c00c2141d102c0d0b603903000120300701e46091244400c650410700142c039403040400002c0007400d004595035503409448070002148204102005000c100001401200b01034543c5607040c405d5280200070010310f8910385001e000013404140c822040701440c030303c92045655881d0000090410001151151456410060700030480d038040d4a42502c0703140c0018100400c00070b0000201c80e40048101c0a404032200140e8a414007116200b0f645d1f92a0002200151020400380400074080d81e28411400029100b15089842101e00180100c0c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 264580845 1250 264579595 264579607
    0x43806040303140c010b100903031e05030105061c0c02060103120503060919180825021503060109080a06020a08010501111b0315040602031e07020a0b100302090a0e12 73
    0x14201d494052050302003c1120396803200307902d0742030040040a4545901041c1078600d0314250354049a00b5094030305c01c2d01c3c2c260a0003103070031200c14160710302c4c1080000514100018072403420301d40301034424980c6c42c00c1c0d03a02c2c0c0807071092180c40540c0c0c4241700302d4005034840e20040040c4142500704112140c42814580d145050400214049110080409035009807a20300d0322500283d41c0c0c05020000800b07652a4907002d95031078015000d070701051800f8052402d2010503518464940c20210245034001c0c0a038282031101c4194110319000245080e05100000a000543e0a4140021906284554030040c1d55203685403002d80b02d6401a00841d040155054040a22184c00925150110180f20031200b4040b84500002e280c00c1074038903192282c41c80c0005100c10040b00340c000c0c5020f143c0380105600072132100c180940543d401103466a005038041da00001c040348081d1140c41e0170450f00f50f1300c6070140d51a9008034282900540310000c829030f032040c400320315003400d102d0203100e188030000c4949409 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 264582095 1250 264580845 264580847
    0x40b0f04050a1e080c070603060b04122003030c010b0405010e0105010c0b041b060e0f15070b04060204030204090813081f020c0c04230601081e06043806040303 70
    0x6400614003c0c110901003c01e01d0541440c1510021425400b003645540c80f1040107400d0745880d818458a00442e080c00c0001c01c03000d2108090b10180c41c0358101c19500c40100703860b1020503054180184400318403841d40102207803010b02c0144483c0404600115089202c0300500040360030587c07050382107002c04401805944e0344402030004441d00b080303509450341c40764105403007050541c0c25100c01d4468181400101340d030700210980624101110030099803550001032103500031140c0910742e20701004200311000551600707090b980050189030014141501c0c2d5000c035045491840090303130175038804116110011001c0700010701400102000c1c00c8085160384005414426680e401021150085100070403079100f001808541c0308014014011054004261903a07005e101c280392044070302490004e03803076500031000c6501562241100071800d40d1102c3c1078504000018003032a41c8980c9541055005510f071400010b180564100703420702c500040010b52400d8421205800e02803d01404100046 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 264583345 1250 264582095 264582103
    0x417090f0409020f100905011103132c0f0610030b0f10110616021006030c050603070e181e0c0306010c050a05060a0c03061403070302011202070b0f040b0f0405 70
    0x403064402060103621031000803248111004070b150802000d0607003080c49540102030000b01e410a80350745501e41180070b099900c911488400e40f00e104031440b400c02030040c0d1103010041180c4003480e80303101c1403e031050410003100250740c0f00303880d08080010701200385005c4000311210311450804114240c2100d0114400140c4c42aa55100d044013003c0b40c21820b014112041d48a0f0102d0251251483c1aa00c00801900400b01440051003125484081c0419500c070301400c1d80e400c0028012030a00e4142041110b6100500a401b0000c51020490342521141140d054088084400b4001c40c50446000ea080c5c0d0000350444c64021031003070a00410100c0318044a030040002e1074140790410b280d060192500c8400b80d4000c1841c030684040025107410796002d1101c616031640c00b4001e4551352090161240400c0031502d034560000402040198012000c50383d20b03240e03100c0d000d41002c0090b1074488240c4000c480001c030191b4807008000801c06103e403529404110a0043c94483c14113403541e5a0b6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 264584595 1250 264583345 264583369
    0xa080606091309050d032412170c1506060406080c0304020a030515070305070806100e030c151804020f0706020f070b01121a0c1812060906041709 64
    0x5528000364401d026100c1c40281c481c112040042884000750704e00d0030640c0d6581d0301c82c000300081d26056801862207508440081403140300900d041d80329040c0440c88880c8440a0411280d00c1d07a100003003042c040b5208060030440f07040d00d016181d5104440c0d440c0203c40c0300206464803c03c0c08000a004540d089801d85030000320021403151256500d10110b004a03403680c0025009210750891001c000072030b020343c1c1e44500310b250307002c4c1322580f14080e06440380e44095802ca0350014600035018180c9100b4203c0c10500e03100101104c0000032400e0104050454040340380303500010009048258100f20034041009090503281103107807020304900300c295401110001840180c00281d1b40041204c0f80056400e0141c2086107a100f55a6410003d080820b07a83d108403003000c0081480f90030280c0490060b4450340d40c4001040c40d0205d00141325400000064090b54003241c41e40c2c010702d00aa04128980c0320751040c00c010111130406040140d9000010a0655540c50082204000a4407400c0072030342 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 264585845 1250 264584595 264584599
    0xc06081303031805030f04030c30061d070305010b09090a0b041106040b0c01050f190b010207030f05010b120d050904230408032202031b0315010602030a030c02030a0806 74
    0x1d411524050150f402100d4401d0241c9607104c007050010749001034034000d008881c452405071444503036402640603001e081806910310a02c40c04859002091030007031050300a0302c200f900281c452484101c11700342801c0c2e20042d0001e80d00110381070040090134400e002c2da29004560301c107620300d004940d580c1d640c0c07210300c4010301c2e400c0f000c0b005c1400c08c0050b05d012803c0400041c81c164495403203185800305500700da00c00f01d1140d1b0802000c90000c1065114040c000c80c0514004000d0800421940010740310454034181103100c3c40380f002020400fa04582c000492240380041403c09200e000c005070181690000300e0940c0000c00c04082c03c540000c1111040901904d000c5140c000e071900d071000700032005200c0e122450841003000304201c0401c0045118038411001030a0b015840001594500d03e4042c0094045d4404180d4800190000c410a00f4036a030040c11580303225580740200320818002c0e4000000341e0b00106003042c00b290580981400c03c1d10300c0c402141000805500100343d5032000d09258 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 264587095 1250 264585845 264585851
    0x30708060105060a1107360b012705040905010c031b1d150a0804260301030605180a03020c1c1a0406110408030d060b04080a0303020310030b0c070c0608130303 70
    0x3170020744003449060002c02c0900c49140024a101c1d8468140e403501803004441c01306910241100d641c0b4610a0210000303040c0e6624540409a07002141c0303010712605080d01c0e80b03118020018240e61240160a800c900c2080040b582c0042d04201405032803440c024841f661038004440040994003200150b13112683c001d42c03c42c81d40d00b41f4003042d00700d18800c030103940f0300f0030019000d109076401180751401148140c90100b0002d091450ba01c11100c7d02203940c0081740010401040030640c0c07034015682010b9440541030b640001e03500d0103031508408800450258010b00386a843e545841c4840016510519032081565003150ba1141c64550303541c001d07411211b4001001c601404000d60141501c00704103502240e0359a1540c01070b0740d407500007601254100b4104000810b80340c403040252412940c5d0400144050740b8560740c01e4000e504000c00c1280741030041e580c0000400c800502d140e000d0004500016903c891506004c413040751103422940c21b1041c0d520078420385441d2107400440840d0075240c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 264588345 1250 264587095 264587117
    0x303020a0b0406150e090607020d0c14030f1c0b090f010504090f12050d11040308190c1502030f06040e19240203091c12050a090609030e030708060105060a 68
    0x26002065021107414807640603040104005c481419031701c1c015640c802c12105159a180422031b928100303000640000b44a4013483c10019040544d003082c0d003601101a00e09021509540da00150000c80e2800e0540711501c00400041909204281d4840c10030703101e04c002e6142c0303018400c840da0010301c64503005655892420040c8a407055140000f6944000300040012090780700510340d81186c0e03004002c0c03928090b0313001500c1500204071400c84e9400462141400703400e0401b40100c0d1040c0e4950014002540c291000040106500f0103070507101700001a1281004580c680700940003d00750b81c042d628054050200038030001c1da0010032171856650607510540c2c0d00d0070182021201e4010b088c10200300815265689458020b5881828514219800d400305040000160720700000c0c0e0b1408103015044034100302034190130040e840b9028560105403d007196645000700ea4125605800050600d0500c00e50ba01d1705110070b1000b40b540000401a550400002404238480c000c00f42c42408921481 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 264589595 1250 264588345 264588353
    0x503041103030915031806160e03071a070b0a090f020906220e06070203070b0604111605100b1009170f1c0f080f150102010e0d0e0306100303020a0b04 66
    0xc03140319040c01380111039031980300082c0c01065001950b0f0480003041d100b01440c484c11000620314454051071440d40307080a10408243c441001d0340018641602407201c0110344040c0d1000444400e8100d01480d40d50b400e8181007902010002404035038145042076550b50103c1c070113914410800390100d40c060456111280050b4620802c0c2086510400312040903000c080322984c0030301ca424019100b41d030385642e501e101c103c1c0c4078800d03c0b070001c19810406010582c941420351102c0d04c400e648551040c81d12516054080400360120400c5880354800907500550000d140145541c601058415940c1c00000d084003500910b050300514000b09400c1d04000342c128000c00030840040780401c107550641d14075203070068092010700034020215801d280d03481e04091155808520850440c4002c0107142c5502080e12982d002284420f41199250b1026420040080c401070b010001d590303c0d000d0401d40351400340b40c245100280300302200921284100003003500810b000d242a6441f250b8015241e03030f1494 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 264590845 1250 264589595 264589597
    0x302010e130609090b04020f0103090201091e09090819140f070f020a08030a02010c02030306010e0904030315080a06110702010212030a060b191803050729031302090109060501050304110303 83
    0x30110b081ca600307013410f6500f807010407492107015034001d8840140540b804001036003501d0358200000d0009400160070007001c84580d098007180320441e0303812282d103641d55584c00150f840e0360605880101d00041c010100000b1480c5421082000307080c480320000c21076000032068042e502c44036941e035000207042c004011145100c04001540105142c80c015194050305907a50841d15582c0d001d5886d044e000700025000200380c0c3e1084e903050f91808030740f0303c07a00d084c00580080640704909258940f47d0402c0c540e8030441d5100e000c0c0407400700518012101c4d04081e8203030740c8000c01c000d441050402080000d41d90201d04094591070680c40556207880b0141d1800003005070341e205e0034030004046440112100c008107100262141c90f5500003090106010003500e414080c40001c1c00c6a006d8401002580400b00d80740402201d8041d5102610350f41c800009115402103903200030302c090045400c4214984a481c25015280d60607080105504040019005210161014090190441844801d5a0200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 264592095 1250 264590845 264590849
    0x318010f020a0809060703020301051c0218040b0709060801081507050706050a140619060e010509030703150e0303150f0a081b03010c0f05070821040f060507090302010e1306 76
    0xc0411540e50341c10180c020040e100a6940c000c0502031080883c1610341310b8001e03130303042e503200500c20032101e8010000303031112010300c0d00200c2c0c00c05010341c03010004040021790b0510803030060b4070290003031520300c00060200c4000d80003002031107030590040c0076001c40040c0600c903000401c804915941c84001c0151018010100c0082500303003042d003002f210718142c0c0c100340b00500b04000c0c208040c0e1540c1080220f1044201406031072801a001d00708040c62062259501041044c10460300d1b181000700802e003406030030303081907580500c28410030006a90354458090a000300c10040d500714140750140164032400c441040b48556000100b90225643c0d282e02040102240e00c120307140d4103000c1c1c2d00d28407090003180206100f03519140d40c4c0d15032140521701a211341c2429550703240c544016035a0b0310001d40c02442041c0c100c0c00114000c96151642a94898007842c05100f0401101e00d26140c50f9050310001407001d410400003071010001170760004212a104001142d60b1008103103040d4140008003915 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 264593345 1250 264592095 264592121
    0x6052b050705031212060f01050a03110904021204020f0a080706180b0d24050a031b0509070809071a07020111010b040c030e0120040b07060219080702011a0303031801 73
    0x403011441c00011131000b0308140400800d040010b40d5000c00b001011600944440d010441c100030030704201e44a0b9206884034200c10034100d050501644c003050480e004200e020304500020310a11055113070031402c0041c5c101c4129985201582007881c042d0321100c0754481d2000b444151034003c1341003000005003030f01030000e00d04075a4a038445100010054040c68080c84000880b100f0082e00d0446c1d4160381c1c1c0151400034003591a03940c07841d0344426134a0f030b0491074690075488070f0902007102d60b034465a00b40070784c1c010381d21904581410032803107040503070f6a404045404020fa100040140c203032800d175504103409003000d00000e2888a0842e001d401407640407580300346400845000e65030140d1001d81d1034a0703010300030006036038910490800240e044500c0840d1800c14041000f01c1000c032002850081e00ca40c401508181801444100c07115100d900b500104120004100c00e0650901c5039aa00c00608600da40c00100840e02194592001900e10641da40004e15061220402504404807480b12 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 264594595 1250 264593345 264593353
    0x20d1104092a030b180f0703061515020a030c0203010b1002100c0503010f03080a020f240903031e0601021f050412080705090607061103090c0406052b05070503 70
    0x142c540001d80035440409041d200700b40280c8402219507082028007900d81c00300041d00030707803992240f4400042c1c00321115400391140b5003001c1c84045c8107000340c400551141078003064a1a14103078203000780d0801c1e00481d01da01e090650001c07010790700148040d007094044c1018240c5010600129015000034030380290010954078207911001d900144501c500c0b001c15a0400c4126603c01044030307144800e100d05a042c000f100001d1000c6162940107100e0028240110703010392409064550403e2401122003101c041b138100c81e000300031961072050303501003446809189140f510000c0c1d442c10819040400b101d140c00b0000040050340200400c0d0000d45c0507a0303088021401c03011401e006044112800c8074103260040300d910843d03001e10650350180d907298650714180388800b030602c0310981100ca821b8801c2501c4e440c0c003d5210b41004015030003112102c01a004450b140d4041c003040d0340c00c95001d070b07015400d10180304849660301d120001c5003100701707400c0c0455500c941c10700c2864590560825941402 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 264595845 1250 264594595 264594611
    0xa050405060a090608060d0506041205120109020408010b09090a032a06091208040b04030c03051e0901080f190509071d0103050610030308070503270a03080c0412020d1104 75
    0x14205120f032086800079502c0e40315039a0782409001c4030203044a401440e9034880f4020400203115500d182d01c41c0f000c949440c50820b0340a00314584009400c0c0d00c43c009140d0f001400b4040802c0a024401c01d000f81590009002d0500400c2c140e620301c0c2c5640060200701440400f00301c00b003184070440103680c000b0560742e00d488126040c10001000d14440c200c40840811a00c520706501909160384915000900d031010341c1d40f40d0310241c408212589003101001020401f044c18003001080300794903541ea012071241c6645600d000540f0100e0040c0105800c503c082003000381001140c0e4008098000d00b01d40032075561120b040035458210141c0110b03191425201c10360010341c840c81f940c281281c0c0039100300c2d4015220500d80302d9629425000203000130310a54009004180104021900700031081050558150144412900035501d003401503007a030400400780b800d01d90f126172003d4114140314140c5181500c2c120400b94102c8042100a00813229101102c045c02400d0180d80000d0001034014000c100b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 264597095 1250 264595845 264595847
    0x90e0703090c350705010507080c070e1f050603070f090e0a0203270a030c030c0b0703050108011401080a12120905030d05011d0114030705040e010204080607050c0607050a050405060a 80
    0xc0d00500400740406a6450090060450a1050b100718440341e0180c80454101801140c092303100d40c5050b2090b5004120110041200f04041c0b001041000005c60450604180c10142100d580014020481d00014284100e588000480c3e4118200f402d1610b0070100541c0141d4044007150b1046202103400c1d010040d400d030302600214840e01207140d0711011003400d40e0306040b0b214110406611181e011101210000340503102a100712402804c0c40140150300d0307079070b81c00303021002c882e1200025290001004080800d00a46194005440780e1a0b4075606107200035a0b207030011034010f80710079541e075200d2484901402030700411012034170090103994101c0c10004d559034058a036160030350745800000100d0a41c1911210025100003000d44026483d26071146042410011125454000c0c0407000400f646c5612035640000e91101c00907840e00d141100072820f001e8010900800d118041107103d0200c600810790035880306640c242183c41c4d0322074074000c40d954016600f00ca40c20250009100b0221 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 264598345 1250 264597095 264597119
    0x605181f0513030b1504180b28050a0b01030b03241b0301031103070e01051e060409021804060e0c030a0e010f0c0305190e0307030e0f0301050f090c01030c090e0703090c 74
    0x80b000944091187d0318000d0243e160140c1011707400340c0a003407400701060074903000e002e8810402c13514144000d4441075a14030030044680540c0d07161841039944000e01e001e540c00d4018003012003011070140c0021044900b010415210303400314080c56102c1c04000078401c07488c82c44140410b4200c025440e48030340c0c50385410944024082c2c50144240300d280d00000382c0483c03502d44581a60005004490895100f0b40f800680c1145040e1581c0c0c411000d100c007052413180b62000d0039032261344194080110b205a418407080351965000341c46010f03120001c0148900440e82105d4100e04440c1c8001151006540300500604000021000321800c008800740400d6040e041140682d0f030203000b5981d0415040e410704201d0340041030170300c0703140c0050011401180c01b40030705203000000585450380c107441d00c00000382101c2044890170140781d802001d000300044108104400c200c001e00301003060618501000e04800d0440c42842d0701c41720400d001400f018829003128540c1c681c080c1a4611407a10b51100302e1003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 264599595 1250 264598345 264598381
    0x605220f050f010c0c060e0715120605040507081906050d03030603150b1005070213060807030512070c1505120108011e0908040603180c0605181f0513030b 68
    0x29200300481080302c1c1c4418030444040300303002d49039802032a146070b482c14003504d401c00c020040c5000720500051440402c1c075010f12100000e0761519401d094016540c000c9581a40080340107901d40340401c50115040382d04550084005010510094100541c51000e0141901700310b402a5914855a0800d901a00404143c074818484030380d980c3e44009141048501c08081d055000891003580c4c00c0d5640100000e0000c03e0003d05403403068828844082d094a00c1a030160781e05502140c020407d210090051005c80700c1c01190a501d08032464076040c0c0c0161190260706600e00120b030205846a00440440341e03890302c1ca460110181d0395401180303000303000000780e01d02031001d1042c51a8000010744074280c6116484004c29003400e08140046004020340b9445403449941d1854210126440700f81c44002819596503d83d56108040800d43c03904500c07a400c24001c5400240485200c1c8105c0d00f01c00d905141840c1c0107486004c2250f241c440082c1d5640068101a090410b00001d1000c0c6009800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 264600845 1250 264599595 264599603
    0x1c0512070b041e050c19080106030c080f06190c0e3f060a0b0105040b040b030412050c030924040602070e1008071404020405130902010806040e0a0605220f 68
    0x84052190405501c82c846442c2001303040703800c2007081d010240740440d41d1480618034010000000c640310a0400e003101d04c01c1e0400d4941441e1070008000b0a2810450302001c404030801174141030801da004e455120142c1901c3c030078a03d44501010040c0b40c450b010030091800000c01408003e14041200100c4d03054012055441000c60030000400c0c0000d109a2450715810f40020a460b99440b44104001d050f95100b860400c079040200007103221f18a00580044e14200841940c0e03070600b85011940c408802e14444180181802407003d00c10010003920b64844055543c04080794a403201c0b489422006980c050841300081070105600da800210751003951a030920403060f903100c00c0e00c6000b40080038071455415030b22101003400500c03804960b10583d0a000b44c009801d180d01d42000628924240c894480041d594040040c15980d2111546410100c141d8003000301402c0f81d00c0c2c0b80d40b00c0031044801f401440c0c890000c140c02090000084494030b141d4155030303003440d81c81c1c0340400700152252016a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 264602095 1250 264600845 264600863
    0x40f090b0f061c05010b1606240b0c01050603010b0f120115080c1c0803042916022104140a08031b0d0e010c142409010f06051c0512070b04 61
    0x89007280e0403008551031451f081e80c04002c02c901036603d110203080d001c5070842011f040d00c0c0344070703041615080f441400341450305191900d0340211810301d400c6400045c00a03220742c0c10308010002c1e584034420642090703502500c40c01c005200c4c9203030703845c058001404403850f41440803100044000000c2910520548219644400e110700c04040c1a0340305101003015041100401c00702d400905981862201da40700c1248081600d40e118800305040482243c0f0090080f5404145551640d030500103603081c00c5070f54607001c110400c0c421503069640100d0240c0058500849208181a41c459031141e006120204c226070b912064240001842803848213020b03500d00c5401c03031320742c20903005094041c5031400c181e40e04180b110050b110040c070489400c00040c568000c110003541c0c10310401c984408000780400c610851b038140030b01030342d085030000c1c02040141850114240940c0c2e891500b4145e44652484c20124184920700302241490074402401c0100c0e40000345071001c02c840800110b02c181e00800451b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 264603345 1250 264602095 264602099
    0x130e0a0c05040606020604151508060a1401060f0909051b130e010b1809190515030606030d1d0a050a031b0e04030806040509010b04060602031c02040f090b0f061c0501 73
    0x40e03994072800d86004118123400c201507a00300340d041d40701c10a040c841c141d404960541d01c0501302e0406109a421135156602c60110000c040071b0315141d5801400070b0315140e1003005035800000c0640000d40109030314281c907180030560450800407520001c039118000551794180c2900d01c04954010b51098400030400320f000003407412805070070b980d000e1900000805480c0d00708020032503541c800034120b00c18001690490071801c052880354920410340104400b5406c18414101490148002c1c1a00c0c402c2d4420070491710001d84c0003c8081c0400303201c1c5241c413811a203260004500442c071340c100d01e0300b102c500310001050080b400301100494403030544241e14240c445403001282d5070301319070240204861902050030750800e41c0c440d9601c0303021880005640102e40d0005019030790154001801a8400300e1503c0025803040b41c5030201c44c0d000442145084d1a0458503240070f441e5119021409545c1c0e09034411031b0b1203007542048180001004035644082040840c559140c403040071519141c500400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 264604595 1250 264603345 264603347
    0x19020106050307030b0403031107050c040605040b03032208030c07060f090303080c1b0111120609040f0803090304031e030f0f080a1505060417150402010509130e0a0c05040606 77
    0x340e00306070389001d07000e001c2d8141183c0b078261004001520441c2016074541c4080b0741100003501a100c600c0c031035005441144003c20411054031071681003188558500104d04096a0700042184c480354903400d50705d14490301c50f00301e0395a8140203900504160000003a01c1005040c0481e03100203655080d251128042840d4034111141e134214000100030803070010200c0c540365802405004158000c04000c001c1d80d0204603003030b00351000500b44000b01c2c80041604c104d5a080c80060907449141940c0070f01c40c4e0320381515007200300f02c000c110207000e10700000301103411410b080c4112400346401500c040014a05662003040ca00c6154105070001646d401d4028013051140800d03012110301607960040589401140f44010494500c6e4582003035110100018a84c5503c0302a20003810400381c10500d114407074035058108a4200c01201d00076520004100050381c0050540f074410200317a40440a01c4100344c81080180544160041c0300d05c01c4010410800c480e1490f40815074900760b07002d005071507903458 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 264605845 1250 264604595 264604601
    0x13090b010e1303050d0213060e01020709051303030203091606020715050a090605030901061a0405190f09050a020c011505030f0706020a08070632010b030c030f071806020102190201 79
    0x1901c00b032078101c0301c210900031902c200003510115079425001807400707a1058058401c10829400303000420074806050b621903805007d4180207208049051041d490500314095804120060007000c0c5640400410215002004190707500c1480520906505407286406965118548614a4580704e05252042141c0c811000c0d5000441c1940b50b0041590404a0a45003500000e042c07541e55075995200013024440301d400358045550f01081e080c2d840d03091801340910b4007103120400301000c12880040010903410040202100c041c0a03001909445504000d0080d208180703181e80550708040b018050014a0700307204007221000c03001c0310322050b50715089603103980d414826140580c02c41907082c408220044001c000c000d00c50003000444800300320b4a5036030000d0034100514140c050090903090b506650400502410310301ca00141145485100700c115403000400700000c000503040845d4220b405085008030318010030800d442c6940e15280028001d4004845548002620141e29400c249c0184 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 264607095 1250 264605845 264605851
    0x40f0e070f050702040c020c03031821030a0c1e03021c09050d08030402040e030c0618010504080702060d06050301020307030f05010509060105070b2e0302010e0118050d080913090b010e 81
    0x2865990403e040b82d001c010052007240318007020341c0207103081c9110580d001c3c001042c1c1c0c0301f0b28010502080c102e0300c0a00004068442c070305008007035041e2070203082180000655a400580d0700c1d10180c4c0c1c503024600406441d002da4407884121206042040801d50003040c03a035916841c902c2d452142c203001000c2120411a01e00c40e49808c085598926404101000e004540c0305001510100d291040c59218a10b903a01c0205000d00340e4100d1410700a19171310440c0601440c9298600034005810140c813280020301c5031041c006c0c0b00b0640000c00c071400c003015412a00050100500071034882ca80f90350b0141c0504a600d0000404038900000840c0324a040202c5500800b8103a4400c0c0c20306455954658241c08041d11010415000c2c0c004400c2c030000195092608442d17051040140718650710024000c03814280c20725050001e070150b00450b04101e030f04444101c8008544a5001900c203007040310070ba100c0e00d461190003868100c242c0121482c0d581000100621402841e5402c0ea6034000c001d600d01015 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 264608345 1250 264607095 264607097
    0x22a040f0b060f0903030f0301060f020f0706080c0a02160e07110a0f1101091e03020111012a05090405010308090307120f151d0106030606090c14070c0b040f0e070f 72
    0x14807001c1c035509500b9000c4c101c00300014046078504100d12242d00d032141c1003640044000b51005162868441c1d043c000c120440d42c4510090000e282441000780030440c00915140c0b4504002c0765600c0360500c00c002c0540040540302240d11629244c58409003c01c8080340c0e40740200d0303005038124279100000500400004d812104e50b0310031801540c3c2c1c210505444061450400040442c00310b0811b403081600582c0d0341d003080c99085a41d10714400500144001c00f21130749541d00d012145202103000207000c40c489065444203004100c40c0c1c404c2a20b150003039400e040c1d009481d04c000801001008001000c07016012011030350065030f983d0001c0c40100f10f064000304039006050002002130144040c0d0341c50031410800200e01070403403005085002000400484040e0b45070142002070040920a0001600c0d031000d0900902003c3c40000d400c2103107442003044c2c000c000207100c0301482a010180e1029141c1c40017029070b5595200010001e202e1103000e8400603514810110b2066070240c40c00400c00045 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 264609595 1250 264608345 264608347
    0xc0e010c1109060f06041403010f05070c02131d07030204110f07030e0f041b0f030507140706060b07080c01060b070b010b0a090b0a030204030507050901081c022a040f0b06 75
    0x2074041031208050003d0901e641140c00c000e41900580d41e01d8003d08040d00140480b0340c00b0404903001c05094450750a40b452741c00b0b10308000e00943d161b101290480d403035015540e0340c000600010420740100302140402e40034150b0400f0580f090b00000c03480e50f045038004c80f000c4c030900b85202e034003040c588509119500720349405c11881001a02990141c00b5010006240d26400b070507090105058580800078424070710000c1d0600b40b00076402040304aa0840240740400c207a240c402c0c4040d110036250154240304540c0400d212042000d150410710150108444194070740d40ca44c0b4000c102600841c80160095003080c0f40440d0414003c010349140315008000c52a0b01c0c0d00e007807100c030b02607400740c9504c0d000c002e50b03144042842c480c0e550040401d94841e640044e03446155040140c1040803c1c0c111602c110400c031300400240f04006030700100e100e41c80c0503281914545d40810303490301150194031507507810310381071401c0038045507c0320080050050b0740038170881a10303803003a00844039110000d543c0000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 264610845 1250 264609595 264609623
    0xc09240c0b1e0105030f06160c0210030207060516051c0905010e15090c030309120a02030a0c0f05040b0303070b180d03060608060402070203070317040b030103060f0e0316030c081c0c0e010c 83
    0x750814031218030711f23901e090481380308031203401084003501c400c0042d001081c2c0005000c0c0030000c140c4034440d40b103112110054030403c0b00ca9030081052203201d05001c176500c004544041c2c074400c10342c0002c000c10f90020003002610003540c0040c0e1100c441c25162100780c0c4004001690f4944042103044101c81d00401541c6401c03175140800c40c8003c40082c018100b80b0480c00710754010788040005601650080c0c07035450202d40341c100e00f407050701c90b290010360150303003000c0201003161800020380d88000e91040b0307940a207983d024807000712240340ca800c0c404540700d000d1a00c91002c0d019402142912002c0e500c210745617403100c05000036485940b00c025010b42c0026030810100d0300072401c1c0026600010070603441c0039a5490700070016002a08141c80a9175900c05424803801d952240b00340003484817002d90708000c0702a8401c43d040d203c051000d41404160a031a40030020301e2001c40b031500394030b0b40340c8034850710005410703600400303401e92201c0201d0741e80d0205a11641c080e4247e041560703844030480c02c1e424 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 264612095 1250 264610845 264610861
    0x60103080a0903051e100e060408091c03081009050903221205240c030417090607110a08060c0a230403030c05010c09240c0b1e0105030f06 61
    0x948a15101c1080148586010000503810721091102000e00300004c820102443c0da0303103041080c080f91a00c142e511b4040040102103000c1940c643c004c0d080000e45880303c4140d0081a440c4403102c0310403802c40c50281c414000c040d00150300c0c60042c8408107103400c1c50794135a040341048510580d84210503600911010001800380402c03940700380802d000c100c152650b01c011000c1d8000c0c2c42c62080b2840d4000103aa050700f0300c003860034400c154180fa03585172014144041c0c0403040d0300c0050006400d01001000024a5140b00022180340d99005042c95a441c0784500340580d0094100c401c00d03228002c008000650301e100011424010130302a151a45080c09201e02598402061005c0045c06842080c804803482e04d10000741c00114040d45803940ca2501d0303407a00702d003107868100b00c580612655103001d000c0e0245403014120500c00100c0d49030102c20b0700180603900c03614580c40c010f10030403a0030100540c411201607403c2408454001034a0181d03218400c0549808508071001400d034031610000c0c06039 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 264613345 1250 264612095 264612097
    0x40b04030638040b0913021e0a180e0706030902090a0603030f0e0f060a0c03020f19020d0510090c141e0405060a0306050a0203060a0605130b0a050d050420010206040506010308 77
    0x250b040104002900301d1480302095629030210391100c1c800c00041340c10700560800c0100e0801207120300c0d5551030380429000024140c0e40b4030740103403007414819208c1c40c890306035590300c084050300303054084035810340c4c0e41c1c140207015061a4400300c5c0a01a50340c0030a05a040e02c5c054030040e01d5043d126403409045200080b54014022200702e5071000003035a1108842d11807800802400d409541c4a074035809950502034601810680c0b0b0464580c452801c4070385944000d40110360440d030458040c4007001c26804c00d18909100200c800d000325250071260420040c80900704000c8a05c032180305102c2904a1082010009203004d5500c004480c0654240319131901d988040d500480040036101c4882c0ca9450f1441101c1d8110b5604840aa0010500c055803508040750801032049107012450241c040310407030700741407241c410ac8464000200d1481c403194050015100041c0d070380714041004d85003034241b03090400b84020b40f80011001307103a0301c00c03815403021450f18890b0350040020a01a4a540d454041c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 264614595 1250 264613345 264613451
    0x120302030901091a04020a06090806010b07060b03240c210603031b0604110f03100507030219120b060909041220010c08010509070e0402030a11040b040306 68
    0x402d560711406140050b80528404000b583d11044062403442e2034414003d001c1d0045e0880030a10422042c20440231400003a601d040d56540c0302c10540361262031412130007421b0703030000040d81401031754980c1d0719009945040c003103d40c9804552031400e0711081204450340c450400840504440f00c0700796106c02186050140e0400d00c007070202e03440c0103c40165a40a40c1824012000d650001e40034841840544000500c291a048031200c600141007070000360341c0c0000300700b0740400d50f13155000a15582c4c00795060792440d01d1044c032814400750b0108001003052010158005116143c11102c60302400e040f025900600406010565145c40b251584111500008022020059050aa00c3c108142482c0380c1d40110320310400030545118641c0c0c00f4052001c1600a103018512100401290907486008941200d4003520016034079220070341118060007051101d41800e800004000032260241401801240c0c000c3e8400c01024400050754000341d64086800e61101c00c0d42c002c0f52109042d02c0080b082 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 264615845 1250 264614595 264614611
    0x2070302040e030409020325030c120903020a02031e061308041a04051f0807020a0809010c0f050105150a080f1b0f150901030b030f0d0f0203041d0414010912030203 72
    0x41895a05c9481c4402c3c1da004072458134000307a08618209401a4025081070202c2142c1024040c2c0c169111004010381544081d000d0200c1d29090310a0504d80240014801190094243c41660300c1e0b0110303074004402d269140903818850007000800a0b074102031361050550307000010714a06445e2088206c0349805040b0080c007980820003000666036505005299004466038a100042c0d901100160a0f550020010002c0d5000962000d00155009040340c4404d0001d0030551041d560740d007040c105802d280328006101c0d40c41c050600060031110140103d0243d0210390500c20a521901426100c50390f8a103000312580c001d9818417074441b5800842285072102a0468040800b00000500304021012403ca000c4000051003a45540c8c14001c25900143c150010039210103500d19407551058055150340400808907c0c6500b01d6200740b0844d002400304243d000d5048031000c4455100440c01e95040703451090700601003200398410f000c1c64400681003001c0c520007406400e01a4083e610090000c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 264617095 1250 264615845 264615847
    0x70e190b180714040f030204141003061505040e06040b010807030537060506040f0605060304023606090609010b03070c030216030c0504050603010e030f071e030e010207140102070302040e03 83
    0x3c40c1102000c005080100198800440c3d4245940140701c01c8030b624001c180f080040728810852010034442002c4200c9901440c0056800700024512150003695040203a000b4244410760354640700025042e4090342c00780013480901e903681d080c42035481e009803200a000ea080040064020074061007404401c118040c2ca482102180c14508a60880c15071070848400355100188031107424148a0700c0c3d000100e41c001000000e08100001c1c001c1d00005200034461540c01946ea010304002009203404240482065040d200c10401445586c07031007254a14015603c030000102d591501c1c4911a04a40640280b680341d601c58500403601950341010580941c270403541c4000107552406806070046020341c96802506007000c040109685002e000f141c420380c140507000c0c20040e800700032128158900f400213966503001d46800b0300c403074041502d90301343c810348008484149600301c98060383c202002d03402d40c3d800c0d513110b207559000ca40c0c01d441914010390050b40217200505141d800040f030404c01104403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 264618345 1250 264617095 264617117
    0x3090108180111041e1406120a090b040b1501080402010c0f0314040602150907050901060c11130b03010f29031c030603020307061e080c0c070e190b1807 67
    0x2030b1169030700039401100b8000080d0140344803245c6107082c18001c1c00d100e044074000d8100100c0011954020140d211900b801c007078010656500c4150b00c4000c801d5407042c02d6078080d103054140304403804811a00c030403c1072029561490558481c8209a00c1140e0523181e48001c1c100b207880c0c2c02018605d04030101c003031041c611346440b00310100101902c02411940c0c01054520340201d4045808800500740c0071080c3e0101c00288165910002d400b03041d40d441c0c0c540012903681c5800c1102030240f01002c001d8001d60614600c0c015000550004444154103a00900101c82461240d00423190000c2864141c1002081c00401c8800041c16625034050020101c1d00320340400e10341c0aa00510411510001c2541d8107420011400c090001100411007410840345840c40040349048283c00d01541a080210000000341c01642c1038050398516201c990440307150781e491b0070310072000004c141e0382040000b805820880300c2005138050b02c40c0d0554050071680e28004100094442c0c0040500100d0a01c1102820 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 264619595 1250 264618345 264618371
    0x20f040504050303010f0b0c0706111002070305030f060d05100c030f15081e0309091009150504051005060f2a0319090608040f0201090f090e0f030901081801 69
    0xd298040c50280b0301655581d4544541111064416070003451120024071089042010108415007141c2143c1014048040416005420a0581100801c24610201c1d003601490b5110014601c10760031001101229210402000107140c050700004040754890059440f5807103040c1c00419000c0002d040c04034403120300c04e0151050303941031610300d0301c1a40c01a07000c1010035010840c5255484040d98920360840030202c41903124421190214003580010000c43c41e24840100680c0003048003c900300300c51604604102822500341c1714040c85130f414240450401c030072106d0354804440008019610748080c40540d5511900018400b103000d0a03045800c41c0e040000e882c030a61405885e00285699540c04c092011819044040c40310400481c00700901103590040d8516070000d400c108010010001d42c070040700c0d03000d030a400c840011580604000380f4000076800c140c0381c0c042d44000351411695081351060762802451081800500c0305801300b1822128141c014205000741e4001261744a50074032 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 264620845 1250 264619595 264619601
    0x30625050316030e032a070605031009050601050f030c03160e01050901080a0e01050403110d0504060815040e0d0e03070920030c0c0d050d050a052710051602060f040f0b04020f04 78
    0x1b0002c134a0700411203c00303c0b9020900a801c082d01940c1483c6003981440c41c030541502040740104001030303540c5d00204142c1d80c0643e0503580124240c408140d9245801800c1003983c1c0c00590b000303419000c410511034420750183e40406140c07841070f500c0506021254004440040c00a012807004650341c8664000c4500280908c40c030980c040e03265942141c4a10030044d10700060001c944081180600040c0803295001103103c2e0020f8204160026290304440018020106607803024141e01c02d82c544242d40c03c0d040a0307154809401242a5401903640f8605403040c1d542244040c80c410062901c030002d040d840a01071078000c1507a6400340d09105613072080b00e24015901ea07255000c1103000c00d100c500800e550003400c0d840085120140494101510241e804c451003440311019004c1d00045596180e00030841010100100401804241085142440c0701c082c40b50440005000c2c400004000c401c1d038807101401254088c0c40301091407150f4032101c0d00d6403030190040b030340414800711140e103e6031140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 264622095 1250 264620845 264620887
    0x5030c0105040219080303060402030403020102160309140103050115080c04030b010905061f020a020135041202030a051c020d050a0506040b030f12030601090302030625050316030e03 80
    0x200010742800c090041000f1440070f1005204000c1c0404028044280d02005494000c0c2098a0140c1c07680ca8a2600340c0c0a400b81902c0005443d69a00c02841450b82c00201c1d07004550b04c20b80c204485444450046064400900070342945030011311042500521a1004aa1090340306000340d00f81600c9680f07035075100c031082c0c0c400b2b046c0703c1e1203800740310f518034011080c01c080f0364441016a1a44082d040069182e4400d181c0103814002807035400c2151841007980d05020038507044070f1458030040c06a130715080c10390569007600c07042041c0f080103090034000411103030545500e03200d55003080041c4030041d5521a030521454032050b02813000742c000c3c0c035082c080c030350240042e40070100741460301c60203000445d48880300f4140302e61300200701d081544d0004601c2c42c0c1040040000d1541e030b40c0c0e034000144ca000d406a40029090301c607903401c000386000d03204010380341800f00a10003410124601d00403540c0d400141c6401400620b404c5966070b681d40640d008039003510100d0140e0703041116a07001c2100c005203a0b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 264623345 1250 264622095 264622117
    0xa0e100203040810050906061e0d0206090d030522081c050d0e011d01061a03090312010b0d0c0905060a030f11030a2304030c0209180a0807120f23070503 67
    0x305d0501542080602c0781c41d502c15410f840865450700c0b04140000041c5004c0d50441c09419000c10440135501c0349801c88501100181c0070a007016018030300109240c1c4454500301400210b9002020480540140e01c004c4032400c00040c100e00c440d030b045807104c0d07401f68003401050100401c00307102c000303100e80180c000d0702c4001000029044002d5111040b0094188044141c0e0791405c1014440b081d081c1822a04510110001545a9852080c0680b079440340a19000380000c4030400010780d494094000e0112145191003032151100344802502c06803020f01409a000c1c602b400044541c3c0c0c4241e128080f0911703c2000800e8681000d2421180b5038000c2e101a41d1190301d8066400c0c140b001e00709620705001c802c50728203085141ca500c8c010580851010024864030040011505007034468010000d41c0c00500700751502c80b140d030f140c603021aa10907a011145200c83c401451031160182081c0b01c81034040351a05003a00c8040004029000310030035007989024002c0c4800000f1a8003000603250703070304603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 264624595 1250 264623345 264623351
    0x5030f0a020a151a09010b04090f090b04050a021305060904060e031204081902060105030714011101152103020d0e030a1a07020f030406270b07050705040e030a0e100203040810 77
    0x19081200e0f403008042d0140d8051801c400041111f104404200c0382210506080051010400e6008001405c280e0001030100040d141c280020b019000c503c2c40840d5208442e0071221004030303141c040540748c0441d03203580d101e003c940c001404a0701e40d800912903840d005044d00d142036403800360102c00c8c1c441682c00740c1e0b2440c3c0c081007400400e51240d4400b100d000c29030006150315854000040d5440086010310840201401c0c0d070482d0603406182c20004403807008000f40034490800d521058003015901c07400c400c18000704c20b9002140916401e120409406601420403042040805e442174521000300603018458040f00e0004262003405143d04900060619642e0f4142104006e1034150400d90031843c681040008008554005c9032600341000c964000c0b040c2c0401d4a0140400c041c2203500280840070300080c1d4004101c004941e03030054030310845081203524540d024641e0f99004882600c00420014103c130b81d0180742210071603000501da481101c0c6815102c0107490304020b15100114001e5803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 264625845 1250 264624595 264624611
    0x2062a031303081e04231c031808090d08040f0602060603011b0813080405040f1d0304050d110f0301180b0615030103030e21030c010b09010305030f0a020a15 69
    0xb0388030381d03566003182d01e0b41d20000075212090409030341c4c400c014000401e551410001500c0d07505526030021a0305008505a8102054403200d0030748104030556003100103440e21280c280a84402482e401c0700c184c000f14000e04024114050012100400b1300646400b00c0c2448005014800c000307085001d02625405040c4505001c01414251005c1c0c41c075600302c6030059a2007010882e40700e03458550104003c09100c3c4080c0e1981400c500c0c0d07120715000a504681880041e07032a44407981c00c02d420407509c5009000584045a42c20350f00c034005e5004880e84603c20040348400f041c2d6000e0043c400c0030740100540b001081000000742110600380181032600703660a418024400d6014100e81e02c504280c4191441d40850543c4240c1444140001002c0c050501400c0320142c464030514201a125011240034262a072407646603a0782041e0049080c560074031000081d5410500c076568104c0f98083c00031818091036500c01001604004403020031813241800e02004107850000e22540c2c028461400241c1131 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 264627095 1250 264625845 264625847
    0x21305060a0c050706030605120a08071e051617011a130b1e1005120609070c0b091f0e03042903040c030c0b0a0e0f01020c04050903030f010f030302062a031303 70
    0xc820401c0042030f0040e10130702e80805c910700d00300c8206030341c02591640130400d44800376840301410702015205100300c81c006070742401100d001e401981e6064007000c8101405030411400c1e248001c0d01d40e4040040040b0424030740c20007506400466080d0800420700d00098030106080345080f00440101c01c584060240041c14040c0c802140c400061400500e03103400c0310325561943c48040e01460040711500002100b0314400c441240f681584184903090074240303090100e51f214105028402402010006100e08040c60f01c5000302c807121000c040c6080526108020f03030342d96801c100c000b4031050750002003816082c104006510031481106155029030840c2080414070485401000141c5802c00c04120703043d400224100c4031103411500c0c1c90003101900c00407810308a405240d1a005800d03d000e0203044071012016500c03504203407500e00200daa82d03029111907542d181c440680580c0040740402c4407120710059001c40c04407003004945c0c401a40c841803224581c0202c4245082c1c001c000440c02c101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 264628345 1250 264627095 264627109
    0x1401020709050c0403061d0c19031e0b070207080604080a030204050a241d090601110a03030e0c0f01090605030606041503091a06130f140106110709021305060a0c050706030605 77
    0x90010345d1f480380c0011034011a090f030318081c42100718869880642d000403030344440c41450000d50b52003c09080c0702d0520807200e0110501291084500254040018200c0c500c001000400c440d01840240402d03211602d0310491540080602801c040c0c00b000301241c0758a500c5900c10040c50055074550070140e2614280075103080301c1122004001d00411204e80d4242e82840003090080101e8a60080b40c80e64001681d158001d41041452801542031210902da0181e01140c004000d031400c0c1c3d0070f00441c0710b08020401008540b100d0102d03131040b07030134000d441c461006140c0c01800030f40722900c1c06458040304107100122400e070400003a00c400c10342040001801c2025181c40c0c0c500c10700291800c1c81c3c0001101d0720b42c0c48903040042c554811100ca41d15a0710340100c0704c809504800c0c03d049503120364000345a041001c001207020b114900c400a242c02c801d10890341c2090200a10640c0d80741040c080180691002c4048800c00040281900116900b0710443c0014605034030000350710741c50f100c10b00282c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 264629595 1250 264628345 264628361
    0x30c0f06190506150a020709051807080a0308040f0c0302090a020d0b04110f0d021b0a0302120711090705090a09150f05060d18050d050403060b0301151401020709050c040306 76
    0xa054104003d0159945800003513a6403503011400260712401d1407441240380500a50141b0406401c00050040c07182c24101800810480901074850040d103485903181c0d108a1000020005520880040c001c01c5407100740c0121035120b444165025540c980000c0c82e0003509a48100102e980040e100039005014402c003158144142d4051201c9440b80c407200300d040c0141480c01158000000f00701413205007540c101d404e016080c1841007816036010a4680e070f50740302c0c000c046000d803040568090b070070003226051b1000030b41c0c130207140051204104244262014040c14003410b00100780803094090741d440c14603c0190007504e6002031180110041c50700500010362005011409403101030055403034050032110042d1403c00c01280200f05010190500b01c4110405080c50160140d0b21500784d030b0000003482203c1c041c41041c4000c00c800420103088507003007180203079017100e84c6104001c00300309100300100050341401540c002664420f6036105445044030b086000c0e100020f0217100b080690311032605 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 264630845 1250 264629595 264629641
    0xb0d05030414042d050a020903250e01120206090d0209070c0b0601052a1c02070312050c0c040507030e0304030606051f05030c07060204050604090b090a05060f010503040203030c0f06 80
    0x8013000c51072440701003040c2440b0745041129190740c0001c0b03404921385c0448070881d0002c0e003158013568402e909600d42e00c40c2c668101c0340d83e4071001c5001610542d11042e05040e5202e034041900841016402c104059106943d20750700207070b0340c01e014005a60781d40c100603c03600d616114490641c40c0b5103046001f1540041c243c90502c8428808400140c00042c0ca0320541d01c04404c44066100b4022001803030300c40544000146500250004000c0e5580411100116445484000c4000901c00e4081e81d59001c1e0900c00c40c070540c4104680ea81c02e01d4603800c1690402c41c641000104804940d0310380b41140e2142e0000e49106031070b000c0410050400c05040d003c84000e100d00000041e200e004010250312000e040a09087e03004210700301807180f580d04481c0145802403025540d1030b0b840000d04040e1940a03030b0325204040c02000520080e1440c0030705441803200405d10b20100c068800103403501d42018005903014402070018007103840042040c0054041c500d0006d099620788014107480e03080741800590 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 264632095 1250 264630845 264630881
    0x507050406021e0708030c1f0614091306020f090102060a020306100c170304030e0306130201021009060b0406060804021c1101050901111209030106080708060103060b0d0503041404 79
    0xc8154082103056140a0388810030b141030f180c030105185018041c3e0800915800002812600301d40005031400c00c100101b846c02404081030701c02c520840302c1030320034444001f0074001114034500d010007445501ca051a0240c81034802130303488203401c07a002801c3c01110340d07800043c0d203800d96804005003540505103000543c5107280000201c2c40914500443d801403088910b0356100304001c680102c2205100111059101d140c107080003071001c0e4814803040c4c0a8052600882d120000d02c40004c801d9580607001000c481415859090013010340724802c0ea02c003603403407843c1e2256595a0244000810940c3d92701e4602e810140100031041307801e003503405640b4070005120f41c00101d280c15040c0c45c04100342050346d02c8201503c01a60450509121100300d4095a0781c1c1000040405000d403410901c1034000b0407070131703807215a41507072110b481c010400c00341e1000004100042c00340d084284928000350582c0d200b44040e0350748a145d500150400d44540c0300741c0451602e1414148200405001544544 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 264633345 1250 264632095 264632099
    0x220513021e090a030503030403030501090c230d11160605060603010305060406020304060b0d050703031818150e0106320901030e07081209130507080c070201180b0d05070504 76
    0x550304060141400403050380c007294020a03561140b10b010001c6410401b034070b5072850180b4005004182c2406010780040c9003000800300c0342c0c412603080801403450070b14020201c04503035101100c2c0c0c200c4104114a1625018140b80c41e9440c03102415200c291052070f00b44a005074a00202611070090140340600d40c107000400218400003007540d04540c000100590b2a01d490801c14040c01d4011116900304100c01c031200d04012000400344226802a0354003580314032041e41031560040148a030360446000720b0303104107400130b40742e02140d075100303c4007024013005544039085400c1700426800940402e806010300355050440d4103051140c09441291901c603840030500701d070483e0258405981c1095036402444d140c044003000f0300c00141110f80100c4500c051410300500180e800900c03004d01880010034641383d130b850140241c0d40034044c1602e96115503a1071082007841900310b40c01c10390410040c02410090103005d28407120213002c034007002c25540c900284160040c1e800240101d804c101c402c00c82 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 264634595 1250 264633345 264633367
    0x51507050106060c1e02010e0d0f030801051509091008070305030c070b04060c0f1a09010c030b0405011d0903070b0708180a1205090604080601080a0c060804050c0103020304060222051302 82
    0x3440800c5072a8061060030710b01800100d900c8c40d8403a9003a90001d03208401c04050200090100300350a1190f0b0720151180c1e226400e2005885611204400400051210a1843c40c0600340183d212003101c2d40303c44006d0317403012403a1030041c05074400d41d0140c20000d0b02d6050300e84284501d0b0041c100307005d900b030328141c6400c0300100103111142003c3d01c0c07021002c070084108620f9020313030000030503849041100d5090181c0301600802d40050b03494080303440c0c1002090503080a004190485111152200d64040b4032923005140c040d0051486505000400101c1c000a0b0303515901d5008600c079903184405403404207003c05e6080300d20b186003026980202d00c480c0011303004555071000b00b00c00d40340032170300c0d266248003280380c0b030140c1d40200740030380a82030007c1400c0301c00007004002d96000c2c2d041d2010b120340d40c1c001990100030545000d445a0404840a9100e5000b50001d54206100ea03400600e440b4507400088142096590303044841c1d0a1040c0411062801190340641c40301702c160300b10725260802030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 264635845 1250 264634595 264634613
    0x1e0306090c1303060f02092e08010b07170f16020a3314030a020a0e12060106080c0705060403020703260d0c09050315090111040302060d15051507050106060c 69
    0x70004015549415205e8220b400350740554511600c040e144c3c81c0c3d800b05507018403a9068040070003403203080c42001c0c04101140b1401d241812964a0036210340792400f551502d00c0c01c048404103e00c6c003400104002c0802e101c10000509542102900c8000920201d10402119a03ca980544030618481c042c800c0c5100d076182030201c541c1e0850600c0a20400806800e440400918815040003e40130040003a5922103070000c260044444d0754a002c3d0031015001c02901100f400c1d2020308503030001c0c5c01131102c10f0003544502e42100405516070300f803a0740e0790344151074084215400c80c0160070140c0100100000d08282d04a24038284801d005501540400c6200c14020000c0d04903e550f1174407944c6c050107019100b440c1c050000501520748101c0341980b4601802429a900601c035845c20701c2e510303035009001094900380c07640244820b1400c10702d011000c0c0541000c890594003843c145600103019034501350078072022407024286c01e03110b85403801c01c06c0c2103425541c007070070901600c414040002281c102c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 264637095 1250 264635845 264635849
    0x1030b070807200f030423060a0c060209460501023c1b0f0a0b090a2301090e0906010501120e19110d261e0306090c13 52
    0x400e240d07000d041c000040e80340084184c8025954000010081481c1a0405000710103c40d90080ca1408012400600509120f541c1c41480011600c820810005280d83c005161040004145040c034403092050320706542d0f981c2d44000c20b8a6442202e000c400340c01e000f60010390054004109100700d15220010b5254070807074440c1008260000801102c1442501c807820b503048003a5450458585441c1d58a555803640c4210000b0500780018640340e03a103050083c440c20404017401007040340740303007010015113904035002c01503001e4155400401d8074000d8955559440700c20f205100c00d1100c01c0350004d07140080a400946007980000200000c2c0030300011301034112082031030b0000041d040d21421000914802c02c0e030b0a00d41c000c0301c1c40014a00c030446100c3c103010340204c0d0080e8440140c04108075440312011002442102030380c030f00580030203801d4062010084014a01468003d400226800512032001d207030103201400b0040c0045424601c8566a000e40000360382da1902c013900340d100403405064 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 264638345 1250 264637095 264637127
    0x815060a0c0203030c010c02070303021912140c120a09050303030402100f0504120503070204060e240102070f12120809060c03100308070c06030b03120405190308030a020301030b070807 81
    0x31080300421503c0400445d034042c02281c0007040707210600c3c00001d44404041c4002d034010b2060458100e6445158003411000e01c0e440a80b1985800e0a454292888490214000c1050000340710012aa07142400090384180100302d0903a550b1043c10400b0f045084950000c0d030003035009004000050316490803420815081d03007018000a80003000c104e469100750b81100003110004905d4000b046000400303003454501c202c8090000315140d244140320f01c04203d401c441100c095421280300c800311340b210450048810320560b1619600c85401c15009045c0303a00100302c00a50040701002e10070343d944200c9040d0800c1c900054182003042051340c3c1c81001801c91410b41c0d40010109110510340040c3c4402141d1042107a52941d10f07030300f86a00c10340c0c564031a100c0401c0c1880c5042c0312501d03010030710000c20300a10300040e0038541802c0911000501d1007103091503002200d0004004101900050b5105110340341c40940c3d00e605500d4180b120060291001007480358410500618542040100e9440c0101e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 264639595 1250 264638345 264638357
    0x3070b04021909020a03140402010206063003030405070504090308070323040f030206072a080d0e070f0504060501090e0915070f0e0d030801061101020408010212070815060a 76
    0x903034000a0065601c40301194000e0488030303400a8a142c0741e4028255018040e10304001e0031140c1c2c1d80d0315490b07902c110380c000e00582116001903420328040845c2d56418a0000e00d0081c280581c03c158450410b10032409000d071b500200070801000010484a005042d09540131322203c2d80b9030740c02805200010303084400b499255001d11f80c41c2550f0200c8030300d6917080321203401040d0401c1d0030100c0791106038031003c0c2c0c0103004032030010309014003600040000c4003540703d0000c0c181240401d4500c4641c05450201c4203404100000c9240806034003800385040f809402902c100362406141100190701a400540102c1c206402001141c0e00b0400b0750003281c0420501d0142c0e07aa0700380915040c82601c1c100102c40800303600a12109650041098141c041d80c3d80380c1c09615101d541c10070204521894006000401a10041c841c651050406080c015141d1001508241c0c65801071800d9801841c1980c100b0080e00c0308002c03d07168080903980d001982c070410310400f0344100d000b240261040208900521103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 264640845 1250 264639595 264639601
    0x3030f0702100f020304110a0303020d030e030d06170706030605010206130302010e0604030509030d080c0a0e03120a08190c12150513060602012307080714070c0905010f060203070b 79
    0x4001c0c050941d105032000c41c02c10404030744003010f0f030003500160303429a03150b03035103001048007410200e0100040d00e4054008060084884000310068800c07003c0502c10340c00f061000f403414581c4d9010395406480d0780c0d2111900c0308060700300b403442c5c0303e850350040081508002040210b66000716842d40c00904681107a0304018580c1000c0e400752409071140b0700240303e00030401c002d0684c002e016045008044054902d2002ca0740c204440e544000d403540c000e070364003c01030705038403a0181c0d50034034661801a05840c031551101d02c401c036140c3c00100114021500d076004001c9090544161400c4800134181c040240c03411075a030003420800203560010040e681c481d0421010840c0071322035002807600801111140c2000070122001d041e261081c070000d9800c1404400c4d09800f000075101c4404d8110404c82540d981348181240c051a0152507881070000c440340c08141003002c0d4006002c11800b469004401c0c5142c0141e8504031a416030028002c0151401d0070f00c801913021084500030b981080c85001552 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 264642095 1250 264640845 264640847
    0x15021c091727150d0f060501050405010207050d061107030201020a02010c260411030f011409210d020702060c061e01080a080f04050a170c01090b0d050a0b120c120f03030f07 76
    0x5140500f0310901d11404109044028819001494002d0140b0130500420b40d03600d0040d00c0c640114000e003405a04204014421410501c020141a82c015a00414050103103030038026513030b01c200801d50050350000307903500180390240225808020980341a8111005003c50b26051009900740d040c0030101e050040b0701844814030b45c0384000d200040035180204104840c031402400403100003120900e00c0b80004000d60800700710318618121805007012444400c19000c030595000d50a40c801b403503801c1c000840542c48604c064600e01300e40c0401044181040340c24589180000030782a8403c0b03440500500000001041192103c0e510508454840e11003102c07852103400340d0b40041c0c1e04039051520002c0c4407840d0904140080b185d0074223403040301882c0c900444049205000b21003150b070080200350a00011644603e41c030401482001072070454050000d4000098044010382c41e92140c1ca0300c40162400445041140b504407005000c0c0c1801c500e9440d03102d000007480c01c80d0404014000405503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 264643345 1250 264642095 264642109
    0x403080606130e090a2009160504030b010306050a0e0f030a03020c0c0306090604031202070203031b0a061a011715010e011e0f0801060e0102060415021c091727 70
    0x1910712003505004528107001031950715042002d0a5500c21b005d50155801e030740c020030403070070860b001525040c40c564032a08201d84940020740d02c0320401404101c000081900300000f18043d40c498034010402c0d05241c2030a1702030707660440c00b2841a81003544901d0110600104680f40e4203468140076869481800d00c043c28440d031001c7c5540c26000700c00400400e1040415102e105503c01d440d6401070010b0f1102c02d0f030880c058a01e0017900350348104079400d80409140003202ca14030001044444128007943d500d000d0700c408004000c00b1040c24947c5514643c1c205101c2c0940c0200d00c03d0420300e500d0107034001741e2901000340c0b856040c0810708881c410164400d40c0780d071a42054400d0b403020381181842000348844a000000000240c4440002c41c42c00c0c400c0000c0350b40240c050340141313165140c03603e81000c800350754018030070540c0e13082143c00d016000307040c4c4207c0c3c411256000000c116059003000000e4580e0081820b4040c3c40c1085617038051601e10170402c8692411090901d8011000c101140c42 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 264644595 1250 264643345 264643349
    0x804060b030a230f0f0d080a18050d0801120c140105160804030203060f0106230d0e03030115050c06041103010f1b0e0306100b070206090406230306040308060613 71
    0x1030b012071002c070b203100c502e02951000210040350b0841e100c0210400d40c498035860800311096951b007080c8210b01c0038900c28120302d42c01c4520840c00085420310001d141d41005030313011040314030781c001340c1110308001d0300403030824010718a03120714a60741105581c0e0400c50000354003a400c0f9040d990030803012580d03c00ca081e68802e807140701c007119400302503080c0000303079800c603200c200d100f03215a00002d83c0c0d16404c1e0600d203040f1411230b1105610501c1000c4408003155103403245408071a0107000a90340c0340028000d00050801ca1b4000c1c0d0b9495040094820045180c81c0045040c800100107070107021100255059005802a0480c042004400c1c0041c1c007500355040074100f280c1c10007521525804511107001004081500c910100e01854070a140d111402140c03c803024840f238400410100300120700801c1d509100500c120b2030b2580050019040312103e8201c40b40b04d46104668104c03000d45203890080c920340480c01401d0034503150b90014882a00206042c1c01a0004a06161040c040c0711b10000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 264645845 1250 264644595 264644603
    0x5100c11180f0c0f0304020f040b0a060906120507140d020d02071104140f0105010e01051c06181b030b04181104110301081207140d03021801020d0804060b030a 70
    0x10080d031107801041d00c07190098900c816421540c002080c1c1c1c1c00b41c0c520072504c80d41c115030710907403c0d550346800300200e0541e41c407180e40d0025100c075854015036540c81480300c003400c002d48070884200e09006004181d803005d9804070204070b15050900000c15003200b441514900f80c448610f82d942190003222000c0d003c2c00c0c0094810500200342d401c10880080c1001d062484266001c00c00c242d1043c1940c0b03502d12080d05d0f026600c1d100b0300014041540310b0301506103181810b06003203241a80303242c24100e800300342d08071001d00c2039507422080c45000007800c101510142152070a2203152a840c110402c04001000140141541d0704507400242d192604960300420000b00074001d0402181003001241410f288800c1c412440c08040c100c40c041f82100f6079042e500100000c00700c10141610100c026800118152004c000603042e074100581c4c02c000021032100e00d55000740e2a60350318100011a16442c04240d030564000c5542440b54a07880400310350700c10f4021402141182080002c00c1c102a46414054 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 264647095 1250 264645845 264645859
    0x9090b040f14060a09030f170c0c03091905010e03070b030f060a0302030a06051f0b0306100507050601080a050c0103020406020d1d031605120304080a032a0510050f0105100c11 77
    0x1001e901c58540c03000700351714000d446200700040344d40c004441560709903101221072880303100800c041d901580c019040ac106c01008403450309071808001aa2100c004584058800160b1800d12495074408882a0541802d070010520241007460b410068080107100d014044240d000040c22940c03010300c11f00042d600581a01c1c001143c07410540050038040b11010480d1090304591100b203204076001c003080354002c4840a003981c0715441041040c000105140040210900290012800c14030445008160180007490017001910b422410b0400740c4210714103040c0305001c1002002e4000c1081c03071201c00702d4030f0040415a40003680e200742000424039140c05100f8150180100c0ca091b400700340036200201c070107064103903a1000c001d07074a109138052802260401c00204000a000f00f00c10481000940c0046c0007001e114042c0d4060403600711016a0290b00480e41810400d44070310480e5041112303e071092410758103103008034800c040401e161004101d04810000d06102207040c00d0590310314003c01c55 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 264648345 1250 264647095 264647101
    0x306064103090c0a06021e150c03090601050d03050405040513081308100b0f060a270311011e0f020a0c06022109090105060c010e01060801020a0909090b040f1406 71
    0x400d8a03820448403540b20748608100d02d80d081c82c01e4960201150055030040c40112202001c01029200300d0490b06120b100b414800f90f021185808181c0c4981d80c60310015480e4580b0030b030118544801a4441c0e0701580c444800c07180807030790180c201c3d019580c1c203940100303540d110109590b43c1d000030010054032075407010a02c010001485004201281d5050003140c01405031b540d5020110384d6418451035101145c1d8900384841c2c2040000303005101c9071414840c400030000c0030f01c184c89031558280100320905186e014020845100c19194580d039080c40c02882444802e001204950a41900c81d020b00416504520a9a10811100101c15071058200044664404010390768110300e41340c1108030652040c013a28510941e900741c0b096501c0003080361885918100620001d60b020404c02d102954a4181041c0346410900410000704020400180c3c2e50040103001050804980c2004a800d8208814a00072800d5410400d801940022002c4e944120364684050500041180c900c1180525810 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 264649595 1250 264648345 264648467
    0xc021005090109080c060d0b0114070507030209010608090a080306060706021305031516030b01030b04051603051003020f04050a02070209040c030620030a0b03010b180103050d030606 80
    0x16207107030711081c0c96000440c1d8031100a9a104e071071001c00107410200a020400d4084e0303203900000b01c88203040c18143d103001800882c409590348690300035107066011003c00c0046080000e8618014006880d011004c3c3c1840c0c0300c1180c842c6544c1c44e02921402e008000f040560b95200308690105921a804640d80c842c842d60610202c0394510426210780a94241086001407090340c13035106105514111039410580401500140007801d10903040607540c0c6030810281c1c0b9140f01c1d05024080c4001c0c40c4008140448004055410040500700e458900c4c800400043c0c803290007810140801300c03400b04440e50741400d007000038001c2c0c800184d403103d0010140824032200004440580707005a40512950300041c6002c03039100040c40d41d40c80349102c10400101e2010b0140e001c42003041d030090010401d41c2900001811070100d090300f1568214805004008000e810413030440714040c503040620500d4505100038250855682241e900c2c0340350142604c4410481d81401034100b00c902c01d20428050200807 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 264650845 1250 264649595 264649597
    0x14061605010f020d0f063305041203050d0605040c14030c2101140901060f1101090512040501091406040314010906110d05090a080418060503060403020114010f0b040e04030c021005 79
    0x54603100e07880c00c00d0101f1810725544c0b40303501100c1a0304403419120301e5800041c9090b49004003c00030480140f00c00300d411001c1c031411145107070003907852a0701c0724061001c0000b10340d400e6212a10542c82e1100f040001a0000040c2060160380d0381441e4990782c46504070031581c4980401c004214403400c40c855500001c04078000d05888080000c01c400c291f04006100d60724200703029850104440500140c086403090001580d02c01402d00041010840303a50340b00e03d84216070590068050000c1001d00c02940d01803140002081c0b4103004442004846020656510640c0800b402c405010311640e480700c5c1094111032055640b1034001c01100f02c10900001080d080200c043e40c2281c1030001180445400168410107e900540c1700e41c80c01d840e0800f6010944460018000300c0e5880701c0e80005c0750b40d002d02c00244101d000b40c001107606460030010541f5000c4c140c1200c0d082c0c5900c1881881111140010303038050340d20341c4900380340396200c60500750744409801100940c44254009031003078840e4410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 264652095 1250 264650845 264650861
    0xa05151c0e0a030f08090601170a0f060516091508061f05071502120718030b0f010e011a03041101090b1c050105061602060706060308030c04080714061605010f020d 72
    0x258813010400802081203410340000c1c0c503004a603520101c01481602d044044600c0c1c00c07801074040b103800c08c000d039039004030266140c02c0984140307944804204072104040d85003200c800f003074609001054100b0341c1111030400a182c1e05403c000300c120000d000b0b503c6454084048086507001d800f41c408214074010700c6036000c0300c0215995017810400c1d07030b0b50400074001c0c0c2c1c01c41003c10f090484960381d04001111001610000900c170f2604a0b88000089103041160a018109002c0151003d40c1040d000800d580c0b41a071004020700c1a04c0080c0d542400c0780000d5903001a07000300b95924085040004a4011916401a60390301e80700040d09100680101c014a090b240d146e02c00b4006680e8440c100802030041c22500400c0d407440c500e012006140c40300051841d248510310010f94191662101d03046508100d81220340c10400060034440d51034100011401042c1c0c0c84a036040c903a440740080b540c2350180d115103800f41d020a8a598003088003c0d00543c400b1b0842c59000c545175660801c02e030010f4a141 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 264653345 1250 264652095 264652097
    0xf1b0f0a0e060412170904061212020d0c030e1f020109060c0e01020307170403080313110307050f091e0a0204030201030b03030a0c0f03020c10090303020c0a05151c0e0a03 75
    0x10030300780301c41c1441400d0360300f21428111100e84a401c2c64a80e038414460703001350f200007a00104505c0c0c03010364071441201d0103031040700510003040a0310310780041114a00c0e5200019584190084081260b000c2002d00d821a030501c0e2101d0102c1c00d8a0200c0c100114800329006040d488d0307a410f0300103e60562042c0420b9024560034010104940d9050301c84500325001c3c9c84c01600b04000b900d002c01c4001c4201e04a0060b031005003840e20740d0700e84500c4255003040e10080710480140041e4410310019244140c26500201d015101d014a040e0001d0381c0c690401140b140101040e60001d804030b0585207061040c154551540c101c00e240a11101e0003e40c818001240030a00d400075480e014103001041d101e04e03c801e80c4519401d90750907110040d1400c60601c0c100d08500c540c003140701c03464031014010301e1140079a86034010181c0c1140b90181c10040c2c144c07203003070151502c0c8104101c180e84500d46880f010404801407030b9104d0408221040140031034000080c401d092540f00d440a0308d000440d0300c0410b0003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 264654595 1250 264653345 264653357
    0x6011d0a14010825181205030703090b03062b050115050a060206100504090f050d0816031a102604140319180513090c080a0203060f1b0f0a 61
    0x140410003130b02d444010000c400841c039a03094054445000360700640082c0600080300200795568228901c00d06e00801d412070b9070b0381010942da0109900301c40c1c820301074144c2c0118107045240103c00b18000300451030120035004003078620a038503d01e000b0007a0b48403540040c02031050b1094100306c10040c55035485074501440d5800d0f800030b6214804207007540110303840c0000030300d514980f00801000e003185060903034840b042814078400243d4204440c42010001d030311070008034984204014051000f80040c5c41c20300d170810402e28035440b03aa03e0300c0403103450211900130003000c6c10f86003110403a803c1d80d08055003103101e02c20200c104048541d01807096100e10051000c4003ca0104030f80c481c000c074283c21403410042050703441e0960081d07015911040102001401c00c0b5075900025040c41e50055209a01a5540080c0400d105043d200000903042c17110003002c440c038080d80401d584207002030050307402e610200b01045841000342c4542c0302505030509050748030185000f01f98641d41c8141c0d980e00104413 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 264655845 1250 264654595 264654601
    0xb1801140f01080402060307020102040b1306020c040507390501020306030f0a02061605031218010e030f0715230702060106080f0403080a150b0702030c0f0906011d0a140108 76
    0x41e1001606841900603581d02006450b00e03820b2240c5071b0030281004042d9502400040b90118541000e070290912500040800b1031a102c8040d080c0440d0050150045062804002d04180c0000b110203a1452040d42903142042141d224030003403200d000c40d0300380000c4118414080c480c054019501500e0201c081c1c80c40c0704004000617070b91315004c101c02500314105005c14000c01032807044100d40c07140103030240c0746003400f0030181c80c000c081c0c2140c01e00070304000c0c0941000d16010074400c090340e5803181c60080d031400826000b00c28070380c000c401c801400301e4a10014465250040d030010000d40c3c01004410740c0294203d00c1c0e074884c10340e040b151000144269400058418031400c1e0181c041c812100034240c280c3c440d91000c4440e00300c002c0504c0c01c170a8075034240c4041c038000700c8500c0004000d42c03600d41e615605248101810b08480304030407032260030798181c003014a6654400d0141c02c1117003400c1c03200c1015021038405400c4625003500560091300f25400150748445a0b8402c000440260b8540031255 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 264657095 1250 264655845 264655849
    0x106090f0b09010c12050403020301090c08060a0506031b01050702040504030c14121b0109020907020105010f0b3a0213030201080705070c140a0801020c0d09080f190201030b180114 79
    0x400b03512002d81c001480c1891500200702010a1400300c5456442d0446c5002e81300d0b004642074807124003045030100d80d9200e0402c40c10501b804580e4214801d05424081030070400002507841285054100500e00091000501d60f8001d0301201c00b8a50701038801d009900d003d09029081c50080001030b034003220900c0d62140e54100104241d18000f0300d02c01c0f09801c01c100481411062100804031003119903840c0c20503c0582e650200d100c1c4101c4d002c1e0300205456052221101c1b900c69542e00c0920f503400305002014a0806100840082c6040c40380024901c2c01d1501804510030310018900c01c200f403000032941c6613401c1c4400c5403002d480c000e89800d103183d1502481100c1170701ca4070501030714a007944282072054007181c602540810000a15500d02c1603119041c0b41c0c220792200640d0600340d80075113182d05c2c0c050341200c0184003c0c004400901a020400e00c02c094a488041d5001e001c807100203001942107a0096000e400c403040301500741202e513102010603111041c0f080c01340041c01d55212081408078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 264658345 1250 264657095 264657097
    0xb0a140d1a06101b0303050c0c03180a15200c09070c060c0503060f0d081902010e01060b0c060705030a06031e050129060702060f0c070311040204060e0f0a0e0106090f0b 74
    0x10b0342e5448880e001d084d140e1400c0f0010800a400019141e40230065058400d20030001b03400d8401c68009140c2500c0044000c01442d2251940f140c030b1484107440025500030340041c624600a44c1180c404c0806042a5404c80d0a2003c01001c2550240c0792500740300395240d205244584031031103500300b04170f2070501381c3e800e544a01045480590002541500300c6107403c1040300c1c1e6050038031030340980d828258856200202000d60242240041c2e5450485400d01c5101340a00001030220380d01c041d150249030809140c075000024030b44001d005000001c5a403c54069010000664000810341190541d0702d130740c079103070b880440c200f518190308010342c844a040742d12048175940d40b0300907001c5101010500910200390050b01d4103071b901807400d00600c00c0001c0468010701e01560780b0006406c1c00d40c154074019594420200403180154418042480032039003011541904540440b1035910404a40c00000c4000301141c20000940585200028500350400da07490181c07004000c0b65601603454103040041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 264659595 1250 264658345 264658367
    0x405091017070f0306090f020307141306030f03050717070b09010c030e0c0f010c0204060b030f0a02070503040e04050a0213051501020109051005190c0f080a0b0a140d1a0610 76
    0x1c4202d8154013040040c0c0385a02449603c1e128072000b400c41c5010790000303810122103078806014010040c0440140e450212a01080c1168600003040607500396104d00e2400420004001e0a01034005061014400c101c0495118100c555104681e680701910b0420000d45007600c421445608002038114481e009018060720400c90704020f100c084040390400441205210000b41404002c50085001d6113560103030301d01400c480a543c0d07a07a41811076038807210b400020080c1e000d8501c10f00c5500006400481210200c401c03407801007050752954184503040c0090030f90029801400c0c5503010021908640209200d45800c9040c21031140b19940164240c5d80300243c000c103140c02009004007120042d0f0b2005410200c0314a0400d0b0b008140880c4c44101ca56454807200030a441d11111209168020344035030740542c00031000e03c60040b00c03001103000d81825000381442e1001c2405451559100e0441c0380c2d9a2581080035500300746507100510b00132a90903110180070718501c0c090b0030402c0b170003199424a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 264660845 1250 264659595 264659609
    0xf050109031218060c180b04141c110f1009030203010b0a0b0f0a02071511010c0e09040b09030f1303050d050c030f0705030904090320190308060303040509101707 71
    0x10914483da584c5001010403025501c1403041c0c50200800c4042e5107610308021b40310b841600c9a40e81e003413100d5100508281c4003420301c1021070307030108035405c56411864042c103075010803011310301441840000d00341040c441d20103420402610300140c0c1268030256a104890090b4020011403221505000042016010301007000e44c04210703000e00d0400e0b0318010701424115206580c1ca0584039a0a001100c0c4003d8525000401070850324981c40028820204c44008030b00340241050590004a080150010000ba001000e01e0300000c000100500c202c0e00c00c1d2100c1941d00d5607586428842e013101c04040d0009485511842c040c001c00103000c0ca044490301e44000c1c0007141080c3da850340b000040e42c01044200d503580014807903140c854540d801a1101d0310b101c1c1c0c4614104410003640c04031882c0500084603a680e11240e1030721240f0001c2940020110340624118402c0d640c2c650102c1d20710310841d4090764200203000e013000032583c0303000c01520643e92809142c0c494442d88000303d40d9940b0050042e80c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 264662095 1250 264660845 264660881
    0x120f0108031b16030305040f0b03060109050409050a0c090c020106080102250c0510030209010810140609060f030103030e1c1a07020109121e0c0521070f0501090312 72
    0x400300c00901821114190b814008480c00150b441601661034800c0e50300480c04600045400d01401c2100c040c0f000140c0311081c10b0f5400c602d06440020042c1c14903104a60103650703221108001c0c40028420202c40b2500f00441040c0aa42c0703162182c01002c9101040c8015443c000011481c401b060003264035506000303911900c954201074450000681c541400c4450219403e00003580e03450f4890404a01c41303090320300589502141c0c0000d0444100104200c1102401d080709100e0304140c60802401003d00b91441030300c580b5041c0100c0c03080d210301040000901d4003c40004100355108500407003166083c0c0310070a05403002c0030b800c5450407404100034201d2031010300c03488880101e122a55444a240e10010802414684481c03220200c03084c2e41d04006143c0440e00c100622140d03900d50004042e0b40b502e88580c404c036488482e2a201c4180d2070b041914017888600450907805015038285581000f010b10702c2c900300e442c1031341c0208080030301140440c51b0404045200c1d15984503e500d0542c440882ea = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 264663345 1250 264662095 264662107
    0x516081b06102606090c0901060c030207030b070309060603050102030106031107080406050a030906090516080a0510020304020604050907031a0d030c02010309020a09060e0402240a050c07030f0602120f010803 91
    0x24405401d014100801124451440f1040020040040e20b0003034001c03001030443c0d41d016805100062205800c0070090020051030000083e5000031180101c0360070240c40e00107a01c6844044020304a0303000c010308281d08104021080c03010641c004e504075504c9031010002c514503520441d074036005903e0068001c2030203000410215000d10001c0001c080e851400144050042d5216000c4840040003524642d2098a41e4801c1c00e1404613100041c1039504001c00300d00d403090f9509540e0351540ea04c0c5108c40c0d80c001c40420110b440d154243c2d4040c00c00107003030f00600e2411f044010010a00c454140c440801d1070341c00c001c2c090074201155049560556102e13480800d80f600151b020b4010418201e8108410000010340e0030068070a05000e030100002c070358110300f0a8010840244044030f80c07401030441904c1401e0808005500b00d0710301c05120f080803611002c6d042e0100f4107000085e48042d04025903409800c041103030544c01003030380700002c8140301038a4030b07014000e0b1850740003402101401c0d4010881 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 264664595 1250 264663345 264663359
    0x80610060219020a0e01150e040218120a06050903130614040e070c050f0c090606032208040f1401110d0f05070f08160507090e060a0c0516081b0610 65
    0x25100b0300c0c005801200d40039640c84160705011400d90040103000c001540324001140c1c0700109003a220012039096051840740351446600b0502c1c095210710464040300340301c0a0003400d002c0c50030300e960440c000b00300c076141030250b407602c0e41e000074490070342494251808911a1700492b823046c10030700348459060425050504101d087d0001508000a0241d98848640064420060881201c140c200585545000042440710482c4050261480f80005004210032042c054140745448000d18004072940d440f14240a0100e108a4100c0890300b10010004500000100700c0007540d242c00fa41c0b0542e011904105541c0c0b60400004800c0c0060441801d064010f440f0b04043c240d480d0103860030b0031140c03806940d4640d642e44132400038014075040060160a0104c07c0c0815001440381000910210901700d0b225500c43c2e070010161a1081d84d1010b10280329441030f01910380002c0721801e00f0700851007600b401941904004403c442d1004418007480308100040b4155000308040000400c440f81410b00b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 264665845 1250 264664595 264664633
    0xf06090602030307110129011d090403030c05121e0f1605031902030f0f09030a05030403050d09140c03010507030b0a05062118010b0d030503060d0c1706010806100602 73
    0x8991143c0759256024410543c07030600420255207041012151f0000c02d601c0090a803155805074005464000344200c807498070380b1101c49900542c50700e800075020903070407015903813401440440c582151290041100c3c40c00e60440c84000303810010300c030108656403144036840ca0380003290743d01e00007020040c0d2110881e000b0000b568001c1c003e482d02c4281c007000120310000f26001103900c98400001a0b041c4021816903510f01500b0031440e40c065480c0c800b1050b0082d04030300c4068001810008001000c0700712240c0380c0e001c6a84682d0114000c403e03c0ea4441036107075100c0000222a2003075207450081b03010140130748201da15081010f8514600285040c0801125412a02c0300c420504a002d6111002420321101e0a2048160214820702c000a04025a00711802406514000e080418004010a40283c1540e500c0074048610040c201140d1401c4451609a94031040100e00c0926040741a4540072440320b040e5010340048422580d0303160000d1102e00001d124210151b000ba072203103030361f03030103140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 264667095 1250 264665845 264665867
    0x29040e0a09230a030c02060c16170c010212030c04050d0b090c060414152b060902040b0d09060e1c120612020d0c08060a09050c09010e18010906090c0f06090602030307 73
    0x2c0286080c0180103440c0b504040c030303aa40340070000030b048104ac0400130f216000d100d4040303210001404030840c90740010359940b0500b84240700880c000b0002941c40c81071001190040e013400740801d142348038a03152482c0c5000c01500d0200740b07400788800c040d400c0d04081058408840011680f0301001060a081c40890701141c44c40c280e03240d10412182c0700000c2d01e040149064440e201040380d0070514403000034111041c1e40c104001a900411080207a4007000c02070f078114039964800020510340500d0100004c0121130380c0e510140c0034002e2a03c11509955407040119422a100c06290b40030442a500848849005401d09a0706040588004d41460750b501900c80740700d40083c08401f504ca2289900e4948210303802222261138001c032504018050245082c0070301c003070b40c41500550402c0f03503400d2201c6009000d01d030780c08420014401015001d40021080c241c2200040140e19664240b80c45849100d01642844104142e00043c2c00c83c828048041100c000d680a14196284c161080380c1c281c00c10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 264668345 1250 264667095 264667099
    0x922021302180906150a0e0d0b0603060a020304081e12010e0a0f0204030b01091805011b0306080f070612140f0a0b0105040b0307031802030313030b01090629040e0a09230a030c02 78
    0x1c047c01581b244007003182514010008043e0300d28100d81014035100d00205004003060051040c440054608015207400c21103c0340310361482c00d100d42d280d0401d801402000503101c03c1160000030040e0023462142d008101c00d01c030600c601c10700c07a020713041a031086120013010700d426040100008801d40c0e001000070024807005070001d18181e00c03035500f5594858032400c0b504000084280c1065014400c002c0180303a00000b524a44000780c411603180c013800d201c0c80092101c0245a40740c000f4095120002048019000d18800e0601c064007000d9100112031042117103183c103210102ea036000d44107070b80440712500388103465030385c07201c2c03089024080581881c00c0c41c801e11003030750006a07014009800a515581e0303500e0103984c80d606045001070010382c8203a080d245030420034406a1168400c14840307141350789501c102c82e01110550842c40c0b0942c0c0c08501d4101148060044d68416600321070706060203000502c1d141c9241e01da40e4441d9440000d03050f9400e41c01504500300103400782d04004801400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 264669595 1250 264668345 264668357
    0x8071a090d022a1801090e0c040c02060f0601030f02040b04050a06081003141222090b010f050f040b2b14060f0301110a1101140103020922021302180906150a 69
    0x4d0145103864614082e0092101203440f0804a820360345d08115521200c0401c840078000d00b0210500651103080c060030501061442d20000f420320390007034200726807000f080c0900310b680da03680e014540c1c3c00b9007050040d54440c000b0b000c0001a05840340b10070500540c51403620380d84552543d40c410324100f0410708024a54000c1c11410f0036001040f0020704440f641000ca48164051001d4070183c01007010703046000c10b40d10789042e80f201c5903800486e6a405c0e040c036003000da40da44c0200130550308038080c07a840800d6441c1c0016100c2c080032031310041c04214200b40031281d00c020189c4d04c80d000549484e6032031030003c40c1c03c60000444034038203455610210240500001340743c0034005a81e01c100c0d48080c0506012450110801c0300c850f000f4400e4541c0000b0114080149505550000c2c0c10749230060403d086024140604a8000807030002c8005442d50040001181c5503040c0d220101075005800019480d607a140c608122504046060f10310401c4010310200701280c44014110b0280c008400810400c40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 264670845 1250 264669595 264669619
    0x30f0d140109061410020c04020705100c0f02100c0507111c030305011509050f04020c15040c0e0a1b1d040608062a0a0c08071a090d022a 60
    0x103031a0440d58080c1860060100e41c450401c43c0d01514103001002c46806001c2170302c00803500603404195030562181c01c07039025a403030900d0f01304181f800c0544c0c4c00d408201c900e00400d02c405181c101c801200484103580940d1480e040c2044410304898a8601250200e00c080265a00042c4480541c4100460003450880024109034000c2c13400900c040d030441c0400da840006010143c0301400350016a1388a1420900303050501010032006c2150545540c011600402e01c102c6515040c04250348040b10050060360b14a441e0400c0c0101d2020b5110303421400c01e181c0c0120710b481100b401031402c14040c4c03070b200c02180c409800d030880d08007052001494074070b44000b070314a0300da41c0c071401117900421000c402040b60b400d0100904a211440400e0703043c051105a400c1c0b0b0403070a031074003910891700050a01110640d12801c040c41c2c130348a0508018100d850741c40b0540388409400480c103001d603c41000b22503448403c40410b91f41c914060614402404022180a0140361408000642a131000d0107544d4008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 264672095 1250 264670845 264670871
    0x906040f05090d0905042d020f070305091306080c0904030210021309060801020702090103081e030f04030e100918020412030c0506060105031603021806030a090c0902030702030f0d 79
    0x1503042c0d819280c2c43d04500362020905a0094103100a0402118100300c03141c400320325100207007510f0020380340d2410000056141210564180c0b2800c041000009035612420f10300181140e00410000d07100b40580e03103004218a045209103410380360322800a1100c4a102410080e03110802482141140300e14461716400042600113081e0900803a030041001c80d0070400c01d04141d69040e00802d042d81e2041c0500d00241ea180c1011604480e0400d41665507000043c00b004444c00603000130100154002041c044a8a407019449100d54042e40d80ca6015050300802c014000700d00901d0711001800e042018020503075006198280e40110060041c605076444030301084054203100150081001503070201300307100040c4070302c81d8411424a00203145141611321050000380c02c00c100420117a02054120348880e07401c907a41c3c2c02d554014400e58503490900140340c0a40740303500c021211000c00d49800a204030382c44c029240221080d4014504040403030800400c5034025588803110b0a4071541000001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 264673345 1250 264672095 264672101
    0x30c080a06050a02030c0a0c052107140708100f060f030501050405060708060114070213050a150e041e05070905010905060a14030c090a110f092b020906040f 69
    0x8001040152514450600742801240e100034900340800e8010410801002525400c40e2a8400c00d8240070512070124280240342400744c1503400d41d016501d002e486070007082ca0016001e0588151403c08806410030119615520a446040c0782a881018091881034250308100244103032020001225541d442d40f8110b590000d5100341c8940e595030061005102c4140200c41d808141400e061109041000008000c44503084010102078800314001d801c5569451078034400107101003050102d410620401d00040441c1c0e80704800480c01400005410140050442d100300c2d0055041021001c003483c024201307030147c160840d1103000f0168080703001c01c070f03034401c0c11b0191040b03c40000d400e03d401c1c014051604a140c00c51202c001c10b045c165680c560780001d0100580509035507240b4661140c44490340030701000c0d100e0312503106000c030381140c0c000e40d00c001402550000300c41031000b00d000e00d40759800d8022442c40305e240c5001c1c00a0500054203000300141d41154000d0300000d40c040340c0072141421 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 264674595 1250 264673345 264673349
    0x31505040b0402091c0c0602160909060b061315021b040504060608030706020c010b01050306060a030b1201090803040b130f14150711060c030c04122a031401140a02030907030c 77
    0x80c80141740c500c400b4400d04d1840e074805445240001c000e03407100e04030f00b000c2441c1030348104d840d450740782c0fa1034208204454010201e503080207006075854484a5100260201e418003544001d00020102d542985100084581821a0700049404080f03144403d02002d400d000f03109030ba10585500300001e51410400040c400c035400f4110060b1143d010907419802c0d99481c001240c1000420700600c02d0319500d020844800c13a01c1820000340300700c040301c0450407614804031b4204203035180281020500020000551186210b0258000150380f5602c2c5d48000c244003a00140007800b1102c02c160025100d60045101c5000c1001200e0344481c6d031304861945e0413001c540100010b000001701c0800c1c64400c01025800814204100b4114503243d030b0301c040349016500c2080401e001940718981400140110501c880d042203550032283d180b00007004442e00024030007210400c0d5450344900700004103214007142c400580c00b064520f6212001c0200280d00b0141ca41d00143c0560000040016118038400c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 264675845 1250 264674595 264674629
    0x901111204170a050a0b090105070c0b0c0702310e030309070e071718060f04020102060a09151b12150302042a02010c020d02030306030604030c050f0313030c06031505040b040209 78
    0x21b1498003490450035141c4c0584541c1c1481080010400052403040061390701c900d034410300d00c1d20b441d564000a0030242c140b050750314005200c4071441e0405580301a10712654003040009110b14507034100d05d103503240320440706640f29030003918050000c03c80f40d1003542c0d0018407518040300b043c911400c1d0729080300801d58141442600f000c03000d002c007c4017400381d00d5120900d80000d4219141c40d80020391204402050a81d40f00d0b554040d000411501c80b0f16401c10700d43c0200e0401002d50301c00d6009900c101d81281e00b4001c28491408074040009500034400d05001a04c082c80c0389614603400d02005d0b280300f1048552005e00c2104c031084d082001c030115164044154008200050400710284c2480002400002103403c10000c221003500c0c00240560015414a411a412000c60502c0d0341040d03a140510400d600000441c96686519100c59102740da014060a00c01c250b914241682107904140c581000340c07195002c20010741c545035000710b031400c0c0042d00252a00040d2400200d810402c0c0003110 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 264677095 1250 264675845 264675863
    0xf0302150d0c0507060c05071109070c05061003170307051c020d0f051501050403200d082b0e0c0108061c0602030f01050f1813060c050901111204170a050a 68
    0x805201160091007184000d86c01c1c00c6241000d51b4427514100ca40010089000e07200f00004102d00c40c1c4504840807820f50000103481e0542041c07400600032007840e00c0141c841440c0264000100c407012400ca90080100d80c580b1480c00e450107070301c0300c1075140080004814076800d20154924103c60f005000c12040c20010002e51494040d034140c5080d02050f240303904000003440103000041030046440344541d81c0b580100c0e4038115040c0010760541850000510031000440c005040c451121203030f1040600c0e44528031500aa444011403c0b80d10303240342d0f003100740d0100350060f207594041c0300c0b100c1d0441006086101c0c0789035159901c001c41441a0000c6800d16030002c00c000181003800340103405008221030035000580c12500003a0b12900160304c1d6240f0b800403502154840d8180c0d0b4014440c21303402801403100d007068103005000c80d0041390351503000c29075501e034a40d8021000b042c000c1e5069030410380c5504050400c519180c0100c180c400036030b228441d10a00700d004c15801c000030803c1c01d00c124016 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 264678345 1250 264677095 264677107
    0x30c080307200606031506040f02040f03121e1b21080a14010302060a03020c120d05060d23070b03010806100f0509040206070503090a0303030507020114010f0302150d0c05 75
    0x86101005400310b0a403e070412410300c4815507022907242440046105000c0080e211080040d0041000080807a100c134400200010f01d00380307039a4450b0442c0e004400860b4200e80f07498040e0f803075894640344800040c0c0c401000442c03540c080c0038141c90618000001402c084415503c1184442c40b0b00c160601106a03501110001a0b104d01d0041e40006444000c3c0325000b207c000100304072206020007440b905000c1007000b6118070a6064503515072105085620303508110700700701e80036403168003104c03196400c1030000740882c18500c8095a4555001c40d0f5000704030510702c0c0da0704c25048504541281401880c0000580325846e0780654081c12a140152843d800c00c1c0003502d4451665030301401c40e010102070200215a220b940c0241c1c07268060b00d031281d0354401d5190013030642c412030078582c1d40484129004414140d066005a1140380107800030402030050315440d0140344001d00c2181a4605138100600040c2130100e0128110360080c1178141c1440c3c440c0c0440c106403101441480b00198000c146 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 264679595 1250 264678345 264678377
    0x507090f080a230f010f0c120b1f1803060606091a0306010302070809040504051608030412110103060e0903030402091006120e03130603020d060905060913030c080307 73
    0x18a00189200700091030030400c641e460599240c0c6a00d03c001d8403a000d0441c0420300f0340306118010100300014001c000a44a1034401d00c010701b003040202c80041c18240341504250520312030907241040080c101c003c503510a18030034040580209982c001c104040311080f91388000d03c41b52101440c850100031400d039040001c000c1043d445640001c1050709002c504050921480044a070010801e10300036030345041e1410580030500c1480e421540261030242008280030011952003140c031109041034505070341d1740501075a24095402002c86a902c0039010300d0004002c40324520802c4018100850035541d40c000c1181004003c03126100300782c200204120861514178842c40d403004e00001c0002c001030a02c4801449181c06c002c0110030700f40c1e1032070001d440c01d500b041956402000701000c0040c1e10f85814004019410814030040868107091000c14564030030b014241c0304d01005403040703041e5900c102c1520051125000240d0500c040701e601d440c04a078030000118400c0c030103034551a4410082c2c603a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 264680845 1250 264679595 264679619
    0x40c050d06120618080304060e03070f05011b02160618080f030a17010e010e04020310020a090609050d08030403080c0d0603030e090702010614120118110312030403080c0a05070204050709 82
    0x200c102c5107091320f412580c0066207440989401940000d000102401c814900b1451482000005001c0c4450b65451400300034054111540000c000000049008165041a650384506000b00b4042e41d02001c0c040c44900c1c843c41c154548882d0071a14003500395585c1900c1400c0400d003007158080b80d0000598200c400d504140e03542e6401c088882030025070342c5000c20002c80303108180600c08156041070041415036030104038006010101070030455031020030380c0000d0b00da07950707900c51000441d580030f078001100d26001d80c008900541044460746181e0759030350122000c10000300f100c0d030720301ca00b4401041c070882a0711840c4040e40c070035210a0007034021601048140040100078001716810140305000300b640c045501e80304014141c0d00340420310f15480b855800342c0780ca1300c2180e0165009444910502150707205200701102c1c1541654000829401035034000c2c4000c503006404107a181002c102d15910700401030040d200145407540c106480740e40014113030707102600c00e140061032642c030902960000703107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 264682095 1250 264680845 264680861
    0xb0a0b210103050d080c07140601060f1107120302070807080109031103030615030702070e15091b031605070206070b040b0c0703020a120908060c040806010b0304020f040c050d061206 80
    0x240000c66103600d940d5425603203d440c0313100c0404002941010a12507000e0300d05403402c407030b407010010501c40e06025100780d4a0409103e1540010b200507103002030140030707004a00d000003251028206840c20b04100000400901c80d0031011803060000000d1221310500980700908040c500100d02a1a2030500429a00c9028150801a002001030002c50380d00c0c000140540b0516028294596441c1401a4207294040d4460000e0f02c5a03942000f10309102204038004142d01100c1d03450207034940b0b50480c14080c5801592151001c0c003000800c07071150302c6180c041c0001c2e041d440e00c1444c1c80000d07400b04034142c003d0041181c2c15411f020900c41000078000411f40d00c06800300005082c1031103514025524010f520000d0500d00103c4428411396100784100c5000c0c00c00a01200c00743e08020300b56648a90ac103120b080c07070300d02400340003080c43d003000c80031240510b800608443c1503102d944100002000002c240400707001c01000360b034140d4030703070350140000500e03140d40c03100114541d5082c0316058134090 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 264683345 1250 264682095 264682147
    0x1a04021207030c05090a1e0b0112020703032003061503060420073305040204020f030c0c010c0f050901030203180f0a030327080313050616110703080d020d0b0a0b 71
    0x12a0503d2502e0003941f500740e14042c0c058002080d400340000040c5d649070442c05011004900014500c018560550007201081420382e5a80d032201c0c21413200c003001400199070b4039602442882103201390390001c10207903401c207800410000303502400c0280000c03040c080c46035149107410042900350074001d2211600310148a03140007001c50205c0400c0c0310120b100514400140c01e03a40388041400d5488035410307200590882c0c41c2e619505e04044078005000d4001041d1032429600b445030500b9917520401c1107400422007230b2100c5040c46100070042d0081d400080c541c12207840d411600c1441d1580401c0883c1d20b5140c0c3d2800b40c0300c0b41d103803410005d081c1e4125030000c001e0a240c081810741102d104c280000001500302e408140c80307131511140350102c01d8500030040c003184200014031900030401100c6550710161515131601802032840c05585803a040e00c009014504244403100350301f56a40c00420440d40418400181800201c1c001021488190403060410101044203c1030000812003642003001e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 264684595 1250 264683345 264683351
    0x2b0b04140f16230702030f030301050a081f0b01030e0a0c0501020d0912020f18041113200c1207080315010221090d08160b0a091a04021207030c05090a 66
    0x4038107025140ca0000c103c0b507020942801c0b00040580c4004007030382e521650080c103803080304c2d48060036195250401e0080c1440b0705801e0f03000240c565400100048510b841d5054000203640c01d42c1100001d24001384018107140e03c8000032180408140110032202e4826025042d503182480002850f080721002d029041c03052107202800b9040b640d02c0f0355080c05504403402504195040c01003501010710307109181e4040f0507881403108002c2c1031000b0704001041070364881120322095070a03105903008070035001c42c0e920883c500b09040c3d41c20701c00100b44000304d0500303c40450361007120801007a40300b10801d0310101c0000c414058003084c0c644038441040c00901c002c2c180911700c10b003480018075800813055000000000c4042c00d42d114030203c03620b101c4d0889202600d507090113205400d4200c10340011501d600d0003038002103022046210b034200d05030b004081005403206c0302010715003040f40a401640d0050350b03030544085198003041910040d43c07003030b40e5508415144c0030500400481c080c10129031141 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 264685845 1250 264684595 264684631
    0x515070516141e0a060b0108040b0604090507080f060402030c041b121d030901030e03040b180d02030a033c08150a0906031104022b0b04140f 62
    0xc0a24aa40812a0010321100b5401204160b10303203004003100d00315480c08800302e030000c914400440e00c81c0310f840c0240e00612060320180c1c011207032140e0440300104070103042004900d00d0704041c3e0040b81c0007071240048480090715519858500340d10781c1e28ad01d1060384500c0c108001c40c101441218034982c03003a10140003600310035140b040030258070b51a890400084001c41d44203c07005810440342600f00c0800364a081090000303807501c903400038076120302003420411004207104000003210f0807100241038030ba0402c01c0c0485000600d151180009502c2448840300b603000d69414402c0710300d218401d813a0f075003552004080040d1916140140b204107404040c20450900390176200d901e42485503480c200030540e5405400d020000d81a218040c1c00110456010884480b0f5070710a9040c1d90140280070a8070700d800003007000b0b030f05c650451010300c0e00844e214021031907841d40055420b1410040c02107443d61003040402c040704d803c144200c107005074034030501600082140c1041e030404103040319805808 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 264687095 1250 264685845 264685867
    0x9120c09061504030c060801081510090e0705060318060c040b09060a030e060103080c1015033507030f03021920071811070302060f040609020303030405150705 70
    0xa4020041409034282d140c01c021031038100300850340035590009070341072070644503200100032030001d014030700302c51084584e1150342e030303070315111140c42402508036404516090000c0c550150014091000c020b01c580f00d00410f007907a8100c040c6d40300e02051004c0c0e031160000e0082041c0340c003038040c1c41121244010442848441c0c42e050032100350020594195640301d1020400320000d052a40c100d540502841c2c0002c020040608014241414645c00300d4a0b4075101e00010340440c0d8100c0e4002074040801501000094070004108807802d0f1030000c500082c0514804502c40c2140400040f460301400043c0f000030160014420820b980f0140317011030920100d0583e686803080d032010b17110140a1040007551450241201514000d105142550140b03a82d40031410303480c0d08001d85c044c006034140040380c00c1015000099070700c0143c0550081100b5120384440c03454180020300f058440588600b004030243e1070400040d8002d5106e01c0041c40c0046498601c80034003c405820b1800f013240811a000d080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 264688345 1250 264687095 264687109
    0x40b010809101d0109050a031d2116030c06021009240f02130503070b0703120b0d1e050c09010f061d09010e01171c0e04060b03090309120c 61
    0xb5403203040300248071604044060300128201c110b1041941c240400b00041100c041660802c80d440394803240302d5200c60030f01e01095184900714468212320480083c01c07000303c0385408854210340000c10780d003050090005c6541801c050340c20954003890302200030050300340c1c100024030300f4411081e000c210848250f52038085282821048040d0840008000d10340c03a04581d00201d5210a030703038000c554905200802e8070803ccd030701d4482c2c14440d005200c000a41301640c00221070761141d25a5030501224801c20f2208001d000c9000740ca6000201c03030703800d0000180005100c0d0b100940c140004006090b0924100d4507040d00411010300070800b64004009003e4080107010a4507842d003410610140908580c0c1c1c00701c44113a107040c1c3d01680b244000500400081c0b0454180d0f045559002c03c2c01d0011200e0340e40d6508003141d050490281032529250091240c004c000350000001c002041803541c5010045207078000b980c081000e40c1001a43c0c15103854268009982e521900004c0c02c0b416804134001021 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 264689595 1250 264688345 264688363
    0x1503052a0d08090f0418021e031c02070e0a021b0a050304050f01030f0f0213080606030d0e180702071701060b0d020a0507081317151909050709050402040b010809 71
    0x4500030201c3c0c80f865541e510845071280381c0010b4800c2100c000400c00c41e040491030038400340e000e4621200c40300306070712503011000703080f10024004000e04d4070320a08103031740c44c107464040404600035400041910000c503140c141c0030341220741000d40c030b4030310b18411410351004108010300c0d65400030038040002000070003950105e40e012a19000780540e44401a000f4007521801480c00c0c5107441c00600c1c45d0300447d800b0f000351081041c910388001e130310b40c449959108029901e190341544003420200c8841e106403600c4100c410040e00528030040401060700060001ba56040c001d604558410b11403618412150b030760303c2d00d11600a0210514285181107944a905004001a40c002401d060054010000c603049251700100030b55448000d110180e40c404558003e4054820030f400708079024840c00940d8641200c18561114442e440b5440752141940c940807500c0f03580c503107400c69403010071428440d40340202078004001c10149040c2c410070046030b000c1d804080c1846904014814800d20008100e48 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 264690845 1250 264689595 264689603
    0x7020918070e10180c08011505160809030f0f190209040b1f030b190203091915060314070501080c0301230406060c1505010501020d0309061503052a0d 66
    0x1d9103614000103030003c0c064012128880504540b01d113100015030240342411a681d40b02d09099032240381002c58000c6405850000810900048440c0d0b035a0001d0022178601c41e2520310310746004140030a0600584071070046030ba40101c0c980c0c5600c008148070107515403801c040012561300042d030010303c5803440540043c00c00646900050b003268003554519854000c60000603c0c8643e2380c0ca407808014404454890000d01d0aa1610306002224000d5134003800407100548042024540703210310104c1c0c64102a03c0241a40b00c45a00e06074403840740b0b10145000ba40352821161301d41144a02e0106207610036030401004604104101d0b10300780a80b030640d803004110300e41941c40403042c0c20794035403001c1c14140d0140c5080d42c0010903d8020644840003441508030130180b0085401080c00c45070300340300c0d140c09a0004031412038420310a0303000d14074241c401c50340064082d079003800505d0300b0802c4d500b044071107030302a20340c440c00c4004000343e01c10300160440300d189181e81c0410100f07a042d106240010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 264692095 1250 264690845 264690869
    0x1030b061c0e0601030b070f0c0807060e0c040e032809170a0c0b0406180506040b070201120e070e090105010f060f020f0f01020a0e010203070521040b030703020702091807 75
    0x40404103582d0420081c07107112000721480ca503124184900c0e4500152440c90100300c80e104245402d5001e403400300c000c203412032105410192252911000b400303030348560b1443c0b8024001d5130f2503540c0c0d6a1061444041d242c0c402541c503480d031454503000304401948400460785181d041152101e80c01240310003230310303528040e92100300082c505140c80d292440d80c2c000c240f8074001001041c0743c030b0240050009c590031580d0700b07240d42d88980c02d4920040101c1c01603a03080041004140100c05011006141c000e1062500c10306100c014000d01044904044110140340c100c1a001c1003814940c1c11a1508500040020172881d4540000980394190700d2040506101c1041d0704494404d009100c20700080046405540c0408a4120030900079844800c030200131800c0d544a08101f5440003096441d041c3d0300c00c008110441c00b00d044890503000307407608034003148000c00000c61001813600141d802117082e81c0340940c40d206913204000003070500230140c6940c10240c01070b1001003140011144110741c5038005203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 264693345 1250 264692095 264692137
    0xe0708010b01080402150c07031e031b030206040b061c0501022a21120711120a12050603120d020706050c070b040b0402040f091b27020c0a20040b01030b06 68
    0x148c2c2040c83d11341c00034040c00000e490100b103c2980c01a2800c86a01c00e03940d610991110420384500c4c507899000250044e8880c00016001807203d03d02d003070300428000c0c0200f030750720540c110192410084c820111081e94001c1000300349029162018091a49a01c00f010242c01b08154103d603035401c007042021206104c03140203d01c40c41d03030004807800d24038060103010691802c402e02400103400008420554850113405a80c4c000d03025080d01d18000042c0e48000740d4035180008000030340740107454298140a901e00704004c02459000511000381e02c0b44000da210a824145481120070040c80c0b050286003c02c090000903110212080d401507002102c5103280d103960000c14018141c0c004042c1e40c0a02d4202e546050100081034a0380710141c0e1b5100060302c5480c1c40e60081404001c440700800105004a0352042d4451900544100e8800c1ca0840e805c85086807242c0038450301320741f50101c0305010b4030382c90a40703410903014208019800382000c4c454241d4640c0403440d50300c2400c0034000c44070f50f40751320 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 264694595 1250 264693345 264693367
    0xa0e06071703070f031506180b03040506090f070501090605030a06030209071106060d02010f110a080406082d07050c010b0a1502071d0105130f0e0708010b0108040215 73
    0x5403141540c02114a9814001e45081c000721540300340c9540021881040c0500d500621034003d101d01200c4554803194620b15001058607030703034191411080201c00c4058082032244619000c2c51040380030710b00601c0d040c100801600e04040c148412040c15402004041c42141d8200e444101120300a01d8484d0b52035590180301001405a42c00081d800b0340f041c1c041c00402c070f503c0519a041d040140c8160f0380a61030b81c3d010082407004008000780071441d040803000c1070320b004038031100e19403128900341c2d10248119a034001680e170003500114040b400038818485a018895201c1e80404494180902800c07103460202902c064001c040e0307030400100003214088660700703411085002e400a00134a01e05074541d8840d4403544451000c080051049100c00105451481901c296140032006043d26a900b45000c1c4000c402d1498a922012519040c010a21503000d109200f0b42000081c0585131031810103004a0a460031510094100610b9030188400f40e6980390002030126800800340c0da44000941c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 264695845 1250 264694595 264694597
    0x1c0302091206070e010c0f0f080f04030b01060806060a0221040801020f0a1e090504090317070806040f0c1b0c0b0703030e0d0309030f0e0f030a061a0a03080a0e06 71
    0x4285810001d000c11034103a140000507541d003d0515621035004451138140115906076806001070329a01650b000c0c0300128041c26200441180180310191034005d64502100a55000e80d008881a422120041000640c844905078014108846083c1b800d180018000d40d0b407980c40f403010610319110851030203a090181c0403100100240720027591030b040450344406171600003c0100300411400c0703581d0344011009507034882400303c1039104c22640905103002d100040c118041c2c01c800703000a01c1c8000382030034108040c2c40d104025950724280c45e40b4028061000b40e940c3c1107001d62031681050b0f00c022409030403400414031a88440b1007642941d0290401c50038000042d4808800d03079100060540c24180d01d50412100d8903806000c89030b507040050411401c43d00c44c03090103000250701080c0039850500c58443c0510240004045c802458070f05000242801d11505048840769500c240515038503259041105200030115584101c2c107103192039403442440303590480d00400c811010490001c2c0c2c1c40c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 264697095 1250 264695845 264695857
    0x40822120606080c0f03070b0d020904050126010c0c1e080c0d090803030c03060616060c0f02100e060103020d150213033302070314030709050907020309031c0302 71
    0x161400d91096081c40001842c141c0640c40305802801c600400382c1c14440c00c00200b90202800911490386440c8022406400c03c215101c8250340801c400f00803555a40143d80c0a080c2d0007101c01d071051b00c9070240c1a00c1c911079041c01c2c0d903203905100100d5121b80c0c11803a14003c45401c036480b00b00802c2ca4021f40d0800e03080080b0024500030380840c00c8640d203200000d0741e248914041e21041c0c013454551039190390f01d01080340c2c64194500100002041d86c14464094200d0300c0400d14a07200c2c08105aa0315016503203050b2410300005c0399021400c80c6240c2c100320f41d8600100315038007002001703200b249007600c130801408040d008082e0b580482003045210071580c0c000d030000700400c640b18180484a02c0d40c692440c403060702e43d4242d00b00b811071031901c00d9a0380c0390f1185001c2d04100030200c61458190281d0007981045d8103001600e0140d00703130041080000c600c50b2400344e40b10042107007840c00f0490150006003113441198170070702c607090280d00c00040c8060b1090b081c1101031105800740c01c04a0180c4202 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 264698345 1250 264697095 264697109
    0xb030c2e0e0a08010605030607110303060d1506080c01031a0f0f010c060c0e0a0905070207060f0207030206040b04031703010b07020616080a09091b022a090906090d08040822 76
    0x2c2c500011800410360064064071400c5064840d56154100200c42d05a500003d2a10980080010800234904042c006141601c504045c07201c0d0404000502c00f00c1d480c3c1d50040e0001d170020018070b292981d051050003800040740c08601e0250720301e00c01203035a034800c00b0711342e90140800c1c4000f070b20568090704545000c2544080284a480014180144a20035541c4000d0088000c203c02048011b503d02500f80310341c1096008290961034110211817182c3e200074904154010a0380110150b29084001c2004e8030f03181203050364031480d43ca4404201c0149003903000089409100504c00d2b0b81301c030812502c0054040b01d902d46c4a100c100072a0241d1b40c100c883c0244465000206003113a00e40000b040d400311a5020710800c100303003ca540c00a480c400071040070300181c11a2402d104220555030340002e004590a4a001480c000e1402040c5818400d444500381603201c0401c00801030030400032010340000514082c441414107568108090007044100d41100441002c100a03040c0d068034940011b05c11 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 264699595 1250 264698345 264698359
    0x2060705041d0c09090c0d1d0d230a02010b210a0303091a0106031b0305060607150e01060f17070f152a02030f0a0812070509040f0b030c2e0e 62
    0xa06841b480c43e0380f061445000d250300704813912500346809040c101150800c4400303000240d411000894006502e03a9048070b01071010f14140c59007034402d402074031300c2c1d080c580c00004450f810f4a007000101c0400340e0140100f20604c0f100136030500004100c11081c10343c18100403c1c41c850920344403600c18140c0201440349500c034400011000d515800c82940c0d4040a021a0300031401220304406440d01181c0c841d1300b100c3c2c100071b0140007500c5032085a400b00580140007800b8000c800240d82520070640c01074100014481d81880404541c58003079a5215032100100b11007882d2440c002d40d5401d5505c5002560803444165808140c014825018445850454042c02074090740d0300c1c0941e000616801c1e0b0107485030406a1304080e100040351000b043c0c01210403800c1203003005984440c11001460b1408002044c483e0180036126405110307405400b5002c0455203448030300134140381c28001203e19201e08008103079890003640b46444030140001c004928901d090700200300f40c45e502924411140c0000b2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 264700845 1250 264699595 264699601
    0x60c0a0503270a03020604120602070b010e070914030606010c050a020306012711030c0306010903140624130c03020f0f040311010503090c040b0a091b02060705041d0c0909 75
    0x20308000d0565014003600440429290b0354010f0190307014103804000d410500030003040c860700310011209a00707a0f00c00d100151070311600c0c0e510f00310a10b00c20380c4903901060f00d00040c8681c40f5000440c81d000782c22465590820031019000080e5220005041c290600c04c0741c0507280c060010a100c450509034002e0100d508035650342d1188e035821600c5044044605542d041110f04168407801030305c0c0c12400031810203085484000c0d80001b9070780050561070601203c643d00100007100c041c07011209801c010050103807803a1805001c041e040c0c4440c598441c1d040700d541c010b40d1903039070310914020711000741800042100b8204400d500030700ca6410700622240012074203548140b40c4400403c103807882080c1e009a2400c0305001500c241c0000e03154810280c001200100d03041c14903078820404031200410800c0c641e681c9000010840b030203504a0f2424074513100c603070320200350100401500100949407440c6800e00c1c048000900032003036213805040307050240204080080010503211103803001050301010703003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 264702095 1250 264700845 264700867
    0x14010213051009080601050913021f030f0c05071b170102091306050901030b06060d02030a050601020f0f0a14072c0c030f06091312020c180c09060c0a0503 68
    0x120052054500c241c1c4203038020554075100d83e1108040b1140b52004040a03400c1c41c00b0002c98940046c135911950404445403000340e80c40014034158147c60000c4030f40c814140c518020180d514200c45240c8160400c00c2c402c18541c0d00004681207180c001800300240001c1034045a01c02585610118105429005c841c04049065004200403041295096000c00c0350304603210a540b0b0b648540e55000c00c1501c01007011501641750340e9400300005041d030b850500c00648501c200d80040c6c41008489036101c08001c40c0d540c0410026075011070310402041c18201c114034155403000700020003442d8400d80c1c0103030031202e07808200041c054090610001049a02d10380c502440f40c0c2c07641c00344018050b540e0080b032002510041140d0003101000c00c202616030340c600030310a00107000b42000d440a20162010004603808100003899001e59a020300344002c40c140030040c5c942c10244180c01c400140c04c00f40320b00b40c03c40b28102d907111030050326041d17221a895041d142c18a140c019014019010010b05a8060 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 264703345 1250 264702095 264702127
    0xa1205040603060807050303040b0d0605090103290910020d06030b04050d090e070c0f02180408190203091f051204030e1507020f090a0b060d051503031305010c140102 73
    0x1852440c0d604008159582c42c1c640e985c1c8909104054140d00204428402000e5130300050101c040f81000c0450308580d1900401c135516030982c0300307544007031091a070ba049008100c5c050b01c500b0361030700a1040b21400c142076030039102c19031220403a840c20344c00103040002c0c180d0764005900075604507040000c01c0c03410381001070700c2d4000c458003040001c0c900c810125249610104090003082d95980e8121400c5030350351540228248224142d901c00940704000c5660600e929156104900c01c5d502c150700d500300c603e000c0f032446021502c4881076400600182103e5207540c1c100c0c034942c10714400f9082c0304129034101581e0303501c41c1c40359440c4000105000c01040c103410080408012105a9002c20b6150b00352a005140323000744400258044850f540750507080c50800c0c3d0058001d0411007000a00c0d031a40f6000030841c1d4403000315035103000c1d213500801c00b030044103a65050303241c0425000303035250100d08003044c51003140a000746814890516494804d0103c2da04071402881c1e50a07000b1556274000b165003d4403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 264704595 1250 264703345 264703349
    0x150103080c0f060c090907092303300d0902060313120c02060d20120a0c05040e0a020309030904020d0b0901092c03070501020f0a090515040311030a120504 68
    0x300b88a290300c0015802800110107224a0a40307088500b4079800104001d42018040e040904120305010041034807014450b4440d2504152440810030352a90020300d401c000c92011191420122400103810701c505c44100385029101c102d011554504201404500070100001c01940081e404803c0060801c00d660f2050401402070000b950001d4140001701e4600c403a40b40300a401c2502413284d509a10210707004207220040c00119058144441c070400b0285410498000f11000101414002c043e5054821840c0c2e105c038604c0c0c4503103407506003d0301809800c4058994490b40c0d03400400640d200342b090040c2c41000720010010f541e40da603d4140f45002d44809000d16201d07010300701c0002219186481810032204504221381044042c42c8621035004220380407465460104100380d8000490030710082c586503021f8503a043d2a140f6140008000d0001c68204074005d802008a00d604486031209071411680d20007200c000c800c0d14900802d050180c5100d008145000402900e80300580007009041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 264705845 1250 264704595 264704617
    0x918080f07061104120201080a0905030c010c031103010815070203270315040b0a090c03080304060501180e06010e0601030e0f1f180215040f08061b030f0105060c15010308 75
    0x843c1e50300f5602c06440f4a1048480e40400107003d81c006500880d02141d014100540000d9132440d5900c4190855124000708a8540d43d940c06001d07025426101d491074010034005494250343c140390300242d642c074500c01d42c3c2226000a10006106510800c211010300801c0c07850408181c407807002101480746030905840c03280c05450071014a012400001e644a25044902810551100310b01030008064010040d10404030226010021a10600042d4081d07441000e00280300e6150550300012b5100f150401c0d440c0c1d500340f844143c03540400144045c107440851081801c0740d120b502c01030707004043d00103030020707103015070a000b401042011501800064440060000104d49200c4000455010b03d20700d64140c2100380c029405401c281a440c2107201314440001c1c581519803c4032a29410b0a521400340c540c44074080145000c11448960700707208082d40c0050440c00c100700040007021050140c035006a10216003e10b452004000101502645403001d0500356140d00b40340c11707247d00a010f00e403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 264707095 1250 264705845 264705851
    0x102070b070e010903120c0b0f0a051f21150902041a1e03010b03071203020c09270106120602070b010e04020a0909020a09051305071e0918080f0706 65
    0x60116030003030b03210034442141695042c450f9415690b81c0356450b10804900c0c010000030320f000c600000d440145160065445124000c2c0038940b10a81e081aa0070090000c1c0a09050789610304611004030224001d417009461015000c40054514903803030a00d031000900948903608404000076a04c0c0d221000c070500039201401a040782c000340c40594289090740d10f412040000c484520500d040c500a56000c00080c0041034500007240028070307005158103e071500c018070401c104109901080300c0e24106a00365041c08080c43c0c1100c031030180d144180c0c440b6845a40541321655480829071000d000b0b41058248848110f0031414000004d4100e520101d6031120a40f00114240c508406024803440c3c0c001c1098805601f8200b1010203000d9101d4100e822103242c440c0450a0700c140c2c01901d1140260780c0c50b500e07a040312400e259151502070741c88100344e41c0d0444024140102d020710039005803000c00601107204091760814104000c809003019042d100b002c0780380310403201004028150140900014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 264708345 1250 264707095 264707101
    0x110114040e1f0f05120a0602070803010609060804020d0210121a0f0f09060607060207050106030b070f03090c0b07080c03040e070f0207050108220b01080102030604060f0b0d200406020102070b 84
    0x10420b41031030b00625a6460402d8002c00603450681c07000500d810744602554140701c0303035035507071416608152421a6480030110041c0503050b0302031200c0d00140720034038101d040c0782402d4001c0f50302c440003241c010380110003c03801c0408e80d43c0612441c000009001c3d03001c001030b50021010740d07030110f0818495442041e43c20b0003207020f441c10600b0490111401062a5010385a0004000e95540800c50841e941602405013070081582031252400540c0680e868600a282c02c034030007003107007055604810500d49409200004191019003030000c4d21111004643c2e1150710742865440c5004810b01d40085101c005004502c00d10826010b5003e0a656107a0000746050804140d844a44c50300a03240020008000260000c0111000c11851172702d0101c8412201c00a450308044c0c82026000020140c0d0000140103d038103184c46180b0003004c00841841040d401e00300402007520072010000c10440d2100c5d0a481b5500421301103032400f00090355107668880d543d46010f0702075040f603102590303506094000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 264709595 1250 264708345 264708391
    0x30a02090904080903191505180f0102031509190c1206090b03060c0a0206070507110d030914030307030507020405090c1002060108100605030a02040e01020f04030303091e020d110114040e 82
    0x140b031241a03401f501e0103d10017161110080204002012000301001c417110b070701d20603081800742c400364140d40000582e59161a020582da05545c05540902440390300c4100503280d0042040b140002d10341920114402c000200d04440c070f45c40407103196440307600d0440001401000c0c1d60180c1c500100c1035044c0c600c141c1d03407002100000c0c0904403c82001da000713240021181d5200350010b00003640f1030b0394a2001c6c91150004101050301c5d084045011681e40d00050203125820460120b03103a42c110002d5142c168107a030b00800078041e02400900868440c40410f41a00d0f05100807170b4000f401501c1081601007030a0002d603101c00a100d1024140140e2181d44500c031942e010b03c030107494024005000300d035080e6013800020500b011052200d55428842100703003400d402d000b0f00095000e607034003141c1c00d020350910742a9164100040445400010503903001a102d1039820440a03412004100c034801d800c0740141c2c2c104003041c010407805a40040c0100c2c509200140d07030390141d000b520351401180b400c100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 264710845 1250 264709595 264709633
    0xb0a141816111002031f090213050d0c171c0503040209060603060114180316080a030c08040e0403120506010c08041203020f0105010b041a03100506030a02090904080903 74
    0x10075094400190301c80c040c01e039000340c000c51203400008040f90742e0882100c00c500100d82007510484865480f200e4500070b1107050507000006090016401c500d40717201d2a140d0086007406100303c5010343c010440c84400e200d807078010140142142030a8000c10041c010902d510760720307120741c008805110124410080c0d4403807001d0700e00c2903a0190100049480f541c0c00c20540d038000409040c10000b0309035100b981620090041c20200420b1a003940074800070301c0406041509200c15150656120141081200ca0009258074201d0b018208503c0c803d40a041c00d00161203150056404c40e890b100601c806c0550014401b28240315111040000351500e500440d81c80309680b1000d41071040601041c00000c02941001c50014481d00443c4d0518503070a281c142500d90981c0442c0c1c0101d00800c1c1005130660480001c24a1440101000d00d94980178074049145005801518000c86020000620648540e4111010604000e01d0f01003a80b529182c00c0f8815884490b8080c06800342e0b607425414091408 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 264712095 1250 264710845 264710851
    0x110a02030c10150909020619021b0415090b0d06020403150614030c0603060102010f05040809100203040e150109080105040c08100c02030316090e0705030103050c1c02130b0a1418 78
    0x4580503402e0300d082c1440c4060201758800f6640440304128000c004032810089007001041034002d03108071a80400490350071200741a130703140220300780310003e12411800c400800607a0740680001074010807481c0030590f2400903030b90007003171a0b1002601100344511514a03201c0e18a1011041c01101c0d02c0d4190600c2558203021400d8040d4171848064240f03140c00005150b00070011701c00010355100040b2440e00340d900a031402d5540c0f41000914400302e00340040b452000b0b084071300080d0b140078a0480c4007001d103600140b50700046a40c801640015a1003480749800501f0350301c00138403150520741400c3e0309080c01d03482080c1c1944101c50a002c17111019015003003650405801071401c50b92151140c0300604880e0384c030b2074100044002e0200d102c2103e10b100b45e01031216523035034980f20340c110710b80a45801141001f6030310910411640c0901081c64003520b001d8280e040c0c420000ba08202c0d41150003800c40d0100c1c056012034500c8012692443e040703030014442100b10344080d00a003011201c0f94009100f6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 264713345 1250 264712095 264712121
    0xf0c0306140f190f0302090c040305120307021e03030a0b040506060913020702180708060a0e07031e0501060c0b0606120c030405030f0d1d0d02031c110a02030c10 71
    0x1111607424a1800c600000071161000e007808400c0e02031595032485002c150f81201822200310942401581044100e0a03444a61041c4080c941401c60304c42982c0e5250301c00c1a069200c000100150000e40300380040c020280d03c22400300841a10010071540300d8004664451043e1720348200c0700003515050242c140500c07000703042e0f280303805a034006102c000c4a40103501d4007240d40820400c00140c4a405000d0500582c6542200c094289288010200c0c10007915061003850b0f00c0750140228000705900f42d81200c814100020016283c0e0b2403494590200034510303c12518120000540079000150a00303864412075030041142d5030301e010055540202001c000c0018070710400039204a0300100203541103030160045a0900d0386407030134a0002d0344515219000a40c9a9140c1d2091042d9a14982c10190060b000f408141d4940b81000b962030055401302d2410f04109043c09083c200e241d4815600c00d61018000781e615620010042d549500108041041d84200480c0c49081031151283e51049144 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 264714595 1250 264713345 264713369
    0x7020d0e0105090303090a031b090203040809040905100c021f02030c070618080307031a0d02030d031802031009120906090b03150d140c0409020904061113090f0c0306 73
    0x1200d80111100d0704000030035034161008201e03810303031030742c0700b030704482c000c4d03100c4d0b800004030500103d0003000d03003684c550200c00510b0042c014400002c9148058400c0441b054038005040216424024684000703802c035108880d03e0a028001c0c1d03142d01003454010480765007c1c840a030703840d06506508074407040b106003013406414410600014025081400904401d022400141840b52540440382d4020b813000f00109540b4403140c8244803150035400c40e5801c045800c0c0400b2106500825103542840c0385450401d42c0d500042041e140e40c8481c0e4010640d0003500f200e09640c0d0482c0248028541c455040e600318401408a110191184d000361040c1c508560351291400e103040d400c0d10a5800103071040302141c54110542e8165210010003104040c000d03c01d44c0740c0800ca81c22841c0c140949070360854095402c02c200000035031a000841c54005503c140e0000366042220306c240c42c01c0c05400c8080c0441c000394600050700b410980c01410303081d090480100700d540d0b540c103016011141140300e202c1403503032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 264715845 1250 264714595 264714617
    0x30c09032001031e1a0a050306040b040602040807030b090118030c1b090504060b0109080705010c2004051e07021527010c0302130b130506030c120f010e07020d 70
    0x2000c0ca03003803004000c040c1000702e000c881c3c1c04260300300c0403444540081c01c0d9a4822603c5c50515038800301c1c110300c42041d100560700d213040c0302c00300e034403584000c1000e00b40004400118040040b198100c5000340413003801d880115840f49056401020207584040c0c0c1503003028280583c81c2c440c4880c0760601545500d825244030070950301c03061500c4202810030748104c0502800a20707180e041c00342078407075881913100054155904002404010642d00200560313070003c141070017940d81203401400d641d50442007806c0e0840c22400142c5c2045090103e8a0b009401d00040c40a5140d800e40785520b605e803009800c0c0d8081d521144120307500d02c62403100a151b0364002000c0f42623802c981c480f1034540054964580c1405002140003801d4988003801003001950000350100c1000c502415080034021904419191660241a044200e0024010103100d17000c0000404c4180e80954115000022140103860007450301900c1c40c01d0100c424400c0c203481e1810900024002c0303101150081030341d4410740794603045031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 264717095 1250 264715845 264715883
    0xf0e070801120c050411040312020f030409020c0313030b06031903080601030e01090f050607021501030f11010903060f0501030201030606110703060e0f0a140123010302010e040908030f0403030c0903 87
    0x80a010070341d0a240102c00105017901d0728002d00c20380000460324241d0b61807551174041100758040e070b000021900400c82811000c20003000b140c0480d07040c03140150b2a448035503051401c5200d124500c3c041001d040400004204124042c40d1103844210103030740800c2420002c10512250070400180040c15420000b00c0175070180d0320044c1e000300200000901281c0320303a50341010a9502c81c0070340c2c41da0f0007001001706069040040000c009650303500c161b110351641c1e4641c4084a9041340c0181303d070b920004810700603489500288010350704514140402a2000d1025004000a00041c1d002034280403000c5000360041824203103400b007840040250300e2541e21100300429482410300601d008050f1100c44d612020031607001901c0c0500710156045070001c3c803442c00c40c2c00c0d40049240d5000c0e0344600441036140faa41250440c2d4081c00c108801d05001c5002a0041500280007007035480d0200a000d004040100d40520603032090f00c1c100128240d1581c180c5070940700307200042042c2e404080018282c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 264718345 1250 264717095 264717119
    0x340e0406110a2f0109200103092414011202010e010801030b041106091815010905060715021c050402010315080d0311070b07020a0b01060f050a030905070509100f0e070801 75
    0xd601a0003480f07529440034640341c25143c1c0c8082c2900c260300b564011010000c61456541408402401c0030402d0717081c0341e039030032007000320300380007542203445040442c88485083c2c0c204a00c00d00c4e00a880744415a150704405c001c041107904164000341c07846196a030654003404109050301e400551111f0a951507944140d12001c842140c0e542100c0c090011880c10b0b15401c45071035401c0e11054035a00c0354544aa42c403464225100b150a040bc03498140c10040d60b100c1c41d0840342240c1d04920148410b0440c465448041d110b101e04903940c920b02038040c01c44004866101c1030055100b44ea0510100c42806e940f00e035000340d503004030345494010f008a481003500940c4010918128955441c1c10041c0030744844062200440d00000940c01c2a00e560302046943c003180783c09400c06003071035101250803e9006106029200c21481415592040320041c00410810340c030091900900d041d03058541003c0c010342c0741c000f43c0f1419250305108013001c07980c0841c031180d0900c10307100366403800010780c038211000340e503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 264719595 1250 264718345 264718397
    0x80f060f04020c1011072018070c050a08210903160204060e0f01030c1d060405060609131d0a02090721020d020a1101020705340e0406110a 61
    0x51407150740a403103d54000ca01130300c0c84002c1c0c80305d44203888402904200e10000003c0400d045a8240d02030104025a80c070303046d007001080c3c04000008203944102c815500480b5494004d8a5807003401c4100e002c011076030000f02819980109443c01c1c41c02c200b200b40203d034000b0f942c00c88141d0414050043d060106016142d0b000d40014404100c0a40c0c1c1e000020030b0b48000d403458130441d0560001402030011702d41c0010000c0c0801a0160105903580060010b00040030303004d0b51041d600c410100c7c0c000d640368019100d40c814000d0481c0c82105d01040f03c1d50003041251000307880d01011b0081100c1c050b80204000485503005030507900282c0c0e0707501c000c43e410a10b143d45030303601d61180903031142010380d544007a1a1004880c0b0005a41340181840a08210303543c4051068903030041040c90300152f4089101e12440b50100c1c841c840d102ca203041481009541c0c1070b40d03444040c140040000e82007a40c02c044c24010742c01441c0401c180b4003044d900c00b481c1d20406640c4000300d8420315190b880d0015951031000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 264720845 1250 264719595 264719617
    0x1118130b22050d02010c05120f0613050a05010f0605070f120311070503040317030610030e0f030d0911040212071101020d09080a0e0316090e030d1b080f060f0402 71
    0x101607480d035401a00c18120154041d24198494a1040b008940903c80d0124280050810500740b07540f0180143c485c4400074240001341d403607000402c00700d03118100c4d407040700d80010005200500d0150515001000240726107140c8410034040092560f0040048034445504039140441840640d03c03850302c0c004081500404044c0d41e601c05a82c95080c02000d0500240b158000e180d40383e03c0c500313240c0c9601d041520100032030401003040c04401da80700d6103040c944002c1424045004146540028103200340321003d60018000021100310210b000e6000c1e6004910480100c0807015441c0b003400b0403400340e002500aa00e5403007010698040c091070104054401c05400549070809020742c0b00300762001c0c0c0320308075505800820004040758106910708101502540200201942c00e00144101c507568844d42c3c0d00c40e995051044115031043c8116440c00c210f1035000e125424070542050580400d041c00c1100040580c0081088288281355890155038002e0140d00d680b000e5070708120095001561760740d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 264722095 1250 264720845 264720871
    0x206030411090106020304060f02030f0a03091b080309210c011407020a0e06130b0f100c06021603021501051f170c090a080304080601140607050102071118130b 70
    0xd1007640d1015403490181030382d5800b85468600e40540a016030704008200f106540091044601c28031000007a40c0503044d1603e00440c0d400c520b41400c1412509401141c00c0382ca56503240403540f400000000d001c3c0010664400411201085841000c2500002c00719101d800002c03050810750304c21003980214030048a0682e1410584d5800546040f20325400f00988460a60800a40f0300c1e03e040c0d0030030302e03a881da0f0307041c049008040d000a03092008180890b102e251700900600d551b82c030580051040030340c0980c3c11540c1c0c807282400070911074a40036080740140702c0d40c1e500609111160340d00504994029042203030282400d8940030001d07204604074810000b001f194803103056488815107000d01d03100e01901e0399034203402051100501843d0401c09185c3d000700002c02c045940080c0482c1102c0c0440c4d090100c400c82000000c10611882e4009010341d800407901c4401d000c40b445411003164000c43e00312031074200700c074030044c1030310f071308694104040d5551003200c0042100f5a01885d44203103405009 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 264723345 1250 264722095 264722123
    0x1050c0304063206181003080d060b041e061106010501080a0216030306030b010602010903020c280306021201051005090d02030f0d02060f09070f06050901140403060b0f04020f0702060304 82
    0x407005440f032009450100003280828451031303082911049030b210405601103281031070410107450314100103220042102c074000419030704440d505e0340032402408a0728200b0b40c4d1166141c054252062801d401079490500c07040c030000d4814050002484840c41307003006064541e181c0801502d10042c020880041141c007000010401c070405c0400c1403045100c0e03100003072040e04600300801d81150517000b0909680c94046400046900040e20034503102084402c1404101d5010503144c20018056070a042809010004000c0240c07607006448102c140043c0d080c0c05a90711800c03c4a00c0740140d207500c0116104100580700c50030040c1d010280b05001804559429010003c0d1a00e40002000547e0058000100380524400944580c5030852684402085e40e1800c188a20301030440d00d01c00c1c41c081c03000002c1d0080c0c1350790084980b400344000316140c8940740d5a40382864000340c503c0071881e91003025183c891010b00d00d803070310903100800d031049211814084654240300e05a03101a1040c0c41801c0d0074120 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 264724595 1250 264723345 264723401
    0x40201031d0a170306010203220302103603030e010c0203030316031b02150406150e070f0908100f09050f010e0601080715120f09060c09060201050c030406 68
    0x400c800040700041014401908005150b02c2840f559200710110810500059070b9001044e148082000030101100d40c00c84100025046560f41c80203400040c542007031a075107900082141c029821480300356071842e007402000c0080314212031503106801c100c45000c0c03010034410350008001e1803060402c1c0031401c04640009203107400464190701001d4086084001c000d60500881105002800030090350100b4108003a441e40c170350301d11007115541107000243c184000f07070b0010400705046081000015481386a2460300c0042124008046034025044015040c4503080c00b03000c0710000405030440c0d02c0646c190202914102198582d803640300c4c0d107000c0c0400c1c0c2c144440744038881c0e407500026817007030b507444c84600380f6905a1051001e500960000c101190344c00710f4001481c501c03850180780f201c02d54440c5000528000310301c41b40c01844c0c00f9020017000460340c00015290f909032648590a035a80c50102e00f0f850b03045903900d43e5460305001007000190160800080c2000c40641c502004c20140c0e5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 264725845 1250 264724595 264724631
    0x1020f070b0315180402101707020601050a050102030c120a020102040503010e060a0b0307150c03050d1410080d0c080d06030b07080a060f0506091e130e100b1804020103 74
    0x30800d040740c000b0501c04a0320410341c11200e840000d8602d003102c4408600010f618100041c0040c0c041e0843c0c50810400c0d0b44550100c11b00d4105041c06440d87d420200c10003580c8400900803103010300d8950b880454a0340c000400d0743d00d20f51601c4001c1041e50b05a84a00aa540120b2000010340d9003d02c40422959828000e103000414180000c1c81946007911600e000d90304d40090380d50113a000b21009000450002181d070808105078141119206020f1074200d0306881003680740300050b407401d010306101001d5481000d001c4e07a400b001c001d0b48940c48104040c0c07130307040c00f07024040072a406185403030000b84002c014225010380000d000860954035211048451400c64000e80040e00003020407144100500c145000b92031400c054001d19030900340451000c1c89001e86151050329503d0380c409160081d42c94114504c0005446640d404802c40382600240081c0b005401c6c05001318820034000002901c02c0c0803003c080108580b42d03103042c2d071000c03000018001d40143d0400d61a015080b400109001d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 264727095 1250 264725845 264725849
    0x30c09080f06150d2117011203080c0301080a030c020301020f16121707110708010609021803120a120216030c120e130b040608010f1d03070c1401020f07 67
    0x1c0241000e840c00540341c04a49100b4200306104280c15803403800804c00174504805002680180c00a01c034080070401c1d107001c1038158040c8014070000d0008503184c20100703101081c0c54407e442d2408a52103440c004103a0740024001c0070200e40c4600c65840109208680c84031690340054001890f2445e0400c0e00c1500c1d80c046c04840d081840c41300103000800001306545502542c0c10f15010b6000c984041000b00c2000014080204000740300c03080645542080c40290002d02e030480003040902c0e40c42c0c5c5000040e400a942000c1d40c0d40ea94008103140c1e09000c15a4042c07801c0b42401c4905e4070300c403e40c6c01c0d034502d03031440e00440160b43e00b07114200c1d5a1001e002c0c0300070380034040e0702c3e1955a0500c6240240e20741e842014804204000708a45444545501c0703035088041300c4802001c182c6030007007004600246429404480698203140b08940d414907903074008142084961100c80d2360f43c0c40180c800303541c0e10640d00c000700f070a41031001c10480340740f040c1000d1501c141c0501c181c1e110340c02c507840d07000c0c40c040103a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 264728345 1250 264727095 264727123
    0x50403020a02100504080c010e01020c09070906091707060f02280c08210c030d1e050907140105070201091d07020601051002070b0f09060d0b040506040912030c0908 72
    0x4601403406600d01120f89045000242c034241e80340505080c5000d841d080200c0c006070502c60f407132207829550b07030091251101582e4060048003e52512039401411030000d40b04035008103107455004188860075841141e141400301004040301803070030710b00300c4013404518110300440c00703007040c1d40c0704005684c2c0140e800404243d03040301c0704e85030701e0500c0031119501e907000243d15448514050048030003452000c01500702100d0b03403502c07040c1d01080207086204400074040e1301450b000000b0050400e091011142807e90802003180d0340e02c114846070b5882c1580180c02c00c40c0d201c0720020f003156204c0e41c01030071028410b01d0540702d0302d540d951541604c810400c0003281d86601401c1008511541044800d00401080f60b80002410342102c000e503c8050314003c0000178880024041086944001121104540a0007807503035000784900fa5030081480502c454070903828040410260b242070300a0030000f58015041c1041004940419401401180c00e00c0b01171140031880010417200900801000d0444 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 264729595 1250 264728345 264728353
    0x4060203010e070306030b0f0402040e070b0310050d08030c090f040608030c1c170a020c120705070e04020f19180f0b030d09182007060b01112e05040302 67
    0x421425602c0040020540c038105850181704001103602e901c08560020f40c00400d0358202d840754000b1030f02424030928030400707034070405900044c55104540203602c21410044100f41140d102c904100c2c101a856901412044040c0302041e248038440c001884071860041c100400d22041c200801d0540740250f0041c0b885400214042c0d80422050110b0052426040b045d0200700e480342034042c0010101004c4002c00c1c0203c400054404000303541102d240b0b14100040300c070350b81d01078800c1a07d00c0c0e00640741210240118100058440c4e0350b07450080c0030781e5000700048107688030102840a0818245449030185400b11b00000f0700c0d081100402c251007a11080c045101c804d81e840c01000d0310141c6000318080c1c0e002e507002c1c80d10594000e0500c0250b03400e64180304021821800c0100c0500580d040c1603202801c07641c1d203103240401030001069031900c0743e001401184403480041d100d0511070035460711540c03c8502324044c4240c00d0120340a004d0010008890b045489480340c000700e035012201240503901c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 264730845 1250 264729595 264729599
    0xa03030203010608162708010905031b1501090e0a12050306101e05070c0b030106091404150302040b0d060905010c200304060e130507020c0a0504020a1407080405090406020301 77
    0x58413000144d80401d0440c0900c95124648800074444400c440402081c01c51181d040204402c40400b080010455980280030a030a01d0401e95200c2c0e02190306150002c0b0040d6040a03415800301d000c00351100030381c0c40000660b181c0b00e02030f0060480c00c060b4456a0062074101000503504290811b04c1170025544d454032860154140525032441d007401c0310074880c156401090f8851031a000c221180003070314050ba03d0302c2151504000241594110143c4800c001c000400c2081d4041002011a130078030400214200c4ea903c140001c032a0307494003e00c415103010030140058141034000b000140e0026081002c3c10752561109012038000e4102210141d44620840c565164803003401d41c82d103503899014104804410303030195a240300d54844c00060011030b5103168515a6810b41c00c1c440341500c900140618580014003e445000c0f946005110750103904010913981014401e40700000c243d0f86410b004500b0110454003141c2000d20129400e810821000c90715441d4050000d001300d216035005a00c0754 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 264732095 1250 264730845 264730847
    0x160303030b041503110607170c1501050906040519150504050604050f01030605060109330e1005220605040306051506070809041103070e01111506090c0c0a030302030106 74
    0x524107044075214a0406035116184a1244034001c11694086030311008010441c0c0030806900402c14003801d00e0340f414211046064401c0014005407501c5820382e09080c5681280d5800d020003030140715007061a0100003421800c0c194030050300400c07441201c403d006200c814070010389030f1401d905942a084940e082205080c18055a50011802c640521161030b103114429400d00301440058011503c520100300d040e409199514003034201d030440030034034030340d0f07000035402c421f50702002da8010340c042107103482c50503104003000d00c06000c2c0106981620298024211f03400e03002030700c803091440c2100d85981190a94452808010150347e182d050315a0b1440c2003c0e4101c41c001092400f090054950254107a81c43e2411601c2c41d552140750507403910054800f190051014070508442001c0000510803416040500010300c20f070f00341e0f11101c0221103003510517150303000e441011644410010100d0201e141030b07214254414424079101c0c4c1400c0d14291410718050b20f0840c01c0e4003103580007005120007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 264733345 1250 264732095 264732101
    0x8032419090f0501050d031b0206030a05060310050106140705010b060406031d0d0203040b2203060605100c0203030904110f04030b010e0c190e1c08090f0a150f09030516030303 77
    0x10302d105004104a42c94000402c20606809000404110404400e283d14031201110f03d0045900030f0030149c0c60340750090820300144415910703c2d119110341c0d1499584c400c0540200740c143d070750366a80d50410030b010b01403441746c5411421040310030f952105001200e1b81c0302d0302d025000074011954045280e8442e5100f0714202c049411406903240c00210302e90310015000811101241e40003401103965540e03244041003061040b008001c80070b03424441c004144200754024405803078045480310707900d243e0a00300340c544041e0202c000350543c000740044030031440d085e8000c251000105941510301500c0c0148404e0950240d0400c4600081031401070240031070000303600f03920030107081003a481c0201d2110030003040d00d00c09558400300081e4282d42a05034440085016030009540051181c1c00403503c3c00f0f244e16044040c925014080595080c605440c0c0240214107e031038040c080520013440c0c08044a03142440f9030007405200703c4407000400a01c04000003850741c1c2d5000100d20200c0e085180003015 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 264734595 1250 264733345 264733361
    0x1e12030a141f06050d0e0a032007271d15060907020327190e10150804110a0311010e0a06021020070318120803241909 52
    0x11116440c0401c00c12580b152400c00650f4080e0030100c2e210701070b41c2c4483d40a05000b41682c0c00f10f0040000d03040805070003140c1c00c4991092503041001e040d07100c03280d840e552400d901c6040940c0c001302c0521414100b1076065444480a4404041001b180358502c1c0d848998502a04030045d40c00181070b41071602c042000c40d031700020203e440755001e00317081400a51740d000c0c1c014440c0b4600b0341915184841000381d40104522040900211410540c0e8200403400304207a200c1d40d0805400900060010400a800201625034030881840c1d0404003200c11100d60100810442d0040c20050100009541e01c407030319001540f20b0600344100c2c03010100018440c411400701c560080b00801c0003800455008178200192458900c0002002140410f4425160094405081d8002000149481031560003010380c03180d40158444006001e646d041d030480d42004010018004100510114826081c0450310540310004500180c4111782a80d000516a6042c0902c0b11018480325004000d034134564065102 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 264735845 1250 264734595 264734611
    0x90605240109050d080c0c030d1206140a030b0901060b030a06050111010504020616080d0e072303071203030e0d080603010c08060f0114071a06041404051e12030a14 72
    0x2c20600c1c11000c9030ba000c41848001307003944400300b000704a0020800206907544001411103000228048000d0090420451035020042c01c00d50041132540002601264241c005820222a80d14640700c4152062014040000b01e5403a03400c00506c90b12000095406554224400500e4a140c90005000b141e40700d4811082d59041104010150b61104183d800000880c0303410944c0c200d051a1240d120300c00d200b485060180750610058002070001071200648000d00956882d028414080c40c80080101030001e40c1a400404140188610000c12a000c18481d0070003048e864600134181c0e0070144042450f8001402050401005240900600c5103c8606060180307042c00c00c2000314100750740c6660b015044c44000400c01d000f00c0928000c441506410202e0300b42ca0012040900c07542038000d44a8030300ca80d09290340b144092214090f1180500d5010000700313010390703510400f40f1590380e40c0d418a044030b00807010ba01140d1207480c030046105013240030000a1002d1083c3c240c0340d4400300604505 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 264737095 1250 264735845 264735857
    0x1e09051206101403030f0304080301030b0711030409020a030b030d0809060c0f0405100e0d0303050f0618060405060103020d060b0306041d0d0c060902041b020120070809040906052401 80
    0x1c405203800d020340043d280248002c1201c2c00001010070300e0343c4100101c414841000204000600240402640c1600d1055050007aa52140c1c0421211031010700d00e021b01d6030b00108003c00c154401540280420303040b0b0708021030980755403000607007003184840940001c501600100302c0300101c140040c41e03000e6062104542031050b41410040207000d13501030700340181c59010740b0081c0140200e400b0754400c8030003000c6503583c0b000d0b031038014081c000a4608141c50761005000c20a146000c1c441d00e4102c000c0210001d41c1c40d03403040d0070040a040e02030305260601d5801c110314020100b081c0a0300c40640541181d181d6281800303c1400100e03445081404111b104411002d20200c3d000728000c03900511921b81002c2c0166941030201c01003441e10b800070b41c42440c2040b5010442003454642c031076007480703400800c80442c0d0f008041c4681c603041000c0880b00c200800c03d240000d0315100c003034010200301502c00a035031b400715681e5200b110340c10740d040d50035668100402201c01c10140e071080b8140c6d0007841e2036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 264738345 1250 264737095 264737101
    0x80604061206050a02041e030506010806070813020f03070b0913060e01030f15060617070807140703020f0712051b0607030e0d0204050106080a060501090509161e09051206 75
    0x32080c000745003100140015100da000c01c440d150240c06850203844030f1075003180420f40444111200032030034481100c0d50300074000002951180491a5846003800383c03110300165840d074180e10503403000c400c1c00700e0307000e42c1c41d4112510980301000120b015081201200f40da40014008201d41c454002401181680c05d1080078810103002076640d030304403580a50614480501803a110008400100503802e282c0d107841000203059501140c2989840c0005003070381c80c40e484004003104d014108a80000102d03284007000d0740f10500140c0141a03080c000c0c4103840005520b0203030a401c250180c1c0c08140d251000c240541c062100500c2246954841071142c07101d040074117000309600c0d00409101500340f1070203142000803034944d1042d0a02ca20ba004108200540e10342201070b12400c800c4d56030705940c03480c008011070654019540c2d2001d45900404d0403101d6500d20104a1422034907181f807000b0421445081488183c141860f41c041510903190204621f0410042c0b20520040c2c00c50410710b0780c824428 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 264739595 1250 264738345 264738359
    0x60406080c1005130914070909020c06072f07080708060405070501030c032307120b0616060b09040f020321192627061303020712060c08060406 63
    0x7841041c0d00b03140c104903840f90540d04442e80020000d0b405501010704014000c0079010700c480c8030500c500c0780346d101c801016071904072041c1280900100c24415500c09000306040f075000749000d0348401940200c5138080c11001034062030701040417800c2000c90f0300c450700034018060107100040241281400130319135842d06440f6107940d05000d01c105810b040c0e41d06480170f4480c0c0b294009107154207400852602d641125100e642c50300c43c044800d04001204000c01312052410350140140c040e00c014505800c001c81d6207203426907642c04460072103c4695034039404d5a0341e100d030300b5120300c140e002c1c03681d003017514070f4900605041c81103a96000c0c869800240c00c10f00c8164804060f00d0044440b8205401c0181c0014002e99001c840d40c11140c108508004240103070200c000c014038403940ca030704000008005080e1000484d158900d00001e01d135004040010984075102400c51500c43c064030490745030f01d45e1100e800e41c0703600070040306540041e160f024040c801a04050540e07009282610104110303464040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 264740845 1250 264739595 264739609
    0x6080c0607060e0703080301080c10020c010203041e050d0302060901052203080403030f021305130e03040302240d0e010b01080106050f0a030f060b36040c030e15060406080c 76
    0xb4241a691010f002c0c409608000e03004c05580d000921680e6541c590000e15910020a800f19205440c400c181030700b201d2010078403c601c2c141c1030f001981041e00304200d502c034849032010100341035400500c000a81e9a614410461124000e8015185e03a0400070586801c0d182c0041030010014140c0d14030340c1d9482c4075000142c190a030035160101c03142d1102e01e0100d0141414003500d004c840d0010600c0101c41c040c84c0c852004540048038181118a480c03120b81c1c059901801c58580305800c10f20007000076041003417041d42050010b604160340d214400c403054920360444214113502d169a445a64091807003440b42c20b124400908000706e0962510000429030f1040c0210714403541c0e400328103140420300a421040703d11160740401e04c940354a40386055001d4104081030b003403020b000d1409172264038421191400003a400f507000c40c3c4165001003400042c14520303400900301941c0e118003204d020824002a01d86820051100425042500421043d205150005440e03508001c0e040f501940d1f50103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 264742095 1250 264740845 264740857
    0x31c1202090d030809030909100f0603230c0d1e05060d02030c041109090f0601091a0a0c020609060d05040b0106020708030d051e040302030a020105070f0e01140417010203010906080c06 81
    0x11500600c3c43e84d1703e06805c0d007107001d0450420742214140082c05003c3c2c000f514402c056803440e103030200c0d1407543d0324001c40030390340c1c102140080b103c2c9402c403290700304500c10080782d03206103801c280f1898221204958000c80701c40c480b608906d0041154102182a03940c05900d42008003128411407501c40c1c0e80000f9160300040d014540311740d07a58401000c0c4030030400b00b55400c042d0020b00104452034062001c00300f00c403045840c5070006096081c04030781406c9115040301d000055a4100d82040d08a400c15030750070500e42d0301a03070302c1001800060781550ba081c00604c094040a10302182c0d83c20145080f074074500044c0c11040a5400031030041c03124a00c0042518491450110f010640d900c035240d42d51100781030301c61840090300002041105154000004082c84500c6500030022582c0d600300c100d4040c1103042154000403c26a14030f4001c0d032180c2003800707000c1011030b24a4a807941e01c101030700190040203040640c40c2d40200042241900700c1c81040010000d00d009040708200309070000c1c4044c801c0c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 264743345 1250 264742095 264742097
    0x6010e0103090506340507060b03070806180304270e030a050906070c051002060f01080607210b12010f0f02120c0a0207030b04030c2907050a0e031c1202090d03 70
    0x56040480843d0031111605c14600080740b10101c9a80040401804e642c490360041e50742a08280180c0414100020308c041210320200140059445424504042c0351801400902c40d1105110118001039201d070001031001c00020107800d0000000540c2095417806280b1007229002808500d80d4640c211003211721200c2c0880706c00b56200081c1c6000450104d25030402d98103c440000050402600000c4040c01078400401c2c5030342c036070703695401c41d0344c0e9031008c4a90721700042042110900002c038070072502c402c1a02204010407514184004115042d81640313948240ba074440c1c9122498200d244204032041c0344046055141c680c1454401001c41c0010f000008205c0002031001440c1d40b00340807c8001c0c6034412240f17070590415003001400f6180d91001030312007052415850709064808004440f0040004c88036034155566084182e440b034008501c050280000714404039200d0368180003210007185a058402c2c04010b8a0074002c010707a602148544030b441c81006512490359a05e500346820a0741 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 264744595 1250 264743345 264743371
    0x51213021804080a050f0d060801020a1812020609060c010c020321061c14030a0513050405040302343f08070606030204090b060906030307110d020d02060f0306010e0103090506 77
    0x703070a1b140700161082000181102d4640b09010401120640052140c465541c1c2e46c3c0201c4101c03c41e090704403000034450240300004540c00720006050400160803800001842541044801c40c64907081d1135030840c034200181c00000b284a94041e01900040204510007401c041d5480c014001c6040340b03606400c01c142402d100d070340782e01c20080740340142001400e400c0f007a652a0701400c0c00c00303085908240f100000007003c244c2d01040ca41000d1284074440c1e40c040d401030588c1042e6210201285c804c85010700d0300201801e40040d0400c1503848024018201c020355003c0d010511413199242080007901041003145d66080c4019a520b09110a030319079400c825000d035a41c0d480e1620400274251070788000c0d0024200303400301c400d202e070386245248102c00641c2d91454643e40d140c02c06840c1c1c0b05441c8010720401a00600b1401803c06525000503280f018003141c202916a4000984903000000180101c5000004010b450b5920025480b0842f200b806c040c854459181c0c1c0381d0784c0702e1134028450148148 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 264745845 1250 264744595 264744607
    0x5101512141606030f0c0f0c050f0a0318050d08040603020a020c090c0a1e0c1e0b04050a0620070b0604060302040606020a17070f080307051213021804080a05 69
    0x140400e0201100302441044508609107110034000b03080305880342101007890151001080705043c000c04444540d19603410400c6038050034183e039880c0c2501c0017690103205102c0464401c250801209107040d00a86413140c800103c0100c2054070317070403608210300600107921040000307100282a0b07020b85030242005a25101001c00c120b00d0040d01ea024982e02502c01006c1c8280c042c00c0a001f024545200d0360360309101c00310660300d848060001961000011110078041c40803900680746d1748000741102d079119816107a243ca0313110800005480640c2d680d000b842c0c2c100104000ca200f102c0c1c48422441780260344016280711010103001d40480501100309020000710503a50b154032080217998001d104003c2d440d21410000d50f50308020000712045c880c1030b081710100c1110442139a12440c0d105800900303416142d0b84144042d000070340b00301c040c0701c0b06000f0107003205a0054210300c10145000132009148140c0100311040680e0070b0a5861000100c081c00041842282200d00400305820515600c030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 264747095 1250 264745845 264745853
    0xa060f0605012c030a0f1208060609100909023006060f03071b05161721130e070306060804030e100507050609030a020d17060103051302030d02010905101512 69
    0x4060f4120561500035038180c3c0e81001808030003a101c00303000f040a07454003501c034031042c0c034158001d0740c40550001007449130180b14504003005005064103490032004084c0d07164250b405903044254030b4600e00420052810450128244429501504800100083c10a000425928440d030240301884010010003d805035009815070140306102c4c0280720706180c96810016200c1c00511581d44a0041d20300d00007440718020f030b502005001400000e400308640440c440d452003c0d0554880d10f803803509001c07500c02000240e40160040000c02d2003400c042c54190f81c01804c03904a90004414002d8240c00c3c000880d6100a117000c2d01d01c000e0701c0d200c4180c100613000b0f50302c50045034001806482040c040080d01030000c000f41155810b603400710f03030000303804100680c1c54030920440d0a495040a00c0003d5a0390710a030013041e04540c0880030603200c01142d80200c2e0070041d481043d40e003d81c1d100c0e0021010000e04000803104486884400c000c18400100392840801891040d5a8525030541c1c44074248 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 264748201 1106 264747095 264747167
    0x32d27050108012310090503060703020f070605060411160b070e03100c031e0e160513051e01030b1806041a07021c020a060f060501 58
    0x190f130900070903128050140da4030041c45507003e825180e00743c0700c0c28000c015401150340c4141754030307007050181032070f020b0f024010f6070405104100300e0292818000c10f0707443e100e42c01007001c5455111040000e0207810b030b00e00d0300e441542e40004d0745110301001440e00c644480c8155038020706a0703115242520225140c0000c0780c0c154002c4a25940803950035807000c0d05004880c100000e20302c0d8054450090300c0b024207042d658166844e03140c060f03880401c03c80c4010700c00038000c22010130341c01c0801081c4074803a04083c0c0ca24035900c2d00c000c103040102c4404059046d0b41c044074961040c0d031303480c00c0821400206840eaa020200306140c03407011404003040740ca10070b9400a20b044070181c0548003414001c080100340c007045004030070262240c1c2c13100350b902007241e01c282d0303000300355a0001341029011107190901c40e26100789400c06c204002c0e60007a00108103001e06411a03c660041d9100c00c29030 = true := by decide +kernel

theorem cover : BRFrame.Cov 264568345 264748201 := by
  have h0 := BRFrame.cov_init 264568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 264568345 ≤ n) (h2 : n < 264748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
