-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0383
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:31:47.308529+00:00
-- url     : https://prove2.me/submissions/dfb351d3-56b8-461a-875a-0f92f0062218

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 68705038 ≤ n < 68884894 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 68706288 1250 68705038 68705107
    0x11061b03010b07021c061d070f09110c1501061e080105041805010608060702210409020d0e01020a080103020a05061e0903150709060201050a02040501050711060f07050102 75
    0x104016241034078556540250790b0480c500000c1c104100741480040c440c0201088001041803036080b0b00b02c26503070b000d40e000c47d08401402082d1030711031900400e842c1c00b88171042000614419040f01ca580310101084500c0c00703141c084170780e082c02c1d007003080c0e80c04014240c8010400f00364800c0f101d000c1d4120300714a0304102c80b030840e0003d0299006201d11440b50340c440c0042d00d0310301d00400861300b005a21100800040d5543d802040e00d4074402c80300d000c054080c81442c01d040440944080750f80e0f444520000d03241600b0440302d0b4000350071260441455650311004038900c0402407004180740b072003030344403140c0561441c81007003421103150f080740d4055403050080c3c0c91503d0790040407180c0040c049900c00c1d250140400441d00e05000120400d610204200520109540141b001c00949800768003d01c201e030f03070f804480c038164440d901c00e080c0010420001140803845c0c60413400781020008003914070f4445182203031a501e03008000c1c103490300d943c009107103008800f40902d500c11610021000c440c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 68707538 1250 68706288 68706331
    0x30405010e1002030d1d0a03020a05010c0c05060f190204080307020f0102030f0f090d061b03050a0612020d0606180c02160b0f16080703030221060310110903030a1106 73
    0x240e015065043d5180c41c0c451b0040c211180c0c55440400b1801d81880c01c907034030008142002983c914401400359840d510b0304181100d6a40b08405001c10290803800400058640b219903142606004000300c00012442125410798009130000b84010081d0034010750300c400d0380b80100850740c1103201d800380c1035600801c06a8442e0b03500d03000340c5804c01000030025854181180c04514080350b200c2c0028012441d00107030100c01c507540c1d0090f151840b116601001140c3d07650110b08100d030f001d8042d241d00d54146032803410044c60000b0851501910690703011800b00d50f16684550641c92034200345000da41c5500803141e8850303041002010211902c03e1120b4510b140030038401951107a121407400e0402c0c00500d6444080c100c26070480601d0340004901e90b0f81141d410003c00130740040c908100d81075440e548a1509201422040c0d004940041c0a4600b0100e802e5800000b45200c0c070084280c04428803580721250b405001030400f400e4184c40b000d00c0820700207403941c1010700c010310301140d40a2120b000c885 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 68708788 1250 68707538 68707543
    0x10306030b010501030213050604080a0308100302090a0203130b040b010611010615050a020307081615020a021203060a0305030430030207030209060d060219020c151617030702030405010e1002 84
    0x1101c83c2800c0050340c89901c620360a032035090700e82003143c0002e8005400a0203600016180103a07070f00a503103401c0c4c29114200b0074403000c3c2e00b902c806940100300a0201d00c59049a03801960001b41c0900001107804250741c0d017445c80c0380201d80a640c0607040384010041150020701c0c0e015001d03070b118001c01000e0b08202000c0c04a0102c1c1031100c04100000c1107000100e402001142c00705500207002540314409c0b0000f24260035140d05088640316240c2580700300765032031402aa85030110035005131020b002020300000c01504010200e5600c41c0840000201040c0e052008001030000c1d5400d40031700b0007208459110600c005008800004510509480401d0340403404600340d0354100e0b000003007038680300f0000304102c07040c41001e48854070002e0f400b045481c00504103800e40740720350244d404014158081000b11040b940201c0c150080410062030030300d004a58480005200e0142c98415900b610b18505003a0401c5842c1400360b4400101403000751b070805100e0a5804046403540380440c2c0b5444000d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 68710038 1250 68708788 68708791
    0xc02070e0c1e04090504050d03020909070309020406090f0f0b030604030c120201020405040c020c1005030106090b1e0f070501060b04031a060102010b130204050901050901030c15021504030305060906010306030b 92
    0x5641100100301c2e00c0d2901d840c4540c00d02101c9420009584841d00c83c4401c000608080c6d804036200d20610110303020150207030090722458240100000349680d14020154081e19001104a034001d0766540b002c6060541407080a90840e11080002400000d4202c42000c4480811a030743c8641d03c40c0341044006640415000f409079808001601030003075005043e4064016a0440c80c0d009041010303002c550740c0d00080016510104503804002e10790145810350700751000f0700815001580003c810701c28142400000d098210085146080c00b02c4074010040503034004071600616031000080480520109000d000040d21038620941c1c9454075540d00c102441c04504143d0540200074030001d01980e000b94030019103583c0142084210441504c80302e00250311500440d4811580000007048508207c4039140c141c0303510001c3e6501c1181044c0044101300070129007a000c40c481c8040314090b055082105078040d602c00c3d14085150b0a00901b00641818000d00407810945000000c102040301410800d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 68711288 1250 68710038 68710051
    0x20a02010801090b0d0213060909150f05010e0a1109030109032001020306010c03030903170a061701061809020607140102031503030304020a05010f09050303120901180506040b0a0b03011802040c02070e 88
    0x12220f87c04000c001009401d42d60b110b03c05203440d016029003030100801606e080a01c000c5000c00c610140441240c045035000e000c0c0ea40010000130021300c1e002200e512420110440321a1103060031070ba030300001d00307460b8541002c4000070511980310300c0841c03c4014004113601010001e505619144000030b1550490480c06030405072540542814540520304034241f180d503043d40f0b4812490140203507000b41601c2e00c91302c2031070742d01d09121094030001842030100352100501e07a01d101d4141d1840c61800740c4008181664032550811445002910040c00d8081038040040090b0312441d00310001b41001440403503045c0260410000c0100598910500c841580c0c0c090034904416810780500300c1d055401e64002607050704c0005000c8034184420b982c214418407655000380708100c2d181d40080039100102800174250361091b070201c0e0005d0303000c4a0f0a42e00014002d000941201d190001070701b5689520713884e11044115080c01001c4d414580543d0744a01000d00080081510f480003c003280c00009000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 68712538 1250 68711288 68711299
    0x105070206070b161806020a0b0a020405060a090e0106090308070b090129091303050a080c0d090b1b090303090607050c0301020316090915060503090f0607020a02010801090b0d02 78
    0x20011961440e040c0e0350419049407200585140401c6a6500e4100240c0014040340f03500c10142c40030940d10b00140160340350356015010110b003d9680034076050003c0c0048003195000c2c040452031740c0f2424060000c0c030184d40e42d45100945801c600443d066010780000c420000030000500120703180d102102d44050f80301086a10960380c0348060341c0180b01c07107040e026030081c80c0d0f480001d1012200b02120b85200040303d68072201d417240c50080403040740722000140030031410300020f1030490040d00203541c0400b4801d9420319006105a00d101101c0305008103c410795402801d10481c0300b40c4003840c550b42080800d0f03840c40c0041c0c840c0060382c0c03405030441e91032007840000f503d01d0801c00144126001c680025000b5510b90501a0343d482c07450300401042e100044041c000068001100d01540c80410020440c0c8070402c0c5c14541c003115160320040001c421840b0351050b40e211702008222892080c0c4166020b80140c401a1000410300754042e805504017030304014911040307648480307140000c1d81e41101c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 68713788 1250 68712538 68712547
    0x90319050a0905030105010603020c01050c03010621110703080f07111b03010b0d06021902010b0607031d0d15060522091403040e01090506061602120a0816060c020601080a020105 78
    0x20700b201c0c00307401608481e4055003800000a9880d070141c01400c0316145a400a2005941e80c2c14200000e000c00d1242000064081f091050f100c0c0f151002c11094403c00d01000c42c290351094640c00e85580000720840000741e03881c3c01c006641d41800a00303504090039107002c0e080251030918855a45819410061042c10101d841503000c2e80d007540100e1520502030443c942c080b0060030140000d4011281d007100c041e409280d07500c11130780306100700d002e4008000c0081e410030050781c80460306041c21680300301c0211190b031020a61b1743e40700300203016014410a03c60341e07074111010000060300e803680d006030f0003010010884204181a000c1803508110384040000b083e41840c200543d10803500c09811546000018001c1003c021205810341a90400e0400344811f403603442c00e00c003061041002c07c150403105003000030014039001000040c00d0a008040310182e0130203803106815503022856488545480c1c51040301048590700a0b40728039101d500207030040c0d61510b50180e4455244d044020704102000a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 68715038 1250 68713788 68713807
    0x20717010605030109150e07120803040303060801020304061a0612010e0903130303020f06011a030613020f162105041202040603062301080303060a060c0507090e0706030509031905 79
    0x52101c0c00420000700240058420707030800d4604080b2400040c0c45060400480c0c1c0c151340400500202105d054038644103084c01e82d9180d0038281e80014104508041d2190380000b0501800d001440c09540035110001d414402d0304c1405c41c82d04481246c160140e40144096007a41c821100701d1030468040d2a80220300f035403100300e954254030440038003a20740c0918030004014941e0000d41006032003202c42c212103599881d00c28401c1600803400056906840400020f6041c1c1030410f4070101040800703d0250900d110f25a0340f04043d040100f10130320003280160880107001d6040501400080d6041d00c40e4418411008028400d11403402442d10b0451584400c00c00c6483d1035106e04015a0400400c00444400c00542e048001d403201e01c91102110103000450076030301c00b0040b240078a000501012a8034913101003522070013048001a207450280683c0003c0020441c010015011403540c043c0161509000300541224005002504560300030300812180110356960032450b0304240c140140c42d0910803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 68716288 1250 68715038 68715041
    0x115050304141603050606030703080702041a120a0201021002070f140744031812010204090518061b0921060105040605060f0406030504020d050a050c010807030b0102071701 76
    0x440d075084503c1401c00303007444040107003608410389200340c4c19240c1513203514082655a032034502000d0a906001c005600061504ad804401e04114031590031061604910000d441c80b10191401c0e00680c00900303040e011580d041c1f000010180741d1302c0d411418a84c0300e455a610800d035255000f4400c0c800c002d2054050442042098000c0c20300d000401441c8840302082000d0308440b010400c203070b1804d80c02c0f01d50101002c80d020300403c04014019810409003810302000944803851407600900090f9480407851400c0c00148094030b40d800010840341403580811064229030a1100c180341c0105080c02411114986840c102000c115400e64844016900054841a86003641028880e50072165180f01c00d02141da20b048400448080014564540a0000a10400a44850741c1d030040105200141c0654401600140054031291140e46555103540ca0105051000e95003a40289502c200640e80400310990105440c0307070a01c1a003e000e0000303035030b0348564052004601464502c08030400c44c00d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 68717538 1250 68716288 68716313
    0x40305040b0708120c0c0607080a0e01090f05074a090109030906170609071403070e0a050a030203100c030f240807150c0201020307060203040b100801050115050304 72
    0x600580650360941c40c905440fa940c8185003001d03130b01d28940c00003810304101c002922a00c00589000e4029551403400460301c080300106014541d550318000d194560b00c09210342030401d8401c1c42d20b1400f04010b400c0c020f1030005581d0019040103c4c440d03044d210403c07000440440c42d01e0303407407140144072405044044540401010708581500170020040c8502c2c0540011342d0050003502c8840c0a1900c030407003182c450889105e40e0130200100e001045071400c00d0b188556100125140c242c0313054a040d00c84100643c42507818100048010703485da1007529107c0104030050608079669002c003440c43d03000c40d0310348120702209001e480d592642000c4050080d04603d140b0360010034108980243d10082e0210303410520204252610041d10106120000040030001e6602100c0b80d408a030407002812545080f08110490450006008100c0015440d0004d14011445003441610510f011428400c1c60b031040d0380150120780c1460010000480100c061700c142d00038503c0c0c00755980d40c031801c2030341c0d22464 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 68718788 1250 68717538 68717549
    0x106051e010807030e0d1b020a1706090a0201120f0b030d030903120509070b07060f050c09120601060509120307050f0d0f0f0206130516090c0f1704060504030504 71
    0x94100c0c0303401a1010352030285544500340c80700c91580d15404011022202018000355041e8044400e0040d0703507020b50f4010b80107042140d2204203003840c582c003091081c2d141e5031102d91441500141d20140440c20310550b03500c0031440c001031080c2803164000a240e80c40b5408280384031540c80c0c00607a50349910390082d00b41500050200c3d80d0383d45030414010020880c251040d40094078000040340c815240b030003018024601c5c0001098280d06103401c0302c002d544140b030122541c0b81d84d20600e801003141d5001d50340c45040c0d082c02c00340e1200100c90a12480403e40c543c4800e61750000c100500c200c580240c143c0b002601e0560380c183c07506480d0460702d8035502c900e84010f4140d00c40c1680f400c820520001d842900345580d551080c0c40340c0c013080000c0c0c419840440c40c52026810200000f80f07601100948403d41d00d000314104d0301145913007251029029441d401002045403103065446029070451315003445640d032407624078190030f104921102c2d4188040c2000704400d07210400306003418031503015a0058070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 68720038 1250 68718788 68718799
    0x50f0d09030801080114040b04080c03130f0f0501021c08060105090909030711060c03180a031a040501051b030a1508070f15030b010c020906011e05130e06030d0c0302010605 76
    0x340c80c0d00340608091424401c195240d820a081c4183c2206400c035031038042e82d441220b011003030b1a103584910041c0c101c000068240c1c8018403140303208100703444c4000001d20b000703502501410705055500500100c2e0f1b82269065600000a01c40030442e0038000700d504c00d40516003448561200d0b00100c038203107d40c240c11544081008140407094034040010a0035502c2070107458080a2000c00f4410035000c0da84a204144d0401d00c104c00e5140802e11007561840001010008000e403203540b0b04428003c2e09064081c2e00c0602820001003200912480f9003001e07241d20500399801c0c0c0415a590349120082082e012507841c2c074062841100c643c0380c0080500cc00303074243c2e03211a031542800c0c1c1880c6103d225440404584410320b00c005030180c40344144c00a01030313480240d0080c40b074080c005c8045000d13001314100316109000c80360440038400c40601e902c041d40d949950702c0486031008014403c0c1604001d1070321103110107021070307581d0001302d40003050500c0c20609110701660078103074010825a8461500207 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 68721288 1250 68720038 68720051
    0xd230d090f1403030a0f03020910080402010305090102190507171b070e010b04060309020f0306070e1e01050912031608070203011506051b0c03030703020a1403031006050f0d 76
    0x6400021210a032400c4940500ca29681d030168241c000d8410b81050341c041d0802c00c024100e0b98840d14441092428074100940780000304400709840100b580d0b548000588a1402c1c04119a45801800e420071561030081d820110411000344600c5045080c481c180500010300f8010000b00503241c0440c3ca00e0a29159290300e1449007408031252101d64600250144840c0461241c01e02407080d8161040140c60a00f4076013000304c10b400810103100166401a4540203500c55960300300100f0348540046c0c0d443c1c901400282040c004601e4580e8460083e10341000748800305c42e40d000043d607802880031210110081350384501c06041d07104116907991045481c403001020701000c44014081c461007507008022000ca1000d40d030903203040702c0c080c82c030000d00c0130448030b85070080c024480300480058605a0b19510225400a855544400d4003100540c0001225030140540302003211104181e1344061032451034080b42160940900d40110340c00d01ca000720783c042d03007500700206031020a00c2d0031134100b001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 68722538 1250 68721288 68721313
    0x1b0506040c090c020303011a0c0106030501020a03180b04020f2707200a110103110304261806070309080619060501091404050a0908040902030709060c020d23 69
    0x11048129415100742204180010742103840e40300d842c005103010340c0a10300396402d1001d40242807031899403111301d03804103109844062000788218001103105e04001641c81c1c0401e00040c055690540f8410b00600726050a0008074a00203800e5500590407500034044044010010b0480042070030503503400380f400c01c41407911104030f1440741e000b40c00780c0d140c0301260703104030b90104c801d5026851600302c1c2e5000f11000c0d0001070320341503c2c007481c110305040100d110700590004034402d420032141680c0500700c7c00a2040c112000b08841c6070103020781c005045c540001c1d42d0310001a0210444420b00807480081c610050501c107940450280c4203c0007526054240015030040400110040541c414600500042c0039070040500c0780c1101c1844007403242100607801084028003000b0140302c00d003600c400c481000204440010030140c80e0240c401038a034103003600018444185604400244200d41d440400541e0342e410419408039030015480d20080c441d143c00f95919000c0719842400340c82140e200c8200e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 68723788 1250 68722538 68722543
    0x81e04030b012318040311030c060a0b1009030308060a091b080a0606020a02011103130303050a020606040b0f130f0c050a030b030c180907120605150108040c090c1b05 73
    0x4955503103000240035111800c100c00086445502960b01810300804202c0c40000e0003131a5038410f0013814030076854480c0300c0b081411640302d0301c280c4403190001c0c1d040184002c1039120f501d1781c9147c01e8500003803d910000015015181c2c602000e418862a180050180c0d03490840c02c0e4082c0540030303410302240c101104c411100b844291104008200d9210006010085c1481601e0032150550300411000c0d090790015290b0740808a004e08582c08104808070b01790414511500c01903101c3e650729503039030000c103c0007402c00401410341c034407850800519035065640d030724441d91f10700700440b880600b03407111010032401010840c01080d1120300f007070305031805190068080d00b1400e00300e86007030001c4030717a0404041e102d00c0141401176005120072001c2c0340600221040a0348010b040c411240601e40700e50640020f40c00e010000ca856503221020030000000454410f51106401e0030f0481140c1005d54070300320524030740d0051070740305d03a41c4d5441031507598481c0007680d0000c100601008103007000380c2409074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 68725038 1250 68723788 68723791
    0x10c23070f08070212010e0309060a0c02031501030b1b04170102071505012102061b0a151b05030702070b090d0c090e0c0303030c040603231503010507050901020703081e04030b 77
    0x83c803650300e21702e0035910008107021b02604400007a025500d005000c1d410004203400c05c4e95130004002d295543c82d0f006840802450980b0340d00f85603010060b41c03441c540048d03c4c510007000b0580c40030810241c003c900b01030750151008d0300c80c0354080324004858802054024016060080d081e06602030101a0f480065445203050307811001c81c0c016024030500401d00c44100545000350004002c100807184488107034046441c40c0003140554854603420344032101000a42401542c205554070143d0240000b24030010f5011807960400c04e086141481000e5280c2046209041c1498000a20041c640c1d0385d0400103940c8540c003075078919006484441c800c004150600d049061031042038890b40441c60000290b03449140c01600c0c161810381031002c100c015040280c0609003000c1ca500c500c03500c1c8504440c0c018400c3c0100c002848403104482c0400d8203445001c7d01400c14080200b00040160f40d006c60302c20705507034010645982e01c080326100710154040c0304881000904003c100801040035880c0e105 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 68726288 1250 68725038 68725043
    0x103030e1005040b03040c15120f0504050c041a04060b09030f0106050913030309060e06090715050d0b0a0803070305040303020d050f030105040e0a0803011412010c23070f0807 77
    0x4204105060180103000101c01c6408010480500007000394903021030043d540a40b0902d10040e01c0380d030b9892012600e17032500400b00003141c6801100b0b03090303410b180308031311a8000ca91403e00c80d90825840359134403607444400345030090351621080e03a0350015680c04001c11000c0908100325450750f804a0002c260428107510340710340a003055a60034032005002c1c25050b0f503801809005545c5070022081c1e00700c2c026020440c24903466040e4030000c02d00c24402c81890351801d101420840ca0200081818480960002c002034512280b101c090980d000d0b095650341044840002884102480082c140d004642c0c40b04180b40b00000b12142055802005041103034880c0e004c0340c00319011640182d0b524000e64500421020702440104820310b41034110008006401080e02c4a5400780d460700d485030750098020020212481030700304041d04011134521740440e0090000c001d074411901004020980940d6104420300189040c0180341000304119444a0f81c00074404540700d9052400d415603411181c001d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 68727538 1250 68726288 68726297
    0xf01020703050712021503100501050d0f020a03060806240d03020a0b010807060809010218040906180506060f040212040b1807030c0501030b06070b1f1d010816030309051003020d0212010303 83
    0x111480d14420005483c040d441400b9242301090a2000440b000e81240440e110501d03102d90b4842c038080d610b880140a124019500403078aa402c2c003080a180c1500540700c8070720304840c6180ca80030814110130517070007440d04480e4400e0700354007420101c1c500140401c1c0a40f540190070700000b45050001211012030381503849180c4e442e61201c0c0e22900701c0c082c911000c2061110004d01041500d000e601150205100f2580081c00100102001d034454242c0b140448003584014240040de03d0003401c0015a6202101c080d8900301440310018821800a04001c2140a801c00814424920518011400b41c034050490b25880c2e43e03424440c880308610b04c2040e000c64900020420a410518111841260048030069a40d21604010403081c44030141c0300c1d0310340e0344049003c16048551f201d01400c49904a1072182c455040483d104d05162a807a40c1d20102c00d1944010000a03400c40348800440740b003250784400b50f01380c8442c03e8010340300d45007a000003144000b0341ca2202d42d8824491174140c80c003ea0b038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 68728788 1250 68727538 68727559
    0x12150b0309070e040b040219180902130b13020c01060b0307050d0b010f0807080c0910030204090507210203091002030106030914030a0210050901140702060117030a0903020f0102070305071202 84
    0x41d1103c0c40c07202a20060080d04141c4005005400c08085840a80034540c505407501c4c1ea40c6e4142c15040009070b0351040419072101a81000c3d454100e031405040c40c0c502c8001c00003c1105000602d09004802e003012445402150b6035100440030750152005117a6240929580e28094500814a40c404e9001d990030910340012030105510075030400401c0c41c1e0948504425403a50310090340c0f107400050041600407410001002240c031881d05c54010303803009807400740e00d0314100361440c1c040d1940207000108110706a03107191011151800101c40b009901000180d0303a807075a01500d410602c0c150807201e65503000000000e1440e46c1980000215800740d1000c058256030084550344922030ac015010059100c038551591100c3c0e994000d542200580e800003a40030320030703c012209200d044803044c01503000280100007a4142c41030180e26000060059403404902d00d401400040b15400007030b01034803d0007030114080e4002c00c1440041e54000040f14802981c0f1f1000035841c400c00142240190400503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 68730038 1250 68728788 68728799
    0xf080c0609030a08040206130f09060e13110d050a0b04110f040b01080105010e0109120c08070807080a03050d0b040603080a020c060403050a023007091103100612150b030907 76
    0x161407071103a856a413140c1589450b000c1003802d402201031801c085a5603180005c40d140302d02448401000000e9010410a203030282030350820380c3c028803600c050302400d506040081e000c07900e07500e20300400b280c0101c0e410089003003030380c0b13041049070008001840030020701c800e01c00a40f4050320000da04641c8441120303045010700041e07a5826201302c1c045145000144065030080100120141c0d043c076007422019a1400c0400d44400da84d2019034190000540a00072040d040c080d407000f4000003c01000050303d00300d4506da445400d40406000c008001c540039514000ca5040407420003002441404043d40b0b82c10204855880f4178088005449a844042d01d142004400d58088907002405440c5c965419028000703800e601c1184000310484996a0307403941601c46d00320400c1d01c902c400c000c0070f1090804480e00122a0451210b000e0f910b024030411131420320420003201a01c01d030f46864400a02c0d41e114000141403284c046901c4041480c002144140d421006540300d11a071004030b840f095542c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 68731288 1250 68730038 68730043
    0x225050915010804060b13020f030708010503060702070311040f1b0813020f060f0f0a0f080f040b070c020a0b04030303050a050a0c0f03020c070e04050c01020d02011a0f0d0f080c0609 80
    0x1001c00c501103500f050018020540fa40d0010300310840150900e05819030340441a402c0343c0c000103440503402d1011090007142e660280f825400760034240c0083c0082d05010b44080d541c0c81c02c51100409158840e01200c40a4541d9000900040404103080c001154241289220350320302d00c8120f400500200e0021380c07850faa08202000c03107230f00500000014400801071183c55800f01d001061040000c0140c001c521400400500e00c10b1415991380241052a030001031042c48007501842d068044034052001080d11950f4494020304141416402d030603462000c2031951001e07910124103240085000028141c041d003210b80300d840110810003081d070f208032803401100d045050810020302c0c240421031009000703900400298004404071410503136a07602000781800c0803541202d19070000e00d00c0301a503580400c004222140d50340000d1101400302900c20181c004106c680503c00c441c1600d40000700d07150940f089032110341101030305210342d109041c00c2d441d0717a011054a1141348203031000207680b003e01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 68732538 1250 68731288 68731321
    0xf020c011202160f0b01030b0901090b1501020a060e10060909080a0f0c0b0106090303020105060a030b060d02011e0201020c12040503030405040504110409120f14071202250509 77
    0x50311421000400740c40340e00000e400042e1442906840701c84070341d020900840d01d080d0039138804d840100e1150f05510340740c0007104019200711890b03814824400e002a04841820764020700c0038600e2075882d15502c004078649050444007420302840c062007100800b002148010b490703003035401c05121041d0360320440e00480703000d090003900901044c4490307103605116586150140a8503d4148001581078803104500e90b02130380701d0000308980010810801d0340a00825911000840d4400c002919503200e600b09100003c0c407240c070925403166600300f160b0290000c8807043c0310450b803409500708a098060b00075840011901c070a440340828500420011400301c030f00b605d8014001d10305142c90481484040e04015100301c4a070440940d01c4041c5807507902c60740c0d8156024200b40c0c410843c212070003a105807041102e01c1d040000440008800c0407400080342c440750381c8001c08020614034040c040782455a0f0980780c10710350072a4405e01c915a01c4100d030100c00e4803006c42c0c02d2780d580d464a00340c2c103010300e00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 68733788 1250 68732538 68732563
    0x601031a092d120403050d111018020a0504090c1a07081b0c090118020304021309060902130c02030301050f280603050109062d0b1b010606020102090607080706060b0c0d0f02 76
    0x403400582220500c9445d4001110751000d04843c50007078625145020354070100c52b412001c00840842d241503103404c4d00044018503082d46c00700010b5040340c503a0040f50f4410701a2130030000141200c0c1030740c95848070803070300019000858542c4840d44081c1c4c075807641152807062401440780b20500c1800e480d007082914101c41c03030380c494a11022250701a500c0a504001c209aa01041d00800d21800c03c15a001f98120b49105800c00940c115491040001184801c1c00550419280c51000389407140c000003249e040d224211148500310411000062101c3c0440320b102d41c0b000c10403102e207a41c40c22520f0003c000c0da0039a0b00d060000e070b85c0390700c0882d04444c0c082c8206202035501ea000c43e07880403e10081541d105801240e1050f12540b101c00b003505580c00885034044a2424001400754000c080c41011b0103003403d440203515040852000500d1402071400103030200100081d00030403c045070b80171000902c140500076440d00006001c441d1101c01076814034012030030380e1b580c07550160301c041640c0c8041f14 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 68735038 1250 68733788 68733793
    0x40c030e0a060b03030702060c06060306010b391603121b29010b09031e060402121903080601120507120c140408030406110601031a092d12040305 64
    0x24254940a0152000040058040c0006c11104001d80c07900c2c0001c3ca6841a4a00140800d00744a0245850001d059106040c40c0c04184041e415807211507050385289400b03460940080e0b15928100380c0c424690400d500c0c024461025800a03500c8a01e1000007101d005280701907100c10f820000740c51001480300703201401120755022400040d00500c1901e2281e00525a0b004100201340c80da412403902070f0002c01003644081202e0400d4902042100102692400e0480c0c1a005081c129940da040207003000788241801100f0398501c030320420014100d0b40c01081c15540d449594200a8040c1d00705803040350000d41d07030401041c01d80d495401902d001c0c0320251b9460180396513800b9403000030030501c0303160810001011000c0b48401044809400036200080141d6500e07031403c0750240c1040c101414030f80342900b2440042002c108004840c00300d00400340d40c641c219582d80d0003080d08115000c50020a00ba210640140300400c240300484480c000c0030089680d803d0f004c400d121454015440024410b0b03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 68736288 1250 68735038 68735053
    0x10603140c0706020903010c030510050303070503040522020a08070305060418140a020a030c060f08150112240807060918150b0a0216060503010302060702010305060102120c030702040c030e 83
    0x1440020081a242e4001c41c0c00605001ca1100040d0940d0b45044240002985400a00c400c0304a500304500048c41c00314001c51400016039101c68a81c0154800c0c54803552010500300001540c41c0220109003440120440d030343c044020002c2c101c0c1c6030540708500040e14109c009420740c01d00e40f01d0003030441520828044050f00c0c07692414a8a42100820f40c180d0161048030742c010b850b000c3c4000003a510036000341c42102e04000004100400149960080080c4003081c0b21400f13808d0300c80201c51000030719041c01000d002303680300700103080c140f6505660b060a841001040d802a216890181c1d0340e40000e6a0246039609401c072034600d10303801501103011038801c01d86030b503d0b0164000c1d005000850310810380300da074818200040b60010701c062030260300141700b6295545082c07001207014141c5414507a0641d41103070042200e80c016044001c0c149a503546c0807985e40ea0081007904041501951010703a191800d010194594000a10803400343e8100311100f1300c00f0f4080c1c0280c8103032508020040410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 68737538 1250 68736288 68736301
    0x5011a0d09020109050301090b060907030203040b0f10180c02010f060f0e130c0b0a110718091106040801060302040510030b060607030302040b1908090d0206070e03011b03090b01060314 81
    0x41c48030400403414880e581c13000180e1a1428082c0c4400f040c001d112a42c1a45088018400c400600506400070544100100400911000f5034260060a000d400341980d03a103080328081c00742405c1d0040540d5404c441d000519003c960341017030003c466038bc0e0003840003070062420700d4159111405200c00e03000000c08180003035241c0380c5580d50300c0300040c0042140100a512140d4081c01e01c1c0d00041200700001608040081d0000c210a4940d59200c00800341c0f0781ca80501c90400c00851424054210b03290300a500c1031000b080302000c0c42c0e140080c11540d503123a0b0b98141d01c1c000c184920007207001d182000c00003102035000d520000b044903040700042105641d03183c20880c1507845488102d050650a020208000403203401506010f545040030030029062000c0252542500910b200080e1b03100c56a8070b074003540d000c00d00b150040c46505041d00005034520000b80944005a4101c60b1012900b05124115516070481c1200c1c03400703880406c800783d07224101142500c0e640c0c022004a0000d08011410f03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 68738788 1250 68737538 68737541
    0x30c0b0a020a0b0c0405120303071d0d020a0e070207092a02070e010905040209010801090515181002030403112e0b041a011101230408040f0b0d05011a0d 67
    0xc41910680340041c103581d03180c4980c6034042d28190300802012405220b5803c2001d50880040407100c01107040d441e154200a200e4034079045010b07500e41140d0002201900e40c1500308941982c001e00d151869a200c0c0c015565072901201c0300401803141b280000b5407560f9900c1080f1002c4400807240c00404001202a0350081500403501c00b18800c802e400102e01c185441c40c00d01030481d015000c2550f06060040080c00001a0031805a0707034985040c50f00010b4000809001041c2c00c800071000b1640c3c0e0005042e010740d2000c603001c02a0256803941031086800f54001d6114901c030fa00d07030000d01042c01c50043d1342e50320603114500350103501d0034031140803409541040c01c0c0301c041d00e43c0104807241d010001c2400c0c0d600380722400d20309071090384e418520340d0b070404440d8000c00107140007007114513505903001c1e8410744c0080c1811456640c6201240611404108a5002e84000c03811520200d50725410200e8580c4641e2000c0a064501800420480c03d286c142c0c1813802c04031002c55040c101704411280 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 68740038 1250 68738788 68738797
    0x20a021c150b0f010305010b09150f160507121e080d0c020c03100203060f1c02120d031404020d080a0c06060602030c0705060702091303050706140105100306030c0b 72
    0x221500381445144002030310010001026000d49101141c0709106a040c80f0352000c103d0f10103414035044c4001032166003c164140c2c1d0345c0e138008071100314007070a15002118003032040281d4583c00701000151102d44101850440ea1003e2050080711503140c0c0d181c1c404030100d420014000c04400c1d290040d0f60103088a043d2107181940243c1c04280350580104940003103900400b0b000015030081c80b1001103a15060007050740718045480d00350300d50700d04100003c82d00980031400c1ca204815618084241481c0d0308050244d1560180040d000b00800c119016601d0b00083d500308000390410750382064944129410a0243d98043c00c160040c0c000d598031644150810f02040080007036068412000c0744042c040c02c401401c503900519502c032920840380b42821440e0700514010f80303040048a005071100a401a48500d80c0e60001d06a0360081c54112503034422a040542500d06210181d208844075240f40c0c0c0c100c581c11501c1c0702500c4100ca00035415105103100103050340110756402c215450701c140042 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 68741288 1250 68740038 68740069
    0x10b091308090d030e03210a031a0d03050423060a0305090a0c0e0115030b1003021e04080105190b03060604050c0702040e010203090d090806010506070303090609062a020a02 76
    0xb400d1092200101d01a484004000d50001d6001000705540c0d0070180700801071440d596075580044a0501e440364203a202e600358503805c0564900c0903188444d14030408008000300241880006913140c02c1c010415003080c0541c50703c44a000d00c58034801c060008260142e00c201401c11400c200516405400a010041200000b03020f000402c900207603001e07a032840034000b5944840b4445d4181070408680b141c0300110002031502d042c140c550190f5841c0041000010350f8a00541d0720082000c00c4d075a03140490b140b4894490703010501051050b410340010b441228149550204980781c0c290004c10f40c2c5000c00780170382540000c800702d081c0e42041d42100d07502c403503400802407030710840e41d012808842c00c030512490941d42c084140005600140200361180240c0d1a0501c0170b0b0341080406c80d210001849180d202d03000005600c000c04d40640c020442e00c03500a2000c000540c04c03800d0620290503020040c82164207143d100a6621400640801100030940d00400400b074180c0d00303211698610000d070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 68742538 1250 68741288 68741303
    0x14090607180b16060501050f0a05060a110706111203072316030314011e0603020307030b06041205100e071403100e0d020609030403030f050a12020c1e010b0913 70
    0x442c5500d00c4400500841a034200600d40300c1c81c840c100302d030443c2e01c185c020307a120700b11807100c4201030380d60103030f240b001c0d258203c41542d5200c200c0071041d500601c0404174801140500140019516041803000320b083c9041d01c103641581000c001141d0361840100c8543d00401d61100440303074621245071f44a00c6440d0f0080c0e00e03c0c50003015207111b6441e0f03000808100e00107919014410104000d07440c01600610000c40c0361b804250240d459801754001d40d0042d1700802d540032000600c414800e0300304c24007071300020388066a69070720f0f43c64440b0f28408240d800d403030310b100b41420a4041c400c40d20510740e007850304001500340b050800b544603800e4001510042e030300d03100b009044607500145d48a0401100904401404120788001010b401c0031001440a411900240410404290008038542c0b5082d6a46020f03035452261200943d45950080a142c0c0031501c041140c0d100382c200082c1202200c120211144a01c40c0e441c5c1c2254241c0342401065a0801d81c1c00003c5041d51000803108250603200358034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 68743788 1250 68742538 68742587
    0x30e040f02042904150c050c06030403050a0e010206190207030329030d030b030303011a0705060c04060e0402071a060a081209040c030b0a03030e0d150f14090607 71
    0x450005a0300240c01802d0030b5808142d6840380d10f00940e49500d0041074522100c2d041510741070318441883e81d180c43c0c0c50709200b00800b0500c01c20030309103d90a801c100c000c1900e900d81c1002e060003842900a410342e0304c041841c00036981c8140d800004e2081c4211403016100c00c481c0c03052603485000e5000f5a0080701419100d001c0148000d102440c01d06101010486a41980c603440c4201450f002c80c41000c0d406043c0782083c4c050301518084212030545491043d500c0d0701410f60700e100d004a1140e40c5018045003d488180310305440c98000900031110581d840d4903501d10600100801c034422500002c1080052001120f181a01102c2c2c5560060000300304244a0b581d8404032414510a6610035095200014000c03006241c288a00c001011302440d003084a009100b001c10a40c81da1400007500388a1105001c0c0c010340c0c1ea040001c15203590014080c0520790810010501a1855020500c009414079004082030440500903034894070092000700400c0c4c44407841130350f40310407074020b20100c1c040148 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 68745038 1250 68743788 68743811
    0x50105120d21090818191505041805010303090f0f030605090309030f0616030504020612060303130f080f010212190204031a060a050a05030a020405060307080a051f02090904030e04 79
    0x2145401c400c1c0109003071342c0c1d00d02000b110344240d400c900c2c04080c4142c00c08030800910000441e941e0342551222030008440c0e031a901d005a80c01e001302e9101c094500c1d42e0565880c0324000c5600410b040b41c2c0b0035101e444a072a100c20300007a140300c4070f010b04420a6441da2003000030a0084e0403180d00940804160f0740784c8406680803900f010859105010250722400034003228450880341000f810405140c2000fa904080d030010380103200d4829500400c2010342c0104400b0740c0c0c24012140103055003460b0742403859880704464013102c0540b00c0d0001601524000c0b030343c540d1040c000c4425214150702100b5203aa00c2c5880f41ca102010350f0480356141e6800d210100c00550380407201c41c0d50000c0495a0791603440c103042002501801a00403600030000b0410400c49074500043c0d00130030590413079020450b0740c0d5010100749464516800f44100f44242503108040c80030100d08581445001c07902d820a0040d007095070b40980c4545000d05070006400000100428860b0761107802c0c07120028000b00c0c14a8042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 68746288 1250 68745038 68745041
    0x60503060906040b06030604030e010e130515040609050f010e0705040308041d061002030a0302090d0b04140d0302120103030c050f06070302030105030c0109080304030b0613050a090204050105120d21 87
    0x3190311000c542c0c00002444140065034400c10341c00b0100300c0003880c42d840c0c01e0b540100b15240e041c004c9414400d02c41e00c800070b981e0313030313844010448607180108201c1c0740fa200103040c5101c0703a16000b5902461030714001140700805402200d1054280201c20800340c3d281c4142c55070309080003850041080317800d02c804070010b06808001c000524501c55001d880100090383c003001400b0140500b80f003604220a28441903401105440c003040740c909006840704010b0011a61100c904c00c4010a40c14014041004010b20301d6003004c00d020320b00d01101c0105400000507000c03441402e00500408420100410000c0c0c898888814124810007e407070340c40d402d2908071351a20b61306542c4080440d0700400140030380e01301080360070032003582442d015007464901440325850344228000640303460800d0002645642b620080c004010045580410070b520304064a08002c04d01c07820200c0c4a07504280c0001007034505000030354840d0500b00d0141411411000041d184140d003060210f0110381903003c1548442403e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 68747538 1250 68746288 68746291
    0x1a0114041e080f030306040c05031b09040905030706050106200304180f0c0e01140703050f13031704051302071101080415150f081203070e010c082709060d030309020406050306 77
    0x3c40011902c034240501048107803154903001d0710804c01c0c1070080040010b200070440f8081094015181d40d82c0110201050140c010704001030258800040e0080030010130b540014102c1c0c040d9602d45508201070301c00120303081c0710b00188422580c01407100344103d0460045007000c000c02564000340510340030420209981448140002084080001030f40715600142d403035010303010311000145401c0046d0f4020b0700314050024150480c08002c03980483c1840001c2c0100043c5400211030f0f245e082241740c28800070f512034000e84d80194018510b21038044024001e0b907400a80c010002201405210300450b4001e400070010389842101d000701c42005100d038030a4404001d000d2000c0041c407800d210089001c3d480903440300d4101c1e800881c2190019000300190394001d0030794508110b8050070341004950810401c080501000d6000600c150780b40c9000b14000300c00a002e2224242000340c1d40e0402543c45000c4409540201105000b100040c0c8a88e0100c10729034030042001503020b45800100c0e02e046c10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 68748788 1250 68747538 68747563
    0x1020c03070b03150a12060b01110a061d010e03030a0e01110f0a0c14280519030203070c090509100603050d03110f1206031902300a03031a0114041e08 66
    0x30341b0104000b80141402081c50700002170a102c1c5100780c000c080d9070b540c0c0200c120040d25042d620f4907404031080050754032150006002e0001c3c44242404091f00c0e480345d0043d0740081225241c0700150883ca038060113903542c4561803000ca503042c07801c210032004065100003002820810074403880e0f00003400105400c4951041c400040c640c0848400d1044102c3c40c1d100c1003002d40c03c0b03055512000041001a9100e04040b04040c200130b16826864283c0c910302480400420039240c101e4040707080c031241d030701c203a02c0354141c1e40440d001c0414008401e41120407502018125400440009900c2402600300d245440d510140541c03600c410301c0318420369504030300900780d07441c00140d05119a515003000a040b00ca07a0160341c01c2d200028581c0000c0d0856040100c0262540a4100400c01100540301d2081c2d0081400b00703417064000c20389402401003040415480e8200d1404c010102194812001c1001103071b8804400c0f8a0035040220035211805c030142c2c10b032890301035054089103210041c441c0190008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 68750038 1250 68748788 68748809
    0x3070f0c02130b041a030604140a05010f091203020c0c0906010509130203060103111201030f03090915031401020f0d0b150d0605090601050304020f01030506120706170601020c03070b03150a 83
    0x2074100c01001300303407111a40160105050590000d0050781d003c10310a400a5011405d9000d087c0a089024140f00d1061405030481d460016101c4411805800c03200407184610301c0481490501c0d4800e4040740101c404404543d4000341491425080800c405500308905040c82c60814081400090200d480b24642040c0b6a40100610105503014040c0c1e8401601c0301455905041803092411950745051200be400707642940190400e050140d44044007030950b818041c4003460704d22018510300c501a2000b190031420401d042040701c5c80620a840034429102c3c3d00d00d2804e005d80f441540546200c02b1b480d61300c1482400446035410411001340b07001d0444031000b007659031420301044001035000f0151030611400f0020800180d42d41d245d5508070500900b40011b941d21204082004a55442c05000892150403408901e0641241c01d541c55180400740360085607586e00012038030f0f8000d2081d2281c040c0d014081c28491014180099540100715084581140525000107603078581180d12808507003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 68751288 1250 68750038 68750051
    0x601120c09080c0d0f0f02011202040b03090d180b09150a02070801060603020403030c0206030a06080105070e13151a120a0b010e0315010b13120b240603070f0c0213 72
    0x1d1000c2c04540c801c54000c6543c13020060321074440240f40849000000c008559a0340f8010841e03004406022240c400038404548490f1100c00814895000342c503540d0031807041e507141e80140b51050320300348000c020301700c60713400b0f030314070303100305242940c1281210030b600c098503d1050380d03000700c2203004d08000c030034982c000c001d41807070320104c1802c5801d91340001c02054010082800443d821450b04450304d80c0c1980c24594076a070385285040102000e4110205071f50800c0148068a41d0100b44102c13050701c200d880306848204181688116003408051080c1c601544804000c20301101f501d505400184103012460241d9465901920703200480d202c020b10380d0782d401d414505590000c050700090300d0a60050441094002c64a07a00d60300c14410700054440005002c042d14008000003070040c210100284902d146500c0d101c424100200d0391912040c0d400705106400043d811440594102e001c1c14980c0746850304002202d0003c0651507070030501814504032401600d90b041d003c0500f415074040007864 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 68752538 1250 68751288 68751299
    0x30b060d0c08070f030c021e100609050a0b1206180a17070c0801020a090312050c0304230d0308040206070f0b100e0c0f16020f09090703060c0f080406050601120c09 72
    0x840290b00201390030586001c40310f181d5285c000402e8409042c074801001d0100183e080d501c0d1030144041d820116840c20706000194240d5681c0000e4003686070300381d05000c48001e00051203540c0d0030041c01c3c030b641c40d8440070200311001c4d81c07001c003410044981b0080ea034450b0025164000c1480105032803410310100050f880050040206002000e40780c040020b501e44110144000c0607441113000180444901c111210005801001218400c03801c0d44140d94907140c0c1e840d8506040c2c9292100010308030115483e001082c0390841c071a04020340e02d52542500da440300c2d000e0052581000700102c42d00700c441c01d581c0c008140c5600c1140e10400030303541c071421154140200c00342040b1000e090036210481c14410480301084501c160782300441780c2140e403031040c2c010b4000a9a00070100e42201c0e001707000e903030910400c1d000115081050341d02421040c82840d100f01c034211140150818000e0003d0620000b00780010402e03000356420500501d8041c2c05044003080200850b030011301c400001c5a202c2404212 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 68753788 1250 68752538 68752547
    0x120c0d050c0405030606100201020c070803031005060a08070507050a021807021c050703080901060506070f0311160314010f020d020d05150a031401020c03130602060612030a030b060d0c0807 83
    0x1d0020280c00d02030b0a09103000f000c80c2d503441014008500c240d04a0440104d054803d6042d100704c104103004070380d0506e07078419419446c1c2e8800d58100c10090320402c40812a42040c40444001c103100f41c0e100d0301c9554884c4022143c40c0c00404040390507001d59941030001daa912102c5510340170b41c50a8202c210306042d00082e1804841c000f07410101c002101601c0c00190300705040d03a60550f050704188410790b03200d80c81c0a0040c24250072055000c14049601c0e020302c4070f40781e03841484070302c26101d070381100b103e00d40080e5070b80402c0d8030014411625440180001000c1c6a4503440d02d40421001240450b440484c92081c0e070010030401d82e43c0b03980440c501802031854059560013807850844001901d514601080c2005540d0002415101c0d150314040000c40e425030407070381010703410020707681c456000c1c074035007007402805200b01801131007044041813980c5055218002401c0c403a200a40c904101c01009401a107030600701154820b03c01d016548402c84c180c001c0092264443e50340722094070b401c11001c2c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 68755038 1250 68753788 68753791
    0x80f071a0103200d05031803010e1b0109080601180209030f0d080a0606030603080a030903020708060f0109290f01020c09150103060e0f01140607200109140102060a020a05120c0d05 79
    0x38411320100d4950000f00d040402211080344403000b20314032130b00b60840070074054558084140078611405001031600070340c40c1c1401c0741c101001d03615840e01598510503195581428041d50b60900c142000e42c00b80d030003450740100802d1402400380e0b02d00c11000640d441c1040518410701e000304100a04000303150070988100700281803a81020058103085441c3c0404030f001e080d0218050650703403c009000e15008102c440020100c0c4d00885545140809441d480c0180038071170141d201d41040c1c20015a081410b40c0c8001c52601034180e4040300c952442000b4854800704c4010307043d8080c5607000d50150702c5e400c2c2c0b102e102d140075a030000c6290441c203000400300d03402580070300e40d02024a414420811116400b190446018080d50443c1408920000e0594420070b00000c2c095070300b40c0c0c24003034450000f00111102010980310320303001554858000c00c20100082c445801a044140001e0b102c080523400381941c114545003c90420f4010481001480070a880d40b036403182e40418064002c0085001c2e19 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 68756288 1250 68755038 68755103
    0x1112010f080f0604020d080c0a1110030b1315090c1709160b031b0a0c060b030c061c020c0313031104060b030f070c02040c090501081003080f071a0103 66
    0x10204014003910141e142c42002c1d000034490942c0140c4081405412008e84000711222000c0d20a2281646414800040c1002c0107a01944c00c1c9004440e50318080c0c420361002c041c015205103000540c0780398120051000403c0444041c00c2c0505c08240c0c0290b501c9401520402612013040c8000c00000c00d01c0b480303c0c003c000303400300d030701003a0b031207240d10900515403046406902d80c1607100c0c3c45030340a235040d5400000d807148507220b01160706241c482e44203540f10f0507140920704c2084520002e000381a00c0b03070014184290454420000d1520f0021505401481411001030041c103080c000084d031400c590100001048006041c0c1c010b00a02c05100c0004909c001c00301c0e001c00c4614542070710031005000040a246240c0550781c00128440d02030172480c0e40301c0d54020010442007038901c00140102d00d090244d0350000f03010800280b070b400d4958840c0fa00f40d0760009049414440820001e00d843c0d8000c43d41210350000b8a08000740419081e8459030203588a805104035000300300d1100401e4a40400d2007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 68757538 1250 68756288 68756293
    0x6080a051b0a05060f0708131d06011409280e09010207020109050f0609090f01170f03030f07020f0a0c05010806061e0a0302040302060f0c0105180607121112010f08 72
    0x40c40099620348100c2002c8410070f40f0015240c0e643d1a170814032034000d110001e4a91000010b00b04c0300260340c20850419144403036888103070409c03081800c0080d40000c031513190214603404505d88200390b81c0310240403c0c3c80010603552000948030008485800b009150344000c0040420510503254032040b400c1e48410a90000c6003000b038960002015000d142c03050a00647c5841c007000c0c0030f0b4550108503040400e0141c800186403c1030740074000301d00000d21401c45240d80c0149499103503c1c0124968a074007000400441c110f40f100b51808040c3c02003d400402540700c0c0307845240c54000140100700e42d03039004030300c050034461404c4009041c0c1c8000030f02007881048204000d1a19040420966121006004138292103501402d005c1d0024883c0e500003961025010a06440c1c403414000201641300e190802440b041c3c0b99515071000341c205421002d10903820075000500150311802980310f07241d80100c0b0201c0c80c2403d444401d51203900c100d4420424044a5005002080b0000455001403140d21300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 68758788 1250 68757538 68757583
    0x1020a0206091606050d0216030c03092c10030b0f01030201080f010b0304030e0406080f01090203010617100207080d060e060306070822020f0603091b030a1a040f0606080a05 76
    0x4550012042400b134442072060101d480e20041c0840d5040d2140c10b45001041c42040705182405070000741400401c50010788075180c00301d2003050403070010000c10035201201843c00d50b58104240d2044000301441c018240c0148000040703400541c8281c0100c0b40d0721117070011541907000040c0654401008070390741e04900001003101c68294002c81c1d912603050310304680042800320001d0007034401a0302242580c032030008164070f481019030158041390b20840003000714aa9940801078803548e2203103182001e0300000c0850001c44605d400410041d48201c8c0c000b440d0130f01c8555140100ea440f5000140b01114003010060a0300f030801013180c00510500300110705241508180d100c003101064001482100001603104540328550202840d01005202c20345a252121185540f04090310b2081c1c18850310314440b10103800d001c0340d41040942c01003030222801d40d0340a0301c840403040c0584210b641845484985000c583c685c4235a1010307083c00b001030100454181851858140039051030490960f4208 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 68760038 1250 68758788 68758813
    0x6050109020f0f0306030715110c030105040302030f0307030609060e010806070804080910090509040308090706050a02070302010309110409030503070e060316080405030d061401090e130206090f0307030501020a020609 95
    0x202070f510704080c2c0083d099904d0740c801022a00708000355200c9003e8041c6400130702c2c00f580e0015600245c0050b40805c55209031649420035083c4d0340d041c1c80207805a0810020202108019070007150303c21502e0038082a229515a03950f4215001944500200510203006101041050241e990004041c2c60004d116040a480b00c05061081040fa54401c041340825148540d0046050400130000244900041d141c44e080182040c102211901c1d624012180c000c40e00764052815101401d0495000b0402241580d0040d0001c00c0003800580380d420709003000d650240d0740c03030041191007131082e59580c2c0c403821f00000c0076210030030b40c4142500c545818001c0104903030002e080c4a0b41d20405103000b000c1c0c1d80b03503030800b5400d500c1114040548036042034004903900032840c48140c8412002e907a42c2c981255186281c04514209584a240700c010209812001d0700c1d1120107030420400041041d41c42d000c2e0200000e1503c41c02d94400c80744d40c0d40200b1b03040340b01038040c000980d1210519000d01210407008 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 68761288 1250 68760038 68760067
    0xc08090d0905040506041e0207050f0607090e070309051605150708030a0513020d0b010510081603090201030e0f0a0618051f091713090204081207020f090709030605010902 75
    0x501500340240d0381c1d013001440640c0d0f541c02103211503c000100c41d907030004211952010b580400401e58003449850108407101e00000f82440c031540345c59070742041c040d00344074003690341c864054403013020182c450a003130002c224140030350340d03166508180640d10f16141000788901001c09281108034030505110f6a00864540011240e0101d070f040d900081c40e545112290840503980c2502a40203440001d00078200600b141e02e070307030503601c08544102c007481c1c5800c402c6402d07007000c80e042e410f55400308a840c51454069041440320b24030504010818100e4040c4a614080c0410000e0840b507200303034032000c00d0058603c00d51190201c0301c0742001d0905d02d103840d001d9945291b00090101400c000d0303094160011294072000810341c0c0300c010072000400396603406445070040341c18400013105000b4006080c140c40d10889003114085000741200d05e8020240c407a16800524050341c010f07010301d050140c207a9801203035500c141c81940b20b100700079043d82400d800700c0b101600321440003881000200090a183d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 68762538 1250 68761288 68761307
    0x10513080309160b030f0901020f040504150e0a0b0906030f1c05040305030a080412080105030705010c0311060a0516052a0102120106110114101205120309010c08090d 73
    0xc4100d05660740c03100c80d0414030f04101d07601114070b004064000401d0140d4084010750041c0c050030358401c4281c0340c5084407802c034800c52510102038a0204010440f40c24207800c540100c00341507500741c120995820100c2d8000d401110320054180da02d000d100c82c2c40c034004000c180c12417404e5009200795040f80c0b1030701e6950000c80500240e09010b858110364150f210f041118069a0b02c101078135151a0781080c0900944010b40e4100c482c15000746526248920400d5600c0c12a00010014041c2d545040015211341041d1181a01008552101c005e03042c0c0e0f0400070b441c007407a82034030009040d2070b00340d21700203150511382100410000c003041281c3c02041c5d080c5030080003850540b00c0402004044843c18028840d0001d0704800d06802000020384039013181c401d2012516210090040301d447c11103401c18003004842d181121148980280404000101012850352160381280c1c41c0e1102a442146642c100311081003060791502011040701764402e400c03d801c807500d480140000074116074054450300d003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 68763788 1250 68762538 68762543
    0x10f0e03151003060608010f050718090b06070506040c0518100605090f0d060507080c0a0c08030702030412050601091a010c020411090a0e0a0605060a0f05030a0915050906060102010513 81
    0x2144030110b107030464081800c900a6a1000701000344690740e0070001c1c00307000d001412020351032808000444860003104400c00781e41101c2401000720b030801040070700a0119004c5660480c405003c0c440002c0c00c204042805240981d4600c1c1030f03a481c0c101001114072020030100c103040042c03000d01c002c11000940308070a8402e00d0030041d0725014014041032040040b11815544035041d00c002d4402c3c040c8660209001d0041969441050f603100c031440582e42c0300f0805200006030756a80b13400007207440321025603001283c51064910746651080001c4151422500554154002c000100001c00143c810080704c01b40341d161043d007401008001130042e80300944040d0080d61907940c115040507190341112070250000780700103141178940302200b540c000c040320701209039841c2030408191450b009065421b00506959081e50034035041904880325000508400105a00c4650300c00029003900e06200824000100009181c900440e440e4a403000281c141e50541e450b00090040d50340d00305e07041120454 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 68765038 1250 68763788 68763823
    0x3020a12140406050a14040506040315090f0803150a051008130516050f030f03070f060204050402030a020909060406060519020f030c010212010801050601050712030207060f0605010f0e03 82
    0x141810030540d8800a150110428101c0010300881c3c1c480d044000f07031a00c03030210b5444100b00c4050030f6090201d44a82d01409900c04800c0c0801c00004204528241003d5003408010030000e4880e6540382d8a5052800700710dea401c030100810400703c078101890360b00e8010841e0341601091500c80402c00184103806064100180b58001498120040b008203900303aa004045400c90881c48a40704512046801080e00c100c04080465038185070024085a640807544040c510b80b9141303990f0042c41020985046400f10340a0100141e00e0ba100d02c09503100d400c40c00009680d40d4460420404145c6005101c14813640c9049001c0c03110700c0c0d10400740c40010640c4e05440c004040c0020342a86891145000c00a6a100c0000e86042c40d20040d00a803684500749510b003a032a98903107185500360760089824600091041c40000040b80804294030944c2c40241401480d0030581c2d15010161600240d00b2041c45031281000c00555a000316281c2c1e28910b03138909440f460740c0ca0320001e500c030b581d440020082c50 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 68766288 1250 68765038 68765063
    0x2010509060c041202010c1110090f1e050105071511030a110705060f09100e0703020301060b1c02090a0e0406240308030f0603010605060a0c05060f0103030c02190f1805090a03020a 79
    0xc40700d500100e81c110002400003006127115040144041d446005680340a000710000050a000c3c000e030400c50860451564411541041c0044409401c03035201915084000c154189034403105100d08110a02c619004984e40e251910421090328581411902440c40401880010607004148503401881c103e07508813076915207080903860012448582c00c003151a08010810201c40050f40302d08803442076009100b010340c0c0d240d850150740114261700d00440445e1008806808240c1c0c0106494000200035548541e15404206160f481c103c40403a51140c1e41c241000031801c148175440300056201080c03440a0381995517864040c0805098a02c1070007207540400c0b2195030a401ca60080c02c0301400d220303101c00c00420014584554003c0541d0b46010701408500c00c00c0381d12a4590580c1e8054842d024415800c0d403d00044041c80040d001c6058200000420706900317810070200246000d004480c070041d04521040d003183d4002e072018060340d008030700c000700081e0040b40803469517404c40400d0618 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 68767538 1250 68766288 68766293
    0x5040308030a020a081b03150a0503030a02070302031002130b130918020f12070b030408040b161401090314030907081606021b0109150302040503010203070305040302150609010b181002010509060c041202010c 91
    0x100e00154003c0b2f54980008200e0043e215400981c10088a008500719102803c03407420200c1284101d000c0080d101c090f001082c0102210300008042d5072103418000c004071580c98000302d00311408034900e140000c406100210035071901410a9010440898407404032402050140345c0d40c41c400d20400f402190080300240038020b10b54113540040a425841c2a5070b10480e140c4004038842c12071044800300e500d06845646201c05201d1224580da054884014112031106180d4454000401c2a842032082410101c0d011809000c41e50b20240000c6404010500b044070190918208501100d0018040da06141d0640e0344041d640d0110b43c250a40b020b2144880710048010717202d10341104c0c0d0198000014841c00c2945a03000030322443c003980c2901e4080c2c0c005440e000c0030646c169403456200f20400c0040c40383c5002d090050000e0000d030049184241c0c100400714ad1044e420f100e0500150755503c0170000401014001c2d80c0d40000e421009515150402000304403c080c85d1501a0411402c20703114002c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 68768788 1250 68767538 68767549
    0x9010c051608160b070803010b03130c170106061d0609010504030804030f1e0b160309020306010b030a060b04060f0e0604050405160e0d020109050d0305040308030a020a081b0315 78
    0x250200c0c1c4414052480e101c040c216034840c000c12800c140000342c40ca002a0700303181c003070564503d10340c8030078114070b1070340390520801d280d40010f460200b6040704010000006540d40507814010600391802e0700d20421a1009035085501d6680704100b40040f040f0350750207500c110842a04403c108550349138880001000403034150180d03410040035008005000b101b4030040026840d650f038400c1030910807004421100404c014901c960040041040c2808685405440d4080d00c48a000d50301e80001c0c1000ca50b00082d26203c03081e84007003121280001480703104038550188501400440701d020f441c1614000f0700800640c490210a020071502c1c01545e010b40d681c15044034001c01004009208c80e00341414143c1c800101c2c40315900108506020480203402c00c6034080078429016110b148074185008144005559460421020480100004000180074001440c00b5191203031005840d2984018054010346000d00000040a280d45008200401c50001c490f40480121242d00709070032804080388 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 68770038 1250 68768788 68768803
    0x150302070c06020106090f09030806090c090d080306030c040606080c180d050d0806030607050f071a040506090f0312070509030a050f030a090e010e010303082d041b0b09010c05 77
    0x20031071402074000244069054024100355aa600d00800c0310303502211100048601d60000100410150000601d02e03103402540c0d0741e0701400509a651605544c1e02c00111081c0d40c0d80012160300d00c01005000c40c60078104a507040ba030034142e404000c25810210040c003541e20040260501d400300048402e05035400007400c4c6010b000180800034030018519240d80c4648001c07902d8400180d2000c002800c9140000d155801174001c0c2d00d400f464141585010740701603020440645203246036841500e28407901c6101c040c8901d0080d07000d00345908003110b000303040c035020f0100102c0c90303401800082d03103880d54800b9064110141e418456514045c0ca00401c2c1491550003015110707020b07100300014a0103004c00103000c101040d0b500d650b145912800007440240c420b014200310842c4c560300500c0001d00500c2101d4200031016000340344003901c0501e40b030300c0100856004643d001954244130802c56848050740d1200c1a00665401740c0c0d003000c280c88028051003590504200202045001b409014440e00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 68771288 1250 68770038 68770043
    0x4020d0f0b0f0a0507080f06240307080103050f0705061603020c0a0f141f0806010215130c080606030a0303050c0706060b03010f120503160602191d01050702010915030207 75
    0x141140c50039840c500031038041120f500000c24241000518140c0c4a2212148100144004860180c55280502000c4040d0303802001c06001d85d54441031301c242e140409903110700a59501c20340700e0740c154078015060085021210307942d40d0040e002445240d8a0300700703458000585081d0004101e0a60400703d1800c004000482c1c0c000c40391200208a440e5050040c40c2500c01190001d461482403005105441e020242804145004040002e103600d00c240c0541da0040c205104442070441a07500d81c15042400380c0e005481c2ca501c1884800800501003522801081c204016118624211020a031920316281c0c1c01020169641d0005488040c00d406503191550803039000c00c6440d49845106100743e00a000d03005020350b0841000915600741c0a4000c441030740b060286040903d07440c1c40b020002c00110080b54803a80034070a2100301401b54048207044c0e4101d030f0300c814098121a00c0303031102100b0880d200d410400104405409070341c104114000300c514614003450b8050601000710000e005201c0700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 68772538 1250 68771288 68771303
    0x27020f0706020a0e04060501110a080304050102040f060906020d030203010617091f1a0603010305151506070f03030f0e030a0c050307050105091b220504030309020307090606090b1204020d0f 83
    0x800642c1e548140404c4403114181c500304030954603a001550180c1c510495481c00d82d01011802c1e00041b9128050f41d0441e02c12800075007029115501481c41e11103903000031000581c1c2d078504000060b810071002070700030702a060451465060000082c8640702c0c00384050a011600400b040702c45a0801620a84510151070310080c15541042a4090141d00da010040e0281c00d42c007000d1940b41c01c0d8100c9041300d0b0301c50000c2003000c41d642c0144d00154001407001c5440f00904120080c0354640c000242252031084125240444561401600b1146a036000c504510300d040d00c0780600e40700c00001c40300c11030401c0c1400c00e43c14000d403400920758881d128008002d54205012320205c0040069140b8a540c01090548500d140340414040b81c8103c143c0900180c04040315081045502a40401d4100f4040d10f0007190105c140d4004c00c1c50218103600c09100ca5640d00c41c1000f1480d888090140684450010549000082c0d24540100e01c4007078000783c82241008018410442010341c40440c0e1944502c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 68773788 1250 68772538 68772547
    0x60d020c160b0c010605030c01170702010b100309030315140409020f0411040626010918050a08040611010e03180d1b030b06060a080106080907080708010204030c27020f070602 77
    0x9585400d40202c000f4900940c00e0107404520351070042104000c8207010303507030842103c02211706040500fa0141c00d51007995a00c0e010303610252903c00e00070103500c100e51804a141e482c5850006c04503a00c0750301c0207103000e180c1c0340e00703110011064452015084044401041042003800090f013805c0481d80c0180d80301d8a4410908001108640500f04039100c90301e039558580b030001c5200380320030031610080482d458002c0c01880314110b194005441e00044845800d403010641d52040c2ca04010040241c40320303440031408029066114400201410780140248035002509107555a00d024540c241080d481c0401b40302c0b5440d84642c50400c69094100c00051101007407403402c2401100240000d58130100c100c800103229003000000c94225100994031100c0c0d41e807814804444c00200500790301b42d0b60049910011300e51508221400c0504018000180c4c0d881c55860495101c031106d5201c4a10700071209806640e600325001c02d8140344040100c00f5990b10401d44684041c0e1080c2c85004110a20106 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 68775038 1250 68773788 68773799
    0x109060c023f070e0603030f0304021c1a01090507050c0601091a0310020403030305010b0c06040b06061b0f06010f0803030703090813080d17100902090604050907052106060d020c16 79
    0x3c81404503138100b0066015600c940007403540303d100e04c1405a5180c034040001c9001800d2a00e40380034904411580c81d0350781d03946961040c00720100018061b180c908500014000d10401d84034054122940382041c0c0d00e811454031040e619100305116115500303a5503a51b050b01404070352040004044014181d07903c0d030b002072107144000d410034002035000a28140000c101200e11074211680c505910004043c070356030380c3c1d45166031000020710103904150280501120800d1900c5c1da0014401000d001d014001540504640380030300591045651110041c0204400e07600442202c0c0c12551a160100d5440c0660904030581c1c454288182012524407400140c0850040389940c47d90301c0b16500c110395007032a10b030b0307a116032401030f10f0818a03060180420003280e801c580c01011214006071a00d82884da40e00000707441a0011603404010841c001084401c800120760200701d028000d40322141207041440c0840c0c1c95000d07080300e80903420750009402c01c045008008040218a0021440c004d240d2a02c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 68776288 1250 68775038 68775043
    0x1060f0e0f070804030e06030403020109080408010608010b090402060405100203160b01090507090b0a1b080307110f032107110601080c01030c0e0f060714030c03090109060c023f 78
    0x100e4070194011550404100c48512030540c05010b150156a03c40c48210644108940740d4009081101599600c09078807001607040e2015200800d03c627070001412915010405082d070f0074aa040622403802d600c2000010382d5400c003a1402c0e00c0d010303642460440c00c2070340706a285100e403081402d0012a10390310f440822050841c0d0a060341c070004002d005c00e407202201610480c005000c0c0b403405800922118150911038400f241944585400d80f242c208500d032559082075100703031105000180d41e800d40a0312520100455640c20201c40003d41c41c0026410540c0c940c0e1b0004101c2d0464080c640001c900341354400c03610000c1c00340c8030300c080d91306959480400e03607514400d002459000c2400e21642802c4107010307a0450210581c0545207420b900c2c145000c022031980440800c0b14030107080001c0b008801e070304001500c0e0340041c4000440d0b40d0945140007501d4840c05510910800c554003c9030720050b25060545404101c500080c290b288604049422400c058880c00700e2112850307194018140400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 68777538 1250 68776288 68776291
    0x1a07230703090e040f0b060a05130504030f0c0c05010815120a0b0c070804090c020a050307030c0b012709031e1e02070b07080702040204050a0603050603010e1b01050c01060f0e 77
    0x19407680031607690380c0e940755074412404490181c17094000d8015030b00418280f24080350f0040d03004000c481501d440381c0001d008000d82c040d2010880342ea50040004160b0022101d008260540c1042c0c640c0d1b2100d940c440e5200b0f110b41c058141002054000309044403c410f60311341c105000100b822401c070501c4620b150740c5902d881019100701544070085881d103403003641102d44454000031124905810080382d08040c00024a04108521500d405007010a01c00e0004c0c1169911070343d2809407511403410190801340381a0407443c0309505a00b1140c001600b04400b013a5011010500412917240500f4144c82030744000d255940d40d040c1f090b4202e662281e00c0140e44880303d806010500c00c1641508040382e40312a5401403c01c00081004404013007a4444090905a0b00c020000b62620351a00080390003400aa4019000700e030b00c550902095140a004182c007620014005081444460904403290842c01c000981402000140601804007e401c041e010308003089460003059520400e0070b015200 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 68778788 1250 68777538 68777543
    0x21e0a020106090c0c110d0615060f031512111005070317060a0611070b1b0f060603030307050f07080309030a0909060e1603141008010b010c1a072307 66
    0x39007030b008070b800c0003e40705a8102101659031400091051b6980301305e090a15160b80e0380c00032420342e20384d001401138010000e4040004084514a030701c0d12101401c49a0044440014181440901c5c071010121701d100a04481112405070603210107401d280d502c44441c0c841d900e03045492945900201a00b1100030000140720366911511450a080c0c04004020150b50665014503555803c11456110b0003100e1001c101c0c24064486595032501204003030751010b039030a03a0104086018040d4003e0521080c0403c030020030240646117003502c00039413030f0703c0f00800703040601c480407e81680020460041c2e03450154880482582d0f81445582c8903940d8104400340c20025402e51400300d03c044890080c2c00413600613100313070361340c1d915165644408000841e12000405503200c44007807d0a204030f126038041c52140350492422401c1c40034150039112281001030500040d5200400020392425281040503404c402560503902c4001c42190000070440302d1104046c6030b10f44801c0c201a080303004000f590b1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 68780038 1250 68778788 68778791
    0x112240911031608030d021e12180105071e0207030c0b12060d0302030702060d020d1406030706020705010207050d05010e030304030302091009030201020a0219080307080315090108030418021e0a0201 87
    0xc3d030000d1100c5074040130300030042ca5400600c00300980c141541c01601c2c0301d9603002c030121000c0c0c0d1003248020803508004220b01c08c0ca01c8000c1440f503081607048580b00800c0921009200320715045801400e4003540c00b0036005d04500100c1524503a0703100781b18100240d54030205441010365074141c0d1080ca500015000015529048003140203850154590304400350b064010b0750030700410750200721041c1c03c190b0315050201e400b0071180303140000394818036a200d45110040c10032424031070305041c500485078110009552081c0310a0043c0e03038000580e501121402c480d800ca25041d24503101340035210881044c48a0b20010050004054042d009000d00c50400d40d06200744504c0031004503148550fa100c043d0150700600c00f4200541049d94580200c0d2512a0841c8106c5030754498dc20320791340c00000103a904000100c10300c225aa40c2d003100d8012440c04568846155061502240d107038820351140d0044020300c0390b00c200c050300d0150181c4601c0d080703e02c2c42c080c0c00c0c9502e080d80040d42e03200c1c040080065 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 68781288 1250 68780038 68780053
    0x305180a0507030803060d0b0a14070207080703020904061401150f0207050d02040f0b060301090c02061f060804030e0a1502061e0606160605151206011224091103 71
    0x811001031140011034016009001d01451038a030034503a030b0304c083d02c0c180d041003070a0071145c08100a1300c5828050700805000203121200300d42c01100300f03880a005041107403c150f5040081d02c2001600100fa25011900d600c103507110361404000900b0541e00440c6581fa110700006581821609a081e0003402900d80110261101500700d85540c1180545a400031101c0c101e4005405c107680100480c904044000940c0d00a020024940b504241d00880380f554488a1568071141e0601085801103401c4140c64544140f036800d200148011b4068201000701d42d030002400d1520558090000d1800a05403101494443c40d02c2606149114000000740c800c200100311300040606a101c0c040480340d00c0f8032400d8803170b501089507540c003001021080840981070b18010515500c6405d000302001400200c1c9118900300744011040300100210349074115000420002c41204842c10500d5071148400320441100340172405404401d00c044540d20b881e002280c01045248010720010290840c02ca0300740 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 68782538 1250 68781288 68781331
    0x15070210031b030203010602030307051606050c0307110105090d0e0612040c0603060b0a23040315050a0c0512270a0605070207080708190203010209150a0e06250c05100305 75
    0x145c0c8028031410780180d20820000791441d02c00c40c09020180406080030728220380c2c4d61501d0060f55025518200f45440c00018055001d401400c0039441e148160028011440d04540484c0c480209041714001c0c0010824241c07034658036841201c1c1c80000340485030203030b4113107405c10002400c854003551000c40d03d0094040f54154816042d02c01601d8140d840072600b0003500290070404a442c461120038910902011001412121508401503481c030fa00040c1813820400c1c3c001990100d070949010704c401040060000b0404501540c0d0262600800c44402c000d40c6c08034044844501c0e84030754050084c1ca1038038003044210b411540c0208055822106040d4650103c2074646400b032040758010741c440e0368113801068449000d807459500090005041000c039101082c220f00707000d071b11050080c0000907680d40c5603400c90385c440442c040907203e040c10005a190815000c00d921400d000294060140d40ad08000c2115181c4026000141a055025500e40c2c40034010740701c1580c6042e40e00c81610507a105 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 68783788 1250 68782538 68782541
    0x602010e01050c0306100c06021308030711011b03080622020304050d08070e09040c050312041d070c02060c01090524010e040206190210020415020610031115070210031b03 75
    0x1c5c0d40014a500c07115044000152130b04200100d0843d0115003d02008480d0209845004020405000a1669802c9070300c1c002000170340850540741480318440c424030a9002400c0031901050b41400d1012a0b900c6030360010780310700c10651110b45e11a504d01c40d0408c1041840d0007071401541f1503030480e42c013581c0d21001540d541e9400c448140004070482aa011245014580c4d290414090348548031840e0703c51001c00c0c1820700b08003080e6050600001c00300142040d0f030340640042c038840d58002d0154240440028003200c1e080c1d4010748075150204031641151000c0d400b424540b80e00400b11501c01000c1c00c0c820644200c03010b00d8600000420000180f400780800d102481075500900381440c000d0801200310b146000043c03da0300b14821303103c00d122501001d20062015000181000741581d040d00c8000344ad00e5001411102d180340c94940400005060304424101900e00301c460b0020300b00c50b41c03100c1d1010300803280040e520540781c2c0c6001c6400c641685c440da55065a00d5041c26801002800c10380 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 68785038 1250 68783788 68783791
    0x919050102031801030914060103020a06050a0e040207030215010303030f0c0c15052d01031e12080c0d0204030f05070b070c03020f010c02060721020a2a0f0602010e01050c03 76
    0x40c00350b08104910400700c2d444100100c0c0b0810305041c00600d00780142c55011070b0700d04402e03079003816a00c5071005000f941303000ac10100080c001c2d032610798644544000010242c00854110300c1c01580c0110300c1d003003014005d0151508c940703c5150017504a683d64200100130307100c56000c016a251030008520f113820311070000c03101a1604152000d00501ca12090500189801441c20302a40e880702c3c4402029401c1d00c9034660b02c000300010000680d411401d0201c00d8402d0f0200f03001400902404960020717503000c4403254010490300313205d80e6030350381d40d51a10310714850380860b5800c1520000c2c0110402c400071012146140c01102103034005c0b03071078080007c042d205009018001011802d010001880e140c0c0c4041204101890000d802055a0780400d81c0c940080d441101c1c040003141601000414094100f2020183c520003400c800138251500d1141465101e0850a1341005130407400e5803c0613601440010512040d00d191503558503d8004e0092000c0c410061685d400c000124014103401c90a49 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 68786288 1250 68785038 68785049
    0x4140102040f03080f12010915050d02030c1504091812020304061e030f090f0311030f0d0b0f100206040b06040b060a0e1206090c0108010803040b090105031503070b0919 74
    0x100b151415602d9a103003581040d0305c0030401a5082002c0410344d17403003801c028000c07c000700b40801d8205041103140e0025605410250055034184ca1000140c5c0c0c0c0042c0d61b030005401601d005c0c51000701380ca4003203110b201f40d8024880540c24918201c010800c0402c1700c0640d103010701c030b005c2e40301d12421008903128401c0e4030948000860a0010400041c480785001c1c00e0580d060800262071548840c982003560780b4110700303860b03007040c2c001028181608110300d10307400d0381c024000d14505400408031001c039010305050a407a0b01d0391008400b1803600e880410200e400d2005141c0070b922280307400c009603104030440e81100d0383d1025102240060415029510040700010421070500f5502402107901003003681d141c560100b001245c032440010140003581c01105000c016003c465000c10016101c3c0006038004034042c1d0080100700010450102610108002441c0c11a60781d11407840c41e1440c040c00c421a1135060090410005846000400620034090152080440855612413800710800703188101c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 68787538 1250 68786288 68786309
    0x6090e03040e0f09030702010536130e03030a09050a0b101505041217120c0a0912020603040f030203040f0f050906010c0209010306050c0c031b16081b0a0305010f050414010204 77
    0x1041b00540c0524090f201d5500b2035030708580309000d000d03d0794251041400c09986552181d0808058504003210b001c480c0c90342050003844040b648101603650382c0b1009101c0c4400e40d83d119079103020480b0500003040c070190060752198007401c002070403000703541d490320076050303c820010b010103002c2d400341041d2422100c0c0041a1307410048c0e01e403075014190740009051081000200191200c040f400000103000d00084000d8580382d03801290054820b90841d004005400c1d000c1500c031005070345050031254025070100304803042d2481454241e217140501c1d0001c846441c1100b0b03001c03078601f030300402c64000c640c1c04480300c0f11242c0741c2c00300545041c540040e020350020400c000502c0850290303006140c109000e6140649004485071a881c1141c1043c1c00c803540f03030f4045591200d01c4060400152900501000c41c80480602d850309043d524016901e415401d040f40000c2c082465480450980c0190f401c5802800320702500d03c1c02000a11003102d00301c841c1e4922101240200c0014802c1d50142c0d1100f159 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 68788788 1250 68787538 68787547
    0x601030303091119050a0506040e04080c03070b0f04120c021305061318051608031801020c04050117060c2712010207032606090c0c0106090e03040e0f0903 68
    0x404070040c0c074150009840b07006042000640d00d440c0d00d03942083c11602e83c820003803100e00742000c100844031143d200c0c42c0702c0d1409000c103001d040d8103030791b007250030542c4109019074901018019070b0550180d8003008d0180c945190401c0745009590840d50f00c40c0d4891288121041c92011080e03454030040c06000c2d41003008280126940c002c10b40c0081e4000030014030090500050407154400e4a1858003640d20420220352040d00304407003046440800e03249081300e500a503080186003541d900801300b1851071380d0100394448015900a018070300c0d50810103001805190b071120921351303010b4050007842106224903c0010100304210083d00d4403100e0903045082c60703200795000050795100d0001c289521540c99000307896800400d00c010160b02e8400d4070745c524100300c2c0840311006441e400c1c4203105402c6d40f5000b00b15503503581c01b80a55002101c0c03100f4035100c8220045c0c80e8018010f903040b240f00d26180003180d0891207000005801243d60703020381844a952041d01c504250f8005407210300550b8018403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 68790038 1250 68788788 68788793
    0x8120a0c080904110307020a030305010801050606071506030f0b060f040c05030604090311010911011803020f01050a0e0d051b040e0c060c0f0d09060f0206070905011110050405060f0f0108060103 85
    0xc00901c0350400c002c0000c04c800f55040144034040c0d20907500800941d220180030000c02d41c15000c2c55004021f658003c122130b14000000c030f601440b69880007096120150341c654030f80403242e4440c10242d504449851003c0200d0702d05000c10b048103441d8180f0400001910011502c0e05024000315402140d50765811526035105001c0940084001102441290030321144092030920400107041c0c0103c0d0a04203040c0d1b8000094080966070140b0800c142001c40c080c80940ca0701a450407000d2802e29042d5030b902c20a40003258a840b9104041d076001e81d0600e4441c00307101c1c00040c0c0102c85420020361418810711601084101e03030000c2403c558a420403020000341780b4009001d04000711001080d13908200c0011200303030901e5800711f03019021507160101403010642c4001032080700d030300c0380c0000c20090414110251061065214481c10881e0080920081c40001d0001c3c9208014142d03043c4554101803420503203481c002c4410201b82d90403d00000c041114800045048a182c00040c0c5220f07401c54 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 68791288 1250 68790038 68790053
    0x40506010e0405060a08010207050304050a2c1918050c04090b01050d1b030507080705040606081f08030406080609060f0901060809160305060f011e050111150c0408120a0c 75
    0x18242a40705c4100030f8009040f080a000516002d4404c3c0003841d03a0328204020428000f201e80c209402184100b40d006148886901c01001400c1c4483c0580040c0d66420f90070f05202821100d110110f641440070f24003004900a501c3c01c0e00510540c20307110444104420b1000700c4144900107001c0e071110100411090408803030266802d401010b40118004091440d901c40c1c000540c4121090350140d0010060414240948005080f00315802c7c0030301031501708000c0c646107024004400c50410482da1211154091042ca4010200e1105894845607284d001400380e550031983c2c3c070300400058001641c11b107001e170440c12000300b00070214071459003842011181a90000c00da98890700c11604070f125030207081a4038900540c45203008150500e843d6402400c02c40060b44502108100a885080192580d400344002d8410030318140b454181c400d4082d51506803c403048904c0c4542c01c805001e40b0342c803918024410fa4000d02e013250350140401c9130268040c0302314800c0000240321452010002103e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 68792538 1250 68791288 68791291
    0x10b03030418090b10060e0d0f021e090a060602011116170403050a0f0203010b030606011d010201060902030703050402030f0303070c080304051e01020c010b090103050c0d1e0302030a030b040506010e0405 89
    0x880b9000150311001d0742e03d82c40010000d031006500e03c0540030040242560140c40100070700000e9840f40d5240003155249240d000c1d04400003842000c501c04408680e103144034800c1e0070414014600641801e0210710800182080c2c05054010350070803d110b900018140300721844a02c0e08551030160100d56210b1880000c075940841e02400300400000000c42c40403c81840e4450280d58501c20ba100644101070031101600c07541030094111a0030007405a030005150407403e81100c0c4501c46950b0a000102c1c01008141c110452151011040c0704003152f04d0303031000c0c0c4079a1082e005c440754560480280e583c1d9000031200c08002412024031600083d5419001e1504244207000300d89090940803002150501105401d010580d030114550032190801d00400e410310700152130b0344d034103941161076242d281d4440410307041c06190300300108020440381c6d00d6913000e840d84041d408100141c81e0300c5c009442e64000c0000100181c1030000300f4025103407521600c1c0c00744105031100c0c1c9401558500b4000039140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 68793788 1250 68792538 68792579
    0x10308180d0602040902040906060c05060f060f042f030411040c11010e0604030e041406060310170708010f020408100f0e070306090c08010b030d050d060b1209010e010b030304 77
    0x40a1007080c001450500180c409441c1c041d90261b00c0d90f0030400004115501981701500304804c0b40301c0c082c0400d0010031003a412142c42446142541c2d5000e020840c014494920300e42c102d0b05d082d54440c10120041c0c01041c44800d02d403488207026425501c841182d000603180541070101c90444603078070345410303031100c022480a414140c3d040281d840d40c440c21500c41e1405509a500001c04100c2059801305000c1c1502100300c03420080d162181c000010003400080409020b00c8000010910000d8011841d02c000c141b058446003000c85900e40c2e4a440720103510a000c03080d07081c001c0112006409000361400d03a00c40000400c0480000c0b4891000381c4050900080c2440c0c0e502d00d400400b590504c0400003560040030040341e07110040c500309021000c01d521007255645882c03400c1070145d0b00450000c504135102e14106440b8441205400000e100c8e40d40160300e8644005505000104400f480d0b80c420b21004008002c1900b144020700e00761006141030560540041000344180f00034440602388494 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 68795038 1250 68793788 68793799
    0x70c030c0606080f070f060e040b04060302030d021507022b09030501060f03031b02030604080c0c040203150102060603070302010f0f02030408010c11060a0c050306060304060905250e01030818 84
    0xa0300c0d1079500031540c15030405802c0c0e801440c03441900700000c12000d80140002c0d4400c0f140203103000030080281c801610942e1086071240b480d00c1c01c2e982d032600000051600202516240314582001030340d80c4400c0800101e4250290b80001c241c4c50000c41c200c10304034400000c0030b681c454080d0360b08440301c46030094841841000c460210216109101e4400600011a1452036550540c1000340c04501c0c6000c803813903600c0d241f941c007800580700820590b03003095220082c0c0da2104100e411aa00300030300c0d1941a604a440801080804241c144045e81c2c9001d082e020b031007090302e0301420f15031101c0440c00041e000c94207901071448024400e0500a5800e201481620f0419403140710450039502030710701103000a003110088040810051040b25005550340d01c04100a040f5600050b006000082c03613588640c90103c00203040c003003241c220882e40742c2d100c0103541484131100c07600840321113100c03588112a400d810000c85d928528000e0703681070741d400c108850b041c2101340381c4160500780c6061030941c111 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 68796288 1250 68795038 68795057
    0x403030f0c02090a0c170708180303011401080c0d0c0c061802030703020f01020102040f1409070503010e010b090a050303030a050a1a060706020d1e050702010f0501060509102003250308070c03 84
    0x2280c41b0402501038030781d550b11451710b41003105a4540310100c3c58104d46094004000411031512034011000d411a403e00701603c80355244088a95580103414500c440c803814003a000000c10781c003d40319201244111001c004280109802c6a0398203030358a030080d0581d112000074005883c01d05d8513440c50001c1440050303d13264441804400482d541d43c0b19a1414071402c8810205160480240c7d5000b60b0390320340030781150700d0002110b01031601842401c0000000084040803915088064800b912025044aa5a0900d051100b0003800100c030001c1030303035190026030740b040340301c0f2844442e20020041009041c0362007a110340f4000d5101c1007100180582d148440403d21058600880003200780d10000034440c43c01d02d030040e0a4640e5802071002c020315190060003d917402401744c9100701400d95150701406c000481c2030700c40c1d0481c4c0d603403400500c02941c0800035030314000008114000c0d92286513000d0800c0550700b5030880341e600e80020b0100d1128000101528480c003100612a40203240a901e10f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 68797538 1250 68796288 68796317
    0x31205061c0b040209060d0b19060b0a111509030f090d02040603050a0302060a0908030a0917030109060504060503010207030e0603040f08030705030108010b090606180a030c0b0403030f0c02090a0c 86
    0x10303200701030200e032002001e808000030351801c6200b855001d0000e94042050548554510a0303000000f811681e18800c9501c0380c03c030f02015070780306c1405052403040856562030300e40000303000c260307590402d02440d01c82c843c00c803080586940c40706801510354600640c04e005d10412240040c0c0c120110294021104c80d0303c480240e5558080e4400441c003c0000d1b007029100390400900301980244114502c1c6d0914030034000041c1d2001c1282d50082856200044140080c64009070310100003c03072090382c02001c07002080340303a40c5602400445800321410403804d0b80e9201818281c2c010500083d010540d4981c3d210418104080151380c814071130840d500e5111542d41d41c070f4490341c009581001c0020b601100503c03c90100b48240c120092003241c01901520b0100c0004c0d10a20800402c45c4903000c2c030036881503480e190031401001540c1d00041655015464550600f0590410700c42640000d500c1500c0304403850007031607240c604035000781101c80159200c0c1504005080c500d82c1000070044510301449a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 68798788 1250 68797538 68797579
    0x11071203121418030a09030201120f090c0603060e0f0408090111030d0504020924040b12070306020a0807111203060f040504050105040209160e0f060f040807050307090903120506 78
    0x40b9192804948502410001421022403414070702c040b205502c2041201200381c0c10050601c1181c0d030900e4110715900325802907201400300340b20b0000089084c061200c0400001b00c0b55002030360307400c1d9403c00c2802d96490304a001d03c001a1a6002d0401140c404a000303d2483c4008144180701030400360804007031400058903591201c003036105929510001d10003180340440e82ca6420140c0710141c81181c0c6004ca242e0089181da940b9254421039940100c500e940c7c80b02d440b00347e090b41500d4259800b8980d80d0610301d020354020444c080002d45403100188100d401600c06117a111002c00c0140702c50400384034400350030303031024000075404100e146042245a603240299449907115800100700360a01e407050101d04480640440c098880c13420019548641c4403040b407003081c10441d0603401542e004000300d00c440c8942c06400d0703601e5000260205014078005203c0e01101d0040c2d0071603072941d6555038403008490a6030002800280240c40c011000c0e12144c000c1c42d003040d0f000306045a0f604041e98084c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 68800038 1250 68798788 68798801
    0x10420e010803071707201f0809010b090906010306050c040b0f1305011b020d020a080a12020c061317070b0c010f0b0405040c0303050c160e161107120312 67
    0xd441d4000161002040411404000200740381030100d4282001d56880074900406c4010400301d01c8500d1005e001c15070340d8014110810b000010f180c00030091030140040c87d040080340c013101d40d5800e00c0071030340581c100000b00501c5440c50310b0141100e40d082d0b03a540070117411302034600c0301b00c0300040c003000c41e01102c200d000703014107070200c00c3e119034402200c0070b601401d41c669070110303040c0503c00e0a40180d412401081c3c1e55104d074121502044041e641c80003c00354000360300310440a20401c90702030100706031030150400040e415001c031215003528070100503c0b4410b401c103407103280c900382108220710141041c40145588203802501e4145454518054480d04002e20103200741e91038400003101c250140c450309003140f0040d101840280780c6070f200d074680304680b84001070400000007141003041c441440041c140c070f82c1d101401c0c806142d81c0c40d40c00107100000e4515006a94481c20070110303240c010303541030303841e05c01000180c040325251011411400c10011004c8d8284800c1e42503043c4140c0252107000f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 68801288 1250 68800038 68800049
    0x8010b0309032811060f0a0b040f05070302131406071401140708011e030804060f090e13060c0203030f0420041d0c010c03300e10420e01 60
    0x41401c0007072020000c2104c4120052a03a5541021040c4400141c544030388981c041903509000c01d030007084101281c02032910300d03403104100b03180005000200c1d92540003010406009a00302c0f28443e105d5181c8070b8031b1110442c2d207940c410343c200b000b440040c1e05017119410f200c41d100d000080e160350504080c04591811140b56000510300e00050003040115110880d044128103107029040341503035a041c1e00f80c40780740a202c090042040c101001a445007145002400d140d801d85142801e15a403012110650303000c0440c1e00e50304062440515a2000003520b2080b4200350107010607403181e848907900c110030114a80208460807040204a464a02810300c0c0c0610f04c007121104034507040803003810f00440303200440c10040095114000310350f0080c0c010700f403104125140025104807080254940070102405800c03d41440301c0651065408250713209260210b540500c8402c0410100403003030b030740584980c0d42c4628099442c10507020003c00c079954420002c001d00320000d803604804144860300740d110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 68802538 1250 68801288 68801347
    0x5030a030f0801080109031205180a06060303080f060f0f04020904090506100510050403030807120e01090b070819020702211f09110607021311070b060d0308010b030903 74
    0x1c6444607980001d40c00d00400c0d030b0000030080010b80381c0c2c0c01010f02c2140130f4500382c115140d801181000345460803492a040840c3c080764114204c904d4120090300e054841500801c00c01c1d00061803c440c0d20a116229801c01071500540f0b20280c001c2142850060a030641c01030b90030b0140074080e840b2849808445030051000f804207103062441c8110011f80b5810046c000e1590b4040651456004829101981e034181401c90850303841d90400c48100c0010b6124050180c03c0400302d034100c46041d40003514a40c0070305503050301640d6424060b2840c013010f58003804003482e02c0c5008910520b859025002c01c61005008080d2250b407016a2403d0307070501c03803005100b500700341e50606800892001c04070aa0119000a010f98840e0b52911500c0007800c2014500031038000403e501195102000c860703044843c803c0070440001e0300140f00005800c008002c9445241034004502a17160030242c80400c0d56050759000341903805c01c41c00a0142d040600305c3c1c01c0e148002e00001d08510703100000f148041c03199074203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 68803788 1250 68802538 68802557
    0xf1107120b06150a0503150d0b01170606010e040b04020702060310080d0e0612060d02030624010c05030405040b0d05060103030e01031406030a080a020f0313060324180605030a03 78
    0x104601d0a00010308001d11500a0042003100410039009440421401d07050440e180d5845a181c3d44155900c005440e03070258210000340108192240c5c04c9058605400e296199450744811a82d500e10090390441d0100782c0c68036000721645415040880f07580005040076040c1541640464400d40058507912403080c2030000c18090315504100e000100300291401194001c00c040110340c4910664900e4400c0c03081323050000740b030b85e11400c86900070a9405400c5030454a892220207003174040000d44800280480002d0001540c03054001c01402c6407c00023952400740340a08101c000c0248001c402d8010003002d0209000c21010310149000303601945034102c14410f42000101202c49404c411200d20620500740000340d100020200d2040354030404d075135a2646141c905a00d000c074580410320b4980300004202d031068010000342001c4926a4409001d40341e01020901510381c402c82d01c00c1c0046491000c1001021465424145813a100240000302e603600d40d1302090034010403c0e41980802d08550 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 68805038 1250 68803788 68803793
    0x110904090507140102030a32031501090503150a05090c0604120203010c03020304050d0807181e0f0b031914010602031b061b0f0426010e0705010f0f110712 68
    0x40f20081c102800748041d6141c401d4046018100d50f034006e140000c02c17a03c070940301e0304007002221103038401c072501d44401e074030380c6002041080ca480c099170086002a4102e0300010300c4d03040c0042c0d04500f007100070000d007010f503a0301900e40c0010318004040000a10a000000c0c0190f100c000082c805002e080100c10321283e8280140f44c2902e1940483c441094810020000400d10103c3e040450700d4851510042c40c3d00d446008691030325041c110601402d0f071a1200049804081c464240140e1402d401080e0f01035403840b420b6017400403842083e080100800c00100582a2050180358603100500002807440000800c3d45200c0d03000d0f040040980d10002d003c1446144100103140b482c1c220070000c140d80d00d8119035038001e4001540f040c0701c030000c004c540d081e444000c0205407000342c11b29155007110081409518141c0d00344015084006518254000b8454003022665006483c0306131600340703502c2e140d48021035070b100e000b00c03034030040101d001800c602600c01845840018110000103030250302590 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 68806288 1250 68805038 68805059
    0xf03060d0f1209150905010507060609060b090319051518100203062107050d0201050d020c060403140a14030601210b010e0303070f080702031e0109140c030709110904090507 76
    0x980148807000f00b40b00c405a04c85500c441010140c900a207000ca40358051490048007400c4140c11641c0054109040490340c5000880542001c260840441d070310010814113441421400e10009040354020410000218078429049500510f400151180c001d0b0b0214405041128540d0f080850b10b030000280080c52500394048964040c07004191214807500da80d04030f90f100d9441c4101e034000e804c0c55031145d0039a8080c005807400543c40980c150354418010303800c00e864038011030b400c80c0030038100905e000701c159460003a81c1a8420b10f480d1010310f11900300a00c0364582004000380e04201c00e0321004545504119560b0f0806031100c2c00c04500c03100c01400240110100e191094000d034000d20095010900358000d090195810604040e9075200e5800402c0c1061415030200c0c0b05000010140300c04102c0540c03000b02c205000e81e0001030900303c485040d6443c0d199044034158994004001840103204a50011102a1041903980e1524401101080c140c4503008000d035221f810500f001c0190380c056 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 68807538 1250 68806288 68806307
    0xc120d060512071802040b1305040606050c0a02041a1c110d110d02120d0815040507170601020106150503090609010501050a090207020301150b090301060503010506060f03060d0f12 79
    0x11500140d118002c06982e40d40c9031120f00ca0140d22260808012010302c1d580d43c1150041c5c45d003104079961303c88101100b12001d0302c69100d180c2c0500c0c038040001564030311600c1910540140f0502070310341180503808000140109000d02e40c00f07142c1d56054540381d9525283c2c4600242c240f02d00c09a61181c80e0300b410300c400f02096441c82e0081c5400518040060480a05010702d100c00702d440664030810703400072401c00c00c14082c00013034900c03880e040d8200060300b108029120b42400442c1e8544111030740180019500c0c161495000300388070003101840d8012000402d40c0c401d5042c40002040d9580e6a4009881e03401c41d00c0c00c80100d0000402c0c00305402082c844560b2160070301c0000e0110b94580004510300301124450724446590110f014000c40d6029000740c014410002184030400703445201e03100c43c0da807110310300b54865864040c00150604042c040d462154200504a03030800c4480340ca00c0307000f0781c00203240c80c0e4004802c18010340054105295014642d000e0b103500c40c20301c140c041d00500650007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 68808788 1250 68807538 68807549
    0x807090b014a1804050703021908190b0601031e051608060a0303020c06070602040e0106030b131b120204030503040b03060901061e050a1716140304020f040902060c120d06 75
    0x2182d00344054a0380b01d144090060b9503200050383c4999440d410401d00b8008140c100035030000d9000c4580c150019903005081c180c80c600000d0f5200182c2c201025001c1e0341e2001e400a00d0001c40e0000601e0540c007070740c001504603081d200305404000c0e840d8515011160200c070100e000220002c0e41020741c0303522403032240c1e004805a5001140d2401c5882c0a5a100f05599a00d0f12910f40003072404108110303a0140c40040030f607207040c480d2175615100e019000e4000c0c42402d900500c0c000c900e014080c0b405001e5640d1004407444083c04207010003804903a100b52b550400d00c4031540811001000401c100010302c01408140d01c2c998490500c10200502c0c4907069000e40104080d00005c400c2104668907085503c04603810701301d0340c90341c401806494031110036803d20035030307210441041001c2144808041e1004440c2d6145900042d0348000c228003800161006504100c4001401c40d66040c2544202e51060008080d681011942c0c8013151030b103280b10401948041000c40c40c51a600c05c1030042602815 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 68810038 1250 68808788 68808917
    0x7060f0e0303070605060d12020a03120c0905060906090307030803010302040506030304031a15030619052410110604030302040f051f030f0605030f070e0702070807090b01 75
    0x192103000a9890080020141199507144045a1981c1e00c000080c109290f01014001c00c8040311200a0344602803801300703034080b55281d28038803841d00706440f40c0440d045030b94980c100ca1900b000107011180e000740c90243c1e0089010071105440d03a404003c0c40004520504056503070f5030651040c8002d0340c00280c28103000b584140814000910040c4400304581d584c13420001c140d548408168609413507220000703070180500e8042c807904030420302c040189008c45a800780015240d8408200b01220b0a4880780781d1042d03aa146820f081c5446c140c0e0358200d049629043c41c03480740202001c0d003091010740d070071000f2a60010301004101d88403004080145400c0306c1c005000f9440181d00702c516812585aa820550341d0f8108013204112580143d016004c007408440c8000001840c0907501d40b124060000b4000303240b00040da1452000441805882c100c0b0f006d00034423031034414918040c11081c50058113000c100641d01d0b00d1410030410580301422880808800c000d00e054000c0c0300209118035455001c2c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 68811288 1250 68810038 68810057
    0x20312042409180213030f050a06110c190f06050108060a0608011a06130308190806030105090d230a0504140a030c120c0801020c1608070e1b130807060f 67
    0x3c0e104811290320a440078540940d40b11100c8000c02882c440b50340000f4000d41040c0700c0b82e0248440025042130f4507103d4201081413074211f08200c50326000b2610464003952080c10311303607400c0704140a030045207031140c03018101761041d5a5429064900981001c1103560240e010031180b80d0640c00307075074014021400200030301020988072810003c0041c0741c95004100001e68a0252200015035000079604469070741d80740c95010020700302c0401807815030b50008480401240c40c501d41803182c54000d640d84002040b0361880c124090310958401082c101b51010f10051a01c8a148441c00030a1014500e60315a0f80d51410040140303081264201c41502403071140c0405d00003d00035020207019180c622245005d0b078642d503d46159202c056810000c2103500100e00c0c0c900c650380c0003403040c02541d03500380b0042c03110740c880356525030303403a5544102a4540c00c2074000c01c1c4200d00010a0034442900b48010502d007140180d20301306400700035803080c1d055a000040070002554000d03242d44922415245c0541c0301d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 68812538 1250 68811288 68811299
    0xb010f11060a0e030912011a0f031005101502030406030e0d0f0e04180c080d1407020108060d020d05210406050f0a0203041e060201060e06060a0c020312042409 70
    0x1991001441840456680d101d00c0b1940f05041040e540102c40042c4070440598402058034041e00c049085240325420100c4585c12510301600700c4145120080c0052040116080311000070342405880d05c10154171441e404182d4009c46800a95a1a440c2e00150340d941e00d4440f008084075000030800119401c03011b03054805603480342d080c0d0000e0300c00c0d1504070a450745240000d0014071510340943d40c0c03d080b2001203020024442000c070104c0303904405072540c691806c44242c0c3c0e4484800418440c0c02000c01c4260019070080e0341d203542113003016101c030300200c150f5030228170000b040c12360035691a401074610340819110380d5024850b482d8005900381c02c161800c00d003d4024020400388555200011804440c024400c0003500e005003030480c07102181c28914210300101c81c585004250043d42011408200d010342d0313410f0310b8080c880c0a00010316046055400f11400071420a0899040c000d1050003110008044040c1c800303000c03510001e0060740c030880201a04070103045403090912103443e40030845c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 68813788 1250 68812538 68812543
    0x40515120402090406061701150b0415030f020714010e010b010e0a0501080901150f150503010614030901060503161706070807110c1005071b0302090105041a12010b010f11 75
    0x1040340c2d05960050641c1c03a0b900e0105c010304250b8020380303045034018400d1210000305421101c180a60800b24464654941442050318071960042008040300b0140001c5401c0c4641d00026074515603c100604000140d03450490001003130420215607910b80036071003a90030007846032808181d000d080034850304007030b6000702d0400051840b8140c140103040d80050710700c0b10207401090300e62818245210b49162a0f15100b100800700b40225014800014140342c5ca050042044078142c0310903441d00c001c0c0402070003004242d07a10082403d0465501d50000103400e03102000301d581d450724000e0f91003c1c0386003442e0075420120b401000000d0300e40d0100e030030310a619400506807074100c2c00c50314110040f008040307042882d081c08182c0043c2c2091003103500c50302d91750380100a444282c1c464124480f21012481d030241240019020280d03000100300010041803406901c030b40020076203001491005022100000e050a0b6411604041750351502000c404560f4001004c1c882c00a541c1170185601552091596 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 68815038 1250 68813788 68813791
    0x914040c0506070c080a05031905030f0a0b060c0a060f0b030102070b06091b130e010501050703021507020a0b01090209040605062809050303030a0c0f0c02061204020a030203060c04051512 82
    0x1405982d00284440c140a6800c00460103080d42c00202da642c034000780f170559526400651f03105025140c90420030a01e81c03150302281d0080c0034420940d58291034a02410000f400a10201580894100b040c41c3e014071040c0901c011a500401001400c0c04400000f02c094642030b4030064800d034030402902d0009541030b07001c1c42d04400c003030325080002e0360f80304003c2c031442c000c3e03010f12040407402003030306041550240c1d604015036462400814443e4cd8510056400c0d00502c41c0003405070704480e48011100d800b88000c2030340070149104884554086071540341002000f80c00c4590b0950300000c0c0c40d03a050429004200007444159025881e02c4120701910b003500040b1051144004040d203a5402650310584160b8003400300101903da9a04100c0807071401841c40103103c03400b06018802d441e00190044246c041e01d1074000d05500c1c5062540b10302e0a4006800034002ca070b104040340d2012000d40c81c1089128402c3c9603041d0b0041d030b518100f07800c0144104000d8000414468200150a20211540000c0d03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 68816288 1250 68815038 68815049
    0xf0c080420181b04080a02010e1005092206060909140402060715110a0e0f010207050303070b0a0e0d0804110d110418050d1d09150111010e0a03090914040c 68
    0x2d585500c0d003404680c2d45881e5102c403c2558003011801003036600e4041039820046200342ca40781e030040310b00c40501245044091100b00410b10920048003030f0f04102441d4941013014115003a0703446020490b030006c688050f0040d0000490136241801a03003480d208003c03d010300c008007181607140550000300e041c880c039000108640030055181e141d10030782c1d0b040006040f111260980d25110081c100401d90303c6d43c0341d001440341078500002045540041540012340b44041c020b1403810f60151111500481301501a0040e075030303a44402007040405109145a450b13142e9118030540c101410109080007207100c0d00c0e4811041d03040c0d0140001d9a07032003a10290350701a42c0215030501c1d0b11803040b0740d1000b203c40181072030050142c141200c80d4130a8140040c40e41c00d9810011a140b0001400001c90003115035200043c00130401c2101c56000741c44201800601100210382c0600c0d0300320340c5090458016003140468080795082c8034015242c0560220b0189000300c206c407a2900da210352048e45100d01c210f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 68817538 1250 68816288 68816329
    0x10906061d010b120121020d0f050c01030b0906010309030c0503040609060f030b010207030b09010212041401061703070f171c0b030307020f0108071413140306010305060103150f0c080420 82
    0x46c007900311810710780600069002802e40080c00b526080c00021480362500807a6640070300c01d40100c241d0300911a8210a44000e04104030175a50500150001d2910000903024054603d4505001a01c00c0009201400150755001346291030044090141c848200c00c610500d8200405a003059a0001b800411243c00245042c1c40d51201181d0318024424078442c21900d0b1084420003050003040141590585410002001030f40d580c3d107000c0140001904040d1150707001000b0b0b00010402d406030440100340221000102c0300e050f07908110751540100310f0042e5a0880c104d0b148880815403268504107602036025516040700307940060000407401542d2810710030340c2d01c04100b005104048407451011450500c564a8000c06020034035200f0364441c0007150040c118490000d81804591316048039840350080095908542e075422a01c40e40d138102c942096550001c2c410442c4460280b14030030805034480740c0c0c00f4189400d004154400c0402c030850242c0c0b01c112480559161a449200340c0d0210506 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 68818788 1250 68817538 68817569
    0x10e040204050406110705070611010902090606030702010b0936060f150301060602010506150403170d0209040c110d02030c0309040506040204170706090f0f06030b03010906061d010b1201 82
    0x400d80300500b0110004a050200414146d08000740020720b00159260381d01c40d03500e00c0e106200e1107030036039440c050300030740003111040801d1442c1803550203590040854000841c007001c8010210740d00c254210303000d03605480b20481681030f031901085269241004081c03030b44c6007111002c0d2115074400010308121070310304042001070003040c60030700255070b0084024001d11010b5501c6000034041c11060740c102d4850320003142d47d0a001c5101008440403240d2101e040e42d6002c84202501169821400e81e281c101d607020450154a642d5920429000c00790075100d4000440d101d00035140790400708580c01e029548100031000d16103000009031064058121000705603961200d02107400381c0141c1d4068440381f10309103114001280049070b0b00c0c00743c0d0495a1480c0301c01c0c2d5107422071a0001481e22805000c4002e801003071104502c84c0d000744081040207070000c28a1a1559908801c54111b0381c811007000f01400e803001d04001d0303a4000d03d401028240d513014108240305800c111007031018420403c4801d000c11 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 68820038 1250 68818788 68818793
    0x4150c020102010e030f0c2505010f05130e040506090a031b020d060f021b030403030801060c02220506040b120c0f01140c060103021026090115080a0614010e0402040504 74
    0x10000b11351100880e003502c0c1c135020440f289500320303040210520041d00885500160040884100a0758240d407c01e54403010f502d084010f50301d5104040c07414081003010000245003850160041c00100b0b130010042c803291905003081ca08069010704032030803035007280030b01c03030080b0b0b80c010603e85110341c2c200d180211b0280c01c1e00c0001d02100c0c042c030300142240d0425041c12050300309139014100c40d00010f2078480140500343d0849807039100310300000f00400d0b198801400264450b0031030b4a02c2030b10280400708a14400307103584000c00081c21043e002152039200b00b0206003400d0203814401401510070441400202c0300c1c042e01c95460071500c0d805031004003500c407490380c0b01e222071400c1a4810300308c4d1551100b24101c05916003600b400140d0141d00400940140e4074441e40e07000071051032422070f000f60000112a2900d500202600350120b640d21a81524811540c0f8402c41000744412740c01014031026030b2402d141070385c100d104034560001c0100010818544582107969016a0444001130590b07910b1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 68821288 1250 68820038 68820041
    0x160206090a08101b050a0c060b040608010207050a05070f030506040605090316030c170c102a08040c05090c0f0d0f1406120705010c150f050c130b04150c02010201 71
    0x82e030048505100b40c0c0324401860780140d01075801d10380000e102e040c0c920a0113000390707103a2142e071421100040c10420b0b2140401c805502401003800c0080002c59019a6003403c1420390b08101c8055641d50480100641009001c10542008021002500200d1480c1d41c5400c1d882c2c1070000d002510141e01d80f000175401d07440c2071088420042092038003071110481410000c220a24910f000c0383d11001c0e603280000a10384190070b0303c003042240740003007a40e032400302c0c81c000103000020240c01b44122005201440203070b0000703203214400156940e040c013500d410b040420150b007850703002500400101051003041c00b0709008555000141d440c400350f80313071084400000200340080c0700c58446032400b211440018143d480c000c0c020300e000c582c101c0443c1004014942c858040d0701c560340c0454a4404141c00013080b1117105180040203020000703200f400c3c0d4101e4807d0310002c95407118501c400003070381100c0314030020421018207000c000305401d06007010302c0007c00e900303401c4007a014003510303900c2c0d04c045a00c01d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 68822538 1250 68821288 68821309
    0x90506040f0617010c080c03042010230f0f07110919050f06030712080f04080a02100504030302030409090813031101030b010e030c0105030405070806010b090a0501030216020609 78
    0x2101c420407520b5a01e0304900c0052000c0c0700300a03415400e103069540c401d071203040038602442c0e00505036403031034890783e46842203030810700514040082a83d4020a00e951848203025004180c3d486500498904400740b007403450030741038103131143d801c24042c5910300008941034500c01501034080b00e0356400c3c1d80c01c06900f25081c40300500c2c0c4c8588002c00304840040350341222414000010703000c2c026030b1901070100c10380c0c4108403480c170341583c000c0404006140c502286040301d140144060352910386c00071642d6190307500c690001111a0f0000580b5000c41c100307110000580c0c205460301c103040c03d041d903a009440e403049106003500c0540741d42174072007800030001c1242c4080503440760310507249549207840d00e038012600c04030f103011a2801c8413441f02940240254102800000e000d014143c0e4940015a80c0d03800140056440e44948400801c002c00d0420420340a41092000552103a0b400c0042011010342074100504050062065901940d0708000c00d4846540c116000e60311824a800402c0d09a83d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 68823788 1250 68822538 68822561
    0x60f020f030c01060536070c0f0b040b06030a110105030a02043501020a0203031f0812070203011a060715110f070c08030a051209120f0c06010609080709050604 70
    0x1000542c038184510541c80300c01160b400742e80d5800000107403100001d100d400c00055202c26100780603608149510000e42c10307800f0669003459908865142ca44a80710170000b041202c10141c0f120601052041920416600490440040c812001e40e03640b50512030b200702d660700c0c2c144500032001c20401e0b00a9019a8081c007401104241001845900104010041c1078122402e101c8076100610803c418000c83d0b50040036500114559140c00541c055410034160401c0c8000002503004120f860341401840100c407640c0d204c803a16046280101402c481c07848c84c40c10420f28400702550444e07100c0ca8103994040d0b800c4036000c80800799041034200038020910b40b040601d2800110101c2c038000d010054000d040c000c5080301000c540b0b854041d550b92003000503040c04501c007441b0a2000407040c864855000d00c0c800300f511034601c01204411069003000f940641c1100005c614030040f61010445540184820f1030a03039025403800000e543c5400746130181c05800354869002400588458100004801 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 68825038 1250 68823788 68823793
    0xd0f2402030c090108010906050a12060902030607090603050f070801150201091205070302070503030403020d0b040804080105130b06040606050a0c0503042c130308060f0d050607030e0d08010f060f020f 88
    0x5003001c00c1440c2ca81c00030042d0750104003001d0021411036950f11402c8181d0380c02505442d0300c02e00344041c800c120034401c001114400d890304c114000589042c4902400351615813076003030307105080400180546000801c1541609000820001070941c0320104a04403501890010303112080e1250032805442e440501924080d60441c1300302043d684480184520b5010f50300340c86000c3e440340c00f01901c034850707484041c2d0300411105808000c25107280d4400d800c603106001c6580340a43d260300302429160212414060407961100d100140b0441804055215004075000c1100c503080c410040d18034040d140d860006c01c02e0902002080010400c05c80d030281c40d01c3c0c0308103000d41102c54000c42068910710014854541d00364003040e92824001c248651b0aa416150341085944140c1800048103403030b21420b900844450124000c80c00a00c2902e0003111507940110304181406505403810030b040288900300032682004000d0101e103d4145400d840f070343d203899090003011800882c80c06030084070300c5820b030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 68826288 1250 68825038 68825041
    0x60a021321050d0f1107180c05042102041b0903081815040603060e010f05062b0e010c0f020606091008100c0306060504061707090914010e060d0f240203 67
    0x25084003400a4501185e9904008140003480094440200740300c0e4000010011614070384003c060342180c46a40e0031407402c1400c00fa540c4130706564510038a01418030243c103540e002030641c1000d004100740c0300800c0111210725500d400c070042080c400c070722010301504008541c402a4151000c10411440c0c40209a160321214805100307030940d00c68850740c80420b19210700002c40c806072510890403200206143c0103114078181c02d001103030340202c6a01c1c80003400703842403030024061038036401c3c40006192000602820810802403c56030a070301d41a0034030401501072031041d039001401e00c1e4819815100b001440e00c50403540d14545005810420721400b6500340e9262000310b07070f07100700010700c02d90b50107204107980c4400544551080d4014031b0300051180c50760707454601c01419055084803440c1307880c10300260760b5216203080300e44840030b60300b049a12600400100180d00f400c10b4002d101168030030700300303804d41d6030b050050101c02c50300824880b01e103414440c94242070221074501d0342c003c08003956039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 68827538 1250 68826288 68826313
    0x30608101b0216030f150e010203070e0105030108100207050109051c120911060a09240206010e0f060907111501080609070e18070323060a02132105 65
    0x1501d012101040203910349461196a5840003842100e42c001c2902c3c0303041610b003591580c0003a043c001c1c4054900201074128050008098454060307408800800107842c0d041055004104113521315086040110603c0140700850b0b0100d220000c010604c080140e880c82d440c90f20342c2c00b5000d04407000c2e005000c0c01c44441458000b1a5883d03516600c140c1d182036070550414014412210188409409031a030047e0302415400d01800400320300c0746600300311661550b42c9808080741c60714464111401081c2c800742c1e001281d01001903501401c090203441f8068907000c2e0100300110310003885544034007094808600c0f03980c0115058984450700000ba1742c81888000f505280c0c40f030003841001d0191140b5000182d424402044c504140c1d43c1e10b01d8201140d1300e42031008550f000c00e08558122601526000100184141c1e29580c0441540b81d41701802d0161100d00350704201d402459a00620b004000f003600354010702c1d226030151190745807072018240e0507101000c07020405180040c11840b0741d03903442aa = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 68828788 1250 68827538 68827541
    0x21020c0406060509011101020304030818010216051c0203031312350a05070c060c02010b0d060e010b01080405030906070606030b0907030b0105030129030c0910050108060103140609060103060810 85
    0x540c14001e07240e00e80100d048031b4015081384001c035405000a2241000b04090303503840b45080310a447c3c100000341c10144c0b0340945d1100040c54180c00c4405a2004601e905144e4149a09100541050015608514103141401528441c48a008000800180c0720000e07a6018041c03000c1040103084008040d0103014040aa0141c094406d6050654030000003d00384501d074000d4500c50a1295650078150a0f65600d02029040407001c0c1803d6540b200b04994841d10750960444504c0d000b1680440d816150340748150840c0e5140070090704115000c810000452000400c8864110040d655141d1380c140e242028801001c40d6080144407088042c2402030140c070019600066030700801d860040d0743d80e05c400b050700302c0320384800044c15450785100c4c0c614080c15042000c3c1101c10003034282c480c129400800203012101c112102c1c0c03010b14100f9024005540e2100a05500c8036085c203040111068004091100c00d400a1015201c0c64101d4006003940c1d1180e0018401015800c04036803400425070308120 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 68830038 1250 68828788 68828797
    0xb0a0e01030b040902060a120e100912080103080a050d02090405040503070507140a0e04080702030a08030906010803090105071e150b0319080702060f09100c02120a21020c04060605 79
    0x80c002400d180449480349020700c2040503055006000918001103500203071a00c85850751031442042e95100c0303182280700309200c200640240050001a44100f03454a0f44441c0020031086003008503010040c03000a9100049400584881c10841d441c1d9140500000c040d01c100d00c4986d4101e810501808204a400000f40088a02c5a02079a156684841243d031808044401042e40301101a00c01c100a0201c01407050300030340100c6603c1e240c12500c0d00801e2502240d000112030f1440e00008202404009108103405052a540070310301d80346002000910a0040c00c00c0a0001c0c01e4103556400601d07591500320004661014441c42156031160a01e00144500099540240111400f24085208181c14260f541b1760110819007000310700e400307010040d08410206115091308002140c216603840c01c84c0341ca8902ca0f591401c0340700701c10b0b00c1030090400404091900d2a40090758000000b400125098000000c1400c100c0b0300c0810400100c0c07811850410a0740c10502d400c902140c910761010050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 68831288 1250 68830038 68830067
    0x8070f0302041b0203041403070519030b0106030605011e02010e0609100b01020304030507091113031203060e04020f010f052b05011e0603020a0e030d02010c0201110705060c0f040b0a 80
    0x20010043c40740901c186034158480300c1c00050b0801c0000313014003440546a1140302502400300d60035192a0000b280e030708031808505001150340e9000030810040484c0c0f4160150185140502c036003460400041c0841d40e03000765070710104182c003089041c024401d41c0714000003c280c1c021500c050502405060700c9803810000d401941d4181103130469594000011281240c2c1d10070b00800e07000d45000e84090040c0201155200000c808001e85000e0441d000300210143d0300034030500042002894000c0d0441e0183d074070442c4801c0f408010400540c0c0c0d00061040c195000b8240000d0680307007130b001121240303c0c4445001102002601c062040382d181d448003204520070107010003c6980b038001c01c00382078006071442c05030518202c0081c804c152090f000b42c11250940c2c1460603100c40d602000034185412505101d00603035484141034040c650900410521900105100d49020040c0d00c92903111240146031815030ba00000d0000f4910818400b19401025104101038550701c1c0107100820300319052518 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 68832538 1250 68831288 68831291
    0x50a08180303122e0e090f0f030406120b0105030610030f1a0414010b1b071502060a0605010806060711060d09030f12051513090206030702010213081207140708070f030204 75
    0x610b100c0d101e4842e14040d040184081c913940303545025108045040d00500c81e0050780144501280c846c0810050045c00f101288055a1103500b00080244040c0305009003202c40c0b81409242d003c40e90b0810102c9400400130b4550180504e808001a4060075410032081130161a04012032031582e141c0e4400742c00414100c074140030414010148419440003070140c035146150400c02042d0044800c4182b0130040114001d68200d55503404107401c14405010422001d130b04820b08211101c41d003403240710050542401d08003c1d0342412800315041d0700691500900d01c140345264020386555840544550303640c1c4c0c60b4144483d4016150003040c640c0301260200102d444180000b03600602ca010b968400c2c0c41c4100c440d41744540100410151040c0b4400b5440403560300c207202009a10f03140003c46c0b0401c040c2d000503944030342c1d4500f900d1174444103a100881903045181c1400f0381d40348581c100d4400540108103060904056840301d400d01155612050346441500d6000070000604200841180d0080380e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 68833788 1250 68832538 68832571
    0x240a061101110301031e05120301090207031209050304050111010906110702010f020a030c0b060105090307080606150403020307030303090206120106020d080f040c03150e0f010f06050a03050a0818030312 89
    0x509803018002170000038890300c142580603040d00a4521101c2d07480d8014402c540429920711440310140d80281c0115005a800103001024180c0107501c03030501c04504d890421040fa01e80c0c944940f6401240501c9040001c50803d10000301d400f50415851243c000200b04540d850446a00b0301a52141e00708034041002e96208c0c10120380089003002d015501620744841c01000759403450380c1c21700010319480c10f00005200950716520100075013005010404001e05032401d01070204510380511002c01240d00404103c288010b8401180c1e0200316581410040b40850321440066400c1c000d065000d09224080000000c1e0390741c4c0041e02d00c9003038820f0349941010b51180034081180c100102c401a20364441c659003040011032807800c1d401d03255002940001c0450000071020f0070000e00c2035402400717039110401d8511400c0c5d02c3c443c010043c00c2c11a07003021110700c2d5944494650f101c10401418424021803452000d049c402c113101003501004040d250303a0b10107401e03280b24901080c1d8819400b0b64001d02c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 68835038 1250 68833788 68833811
    0x60602011b09120f1b0504050c090102100b010c080a05031608060f0904030e03070f031110140a020a0b0106030504060501050907140f1b0a030f020312240a061101 71
    0x42015120114030b80d80c9120260406001c1040890030802c210b82030002c1d20b4038000400d20010b00600b128401e820400e503a40e10749420032007601d40c040d1101003081c000b0417140310941c1e0001180841c0c00920900030942000030001a262210402c0c000780105a000070070841203503004000790300c0359034010108800844040001c9400c0c040c100c4030b03150003001890342c4200d0741c5003040d02c0f15402031003407070b201088402250110b4100901030b44000075005001d8014801c1000140b488510b1420a070791450f81720701112001490a0306c0721010f40411400003540380c9800340300f400f03e091040c2d0043d101000650750b51700c00078020142140d00b581e0740d92500d40003003240e29218200d14002e0103555603044003003210180c08020f07640150311030005020108a99401c1040303080000348459040d4014000d450710358280a803e40e44080300001c210b4204120740700e03c081c1034001082e001043c1800d581200301c110040200c0780207602ca14182e100400f24800030b00940d20001c4d013003200e4041c0d0005d10401000c01c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 68836288 1250 68835038 68835071
    0x3090d030902150d0603021e010207050402030408030105011b020315060405090106052214010e16080108060115020114010b0417030301030f020f0310020d050402101106040210170a06060201 83
    0x2290025440900400700c0b03408900e81030f016101e9501901400503046039260300151200b106195001005d030585110541c6541c4c05100a0000300010303507040d07156141958610750703180b00502505060100340822141d030003c45000f8501b613564080e044400b0f94007201e151024152044400c1407280b030419001840318101809044c0440b18058a0901100e00d681d500300c5100c000803210700c1a841d03850250200781a2200a407074000c144100703d8280904101042c0000b000300314100d8403d01c01080010044d140001400300d045070b051115102a440d0318840490141c0014400e80003010740d035100100d078925480d40180112188107544039269000381030405d0701d80c00244030150546014a035803001600303180c501702509000c000d0969285590300e8100d00c00701d80080c2002e0a013150f6a4040004500f004078000e00b9500031800c000416401d070a103411303981e00c0000c2c40280200440e0b130361100c00500402055012041c00700011b81030b440c00810b40ca000301118490000158201441c0b800c08003800c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 68837538 1250 68836288 68836301
    0x6040605011212080601021018020910030c0302130f050f01050a05011103041a0f04030809090a09080d0b060c0a03170f060108040f170703050319050c07030c0c080303010b03090d03 79
    0x200d4021058034040742a134031044020310045c19802910442da044040c188141098244907019802042a190041c001c11410007007002031f0388181403c05001080f03a0801d10012643d0440d10700300c1a54032007840c58050408291a903103074a05010a010341e5080c00c03070410b13042e100160340c024510303542d0304011035a130388500c040b0680e241c20800050060300300c5110f6589864040700c508a14160b02110101c0c1164001d03442a80d035503c0120310300c0c000c0d1415880861700104144414082800c00d0345501c4158403486c4c0303060000303da68170349138201c544500060b10300d48a070020585070202c03950308024010012110000f0705500114002035168410303401084e0007000181e6441d403269880d81d0b183c2d0180c001ca00025991401d9100004540b0200310b8020101d8500c03907030b1a651641081440040c0c400039a070607400013181030a04200c2c0703003a5260240c0c2c2e41d1541502d006c41ea20025828841b2444039640c0020089000000002c0b510407844001103000314030321000c6503040c0c00080411401c8610 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 68838788 1250 68837538 68837543
    0xf0b0702100506060d0b03030405030f0706090602071809020a0f09060602061f0605031308030a02041d06030d0c0206040504020403060903020706021504080a1206030c05030106090203310f05060406050112 89
    0x501c50b0381e1062400d1b51160384804805011a440c06858600192821a030581012142e500800040c4003480e03100d10f24100402550005003001da0071702a00c08524003980200e04481e43c4da58104509540e5044c100307900805600307001c10155522580c0d40c401402c05401420091300c9001c01294013194110240442414a14400c049450821000322000e0340081d04020218101031403480104220750b00031800740100c002e00596131490700400d079034100c14000c144030728480c800c02004400e03240840c0c1c8104507981442c2c529400034840c07000540ea40500c0e04901c0e00244045408000c025176075004005860103a0221000181e503103604070b0383c07a00c022200240c030002d540045000900210080e112580d047c0c109150041e0498035070303c044645603403083c0c4e08a000d108040115043c02c0c814078020f49109a0190302c1c614021200e920310820710002d040007841c5607280491031200e5940f20600c9103900540c044220100ca003041551001f007540d055506501e024000a03250810503418164240e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 68840038 1250 68838788 68838799
    0x609030c0e1308180906031f020307051605060114090712110403050a0b100605040503060c0a0302071704051801080a0f02030717010501090b040203040c090e07030f0b0702100506 78
    0x604041074010070800c003400e0660b01c000b048401000084002e40138215001d00100a040041d90700741c10003a85080203030195000707401c10907914109544a2031540701e06070480d8030140c0e80e500c5400c411250b41c802c030841100d00103035208113002082400328240b41203e41d4001e500c4003459004041003007041060725038030b004c1414000e41e010031070059040a641024101070311814a5030740d4403400d09040c0a0541205c0350b1202600700222002624400350180c81c4518100b0f04041c20900401e42e0364401a00180102c50007081d0110b0443c4079404441085511507400e0350304140391040c18449801502070342d031081061408400241e06840402c078102e414400052208000030b0301c4d4a0414404a002a60540501c00005ca107110600c2e010391050849a000042d1030740c9009400c01c111250301d0703400c1c2d10660041050002080b01e4601150650310038120009400d905001c05528108040c0d00007040d07810b2621000051002042c88584141076503002e035254040d41c10814000c40d4001c50324140d02c079 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 68841288 1250 68840038 68840063
    0x120c060406081902040602030903100516140408070f0305010b060a17060d14030a09090b010c0b0a1b030b010e030c150a05040504050a0203060a1502031c091401020310060903 76
    0x710310840860390030000d0b03c80c030010705401218482c801c1c1e81c015003140d4090782c8001501c00b05824100110b0b0b28007003030721500300308908012100c540b080c1a00c581d502c04008034802c00e5945040b0500031100203040701003c99204a60752980754842841d1413000b52419440c180c0d40002c54182881140c5401c549691000301d030724100b28401014a0014280c0707904220120680030025000e442c02030340c01d400d404001c680b6907003641c03c020010191a088485001d082006110007660030071803a181090384580e003a0041d944171040c51005107100c505e10343d201d02e05d0004441036103402da4800f0308407200030f80e960310004610a0515980d00d000d949a00d400070f9040018031160044000a058041614500f0502c0c084e0b039000068261001500c45981440e400414441c0390710f0102c1342c000007403d42125114a80350b005101039102c2c001c480b1440d1000b5201035083c03280b60f103554041c000e4168041401e110000344610014000d41044541c2c900040300c8030400309689003d4401355003100d038082a400041c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 68842538 1250 68841288 68841299
    0x3070c090f020705010c0e040e0c0a120213050403090303120e0a06020f0f03010f08061b0708030604090b1009061208070f0c0e0f070e10120c0e030d02030306120c0604 73
    0x14090700d0741038054560309000340f4000610070300a41d6103050995495070944d07042d200401c4100c540c80e03d0192080c0d404055050701c940c844580c142d0454280d1f05031400c240800d8000f15035150055142048641e2901c810441010380084110054034040e1340c81d420003c188482030012200105130100903540564800d40009555800411100380c00d1030b102810108603519540c420b401c2070304940b00e11202c080d800d20480c1c00801609602404891120040103120f0144540a12401d0b0300640610030000004000d03440e2034100701c00c0b080d441041a14079103052075903910701100b0360185041d03c0f81494400101a400581950001500100c105240100f90350310707103182e030450140c1145c0c0c0b507000850014480010700f404620803c0001011842d40c0340c4010020200c001400e42c540c81590640b00f600d120a50201512030146114400001c0d100791108050781d02404d81c400c0399a0504c1900207482c030155011000c0e6014000907201c0403c042c1803643c0840e00c0b00c1a4540c07036600900184010841c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 68843788 1250 68842538 68842541
    0x3011a07050c130f1406100e0a0b0310030b0705120906100513060906150212180402070f05010e0a030206130302061b0d0603080403020f0405060303030118020d0204170f03070c09 78
    0xc4024011000060b03854000001006175005140765000068a1004000c280c0c01c00a50517000140c04c1e14204035010304000024640b04494040c02d001c0c060301200240c403514090740c0c00406560840d030342a8036071800740030081250b4000c0203111001e5180201040b61140005502800b500c1720100d8241414200000e1282000714040034500a6494000c0042c122200d441030b000078100c00081c2c05a028400c070800fa151075401426403640c1c0d0801c00c800c0c2c0c0086400254564037040c00c440141c1e403a03186062000361407a180c1000f42c502d5203890214101040c000400303000e01032094090f20056a00c500301c03840d1400140f00082d0158003c140007460060001e8451004603011030030032402c00418220b21021200c030350300201c5005500080a20a40c03900d142040469041200c0500c254603042e80071030303100d01040c45986c18510315584118440318030794041c0c40c45d036110314030210b480319034400c00400031800b60b001001ca00d00565103040e0b02070202000301c9041a03088106800c080d486e01c84901d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 68845038 1250 68843788 68843809
    0x601030f090615030302070b09010f03091b090203060f030102030114042307020307150203060a0506030a0b090a09030318030206061005041502011a100c02090a020903100203011a07050c 81
    0x1016a00c1000740c00180681c49021030101000c1040c0000c9419458040c3c9018119001705080794010300a18403da07911082d4410500e03010316000c68881254a010b1824500c030880d5100c500802c02404103a00c00c0580c0a103109140440300c80e0250005182030500300e2000780102680d00200040b80c0600d404c1681000c000391780740030300d0042410400b02c0440f039040d400352045001a04002240300c00c0c048100c46141c112280d040c801c505e18108403000820403281407040038000d15021000583c1c1181a503c034121544c0040d2a41c14285848d02101005120034501100442c5c034100038128440e000050580c03800b540f54008001548804040200b4020281c1d030000c1006420040130505005060700d180d0246820f40000c26106403140e4000c5c2c0c1c0d104501185402214081d0a55800da680544120302c650b0301502c0c000b145480316000100603100e4450344070740600c152200809048181d80c01036040b0344602d6003000d890020540c800c00c480c401e40502a009600068030107a0301d03e00f140160 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 68846288 1250 68845038 68845061
    0xa020c030910030911041404021207050d060f050a02091305060604030206160c270b03010e030c0609010b010315090c020f06011e05090103030f0507050c030105330306060103 76
    0x803801c061007600041d01d450040c000381d00009445000540400030904076400e542401100c05100301045e0340500c0d821440010400b82c4074490760048101c05100501001c4041c00016040844040044c24040041c0c00300d210710044080c58040040c98102e2a4403d44d0050300c4000c2c107500c421402c03196440060078028105a03400703801000000300682d00da6008040801504000b680030701254208801504515484102e00c10589100e0716101404a03124a5510620301e4000171405002c2c008070b801049103c003e4001c07840001030b525001c0e40300164292040810b40002d101001d000c40c01181514081030200382482020f01041c81014803a8101020100881c412200100c80324041d070b03441d10500b03a00a8840c81d6a03e081c0918072140b8500d4503014003420f484800300b651441d9070040c0422130010f800d50030800040742c01d1342080b000f84040d6442030b000400034010b5050607000c440c401c04001181c0d070342c4080340c511040c03686030078481c800ca20600010003800c84c9a56400c0198050101c01054 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 68847538 1250 68846288 68846293
    0x2030f0a02190b16090501020d0f03060b03090105101e120201020a02210705270403140a0206010f080d0206010e07180320120a08090402120a052202090a020c 69
    0xb800006060380000e01101409500080e55600709081d40d00d110352a60000c60b003c00500c20001d022607600054566980845890300400c1300200f42c804800404040e044100d60000c00424071030600c00c150421401400c4050600c1801642c509154800c0355402c0c54104040184400c1081100c6040c04100c10f814018015100c01c40e203140d00145500542e0042d1601c1e909010041c82100703101005001c026000c2a074a881b40d5002d8520400c1c09071280500c59003044644c1e01c0001d080611584490481420781070079103458148011001c0d4131030500f4006c001c00983c60400004009100061201c10118550060001d9034240b0180c40121100100301c2c03800d001075450b05620004003801010700450141c040c0080880c05a401380203125141200c1601c02da0101c1c0b440b910750000895944180c1e540001c0c203035560304080340810080d0045000c131004c50384100e02081000e00403a000144120344619444000045c00000250034005200c0003a4204200390000b4451141a038018901c0d04140402c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 68848788 1250 68847538 68847553
    0xc090301021908060a0302130c021e010b0321030f06060f0c0c1903150207050c0a0305010e06070203040b04180906020408030d050901060b1207120509250602030f0a02 73
    0x110342603920415801030700d0040b4403000302002d5803042015400500c00c4580b0f07500c0c1842d5400117440360180c1412460b01c06d6035002c0002d03625000b084540307002000b03a8000281c020003104494024070101c11503d011740180d415900015001018548018200341202c13030460b10f0f02400b055007150b0080015030010410040010800c20300c00180001100c4035004000d602c1d03154052220300201028003804071090300c141440040d8940009441d129414200140c035034440b41006440c2c00c0702040155003102d90188040180041034008001c1251400112021f507250b101c0304031ba40788618800c620b4400d030144010700a680d40e2300901011043c584402040310034813a06c90000b280d2250340b1030718459200103034141d102d6000b8080e0b0759007c0100c20003000f144d440e06070042c009228030703003209102c100c041c0c0000b28410700484800504502c15202001a8034190504c950740c2d520f81380c40c080151020290b0502c2525409519100741ca11aa0156043c800d0600800d403403a000029000c0541c0280031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 68850038 1250 68848788 68848807
    0x2100c02031e010603031d01050403080a180b04080d0e0102071703040308030f10090e030901080402130c020f12160b0c0c06070c0c060302030f01050f03100513050601050a1206050c 79
    0x20215402d104034000051161941c9409005a503002440118151082440000a07a0013078183c80889820a50141d03a601041d00202c82048001c040c07014480c44807540440c103051140090000c0d41c0c0315904451104c030703420700241d0310348519426450050707204000a01858a0191908010103a81c1044034140b98a960314500c40e600210740310441007040030104110056460500f100816002104002c03100c50381e03818944a20900102034148080d0b4004103007191500303000d0003080d04175003404000040c00a070b00291505200c0c001c02e2024421000c040402046c82c0003292048250705061050504e855646c40303248010041c11034507030081c2030184c900d4225050101a100f10300907070700c40e04080c009241c14200001141c209604140c4140708000700f55280e024200d0548600b02c1e400e140711940500060300e0000518000707088981008240040c021030044440d030524403900a5070303066030326401030001150b000e2140e451020a104a0400801e05903031005810800e0b0308151441c0c0044107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 68851288 1250 68850038 68850073
    0x10f0203040501150519060e0d06020a080f010b0408030304060b011704050c03070608010b18030c13051b090a031502090d080a03060816170709060b031b040302100c0203 74
    0x4a41c16606a51a01c4103000c041481c07480c0e1101414040311610f82e444918140f51a01d000180510410710030740b5030810310709680f0b00c200060b80c1e41e48220155070792200040010030301c00d03080c4e5a111101c45000008241b40b4028001d035415100d00c20000c500f190790715200c4201408540c00702d00c0c10700050f8411580041c0c0c60900306131055004400910b1250217a005152800f40c4070b83c01312041260032401800001608000c07103c407440458a060100d41107000002c4c20034100721150b07640b2610401441015082c503400081c450754210545500c8010100c0d000d1100d0b101c0c4918141e8808981d803004d2000030784201d800004010840c500508141d05c840100303503620618881650f0303001c80411004940c076890700408002c0c200120103480d0103a045108024004024001e00c040e02009200301c2c1c000c0b410811013a0000c08805800740040d41d40d840c00c0742c07c203038819105500b41a035000c455442e200c1d00201110100e0780c1c00b4006d24040b50000788101c1d1f0b82000b2100880c9c0c0750288031100d41412961 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 68852538 1250 68851288 68851291
    0xf060506150706270b0f06010201050c0403062a0e040614090f04080f0304030309020f030d0e0d0203030c0313080d14090f060c0105090615010201060311060c070902040b120105220e010f0203 83
    0x1a10070007982e0700f815441441d045800807c81411a0304000400c0000c41405c020b0398104c0c0c0d405480030401180c03240f041c1031440a4100d203a081c450b48a101c0760384aa9102c0443c5489420584081013103036100d200458602e04803001c819001040e11012421020001802c01e41c00340c0501c00150501c244988948695070059405400281c0c1369400c2e00294a01400b4000240c10100e001308600855003170040d05140c001c0c00c4651182c80301095403001c4d0b46050048071f4039510804296a500c60082c140b10b04605000e005454062045140076808180140040412100009611428906044200400764624180c09a0828801d0080c036900700000d000d032030301820415000d04914030340803000c0000e14074503060030790440e0304102d010408902c2179103e02c1c1f040e130800c0d59295030b00c4202c50304e114544030080c1d00405406200080c0022000e058901030800603204e20181130241c0d81e03030401c212940001c3c2c3d44294684d0011540c0807064415540309032041c40754800081a04460302c0c03512402c0307800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 68853788 1250 68852538 68852543
    0x3080702041103040f02090702150405011413050304090c0e040c080a0510030c051507170c0d03271e060213150804030c020d020a030f06050615070627 66
    0x401060100441c5001d0094020002c10048030070f0952600e03844015000081d1031000e4059440b460110701c1d00c0d4401d0028200401d050055201241428581180208043c484400300c0d220810302040100d000010386010841e0032400660515090a550000030301c0315011403400d1201d400101c08041d2030f40d000f0601e40c4580382e1140300c024500403051100340c070f000414503440440342032010710004420000e8001a1b035030566040103040003640c002941c034802e0b00c001611506070714100e480c4801c0128020541c501d50340c1e007aa255168144c0058003a02c4003400c0d410f0490300080340304030b407088000b040e03517134802d015005030032030800380c0030250020100a8500f62840c58000501d4607040d10030041e11801030680201c5a00b2024141d48000d0074154080c0c001010002c1c1183d440b02990303594082880c6068000300001c8003240c0c0c91500381e10545406000311003031428600000d106140080828404042c011000d52a1011560380d1400411030340c82d094a04080400e4030354804582884120103052 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 68855038 1250 68853788 68853803
    0xd03020c0d0e0a0e04060f05100503031210030f050a11030106030f0809010c06020c010e070e070c170403051203061903080a0c030908060115080f0103030e06070809130b01170c0406050f070c03 84
    0x15042600364085d150010310014500000c11410031081c1c80c00010dd031400161408208026260406441c0000e542544042c1c0000c03884001201446404140c0100481c8501d021030343c4843d266084c9802d98a0911029191103400f464071804030352000010150004140b603c0d2504034200d41d0740c0c0007241c2140240c0022a0754079003039141050000c0110801a094890070011507241c50b80d07008104500b10840101400009041c4481c0c00342c9000030384c2c0203147e111054842c084010300003200d642e04100d418034822400416250785410000d188070046c0c0317422801203840c00314040781c1a150720180c140218100306900300c2c0022410800cac807045018180b1820207201ea5100030300d0040c401003000d8100e41a00c2c0d410700041001035000000e00c03226141c169600340d2500c0c910305003038146d40901c10741c294108070403400407408003629500401a00000340c9440c00b4074004003112041c000c504441c05074044800308810301041e80501c0140102e0001140040d141c510a90789030002610207030b0085a40c1c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 68856288 1250 68855038 68855051
    0x1503061a0a0801061d041203020a0c06060608040204060b070c26010612120906020d0f050903030313021203040608040609022202040602070b0309030712020c0409050f0d03020c0d0e0a0e0406 83
    0xe0001400c9210044005c01c1c0c3c0124101620b0713054441802034184014160300160b407407100c501a64a03080459080101000b40580da40030242510f44100d0741244128a000004110120000280c034101d580120100f0949410411505950310500c3e46134010303409030300300303820980c017090154101604660300700300c0d013440a41c80e00c074030441079039209a402d00160070421302016600103a001d00d0050149407038410351054000544041c07040b80794050700340c0000820840b40c01c9004070801a12442921603403038400044445a0300ea015a005410000700c0036004a00460080d4101c45c056500040000000c490440c0260440404d862400c0c0c10030713500807800304210740d01401340e60020a41080e0044c0f652510904081d00d81c03281000040080c030080c4640102d1900c2040481c01125000e401008245800d00384030765218044004401d5a11490f11820400b601c00d0082d244200301100c01440000114041030391100500501141c0080c031034200028902e01002c2014000c030301030040021203 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 68857538 1250 68856288 68856299
    0x130302100302070203120d0f0c1d04020f0901050d020409140414070501140d060902130e0a0204030b1801090203030706020702010806190b0f0c16181503061a0a080106 73
    0x901460340455050600c18802c3da0090f84010a08030030824072004078594035034103003034808010400c040302647c11038035244000300382c550421006001080c0c3d043e411031740c0314980c00c104020391007000c0707107200c0031401884960304070b500640181070030f040c1842001d814182c465102d01d003250000441e02558108074010311040c800c030800d0035404c0f03d80c3c44024011550074140082c01c600e4800401003801480007422222030b061590101024240303582095645580b201041442c600c0c15004001c0804104800318030289241e100725000c8075403100c4100941d6885055418152010110828030380d500c0e11601c2c401664240b00510645116110068480966000041c0718290003441c182c01001001e0756103a50041010050301190464840943d841008050b8040240150a810b014520458604031444110840b0003403c3d6050000c8804030f010580c545401510103a803400103600b001201e0910120b6529001316100c4048407161014075102c075000304035032030407079809810719940d6150213201 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 68858788 1250 68857538 68857549
    0xe0f06070203220803040b03060d0210050a020f010b0a14010c0c0e15010806010c081308071811030106051e040b0c010b010906030209030601151701080d0306090e0c09040602040b130302 81
    0x100c281043d0300f03880441d82414500c84d036910039070056000c4490301000041c515075490068807902d41d030141502c000c046031502c0140003034120100c008094007a1000c2e01054290501c60318a09140c01855004142c3c50700203502d0305514015541c604000d441c0c003140011540303460303030300c0010300d8000700c212800e1500700900402045a0010281042001da081c041e05a078402e0410302019045040740743d0b00c8503001b2030940400b005520042082c01360030740001d070a10201c0d407040114020140203010003502601100307600c2c4024010350303010810500c01102ca80c00c000d00070210030074a103904103180030f4485004400c0740c0c2082000744010303074407409800d20b1541c1c4075410f0380007010242000e5050601120001b074803020b050160340540090090b4401c0918420401c5a0819003c14555111035850300c003484d07200d0000510b00c802090038050b000407140c40314456074240040d03910180440350b05030020081100c1c0d0180c004c3c3d4801341c09201c0800c150408070000c00c84005d025070745440451440c0305011 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 68860038 1250 68858788 68858827
    0x1020f03010b072907111c020c0f030a0c090c1407140c0604051c05070504020a050a020706020606090103031d130b27060603040f0f0f21050a030e0f06070203 69
    0x101c05045014084e10b140c003103100b0380c9030001c009050084524002070042440c00144c00340841d1009100802e0341100303034000c02ea05080b51002d5611188000c03030001450b948288283e401850445240000c201162156100140d02100c40c58a01c58070703104066116440d4005a038107541184241202541c50f40d0100f00101c030549058038583d0401e8901400a040200140c25001c00401106183c804111040c841d1102500000300119218401420300500741d4024044640244c03080002c0400c1d00c43c00050410301c100310080005030140e085680403201840c0c0c4140d102d0101d5002c00040f44581c1e18594107a2804200311400601c01e11a44200802030018100508038003a03820140c4052858103c10780741d0010741035540c10f41d01c1e190340c0740c140100d074900a030180c0b4404400e440081003204400300010b14900502102100500d22800540e5054403441001d011882c200b0900041a0003070b006180409816030a48001805082c401400c10a080345c8140040e000021403802c415190303140c05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 68861288 1250 68860038 68860073
    0xd050c03011e0e010614040207020105090907030603050d0801140d1e031d0405130b040510050405030301060306050103050601021e07030206030901020d0e0a0b040b1003080d05190e0a0807020301020f03010b07 91
    0x90100d00d1506c1c0e00da140501502d142c2078010381d00000c40c0300035a4054001c07074203c440040c08002c2e007440e08180041c0145200e000890f51401440390380004130b4032504041381070f10920030030310a2404852082100c9902c8030481250f2018088900400740481000d08900c90780c081d440700442140c00718001c020804001e000716100e00d1401040c400c64180c072007042c081480d4403958181403610743d81000d070b2402c0802c540d402e96540c1841c041000708800400998101c44580c2c44c00e10000b9180c0c401501a1401110b1050041e80242107808041500c0364101310206010802d5407021a100d4011a41c1c0742d204640e01c50181e0740000b91814401c0207845601c2ca5241c1c80780c0070340034a01c45d95545141c0a03d001d00050920044100400c0380c842841181100940e80420841d07940d14004501801401049030451520907166002038054840742c02901c2c0968040b0003d011380e00001e9880340016045030500b0b903010341d030901480303458075101c0f00214081c04600c28010f88840061401600c0141c180261 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 68862538 1250 68861288 68861291
    0x30c01151e030602030907120c03120305040f0615150207030c0506070c06030c02121206010207050906060702010507060f020a0c050d1706040506031510061107080304050d050c03011e0e01 82
    0x1d00300c0c902000005581502d50001c0050b0b900d4540480c07851401c5141c0e0413651101c1d80f1240032070b0822403907585001c2124810300d95100c41c15135416040e4215202258040e120761801a400c00015001c1e901c041d1500d5120340210b12001c4d1100500304c10440030a0340e10016912020080c000c1c4590b040c2d01d600282002c440207443c103822503039101003200480c031030b131000e15444040408420703000703010b9103a06103502e2036940d4035a00e540d0f242401c0c00500351022405402013460100302410501440c80c4122809480c0a1800c2240d500446d4290b002e5901034481c9580ca81203100c094050303000a18540010f42c0c2e84001c581145d051040c00c1040c094142000c0c000d51400c040307505a000c03003000341e100504030340000741030707982d03070042410706803000503201c1c898030a1010411840c1c10200c0004c04d40364590b1300c610702c0303035040391071241d0702d00141c0078005459000b03004c20026442c5c080c14429200d40704006607050740c0d00040c00b0134207444464003d2201300498135142000e11216104629515540100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 68863788 1250 68862538 68862569
    0x703090605010f14010f0318030903061d030a05130513060806090d0c140307020a060908010b06090d020603041401020c030703142b02121311030a0b0a020304020406030203030c0115 79
    0x20710002e4016072444c041d0510001645a080c0c0e10b002e0b0744150310440c0200101d00030201d15140061285c40b00e40001c03200703141703449030540200b000d11802c2404490341d00b00039460100c09071419210350704a0f400c8009060340040f0301042c65210511444085040c003000825840d050108990030100010f11000c00c55101359074005e000e5a000e880702c2c000c2034011f802058501862140181148070b0303280003a4200c0300040340024044d138080313020400c0300d043e20004c00c2090045000c1040b14803814141035403010780c4400b400094588400107640052040c0c169850a460300401e5a09a130001c1a1200494102244032824035810110301c0340c0f483c0b08014694a042080f800702c030741d41e0203500424829880e660540704030144003a81119000950180719042502c8c18a103e15809000344404540c800304c0c440100c1e0a50030001010320201e07038840b110300e0316690345149940094000a00a990150b00d44200001584003840102001540c417170001c6860f03015100301d0b440000c0d0300d900000c2c42d07000d503a8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 68865038 1250 68863788 68863799
    0x7210f060f0e011a0304080915031303030b0102070503030403171b0c01031503120f021905060103020a05040608100b040603060203090a03030b0f061605101b080f07080103030c020409050102030703090605010f 91
    0x480c1d91150780000d0003900da06040f00270542800508071610b0b9442400810702860a042c500703000c42d0305210b81d406100c08020603004903140d000c1481102c1c1c041d030090100b40009180280c00c12610328134035111604107180c03000309141f4402c845003e1204e0350003c0085600d0b0f540d1600980e4180e141a000341144a40385030340d0026410325180440041200028100b5240d030710034481904000d003250b41d0740d4100d00090074916103420082c8412449113620140015481c100303070240d00c048600f40c8002c0c003806c088161800d03014020040c056580a90380e080040006a51480990300928000000304801c003582e140141c00c40b003d072452a0f1040d100856400050369958040341c00d035030000480b204400e00240303001c03458401e401c0b0600d2199420102c0644028610700314400a0340e0716a55405525141c6e0903d0005000d03094070070100044910005101083c01000c042c000c4c0362001e0b02c0041c1c009101d403103c0307089070020b68203000000d840b080c80805101050003107901500206000044951610 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 68866288 1250 68865038 68865089
    0x6060d120503090c13060e06030105040507030f140a0b181f0f02131502061006020d0f17090606190b0306040504020a0305060a0207060c0807210f060f0e01 68
    0xd0200302001000400a600d2100034000e05801c1d010140c840040695290395a10140c0300d079005010f4a200708800180a07890305000b0f02c0e01440d00709010301010b908588811483c3d210400c4141c03240c3d00b554a0114681d90104210100b5502038421900c2a081100d5002104101c0401142c45940045503c1d06107c51124a0182d000c055a80005500a064102902030f001c3d00c0741070002c40750101c034002202040c0030018801c3c01c0c56a4269482c0d95074000c4040944070140c0518401688070626000e00e05010381e26a882410300c0b828420303030b803807540da0840d601c1c10000c59003608180c0011040c05110709000000006420fa07c1c5002c3c0c00d110b0810501d80400d0200800041c812a01c0d240481c00b075444695140000e990010240e0b06036283c45402c02000c2e50040700125865442c00351070010141c0310302d9205000c0c0125a45400385010354815102188420345a000402c40d520418940144803a1186800501816002020741c0b441c160f420030045405a0040c0d0f00342c0d404802c2c04402070001c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 68867538 1250 68866288 68866313
    0x4060e030918060d050f0106140105040b16060209030a03110c0a08120d060803030a15050d0201050d0903020106150806040f060513090c090207150605030c030c010507140a030f0206060d 81
    0x8681040003d990728400280e121007907013005800b50148048401d0b00344019080041600c03004c409e0301149020740350044030320744954440c03585d034414207004140406c0c80e24107594807164080d2002609120311500000d0510209a204401154404564035444507080c0f00c000b0100394111002606140740164290300c0c1c2001c127448400190700000c20b50041134459002101424010040308c1c0c8034a01600c0c040001e103080c0c089078105040c5000c00141030b24010781494000769069503000d040500e404002c00150003014000c400b55501c0b4540402c400d42440384451036504555902c000600b0441d052208554401b422081070300c0c24900d050140d80c4915140582144004d02d001a0182040c2800700400c201500004075107400020700c2000e010303000c0c000c2d4215900e00f6004028440d510420940e0b80c1c0e80d802c0c3d44e942c244c0c20810600080d9030040c0094000c05018202000b14071802a50580c1000f034014000c0340428001525000c03202e504104007540200301b41e41d02d1042d100d0503159811040350 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 68868788 1250 68867538 68867569
    0x70c050402031006031d0303040506100b07020109030213060e07020129300706050405010e01020a0203062805070203031e15130f05042301061410020f1504060e0309 72
    0x129401481001e015121b404030509074201c017500d0b141c2c00d140c60f05a8940e242940c0d0641c0c5450345000220f502c581810480e07441b10b074141c460300c00c65481c41d0300780941031403200d040100b4166070b80c030f000580044042c4858413803402039000094001e1800d59440ea035101c41319010780340b40701c490711000345030b00e440c02ca251300311a0110641071002d21092503121508001e2403600038234014402c0002c0e045801c07070080c000340c540c02d803289601c008050f0300481c0c0d10300d0b0150001c1c0d419400340010810340149000440e004c040369640f40302c0459000c10b01582990803ea0348280140d00010800c544407002000c0d8500d0f009032000840e290b400c1c14118582103039818613440d40b1540004400040d40c09241e03005100c0418445030900083c5028107003a030905240a003510900108070b41400003220061148030141d81d402140c030344186042c0424460542c0c8023001510540c4103102c0f4059008070300700100100316040360401d10319413806103092802d0340c4e400342000361140d00c1408035450a55070031010801421 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 68870038 1250 68868788 68868791
    0x1212091507050a020f1306140a090c0905060d0608010e0c1c03020604030806060c0105040c06030c0302090102100b0303040513020d0605040902060d0f060f08010204030b060102070302060711150d02070c05040203100603 95
    0x900000106c402d03810f01e20343c819043c40c19078000703140903c0280501641d1030480d19044216614602d140568040340c400c90000703003001c1d10902851611a0280880d001603040014605440307821040c02c603011040007462580c0108074540c6240380502401d0f0301c0140e20500038101464070343c0d01a41e0b40c140604010103002403c0300140c480d44949054a01d41c01e1010028085410913007481007018009008140c000fa0824800b88140c0d8003a000705c1301182d07010303070040c0202c0700b180d90b4000003402e0865556a250000300400a2a0340c1e800f0030114001c0d206640041e507408040c0c00400440c0c42030350185004609110480b809030307443c0c3d000c1d01c070407030030b00800801d50341485e40c802c40013012280c101c0440d205207602e01065100c2c0544c05841540e20070440c01d413664840c0c80069070340ea0710b42e200095002804101e0800010b04070480c0851b11040900590003911260308604515000b64024040069002c03030810b0038818513400d040020441a14114a941884000101524607a000e40c03010716 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 68871288 1250 68870038 68870059
    0x120a060821090117160e0108010522060e070503010801140c040608090109120f030f0501080624131407080402010801090207110402030708040209070906021b1212091507050a02 77
    0x740d024446070307100321208165400d13542c41c090310107400070703d40100c4d188005102c44040c501d01b54010031a40381683c00c0203051001c076401c82c01800030550000c402d42101e1f15103600000581000701e034501809400a919010340f2581415081030864001c3e1b071451180f6480d8205029050542c030044030188e80c200c0c40d000034960b5900100ca4003600003040001c205003c000301c480241b50784041d86030b9000041d90380a0100001e031a0900c401c0d200d013230080d407581d42c01c60780c04644174507460301907812000c20203074140150069601c002050358010414181200c6d80301e044403a104440a415990310802034101100242010b40002b0320410301401107241aa6001170100c051151100244901d01001482035540c3e02d08502c000b4000c1000740e40407401021040007041c4c0581c010080b04003a03411580c028800101c114400303400c2c4a030403480450700000c038801043d181150500401448220401081e581c80c030410091041c2d5420a0b0003040481105001d04000140d02269500c0f089404a4850040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 68872538 1250 68871288 68871307
    0xb0109020c0c18100b07020307060f090314030a0f110606060a0c0605150901120b060613050913140c0a090c14040807050103110304020d021905030102120a060821 71
    0xa1440079070000c0c2e484043d5811004400907440c01542c030800c982d2404c42040c40ea110b1000511340101c11001b981604541400d02c805c9205485135043c01c50700c0c6ca4046500caa0f251034400b20b0241c07131f101d80300c801e420000f51198a65080804900c0003113881c03038007808044521072200d0b11800c0c0540407500c12080003c00d01d00c090f11451114440c190450820411400c142e4007448004400126280c0a054184000208000502c070b11203001c50704201e08050542d40c907008c01c081c5520a900c503100d28460703400003107607545422404a00c42c3d260206215811041410a920080b1803c0c14188140d80b060f04628501d4031840030781411544031000101c1c618884440c142c0c1c20780069652414007010100f80000c0c00032000855000b100c9007a201000142c4800f501310fa401d2008a4003c3d42219045a10f000103042c60040c01e4071140c1d01c451260302e81c90b26100000d00b0f90340442081080800f41c0341c103006080545100e00b1004014400082803610100b80c40c4451400c1151480d440140022464400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 68873788 1250 68872538 68872543
    0x50609091906110408030903010e0601030b0414150915011a04062a0510050109052202010909050a091106040302100503090102040306060b1909030809040b010c0b070f1106040b0109020c 81
    0x340140c02c081103504c90340c403090680c0e40d070380040c41d04901ca50300703100540345500404500141a00e41001040446665075261340c0f8803010300300100c89843c4150514a10008180740b0040c8c01404040c02a2100c920510703c00800c15038107800070303180c0985990954001020010440782101e64905004a04040441502d1031002c10220355401d048424400702e010002c0108480000d001c0040c010005a620f0320307844002c03110708803405080c000e076401407040300034a080790680c400703481450000340b65500c68540e20183c52081e1180076950b910791440004020040d15084c0030500140c03401421701e4038540004072044441c036152000d00c640040410781d500000c0d01202e004d150425018084683d80d00302e04043c66110200080d007404a41c0843c941c030354415a482011250001e105038100321540702040000d003000650a414455110034103070010701561003103441508079131140d04800c641d030a4040c0107803211040c00030564207d40c1c1008000b41018003202d055460450740141c0301c40c00101e00a1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 68875038 1250 68873788 68873801
    0x60509121e03071b050d03050c01020706150f06030b0d0204051b0f03010e07030905100203060103241410020316020a0302060d0b03070b0c0705040b0402091c0204050609091906 77
    0x21003000281c0e200c529031070340010041001900c60100300e400c8907150705412103240464003695a00c0700080c0c0303044002c6442030001d0302028500030001442c00358142e903210110340c0a408214103410030b0380030400900d030000c8007440007090b141c2018001160b205001802400000c0c0d4024491343e0368501007894101115402d026906500c1c3c1e1596450300c000c0c110000c030350800d200c1c1d181c6e0900030000190100340b090040400c0181e00800800c002e02c1c034903645401a40008242c80c2c1010340d1004070380c0d8290510350315101d0004804c000c0706445400c00401c66458101c07800010700403451800c031100c4495001084a1a12061141d45001c11100d84000f804440b0b8640c0b010358400008180764a01941581c07100c844800b0850885d4459541c800d4a104075001d030704021450703070300f2075101007000e410301e60400c941000340200300600d081000800a4440b201d42c104100c2e0074102c0c0000401181401c8c071409030000030440ea40c0b021803808035100c56844114168000c04107003d0307554407040085941114 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 68876288 1250 68875038 68875063
    0xc0203040f05060d110a081005010c081912090f110604061d030a080703020309040c141b0c0303120901050a0603020f0f040f020c0a050c0d05030307050f1611041506050912 75
    0x1781d60b44101a000815010081d9100c4800342090480000d8941c0551030181d695540403656a00340a0180d000300c0c0400c80c100c103614107101c15180c07803010f0490ba0b489452000c500c608000c2c0749071403040c01c2001ca0415083e07500c600450040009020581e01700c41c4c00c001903c030420050301104c1d0a00042070402d481c0042c0104120401325000c002c050300880542409582900d0404c800c949200c0c00f00c0c0d8107120020b40c10142c030802c00c8120289100101d003200d8240da48022100c1981588000c203140d54003980a252041410109101c1805002c1c061142c110441c0c0d001444024116000900308801c001d511500ca211440c25500003912039801000c2c5c2468140c400b1915204520300031a282d0304036a10480d114000d10600810390300e004c3c0c5a0121194000c0011415a610322905541660054500d9001003106210f00c40c4c000b440103a480035103511541490451a400c0c400b0b01043c1d505074204000041003c46084c4030196000050344c2099078201c802d038414440401c80d8908190807800b51 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 68877538 1250 68876288 68876321
    0xd11010509030717040308070b01090e07061b02010908060103030f17071d010c0b010b090310020313030305090703050102131503090f021e120102030708060603010806010b07060212130302010c0203040f05060d 91
    0x80e01c0a00854000c000e040780d4bc00c40d001d006c001e111011550700c4119901030400426500c071a0003000001c41d0f42ca030030400f031041c10701e600c6e07203621844076a280480991044001442d010250451a2344c0201d00502c0802c074844c080c0114202000082c1c0340615611542d42ca240c0700c4400100c0d240c0c4545880041543c0040c1c890113596100c08814010798450400e6034003030700c245040c1998461880c42200c5c4a40c500220b02c0581d005181c0d411400303080c000d040f000103441201d5010007c03600a10003051304041003654600030507e0000720301110b4007111880c0d41070500e0000b101001c200030800d00302d00315504803001c6a803c2c04910800f9080c24103202416081030f038000744072900200542c001c502401580d200ca0314503583c0c080810400388024094841c0715080000104500c58a0401030318107079104000140c10002d08030f20144042104880020050040001040c103040d02031152040174050340c80550301d89801d09510102d180d0003481034070700a89001800303581d081d480d0303071280840314042c010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 68878788 1250 68877538 68877547
    0x9010303020606132c010c0504060e0d080f0c1624230a080406050a0b030304060305041712061203180105070203030c1207032a060207030c0c06020d11010509030717040308 75
    0x82c402c40e8005c5802000c803d41d0300e080d218001441c0104150340c215003c6540d240078070305444043c0607100d1792440c1c040360b00410601091800d541040041c210154400f0020300c00c29a21210083d10b10010307600c0448402c0080081c0940b5010040b500281d103041410302c0920045190f0701c0615205000c01c58090b5142e010030361118655122750ba45024a000e60340c10f0205840700c028809c01c4800d0074100e0b980c181e1042100b00807841c001c2e00060780c454007070188400c04034501000d407040750307201c500d003005885801420428070703103012501c409900008030011810030250b51104070b5958203942c1c860f0b040c8800800d400c0c007107550030021203900000b46000d982c0f88a003118920340c90340e001000200c02141c461105481100a035111944c06c130501d81030f022043d644a619010025880b20909408020b401c950030380110741142c1c0301c803000304203650081c0141d0304002e000426003072604814841507410325044c0550a9400000e0703500c0b03a50015107103400b0750440d5254582c0740c8100d52004000020208 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 68880038 1250 68878788 68878841
    0x3041703180601051f12020f0417100504020109060e030a080403211403010504090609020a030b0a1d0d050901110708011d010b03071e0305060c03070207050901030302060613 76
    0x3454800c0703a078180310840d891641c8030020020181003c1511890082d403010700c041c0e030320303104584250080707030383c00c100615000e21081c030052560b1060f000002c04c501d1505140102c1502001030380304240321407074100154149980000c01c040c03d0f40c8620410004600204003036030380d0a0047c071086551000000340c2e81c41d503929141b08951089200e000706408a0942d1060582c001d503685590106105904c600e10782c2842c041100a0100d048190350f46541d512503000181c40b01c1919002840c01030001ca0b1151810031140c105840e000490400c14002c5403414030800300d0005038903000c2c1400c0e810415250341c030400048624902c005c0ca614024407402c10002500841980101c0d03240c1e074242800c440c0035144903105403d83d0341240b00660550301046007080107043e01c1020001281c0000900358605a0725250980340c500e06850a10406030000705001515030100242402030800352070110856140d910080e4860a0080c440e40c000d01400c00d07450040641a070125580d5202224150840120701 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 68881288 1250 68880038 68880061
    0x6030c031b0a0e04120807030e0a1b060302090a14060c070306060501092c070201021306020c1306030305070303020c0703020d1103010e01020c07031b0e070512070e060d0203041703 79
    0x602845000300e00040340464081c840c82c1a0500c2117070082003030650400c0444c0c08840c00d00d0b00412a0081564511079001c015005002901d2454014410380b9280b01b548060600082c0669200ca801d0610410004002c2e032550141c02045400340001c01111526a81c0490490300c00c003e40d401041c051001c0201c02c1002c142d20270000d45000780e946020b441d440e100491000d0b90b074008040c1005141c40c2c0000c01c1381c0540c0125a600c500d091002500b0102c4003200303030704990b2060300300c5809a00980000380041c10080340903a00d42c01e200c04180101c515685014105208080000e420543c000600f208103003020401d0800940d400ba10032940d440c0d040c10410140c107002c5c00c42511039400d104007002d0002050083c2e500c10307483c01000d03048091540c1c0e50310801c070500c1024154001804203001540510059982d449280c1075141c456480248051010000d40001e016105200c3c01503185640340d01c4002c16100300408124005940c0e0710380d4207103003401001d080400a84010700204100e0784e42c110307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 68882538 1250 68881288 68881333
    0x150204090207120314071e09050402040b04090f0c050f0a0905090f0106030b040905060c07060f0e160608070206040f080d0e032104050a03080705130906030308090309150306030c03 79
    0x60344e020040503841c9000c840c00304806686000004051f50b410114121070141d224800b580c4a04042c2415a501d0303000c07405a0300142d1007000e030008003080800c081806401800701c810081c4500f00800c20401c80c010b000341c0691146d00005104c04102038001030f00075450340c000342238001c110054901d0842d2105091400901480001034100845141c46007401d02075a5000365000010305401d540d00c0d915204960000f22054810329291f2810740c030104040d01c40d2081d80c0796528050402401c04074120503030040c00b0b601580805c60300808000f100c1d070703001c03c0b101d81041e0b10242c01e12400080f070820751500d001c1c1c0da1b2103202e486c0c6020010081e00a00000922a64410b002c00c4940040d8034114200e0340350003110082e000d42c104510080001e80304000080d030203481414030300c2c141502800408540c44a6410514a4a45d2a00c00740185900100c0b06c561000030034005610300062200419089801000082080c0501201040c113a81c1d052024804d2003101408545003034162580440100d0070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 68883788 1250 68882538 68882573
    0x30c16090f0e07060813060515010e1002070506030a060801020a0801030c140901090b040e06070203040315050601050a030e01110d020d050a0903050a110106170a0b0a06060c150204090207 82
    0x94410140d0044a240c00b40c0c0c20002e4090000e4841c091402d141560300c100001d2a801120000d0407507140000c15a201d0705008150712544000201c911500140008410050952140145c00c0f0700108056002a10505683d0142e8100c0e40b680c0b030b185030340ca000d00000d400c903018550006c50300c4000c00e41d100440074100c80c0114588e0320708a5444410b2040c03c0011041e00c0d4005602030f00620001c07078281c002c069541c8006d080010f2a100c10002c16041c24426240000140c000240030014032070203003003803030010010030801c20141c01d102001908605c06d207113402e0203040d281e028500098030298002040c90b1244210a6907848100494000a5001500c061565454800418111441481110421030345902c860f440c040e91000142ca050294030075600f151341d280ea1022801d144a0f0100c4d203560020840200880e1b8580d00d40019204402003010b542d840c40c10104100c060340c04201d80a03882d80041e200440701ca440810200640f00300d4210000650000880381d00b0008580401d03071305c286 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 68884894 1106 68883788 68883791
    0x31803030702071815030312090c1e0b0301031101080907050d03030b010206090604150e010b06031501020f0703081e160305030a1d030a0e03030c1609 66
    0x500c00c0320400016085001c04101110307a078480740d0308000400030b080c40883c6080841c048420021710026080200310361032800c949070300b94004001c842d00710005d204000d468032101c030380c00614094140001c0f06100c0300021400e0325102900d060b80c1e8040302c5418903444050044495107406460902980036404001443e6501c1540d09008a4440c1d02c011070205540320001e41003d200a14408281e0415010440001c0120038000312200700001d00117020b0640c010304a005000181800780c004400105010421611815140f42810241e084039040004001d64036200d0070141701c01011184c0a01800341300024481e0910307604841c0240150804905c690045125202c2c840281d003c02c90010038800d00011901800d001e05103807012804049428180c2642e80c0d2160b03985140800542d5240303510f2983d002c3c012903540074000c4084483d00c840d10168581000c030644550411103 = true := by decide +kernel

theorem cover : BRFrame.Cov 68705038 68884894 := by
  have h0 := BRFrame.cov_init 68705038
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68705038 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 68705038 ≤ n) (h2 : n < 68884894) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
